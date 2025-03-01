{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Cardano.Ledger.Alonzo.TxInfo where

-- =============================================

import Cardano.Crypto.Hash.Class (Hash (UnsafeHash))
import Cardano.Ledger.Alonzo.Data (Data (..), getPlutusData)
import Cardano.Ledger.Alonzo.Scripts (CostModel (..), ExUnits (..), Script (..))
import Cardano.Ledger.Alonzo.Tx
import Cardano.Ledger.Alonzo.TxBody
  ( certs',
    inputs',
    mint',
    outputs',
    reqSignerHashes',
    txfee',
    vldt',
    wdrls',
  )
import qualified Cardano.Ledger.Alonzo.TxBody as Alonzo (TxBody (..), TxOut (..))
import Cardano.Ledger.Alonzo.TxWitness (TxWitness, unTxDats)
import Cardano.Ledger.BaseTypes (StrictMaybe (..))
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Core as Core (TxBody, TxOut, Value)
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Keys (KeyHash (..), hashKey)
import qualified Cardano.Ledger.Mary.Value as Mary (AssetName (..), PolicyID (..), Value (..))
import Cardano.Ledger.SafeHash
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..))
import Cardano.Ledger.Val (Val (..))
import Cardano.Slotting.EpochInfo (EpochInfo, epochInfoSlotToUTCTime)
import Cardano.Slotting.Slot (EpochNo (..), SlotNo (..))
import Cardano.Slotting.Time (SystemStart)
import Control.DeepSeq (deepseq)
import Data.ByteString as BS (ByteString, length)
import Data.ByteString.Short as SBS (ShortByteString, fromShort)
import Data.Fixed (HasResolution (resolution))
import Data.Functor.Identity (Identity, runIdentity)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Data.Time.Clock (nominalDiffTimeToSeconds)
import Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds)
import Data.Typeable (Typeable)
import GHC.Records (HasField (..))
import qualified Plutus.V1.Ledger.Ada as P (adaSymbol, adaToken)
import qualified Plutus.V1.Ledger.Address as P (Address (..))
import qualified Plutus.V1.Ledger.Api as P
  ( DCert (..),
    ExBudget (..),
    VerboseMode (..),
    evaluateScriptRestricting,
    validateScript,
  )
import qualified Plutus.V1.Ledger.Contexts as P
  ( ScriptContext (..),
    ScriptPurpose (..),
    TxInInfo (..),
    TxInfo (..),
    TxOut (..),
  )
import qualified Plutus.V1.Ledger.Credential as P (Credential (..), StakingCredential (..))
import qualified Plutus.V1.Ledger.Crypto as P (PubKeyHash (..))
import qualified Plutus.V1.Ledger.Interval as P
  ( Extended (..),
    Interval (..),
    LowerBound (..),
    UpperBound (..),
    always,
  )
import qualified Plutus.V1.Ledger.Scripts as P (Datum (..), DatumHash (..), ValidatorHash (..))
import qualified Plutus.V1.Ledger.Time as P (POSIXTime (..), POSIXTimeRange)
import qualified Plutus.V1.Ledger.Tx as P (TxOutRef (..))
import qualified Plutus.V1.Ledger.TxId as P (TxId (..))
import qualified Plutus.V1.Ledger.Value as P (CurrencySymbol (..), TokenName (..), Value (..), singleton, unionWith)
import qualified PlutusCore.Evaluation.Machine.ExMemory as P (ExCPU (..), ExMemory (..))
import qualified PlutusTx as P (Data (..))
import qualified PlutusTx.IsData.Class as P (IsData (..))
import Shelley.Spec.Ledger.Address (Addr (..), RewardAcnt (..))
import Shelley.Spec.Ledger.Credential (Credential (KeyHashObj, ScriptHashObj), Ptr (..), StakeReference (..))
import Shelley.Spec.Ledger.Scripts (ScriptHash (..))
import Shelley.Spec.Ledger.TxBody
  ( DCert (..),
    DelegCert (..),
    Delegation (..),
    PoolCert (..),
    PoolParams (..),
    TxId (..),
    TxIn (..),
    Wdrl (..),
    WitVKey (..),
  )
import Shelley.Spec.Ledger.UTxO (UTxO (..))

-- =========================================================
-- Translate Hashes, Credentials, Certificates etc.

transDataHash :: StrictMaybe (DataHash c) -> Maybe P.DatumHash
transDataHash (SJust safe) = Just (transDataHash' safe)
transDataHash SNothing = Nothing

transDataHash' :: (DataHash c) -> P.DatumHash
transDataHash' safe = (P.DatumHash (transSafeHash safe))

transKeyHash :: KeyHash d c -> P.PubKeyHash
transKeyHash (KeyHash (UnsafeHash h)) = P.PubKeyHash (fromShort h)

transScriptHash :: ScriptHash i -> P.ValidatorHash
transScriptHash (ScriptHash (UnsafeHash h)) = P.ValidatorHash (fromShort h)

transSafeHash :: SafeHash c i -> BS.ByteString
transSafeHash safe = case extractHash safe of UnsafeHash b -> fromShort b

transHash :: Hash h a -> BS.ByteString
transHash (UnsafeHash h) = fromShort h

txInfoId :: TxId era -> P.TxId
txInfoId (TxId safe) = P.TxId (transSafeHash safe)

transStakeCred :: Credential keyrole crypto -> BS.ByteString
transStakeCred (ScriptHashObj (ScriptHash (UnsafeHash kh))) = (fromShort kh)
transStakeCred (KeyHashObj (KeyHash (UnsafeHash kh))) = (fromShort kh)

transStakeReference :: StakeReference crypto -> Maybe P.StakingCredential
transStakeReference (StakeRefBase cred) = Just (P.StakingHash (transStakeCred cred))
transStakeReference (StakeRefPtr (Ptr (SlotNo slot) i1 i2)) = Just (P.StakingPtr (fromIntegral slot) (fromIntegral i1) (fromIntegral i2))
transStakeReference StakeRefNull = Nothing

transCred :: Credential keyrole crypto -> P.Credential
transCred (KeyHashObj (KeyHash (UnsafeHash kh))) = P.PubKeyCredential (P.PubKeyHash (fromShort kh))
transCred (ScriptHashObj (ScriptHash (UnsafeHash kh))) = P.ScriptCredential (P.ValidatorHash (fromShort kh))

transAddr :: Addr crypto -> Maybe P.Address
transAddr (Addr _net object stake) = Just (P.Address (transCred object) (transStakeReference stake))
transAddr (AddrBootstrap _bootaddr) = Nothing

slotToPOSIXTime ::
  EpochInfo Identity ->
  SystemStart ->
  SlotNo ->
  P.Extended P.POSIXTime
slotToPOSIXTime ei sysS s =
  P.Finite . P.POSIXTime . resolution . nominalDiffTimeToSeconds . utcTimeToPOSIXSeconds . runIdentity $
    epochInfoSlotToUTCTime ei sysS s

-- | translate a validity interval to POSIX time
transVITime ::
  EpochInfo Identity ->
  SystemStart ->
  ValidityInterval ->
  P.POSIXTimeRange
transVITime _ _ (ValidityInterval SNothing SNothing) = P.always
transVITime ei sysS (ValidityInterval (SJust i) SNothing) =
  P.Interval
    (P.LowerBound (slotToPOSIXTime ei sysS i) True)
    (P.UpperBound P.PosInf True)
transVITime ei sysS (ValidityInterval SNothing (SJust i)) =
  P.Interval
    (P.LowerBound P.NegInf True)
    (P.UpperBound (slotToPOSIXTime ei sysS i) False)
transVITime ei sysS (ValidityInterval (SJust i) (SJust j)) =
  P.Interval
    (P.LowerBound (slotToPOSIXTime ei sysS i) True)
    (P.UpperBound (slotToPOSIXTime ei sysS j) False)

-- ========================================
-- translate TxIn and TxOut

txInfoIn' :: CC.Crypto c => TxIn c -> P.TxOutRef
txInfoIn' (TxIn txid nat) = P.TxOutRef (txInfoId txid) (fromIntegral nat)

-- | Given a TxIn, look it up in the UTxO. If it exists, translate it and return
--   (Just translation). If does not exist in the UTxO, return Nothing.
txInfoIn ::
  forall era.
  ( Era era,
    Value era ~ Mary.Value (Crypto era),
    Core.TxOut era ~ Alonzo.TxOut era
  ) =>
  UTxO era ->
  TxIn (Crypto era) ->
  Maybe (P.TxInInfo)
txInfoIn (UTxO mp) txin =
  case Map.lookup txin mp of
    Nothing -> Nothing
    Just txout -> case (transAddr addr) of
      Just ad -> Just (P.TxInInfo (txInfoIn' txin) (P.TxOut ad valout dhash))
      Nothing -> Nothing
      where
        valout = transValue (getField @"value" txout)
        addr = getField @"address" txout
        dhash = case getField @"datahash" txout of
          SNothing -> Nothing
          SJust (safehash) -> Just (P.DatumHash (transSafeHash safehash))

-- | Given a TxOut, translate it and return (Just transalation). It is
--   possible the address part is a Bootstrap Address, in that case return Nothing
--   I.e. don't include Bootstrap Addresses in the answer.
txInfoOut ::
  forall era.
  ( Era era,
    Value era ~ Mary.Value (Crypto era)
  ) =>
  Alonzo.TxOut era ->
  Maybe (P.TxOut)
txInfoOut (Alonzo.TxOut addr val datahash) =
  case (transAddr addr) of
    Just ad -> Just (P.TxOut ad (transValue @(Crypto era) val) (transDataHash datahash))
    Nothing -> Nothing

-- ==================================
-- translate Values

transPolicyID :: Mary.PolicyID crypto -> P.CurrencySymbol
transPolicyID (Mary.PolicyID (ScriptHash (UnsafeHash x))) = P.CurrencySymbol (fromShort x)

transAssetName :: Mary.AssetName -> P.TokenName
transAssetName (Mary.AssetName bs) = P.TokenName bs

transValue :: forall c. Mary.Value c -> P.Value
transValue (Mary.Value n mp) = Map.foldlWithKey' accum1 justada mp
  where
    accum1 ans sym mp2 = Map.foldlWithKey' accum2 ans mp2
      where
        accum2 ans2 tok quantity =
          P.unionWith
            (+)
            ans2
            (P.singleton (transPolicyID sym) (transAssetName tok) quantity)
    justada = P.singleton P.adaSymbol P.adaToken n

-- =============================================
-- translate fileds like DCert, Wdrl, and similar

transDCert :: DCert c -> P.DCert
transDCert (DCertDeleg (RegKey stkcred)) =
  P.DCertDelegRegKey (P.StakingHash (transStakeCred stkcred))
transDCert (DCertDeleg (DeRegKey stkcred)) =
  P.DCertDelegDeRegKey (P.StakingHash (transStakeCred stkcred))
transDCert (DCertDeleg (Delegate (Delegation stkcred keyhash))) =
  P.DCertDelegDelegate
    (P.StakingHash (transStakeCred stkcred))
    (transKeyHash keyhash)
transDCert (DCertPool (RegPool pp)) =
  P.DCertPoolRegister (transKeyHash (_poolId pp)) (P.PubKeyHash (transHash (_poolVrf pp)))
transDCert (DCertPool (RetirePool keyhash (EpochNo i))) =
  P.DCertPoolRetire (transKeyHash keyhash) (fromIntegral i)
transDCert (DCertGenesis _) = P.DCertGenesis
transDCert (DCertMir _) = P.DCertMir

transWdrl :: Wdrl crypto -> Map.Map P.StakingCredential Integer
transWdrl (Wdrl mp) = Map.foldlWithKey' accum Map.empty mp
  where
    accum ans (RewardAcnt _network cred) (Coin n) = Map.insert (P.StakingHash (transStakeCred cred)) n ans

getWitVKeyHash :: (CC.Crypto crypto, Typeable kr) => WitVKey kr crypto -> P.PubKeyHash
getWitVKeyHash = P.PubKeyHash . fromShort . (\(UnsafeHash x) -> x) . (\(KeyHash x) -> x) . hashKey . (\(WitVKey x _) -> x)

transDataPair :: (DataHash c, Data era) -> (P.DatumHash, P.Datum)
transDataPair (x, y) = (transDataHash' x, P.Datum (getPlutusData y))

transExUnits :: ExUnits -> P.ExBudget
transExUnits (ExUnits mem steps) = P.ExBudget (P.ExCPU (fromIntegral steps)) (P.ExMemory (fromIntegral mem))

-- ===================================
-- translate Script Purpose

transScriptPurpose :: CC.Crypto crypto => ScriptPurpose crypto -> P.ScriptPurpose
transScriptPurpose (Minting policyid) = P.Minting (transPolicyID policyid)
transScriptPurpose (Spending txin) = P.Spending (txInfoIn' txin)
transScriptPurpose (Rewarding (RewardAcnt _network cred)) = P.Rewarding (P.StakingHash (transStakeCred cred))
transScriptPurpose (Certifying dcert) = P.Certifying (transDCert dcert)

-- ===================================

-- | Compute a Digest of the current transaction to pass to the script
--   This is the major component of the valContext function.
txInfo ::
  forall era tx.
  ( Era era,
    Core.TxOut era ~ Alonzo.TxOut era,
    Core.TxBody era ~ Alonzo.TxBody era,
    Value era ~ Mary.Value (Crypto era),
    HasField "body" tx (Core.TxBody era),
    HasField "wits" tx (TxWitness era)
  ) =>
  EpochInfo Identity ->
  SystemStart ->
  UTxO era ->
  tx ->
  P.TxInfo
txInfo ei sysS utxo tx =
  P.TxInfo
    { P.txInfoInputs = mapMaybe (txInfoIn utxo) (Set.toList (inputs' tbody)),
      P.txInfoOutputs = mapMaybe txInfoOut (foldr (:) [] outs),
      P.txInfoFee = (transValue (inject @(Mary.Value (Crypto era)) fee)),
      P.txInfoForge = (transValue forge),
      P.txInfoDCert = (foldr (\c ans -> transDCert c : ans) [] (certs' tbody)),
      P.txInfoWdrl = Map.toList (transWdrl (wdrls' tbody)),
      P.txInfoValidRange = transVITime ei sysS interval,
      P.txInfoSignatories = map transKeyHash (Set.toList (reqSignerHashes' tbody)),
      P.txInfoData = (map transDataPair datpairs),
      P.txInfoId = (P.TxId (transSafeHash (hashAnnotated @(Crypto era) tbody)))
    }
  where
    tbody = getField @"body" tx
    _witnesses = getField @"wits" tx
    outs = outputs' tbody
    fee = txfee' tbody
    forge = mint' tbody
    interval = vldt' tbody
    datpairs = Map.toList (unTxDats $ txdats' _witnesses)

-- ===============================================================
-- From the specification, Figure 7 "Script Validation, cont."
-- ===============================================================

-- | valContext collects info from the Tx and the UTxO an
--   translates it into a 'Data', which the Plutus language knows how to interpret.
--   The UTxO and the PtrMap are used to 'resolve' the TxIn and the StakeRefPtr's
valContext ::
  Era era =>
  P.TxInfo ->
  ScriptPurpose (Crypto era) ->
  Data era
valContext txinfo sp = Data (P.toData (P.ScriptContext txinfo (transScriptPurpose sp)))

-- The runPLCScript in the Specification has a slightly different type
-- than the one in the implementation below. Made necessary by the the type
-- of P.evaluateScriptRestricting which is the interface to Plutus

-- | Run a Plutus Script, given the script and the bounds on resources it is allocated.
runPLCScript :: CostModel -> SBS.ShortByteString -> ExUnits -> [P.Data] -> Bool
runPLCScript (CostModel cost) scriptbytestring units ds =
  case P.evaluateScriptRestricting
    P.Quiet
    cost
    (transExUnits units)
    scriptbytestring
    ds of
    (_, Left _e) -> False -- trace ("\nrunPLC fails "++show _e++"\nData = "++show ds) False
    (_, Right ()) -> True

validPlutusdata :: P.Data -> Bool
validPlutusdata (P.Constr _n ds) = all validPlutusdata ds
validPlutusdata (P.Map ds) =
  all (\(x, y) -> validPlutusdata x && validPlutusdata y) ds
validPlutusdata (P.List ds) = all validPlutusdata ds
validPlutusdata (P.I _n) = True
validPlutusdata (P.B bs) = BS.length bs <= 64

-- | Test that every Alonzo script represents a real Script.
--     Run deepseq to see that there are no infinite computations and that
--     every Plutus Script unflattens into a real P.Script
validScript :: Script era -> Bool
validScript scrip = case scrip of
  TimelockScript sc -> deepseq sc True
  PlutusScript bytes -> P.validateScript bytes
