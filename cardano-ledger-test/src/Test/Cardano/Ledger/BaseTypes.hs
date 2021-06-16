{-# LANGUAGE ScopedTypeVariables #-}

module Test.Cardano.Ledger.BaseTypes where

import Cardano.Ledger.BaseTypes
import Data.Aeson
import Data.Either
import Data.GenValidity (genValid)
import Data.GenValidity.Scientific ()
import Data.Maybe
import Data.Scientific
import Data.Word
import Test.QuickCheck
import Test.Shelley.Spec.Ledger.Serialisation.EraIndepGenerators ()
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

baseTypesTests :: TestTree
baseTypesTests = do
  testGroup
    "UnitInterval"
    [ testProperty
        "Rational roundtrip (boundRational . unboundRational)"
        $ \(ui :: UnitInterval) ->
          Just ui === boundRational (unboundRational ui),
      testProperty "bounding produces valid values" $
        forAll genValid $ \r ->
          case boundRational r of
            Nothing ->
              r > unboundRational (maxBound :: UnitInterval)
                .||. r < unboundRational (minBound :: UnitInterval)
            Just (ui :: UnitInterval) -> ui <= maxBound .&&. ui >= minBound,
      testGroup
        "fromScientificUnitInterval"
        [ localOption (mkTimeout 500000) $
            testCase "Check divergence" $
              expectLeft (fromScientificUnitInterval (scientific 10 1234567893456)),
          testCase "Check overflow" $
            expectLeft (fromScientificUnitInterval 3.00141592653589793e-7),
          testCase "Check too big" $
            expectLeft (fromScientificUnitInterval 1.01),
          testCase "Check negative" $
            expectLeft (fromScientificUnitInterval (-1e-3)),
          testProperty "Scientific valid roundtrip" $ \ui ->
            case fromRationalRepetendLimited 20 (unboundRational ui) of
              Left (s, r) ->
                Just ui === boundRational (toRational s + r)
              Right (s, Nothing) ->
                classify
                  True
                  "no-repeat digits"
                  (Right ui === fromScientificUnitInterval s)
              Right (s, Just r) ->
                Just ui === boundRational (toRationalRepetend s r),
          localOption (mkTimeout 500000) $
            testProperty
              "Scientific roundtrip (fromRational . unboundRational . fromScientific)"
              $ forAll genValid $ \s ->
                case fromScientificUnitInterval s of
                  Right ui -> s === fromRational (unboundRational ui)
                  Left _ ->
                    s < 0 .||. s > 1
                      .||. isNothing
                        (toBoundedInteger (s * 10 ^ (19 :: Int)) :: Maybe Word64)
        ],
      testGroup
        "JSON"
        [ testProperty "ToJSON/FromJSON roundtrip up to an epsilon" $ \(ui :: UnitInterval) ->
            within 500000 $
              case eitherDecode (encode ui) of
                Left err -> error err
                Right (ui' :: UnitInterval) ->
                  abs (unboundRational ui - unboundRational ui')
                    < 1e-18
        ]
    ]
  where
    expectLeft = assertBool "Expected Left" . isLeft
