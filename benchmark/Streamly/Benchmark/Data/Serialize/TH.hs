{-# LANGUAGE TemplateHaskell #-}

module Streamly.Benchmark.Data.Serialize.TH (genLargeRecords) where

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

import Language.Haskell.TH

import Streamly.Internal.Data.Serialize.TH.Bottom (makeI)
import Test.QuickCheck.Arbitrary (Arbitrary(..))
import Control.DeepSeq (NFData(..))

--------------------------------------------------------------------------------
-- Large Record
--------------------------------------------------------------------------------

genLargeRecords :: String -> Int -> Q [Dec]
genLargeRecords tyName numFields =
    sequence
        ([ dataD
               (pure [])
               (mkName tyNameL)
               []
               Nothing
               [mkCon tyNameL]
               [derivClause Nothing [conT ''Eq, conT ''Show]]
         , dataD
               (pure [])
               (mkName tyNameR)
               []
               Nothing
               [mkCon tyNameR]
               [derivClause Nothing [conT ''Eq, conT ''Show]]
         , mkConversionSigDec
         , mkConversionDec
         , instanceD
               (pure [])
               (appT (conT ''Arbitrary) (conT (mkName tyNameL)))
               [ funD
                     'arbitrary
                     [clause [] (normalB (mkArbitraryExp tyNameL)) []]
               ]
         , nfDataInstance tyNameL
         , nfDataInstance tyNameR
         ])
  where
    tyNameL = tyName ++ "_L"
    tyNameR = tyName ++ "_R"
    fieldTypeChoices = [conT ''()]
    chooseCycle i xs = xs !! (i `mod` length xs)
    nfDataInstance nm =
        instanceD
            (pure [])
            (appT (conT ''NFData) (conT (mkName nm)))
            [ funD
                  'rnf
                  [ clause
                        [ conP
                              (mkName nm)
                              (varP . makeI <$> [0 .. (numFields - 1)])
                        ]
                        (normalB
                             (foldl
                                  (\b a -> [|rnf $(b) `seq` rnf $(a)|])
                                  [|()|]
                                  (varE . makeI <$> [0 .. (numFields - 1)])))
                        []
                  ]
            ]
    mkArbitraryExp nm =
        foldl
            (\b a -> [|$(b) <*> $(a)|])
            [|pure $(conE (mkName nm))|]
            (replicate numFields (varE 'arbitrary))
    conversionFuncName = (mkName ("convert_" ++ tyNameL ++ "_to_" ++ tyNameR))
    mkConversionSigDec =
        sigD
            conversionFuncName
            [t|$(conT (mkName tyNameL)) -> $(conT (mkName tyNameR))|]
    mkConversionDec =
        funD
            conversionFuncName
            [ clause
                  [ conP
                        (mkName tyNameL)
                        (varP . makeI <$> [0 .. (numFields - 1)])
                  ]
                  (normalB
                       (foldl
                            (\b a -> [|$(b) $(a)|])
                            (conE (mkName tyNameR))
                            (varE . makeI <$> [0 .. (numFields - 1)])))
                  []
            ]
    mkCon nm = recC (mkName nm) (mkField <$> [0 .. (numFields - 1)])
    mkField i =
        varBangType
            (mkName ("field" ++ show i))
            (bangType
                 (bang noSourceUnpackedness noSourceStrictness)
                 (chooseCycle i fieldTypeChoices))
