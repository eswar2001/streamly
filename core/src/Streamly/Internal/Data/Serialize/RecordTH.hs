{-# LANGUAGE TemplateHaskell #-}

-- |
-- Module      : Streamly.Internal.Data.Serialize.RecordTH
-- Copyright   : (c) 2023 Composewell Technologies
-- License     : BSD3-3-Clause
-- Maintainer  : streamly@composewell.com
-- Stability   : experimental
-- Portability : GHC
--
-- This module provides TH helpers to derive backward compatible Serialize
-- instances for single constructor records.
--
module Streamly.Internal.Data.Serialize.RecordTH
    ( deriveSerialize
    , deriveSerializeWith
    ) where

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

import GHC.Ptr (Ptr(..), plusPtr)
import Control.Monad (void)
import Data.List (sortBy)
import Data.Maybe (fromJust, fromMaybe)
import Data.Word (Word32, Word8)
import Data.Char (ord)
import Streamly.Internal.Data.MutArray.Type (memcmp1)

import qualified Foreign.Storable as Storable
import Streamly.Internal.System.IO (unsafeInlineIO)

import Language.Haskell.TH
import Streamly.Internal.Data.Serialize

import qualified Streamly.Internal.Data.Unbox as Unbox

import Streamly.Internal.Data.Unbox (MutableByteArray, getMutableByteArray#)
import GHC.Exts (byteArrayContents#, unsafeCoerce#)

import qualified Streamly.Internal.Data.Array.Type as Array

import Streamly.Internal.Data.Unbox.TH
    ( DataCon(..)
    , DataType(..)
    , appsT
    , plainInstanceD
    , reifyDataType
    )

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

type Field = (Maybe Name, Type)

n_x :: Name
n_x = mkName "x"

n_arr :: Name
n_arr = mkName "arr"

n_initialOffset :: Name
n_initialOffset = mkName "initialOffset"

n_val :: Name
n_val = mkName "val"

mkFieldName :: Int -> Name
mkFieldName i = mkName ("field" ++ show i)

makeIT :: Int -> Int -> Name
makeIT i t = mkName $ "i" ++ show i ++ "t" ++ show t

makeI :: Int -> Name
makeI i = mkName $ "i" ++ show i

n_finalOffOff :: Name
n_finalOffOff = mkName "finalOffOff"

n_finalOff :: Name
n_finalOff = mkName "finalOff"

n_tagArr :: Name
n_tagArr = mkName "tagArr"

n_acc :: Name
n_acc = mkName "acc"

n_capacityOff :: Name
n_capacityOff = mkName "capacityOff"

--------------------------------------------------------------------------------
-- Domain specific helpers
--------------------------------------------------------------------------------

litIntegral :: Integral a => a -> Q Exp
litIntegral i = litE (IntegerL (fromIntegral i))

verifySortedFields :: [Field] -> [Field]
verifySortedFields fields =
    let sortedFields = sortBy cmpF fields
     in if sortedFields == fields
            then fields
            else error
                     ("The fields are not sorted, the correct order is: " ++
                      show (map (nameBase . fromJust . fst) sortedFields))
  where
    cmpF (Just tag1, _) (Just tag2, _) =
        let t1 = nameBase tag1
            t2 = nameBase tag2
         in case compare (length t1) (length t2) of
                EQ -> compare t1 t2
                cmpRes -> cmpRes
    cmpF _ _ = error "Cant use non-tagged value"

matchConstructor :: Name -> Int -> Q Exp -> Q Match
matchConstructor cname numFields exp0 =
    match
        (conP cname (map varP (map mkFieldName [0 .. (numFields - 1)])))
        (normalB exp0)
        []

isMaybeType :: Type -> Bool
isMaybeType (AppT (ConT m) _) = m == ''Maybe
isMaybeType _ = False

exprGetSize :: (Int, Field) -> Q Exp
exprGetSize (_, (Nothing, _)) = error "Cant use non-tagged value"
exprGetSize (i, (Just tag, ty)) =
    let lenTag = length (nameBase tag)
        common = 1 + lenTag + 4
        commonExp = litIntegral common
     in if isMaybeType ty
            then [|case $(varE (mkFieldName i)) of
                       Nothing -> 0
                       Just x ->
                           case size of
                               Size f -> f 0 x + $(commonExp)|]
            else [|case $(varE (mkFieldName i)) of
                       x ->
                           case size of
                               Size f -> f 0 x + $(commonExp)|]

--------------------------------------------------------------------------------
-- Size
--------------------------------------------------------------------------------

isUnitType :: [DataCon] -> Bool
isUnitType [DataCon _ _ _ []] = True
isUnitType _ = False

mkSizeOfExpr :: Type -> [DataCon] -> Q Exp
mkSizeOfExpr headTy constructors =
    case constructors
        -- One constructor with no fields is a unit type. Size of a unit type is
        -- 1.
          of
        [constructor@(DataCon _ _ _ (_:_))] ->
            appE
                (conE 'Size)
                (lamE
                     [varP n_acc, varP n_x]
                     (caseE (varE n_x) [matchCons (varE n_acc) constructor]))
        _ ->
            error $
            unlines
                [ "The datatype should have exatcly 1 constructor."
                , "It has " ++ lenConsStr ++ "."
                , "See " ++ headTyStr
                ]
  where
    headTyStr = pprint headTy
    lenConsStr = show $ length constructors
    sizeOfFields acc fields =
        [|$(acc) + 4 +
          $(appE (varE 'sum) (listE (map exprGetSize (zip [0 ..] fields))))|]
    matchCons acc (DataCon cname _ _ fields) =
        matchConstructor cname (length fields) (sizeOfFields acc fields)

--------------------------------------------------------------------------------
-- Peek
--------------------------------------------------------------------------------

w32ToInt :: Word32 -> Int
w32ToInt = fromIntegral

skipFieldRF ::
       Serialize a
    => Ptr Word8
    -> Int
    -> Int
    -> Int
    -> MutableByteArray
    -> Int
    -> IO (Int, Maybe a)
skipFieldRF tagVal tagLen finalOff afterTagOff arr capacityOff = do
    let nextFieldOffOff = afterTagOff
    (_, nextFieldOff) <- deserialize nextFieldOffOff arr capacityOff
    deserializeRF tagVal tagLen finalOff (w32ToInt nextFieldOff) arr capacityOff

checkTagRF ::
       Serialize a
    => Ptr Word8
    -> Int
    -> Int
    -> Int
    -> Int
    -> MutableByteArray
    -> Int
    -> IO (Int, Maybe a)
checkTagRF tagVal tagLen finalOff backOff tagOff arr capacityOff = do
    case memcmpCStr tagVal arr tagOff tagLen of
        EQ ->
            let newOff = afterTagOff + 4
             in fmap Just <$> deserialize newOff arr capacityOff
        GT -> pure (backOff, Nothing)
        LT -> skipFieldRF tagVal tagLen finalOff afterTagOff arr capacityOff
  where
    afterTagOff = tagLen + tagOff
    slice = Array.Array arr tagOff afterTagOff

deserializeRF ::
       Serialize a
    => Ptr Word8
    -> Int
    -> Int
    -> Int
    -> MutableByteArray
    -> Int
    -> IO (Int, Maybe a)
deserializeRF tagVal tagLen finalOff off arr capacityOff =
    if off >= finalOff
        then pure (off, Nothing)
        else do
            (tagOff, curTagLen) <- deserialize off arr capacityOff
            case curTagLen :: Word8 of
                x
                    | x == tagLenW8 ->
                        checkTagRF
                            tagVal tagLen finalOff off tagOff arr capacityOff
                    | x > tagLenW8 -> pure (off, Nothing)
                    | otherwise ->
                        let afterTagOff = fromIntegral curTagLen + tagOff
                         in skipFieldRF
                              tagVal tagLen finalOff afterTagOff arr capacityOff
  where
    tagLenW8 = fromIntegral tagLen

data DeserializeBindingNames =
    DeserializeBindingNames
        { bnOffset :: Name
        , bnFinalOff :: Name
        , bnArr :: Name
        , bnTagArr :: Name
        , bnTagOff :: Name
        , bnTagLen :: Name
        , bnAfterTagOff :: Name
        }

mapWithLast :: (a -> b) -> (a -> b) -> [a] -> [b]
mapWithLast _ _ [] = []
mapWithLast _ ifLast (x:[]) = ifLast x : []
mapWithLast ifNotLast ifLast (x:xs) =
    ifNotLast x : mapWithLast ifNotLast ifLast xs

{-# INLINE memcmpCStr #-}
memcmpCStr :: Ptr Word8 -> MutableByteArray -> Int -> Int -> Ordering
memcmpCStr ptr0 arr off len = go ptr0 off
  where
    end = off + len
    go _ i
        | i >= end = EQ
    go ptr i =
        case compare
                 (unsafeInlineIO (Unbox.peekByteIndex i arr))
                 (unsafeInlineIO (Storable.peek ptr)) of
            EQ -> go (ptr `plusPtr` 1) (i + 1)
            GT -> GT
            LT -> LT

mkDeserializeExprOne :: DataCon -> Q Exp
mkDeserializeExprOne (DataCon cname _ _ fields) =
    case verifySortedFields fields of
        [] -> [|pure ($(varE (mkName "i0")), $(conE cname))|]
        _ ->
            doE
                (bindS
                     (tupP [varP (makeI 0), varP n_finalOff])
                     [|fmap w32ToInt <$>
                       deserialize
                           $(varE n_finalOffOff)
                           $(varE n_arr)
                           $(varE n_capacityOff)|] :
                 mapWithLast
                     (makeBind False)
                     (makeBind True)
                     (zip [0 ..] fields) ++
                 [ noBindS
                       [|pure
                             ( $(varE n_finalOff)
                             , $(appsE
                                     (conE cname :
                                      (varE . mkFieldName <$>
                                       [0 .. (lenFields - 1)]))))|]
                 ])
  where
    lenFields = length fields
    skipField j bn@(DeserializeBindingNames {..}) field = do
        bnOffset1 <- newName "offset"
        bnTagLen1 <- newName "tagLen"
        bnTagOff1 <- newName "tagOff"
        bnAfterTagOff1 <- newName "afterTagOff"
        let bn1 =
                bn
                    { bnOffset = bnOffset1
                    , bnTagLen = bnTagLen1
                    , bnTagOff = bnTagOff1
                    , bnAfterTagOff = bnAfterTagOff1
                    }
        [|do let nextFieldOffOff =
                     fromIntegral $(varE bnTagLen) + $(varE bnTagOff)
             (_, nextFieldOff) <-
                 deserialize
                     nextFieldOffOff
                     $(varE bnArr)
                     $(varE n_capacityOff)
             let $(varP bnOffset1) = w32ToInt nextFieldOff
             $(makeBindBody j bn1 field)|]
    ifTagEqExp (DeserializeBindingNames {..}) ty = do
        let isMType = isMaybeType ty
        if isMType
            then [|let off = $(varE bnAfterTagOff) + 4
                    in do (off1, val) <-
                              deserialize
                                  off
                                  $(varE bnArr)
                                  $(varE n_capacityOff)
                          pure (off1, Just val)|]
            else [|let off = $(varE bnAfterTagOff) + 4
                    in do (off1, val) <-
                              deserialize
                                  off
                                  $(varE bnArr)
                                  $(varE n_capacityOff)
                          pure (off1, val)|]
    checkTag _ _ (_, (Nothing, _)) = error "Cant use non-tagged value"
    checkTag j bn@(DeserializeBindingNames {..}) field@(_, (Just tag, ty)) = do
        let nothingExp =
                let errStr = litE (StringL (nameBase tag ++ " is not found."))
                 in if isMaybeType ty
                        then [|Nothing|]
                        else [|error $(errStr)|]
            tagLenAbs = litIntegral (length (nameBase tag))
        [|case memcmpCStr
                   $(varE bnTagArr)
                   $(varE bnArr)
                   $(varE bnTagOff)
                   $(tagLenAbs) of
              EQ -> $(ifTagEqExp bn ty)
              GT -> pure ($(varE bnOffset), $(nothingExp))
              LT -> $(skipField (j - 1) bn field)|]
    makeBind _ (_, (Nothing, _)) = error "Cant use non-tagged value"
    makeBind isLastStmt f@(i, (Just tag, _)) = do
        let tagBase = litE (StringPrimL (c2w <$> nameBase tag))
        bnTagLen <- newName "tagLen"
        bnTagOff <- newName "tagOff"
        bnAfterTagOff <- newName "afterTagOff"
        bindS
            (if isLastStmt
                 then tupP [wildP, varP (mkFieldName i)]
                 else tupP [varP (makeI (i + 1)), varP (mkFieldName i)])
            -- XXX Can we ensure there is let-floating? We don't want to compute
            -- this always.
            ([|let $(varP n_tagArr) = Ptr $(tagBase) :: Ptr Word8
                in $(makeBindBody
                         (0 :: Int)
                         (DeserializeBindingNames
                              { bnOffset = makeI i
                              , bnFinalOff = n_finalOff
                              , bnArr = n_arr
                              , bnTagArr = n_tagArr
                              , bnTagOff = bnTagOff
                              , bnTagLen = bnTagLen
                              , bnAfterTagOff = bnAfterTagOff
                              })
                         f)|])
    makeBindBody _ _ (_, (Nothing, _)) = error "Cant use non-tagged value"
    makeBindBody j (DeserializeBindingNames {..}) (_, (Just tag, ty))
        | j < 0 =
            let tagStr = nameBase tag
                lenTag = length tagStr
                isMType = isMaybeType ty
                errStr = litE (StringL (tagStr ++ " is not found."))
             in if isMType
                    then [|deserializeRF
                               $(varE bnTagArr)
                               $(litIntegral lenTag)
                               $(varE bnFinalOff)
                               $(varE bnOffset)
                               $(varE bnArr)
                               $(varE n_capacityOff)|]
                    else [|fmap (fromMaybe (error $(errStr))) <$>
                           deserializeRF
                               $(varE bnTagArr)
                               $(litIntegral lenTag)
                               $(varE bnFinalOff)
                               $(varE bnOffset)
                               $(varE bnArr)
                               $(varE n_capacityOff)|]
    makeBindBody j bn@(DeserializeBindingNames {..}) field@(i, (Just tag, ty)) =
        let tagStr = nameBase tag
            lenTagBaseRaw = length tagStr
            lenTagBase =
                if lenTagBaseRaw > 63
                    then error "Tags with length > 63 are not supported"
                    else i2w lenTagBaseRaw :: Word8
            nothingExp =
                let errStr = litE (StringL (nameBase tag ++ " is not found."))
                 in if isMaybeType ty
                        then [|Nothing|]
                        else [|error $(errStr)|]
         in [|if $(varE bnOffset) >= $(varE bnFinalOff)
                  then pure ($(varE (makeI i)), $(nothingExp))
                  else do
                      ($(varP bnTagOff), $(varP bnTagLen)) <-
                          deserialize
                              $(varE bnOffset)
                              $(varE bnArr)
                              $(varE n_capacityOff)
                      case $(varE bnTagLen) :: Word8 of
                          x
                              | x == $(litIntegral lenTagBase) ->
                                  let $(varP bnAfterTagOff) =
                                          $(varE bnTagOff) +
                                          fromIntegral $(varE bnTagLen)
                                   in $(checkTag j bn field)
                              | x > $(litIntegral lenTagBaseRaw) ->
                                  pure ($(varE bnOffset), $(nothingExp))
                              | otherwise -> $(skipField (j - 1) bn field)|]

mkDeserializeExpr :: Type -> [DataCon] -> Q Exp
mkDeserializeExpr headTy cons =
    case cons of
        [(DataCon cname _ _ [])] ->
            [|pure ($(varE n_initialOffset) + 1, $(conE cname))|]
        [con] ->
            letE
                [valD (varP n_finalOffOff) (normalB (varE n_initialOffset)) []]
                (mkDeserializeExprOne con)
        _ -> error
                 $ unlines
                       [ "The datatype should have exatcly 1 constructor."
                       , "It has " ++ lenConsStr ++ "."
                       , "See " ++ headTyStr
                       ]


  where
    lenCons = length cons
    lenConsStr = show lenCons
    headTyStr = pprint headTy

--------------------------------------------------------------------------------
-- Poke
--------------------------------------------------------------------------------

c2w :: Char -> Word8
c2w = fromIntegral . ord

i2w :: Int -> Word8
i2w = fromIntegral

mkSerializeExprFields :: [Field] -> Q Exp
mkSerializeExprFields fields =
    case verifySortedFields fields of
        [] -> [|pure ($(varE (mkName "i0")))|]
        _ ->
            doE
                (fmap makeBind (zip [0 ..] fields) ++
                 [ noBindS
                       [|void $ serialize
                             $(varE n_finalOffOff)
                             $(varE n_arr)
                             (fromIntegral $(varE (makeI numFields)) :: Word32)|]
                 , noBindS [|pure $(varE (makeI numFields))|]
                 ])
  where
    numFields = length fields
    makeBindTag i (t, w8) = do
        let w8Exp = litIntegral w8
        bindS
            (varP (makeIT i (t + 1)))
            [|serialize $(varE (makeIT i t)) $(varE n_arr) ($(w8Exp) :: Word8)|]
    makeBind (_, (Nothing, _)) = error "Cant use non-tagged value"
    makeBind (i, (Just tag, ty)) =
        let tagBase = fmap c2w (nameBase tag)
            lenTagBaseRaw = length tagBase
            lenTagBase =
                if lenTagBaseRaw > 63
                    then error "Tags with length > 63 are not supported"
                    else i2w lenTagBaseRaw :: Word8
            isMType = isMaybeType ty
            n_value = mkName "value"
            sexpr =
                [|do $(varP (makeIT i 0)) <-
                         serialize
                             $(varE (makeI i))
                             $(varE n_arr)
                             ($(litIntegral lenTagBase) :: Word8)
                     postTagOff <-
                         $(doE (fmap (makeBindTag i) (zip [0 ..] tagBase) ++
                                [ noBindS
                                      [|pure $(varE (makeIT i lenTagBaseRaw))|]
                                ]))
                     nextOff <-
                         serialize (postTagOff + 4) $(varE n_arr) $(varE n_value)
                     void $ serialize
                         postTagOff
                         $(varE n_arr)
                         (fromIntegral nextOff :: Word32)
                     pure nextOff|]
         in bindS
                (varP (makeI (i + 1)))
                (if isMType
                     then [|case $(varE (mkFieldName i)) of
                                Nothing -> pure $(varE (makeI i))
                                Just $(varP n_value) -> $(sexpr)|]
                     else [|case $(varE (mkFieldName i)) of
                                $(varP n_value) -> $(sexpr)|])

mkSerializeExpr :: Type -> [DataCon] -> Q Exp
mkSerializeExpr headTy cons =
    case cons of
        [(DataCon _ _ _ [])] -> [|pure ($(varE n_initialOffset) + 1)|]
        [(DataCon cname _ _ fields)] ->
            [|let $(varP n_finalOffOff) = $(varE n_initialOffset)
                  $(varP (makeI 0)) = $(varE n_initialOffset) + 4
               in $(caseE
                        (varE n_val)
                        [ matchConstructor
                              cname
                              (length fields)
                              (mkSerializeExprFields fields)
                        ])|]
        _ -> error
                 $ unlines
                       [ "The datatype should have exatcly 1 constructor."
                       , "It has " ++ lenConsStr ++ "."
                       , "See " ++ headTyStr
                       ]

  where
    headTyStr = pprint headTy
    lenCons = length cons
    lenConsStr = show lenCons

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

deriveSerializeInternal :: Cxt -> Type -> [DataCon] -> Q [Dec]
deriveSerializeInternal preds headTy cons = do
    sizeOfMethod <- mkSizeOfExpr headTy cons
    peekMethod <- mkDeserializeExpr headTy cons
    pokeMethod <- mkSerializeExpr headTy cons
    let methods =
            [ FunD 'size [Clause [] (NormalB sizeOfMethod) []]
            , FunD
                  'deserialize
                  [ Clause
                        (if isUnitType cons
                             then [VarP n_initialOffset, WildP]
                             else [ VarP n_initialOffset
                                  , VarP n_arr
                                  , VarP n_capacityOff
                                  ])
                        (NormalB peekMethod)
                        []
                  ]
            , FunD
                  'serialize
                  [ Clause
                        (if isUnitType cons
                             then [VarP n_initialOffset, WildP, WildP]
                             else [VarP n_initialOffset, VarP n_arr, VarP n_val])
                        (NormalB pokeMethod)
                        []
                  ]
            ]
    return [plainInstanceD preds (AppT (ConT ''Serialize) headTy) methods]

-- | Template haskell helper to create backward compatible instances of
-- 'Serialize' for single constructor record datatypes.
--
-- Consider the datatype:
-- @
-- data CustomDataType a b c =
--         CustomDataType
--             { field0 :: ...
--             , field1 :: ...
--             ...
--             }
-- @
--
-- Usage: @$(deriveSerialize ''CustomDataType)@
--
-- Note: All type variables automatcally get an "Serialize" constraint.
-- The derived code will look like the following,
-- @
-- instance (Serialize a, Serialize b, Serialize c) => Serialize (CustomDataType a b c) where
-- ...
-- @
--
-- To control which type variables get the Serialize constraint, use
-- 'deriveSerializeWith'.
deriveSerialize :: Name -> Q [Dec]
deriveSerialize name = do
    dt <- reifyDataType name
    let preds = map (unboxPred . VarT) (dtTvs dt)
        headTy = appsT (ConT name) (map VarT (dtTvs dt))
        cons = dtCons dt
    deriveSerializeInternal preds headTy cons

    where

    unboxPred ty =
#if MIN_VERSION_template_haskell(2,10,0)
        AppT (ConT ''Serialize) ty
#else
        ClassP ''Serialize [ty]
#endif

-- | Like 'deriveSerialize' but control which types variables get the 'Serialize'
-- constraint.
--
-- Consider the datatype:
-- @
-- data CustomDataType a b c = ...
-- @
--
-- Usage: @$(deriveSerializeWith ["a", "c"] ''CustomDataType)@
--
-- @
-- instance (Serialize a, Serialize c) => Serialize (CustomDataType a b c) where
-- ...
-- @
--
deriveSerializeWith :: [String] -> Name -> Q [Dec]
deriveSerializeWith vars name = do
    dt <- reifyDataType name
    let preds = map (unboxPred . VarT) (fmap mkName vars)
        headTy = appsT (ConT name) (map VarT (dtTvs dt))
        cons = dtCons dt
    deriveSerializeInternal preds headTy cons

    where

    unboxPred ty =
#if MIN_VERSION_template_haskell(2,10,0)
        AppT (ConT ''Serialize) ty
#else
        ClassP ''Serialize [ty]
#endif
