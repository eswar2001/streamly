{-# LANGUAGE TemplateHaskell #-}

-- |
-- Module      : Streamly.Internal.Data.Serialize.TH
-- Copyright   : (c) 2023 Composewell Technologies
-- License     : BSD3-3-Clause
-- Maintainer  : streamly@composewell.com
-- Stability   : experimental
-- Portability : GHC
--
module Streamly.Internal.Data.Serialize.RecordTH2
    ( deriveCompatSerialize
    , deriveCompatSerializeWith
    , conUpdateFuncExpr
    ) where

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

import Data.List (foldl')
import Data.Word (Word16, Word32, Word64, Word8)
import Data.Maybe (fromJust)
import Data.Char (ord, chr)
import Data.Bits ((.|.), shiftL, zeroBits,Bits, xor)
import Language.Haskell.TH
import Streamly.Internal.Data.Serialize
import Streamly.Internal.System.IO (unsafeInlineIO)
import Data.Foldable (foldlM)
import Streamly.Internal.Data.Unbox.TH
    ( DataCon(..)
    , DataType(..)
    , appsT
    , plainInstanceD
    , reifyDataType
    )
import Streamly.Internal.Data.Unbox (MutableByteArray)

import qualified Streamly.Internal.Data.Unbox as Unbox

import Streamly.Internal.Data.Serialize.TH
    ( Field
    , _arr
    , _endOffset
    , _initialOffset
    , _val
    , makeI
    , matchConstructor
    , mkDeserializeExprOne
    , mkFieldName
    , mkSerializeExprFields
    , openConstructor
    )

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

errorUnsupported :: a
errorUnsupported =
    error $
    unlines
        [ "Unsupported."
        , "The datatype should be a record type with only one constructor."
        , "The number of fields should be <= 63."
        , "The key length for any fields should be <= 63."
        ]

makeN :: Int -> Name
makeN i = mkName $ "n" ++ show i

fieldToNameBase :: Field -> String
fieldToNameBase = nameBase . fromJust . fst

int_w8 :: Int -> Word8
int_w8 = fromIntegral

w8_w16 :: Word8 -> Word16
w8_w16 = fromIntegral

w8_w32 :: Word8 -> Word32
w8_w32 = fromIntegral

w8_w64 :: Word8 -> Word64
w8_w64 = fromIntegral

w32_int :: Word32 -> Int
w32_int = fromIntegral

c2w :: Char -> Word8
c2w = fromIntegral . ord

wListToString :: [Word8] -> String
wListToString = fmap (chr . fromIntegral)

int_w32 :: Int -> Word32
int_w32 = fromIntegral

isMaybeType :: Type -> Bool
isMaybeType (AppT (ConT m) _) = m == ''Maybe
isMaybeType _ = False

--------------------------------------------------------------------------------
-- Size
--------------------------------------------------------------------------------

exprGetSize :: Q Exp -> (Int, Type) -> Q Exp
exprGetSize acc (i, ty) =
    [|case size :: Size $(pure ty) of
          Size f -> f $(acc) $(varE (mkFieldName i)) + 4|]

sizeOfHeader :: DataCon -> Int
sizeOfHeader (DataCon _ _ _ fields) =
    sizeForFinalOff + sizeForHeaderLength + sizeForNumFields +
    sum (map ((+ sizeForFieldLen) . length . fieldToNameBase) fields)
  where
    sizeForFinalOff = 4
    sizeForHeaderLength = 4
    sizeForNumFields = 1
    sizeForFieldLen = 1

mkSizeOfExpr :: DataCon -> Q Exp
mkSizeOfExpr con = do
    n_acc <- newName "acc"
    n_x <- newName "x"
    appE
        (conE 'Size)
        (lamE
             [varP n_acc, varP n_x]
             [|$(litIntegral hlen) +
               $(caseE (varE n_x) [matchCons (varE n_acc) con])|])
  where
    hlen = sizeOfHeader con
    sizeOfFields acc fields = foldl' exprGetSize acc $ zip [0 ..] fields
    matchCons acc (DataCon cname _ _ fields) =
        let expr = sizeOfFields acc (map snd fields)
         in matchConstructor cname (length fields) expr

mkSizeDec :: DataCon -> Q [Dec]
mkSizeDec con = do
    sizeOfMethod <- mkSizeOfExpr con
    pure
        [ PragmaD (InlineP 'size Inlinable FunLike AllPhases)
        , FunD 'size [Clause [] (NormalB sizeOfMethod) []]
        ]

--------------------------------------------------------------------------------
-- Header
--------------------------------------------------------------------------------

headerValue :: DataCon -> [Word8]
headerValue (DataCon _ _ _ fields) =
    int_w8 numFields : concat (fmap lenthPrependedFieldEncoding fields)
  where
    numFields = length fields
    lenthPrependedFieldEncoding field =
        let fEnc = map c2w (fieldToNameBase field)
         in (int_w8 (length fEnc)) : fEnc

--------------------------------------------------------------------------------
-- Peek
--------------------------------------------------------------------------------

{-# INLINE serializeWithSize #-}
serializeWithSize :: Serialize a => Int -> MutableByteArray -> a -> IO Int
serializeWithSize off arr val = do
    off1 <- serialize (off + 4) arr val
    Unbox.pokeByteIndex off arr (int_w32 off1 :: Word32)
    pure off1

litIntegral :: Integral a => a -> Q Exp
litIntegral i = litE (IntegerL (fromIntegral i))

serializeHeaderExpr :: [Word8] -> Q Exp
serializeHeaderExpr w8List =
    doE (fmap makeBind [0 .. (lenW8List - 1)] ++
         [noBindS ([|pure $(varE (makeN lenW8List))|])])
  where
    lenW8List = length w8List
    makeBind i =
        bindS
            (varP (makeN (i + 1)))
            [|$(varE 'serialize)
                  $(varE (makeN i))
                  $(varE _arr)
                  ($(litIntegral (w8List !! i)) :: Word8)|]

mkSerializeExpr :: Name -> DataCon -> Q Exp
mkSerializeExpr initialOffset (con@(DataCon cname _ _ fields)) =
    [|do $(varP (makeN 0)) <-
             serialize
                 ($(varE initialOffset) + 4)
                 $(varE _arr)
                 ($(litIntegral hlen) :: Word32)
         $(varP (makeI 0)) <- $(serializeHeaderExpr hval)
         let $(openConstructor cname (length fields)) = $(varE _val)
         finalOff <- $(mkSerializeExprFields 'serializeWithSize fields)
         Unbox.pokeByteIndex
             $(varE initialOffset)
             $(varE _arr)
             ((fromIntegral :: Int -> Word32) finalOff)
         pure finalOff|]
  where
    hval = headerValue con
    hlen = length hval

mkSerializeDec :: DataCon -> Q [Dec]
mkSerializeDec con = do
    pokeMethod <- mkSerializeExpr _initialOffset con
    pure
        [ PragmaD (InlineP 'serialize Inline FunLike AllPhases)
        , FunD
              'serialize
              [ Clause
                    [VarP _initialOffset, VarP _arr, VarP _val]
                    (NormalB pokeMethod)
                    []
              ]
        ]

--------------------------------------------------------------------------------
-- Poke
--------------------------------------------------------------------------------

shiftAdd :: Bits a => (b -> a) -> [b] -> a
shiftAdd conv xs =
    foldl' (.|.) zeroBits $
    map (\(j, x) -> shiftL x (j * 8)) $ zip [0 ..] $ map conv xs

xorCmp :: [Word8] -> Name -> Name -> Q Exp
xorCmp tag off arr =
    case tagLen of
        x | x < 2 -> [|$(go8 0) == zeroBits|]
        x | x < 4 -> [|$(go16 0) == zeroBits|]
        x | x < 8 -> [|$(go32 0) == zeroBits|]
        _ -> [|$(go64 0) == zeroBits|]
  where
    tagLen = length tag
    go8 i | i >= tagLen = [|zeroBits|]
    go8 i = do
        let wIntegral = litIntegral i
        [|xor (unsafeInlineIO
                   (Unbox.peekByteIndex
                        ($(varE off) + $(litIntegral i))
                        $(varE arr)))
              ($(wIntegral) :: Word8) .|.
          $(go8 (i + 1))|]
    go16 i
        | i >= tagLen = [|zeroBits|]
    go16 i
        | tagLen - i < 2 = go16 (tagLen - 2)
    go16 i = do
        let wIntegral =
                litIntegral
                    (shiftAdd w8_w16 [tag !! i, tag !! (i + 1)] :: Word16)
        [|xor (unsafeInlineIO
                   (Unbox.peekByteIndex
                        ($(varE off) + $(litIntegral i))
                        $(varE arr)))
              ($(wIntegral) :: Word16) .|.
          $(go16 (i + 2))|]
    go32 i
        | i >= tagLen = [|zeroBits|]
    go32 i
        | tagLen - i < 4 = go32 (tagLen - 4)
    go32 i = do
        let wIntegral =
                litIntegral
                    (shiftAdd
                         w8_w32
                         [ tag !! i
                         , tag !! (i + 1)
                         , tag !! (i + 2)
                         , tag !! (i + 3)
                         ] :: Word32)
        [|xor (unsafeInlineIO
                   (Unbox.peekByteIndex
                        ($(varE off) + $(litIntegral i))
                        $(varE arr)))
              ($(wIntegral) :: Word32) .|.
          $(go32 (i + 4))|]
    go64 i
        | i >= tagLen = [|zeroBits|]
    go64 i
        | tagLen - i < 8 = go64 (tagLen - 8)
    go64 i = do
        let wIntegral =
                litIntegral
                    (shiftAdd
                         w8_w64
                         [ tag !! i
                         , tag !! (i + 1)
                         , tag !! (i + 2)
                         , tag !! (i + 3)
                         , tag !! (i + 4)
                         , tag !! (i + 5)
                         , tag !! (i + 6)
                         , tag !! (i + 7)
                         ])
        [|xor (unsafeInlineIO
                   (Unbox.peekByteIndex
                        ($(varE off) + $(litIntegral i))
                        $(varE arr)))
              ($(wIntegral) :: Word64) .|.
          $(go64 (i + 8))|]

{-# INLINE deserializeWithSize #-}
deserializeWithSize ::
       Serialize a => Int -> MutableByteArray -> Int -> IO (Int, a)
deserializeWithSize off arr endOff = deserialize (off + 4) arr endOff

conUpdateFuncExpr :: Name -> Type -> [Field] -> Q [Dec]
conUpdateFuncExpr funcName headTy fields = do
    prevRec <- newName "prevRec"
    curOff <- newName "curOff"
    endOff <- newName "endOff"
    arr <- newName "arr"
    key <- newName "key"
    method <-
        (caseE
             (varE key)
             (concat
                  [ map (matchField arr endOff (prevRec, curOff)) fnames
                  , [ match
                          wildP
                          (normalB
                               [|do (_, jumpOff :: Word32) <-
                                        deserialize
                                            $(varE curOff)
                                            $(varE arr)
                                            $(varE endOff)
                                    pure ($(varE prevRec), w32_int jumpOff)|])
                          []
                    ]
                  ]))
    pure
        [ PragmaD (InlineP funcName NoInline FunLike AllPhases)
        , FunD
              funcName
              [ Clause
                    [ VarP arr
                    , VarP endOff
                    , TupP [VarP prevRec, VarP curOff]
                    , VarP key
                    ]
                    (NormalB method)
                    []
              ]
        ]
  where
    fnames = fmap (fromJust . fst) fields
    matchField :: Name -> Name -> (Name, Name) -> Name -> Q Match
    matchField arr endOff (prevRec, currOff) fname = do
        val <- newName "val"
        newOff <- newName "newOff"
        match
            (litP (StringL (nameBase fname)))
            (normalB
                 [|do ($(varP newOff), $(varP val)) <-
                          deserializeWithSize
                              $(varE currOff)
                              $(varE arr)
                              $(varE endOff)
                      pure
                          ( $(recUpdE (varE prevRec) [pure (fname, VarE val)]) :: $(pure headTy)
                          , $(varE newOff))|])
            []

mkDeserializeKeysExpr ::
       Name -> Name -> Name -> Name -> Name -> DataCon -> Q Exp
mkDeserializeKeysExpr hOff finalOff arr endOff updateFunc (DataCon cname _ _ fields) = do
    [|do (dataOff, hlist :: CompactList (CompactList Word8)) <-
             deserialize $(varE hOff) $(varE arr) $(varE endOff)
         let keys = wListToString . unCompactList <$> unCompactList hlist
         (finalRec, _) <-
             foldlM
                 ($(varE updateFunc) $(varE arr) $(varE endOff))
                 ($(emptyConExpr), dataOff)
                 keys
         pure ($(varE finalOff), finalRec)|]
  where
    emptyTy k ty =
        if isMaybeType ty
            then [|Nothing|]
            else [|error $(litE (StringL (nameBase k ++ " is not found.")))|]
    fieldToEmptyRecC (Just name, ty) = (name, ) <$> emptyTy name ty
    fieldToEmptyRecC _ = errorUnsupported
    emptyConExpr = recConE cname (fmap fieldToEmptyRecC fields)

mkDeserializeExpr :: Name -> Name -> Name -> DataCon -> Q Exp
mkDeserializeExpr initialOff endOff deserializeWithKeys con = do
    hOff <- newName "hOff"
    [|do (hlenOff, finalOff :: Word32) <-
             deserialize $(varE initialOff) $(varE _arr) $(varE endOff)
         ($(varP hOff), hlen1 :: Word32) <-
             deserialize hlenOff $(varE _arr) $(varE endOff)
         if hlen1 == $(litIntegral hlen)
             then if $(xorCmp hval hOff _arr)
                      then do
                          let $(varP (makeI 0)) = $(litIntegral (hlen + 4 + 4))
                          $(mkDeserializeExprOne 'deserializeWithSize con)
                      else $(varE deserializeWithKeys)
                               $(varE hOff)
                               (w32_int finalOff)
             else $(varE deserializeWithKeys) $(varE hOff) (w32_int finalOff)|]
  where
    hval = headerValue con
    hlen = length hval

mkDeserializeDec :: Type -> DataCon -> Q [Dec]
mkDeserializeDec headTy con@(DataCon _ _ _ fields) = do
    deserializeWithKeys <- newName "deserializeWithKeys"
    hOff <- newName "hOff"
    finalOff <- newName "finalOff"
    updateFunc <- newName "updateFunc"
    deserializeWithKeysMethod <-
        mkDeserializeKeysExpr hOff finalOff _arr _endOffset updateFunc con
    updateFuncDec <- conUpdateFuncExpr updateFunc headTy fields
    peekMethod <-
        mkDeserializeExpr _initialOffset _endOffset deserializeWithKeys con
    pure
        [ PragmaD (InlineP 'deserialize Inline FunLike AllPhases)
        , FunD
              'deserialize
              [ Clause
                    [VarP _initialOffset, VarP _arr, VarP _endOffset]
                    (NormalB peekMethod)
                    ([ PragmaD
                           (InlineP
                                deserializeWithKeys
                                NoInline
                                FunLike
                                AllPhases)
                     , FunD
                           deserializeWithKeys
                           [ Clause
                                 [VarP hOff, VarP finalOff]
                                 (NormalB deserializeWithKeysMethod)
                                 []
                           ]
                     ] ++
                     updateFuncDec)
              ]
        ]

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

deriveCompatSerializeInternal :: Cxt -> Type -> [DataCon] -> Q [Dec]
deriveCompatSerializeInternal preds headTy [con@(DataCon _ _ _ fields@(_:_))]
    | checkFieldsSanity fields = do
        sizeOfMethod <- mkSizeDec con
        peekMethod <- mkDeserializeDec headTy con
        pokeMethod <- mkSerializeDec con
        let methods = sizeOfMethod ++ pokeMethod ++ peekMethod
        return [plainInstanceD preds (AppT (ConT ''Serialize) headTy) methods]
    | otherwise = errorUnsupported
  where
    checkOneFieldSanity (Nothing, _) = False
    checkOneFieldSanity (Just name, _) = length (nameBase name) <= 63
    checkFieldsSanity xs =
        length fields <= 63 && and (map checkOneFieldSanity xs)
deriveCompatSerializeInternal _ _ _ = errorUnsupported

deriveCompatSerialize :: Name -> Q [Dec]
deriveCompatSerialize name = do
    dt <- reifyDataType name
    let preds = map (unboxPred . VarT) (dtTvs dt)
        headTy = appsT (ConT name) (map VarT (dtTvs dt))
        cons = dtCons dt
    deriveCompatSerializeInternal preds headTy cons

    where

    unboxPred ty =
#if MIN_VERSION_template_haskell(2,10,0)
        AppT (ConT ''Serialize) ty
#else
        ClassP ''Serialize [ty]
#endif

deriveCompatSerializeWith :: [String] -> Name -> Q [Dec]
deriveCompatSerializeWith vars name = do
    dt <- reifyDataType name
    let preds = map (unboxPred . VarT) (fmap mkName vars)
        headTy = appsT (ConT name) (map VarT (dtTvs dt))
        cons = dtCons dt
    deriveCompatSerializeInternal preds headTy cons

    where

    unboxPred ty =
#if MIN_VERSION_template_haskell(2,10,0)
        AppT (ConT ''Serialize) ty
#else
        ClassP ''Serialize [ty]
#endif
