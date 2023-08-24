{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE UndecidableInstances #-}

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
module Streamly.Internal.Data.Serialize.RecordTH1 where

--------------------------------------------------------------------------------
-- Imports
--------------------------------------------------------------------------------

import GHC.Ptr (Ptr(..), plusPtr)
import Control.Monad (void)
import Data.List (sortBy, findIndex, foldl')
import Data.Maybe (fromJust, fromMaybe)
import Data.Word (Word16, Word32, Word64, Word8)
import Data.Char (ord, chr)
import Data.Proxy (Proxy(..))
import Streamly.Internal.Data.MutArray.Type (memcmp1)

import qualified Foreign.Storable as Storable
import Streamly.Internal.System.IO (unsafeInlineIO)

import Language.Haskell.TH
import Streamly.Internal.Data.Serialize

import Data.Bits (Bits, (.|.), shiftL, shiftR, xor, zeroBits)

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

import Data.Coerce
import Streamly.Internal.Data.Serialize.TH

--------------------------------------------------------------------------------
-- Code
--------------------------------------------------------------------------------

newtype Compat a =
    Compat a

newtype Skipper a =
    Skipper a
    deriving (Show, Eq)

type Key = String

intTow32 :: Int -> Word32
intTow32 = fromIntegral

instance Serialize a => Serialize (Skipper a) where
    {-# INLINE size #-}
    size =
        Size $ \i (Skipper a) ->
            case size :: Size a of
                Size f -> f i a + 4
    {-# INLINE serialize #-}
    serialize off arr (Skipper val) = do
        off1 <- serialize (off + 4) arr val
        Unbox.pokeByteIndex off arr (intTow32 off1)
        pure off1
    {-# INLINE deserialize #-}
    deserialize off arr end = do
        (off1, val) <- deserialize (off + 4) arr end
        pure (off1, Skipper val)

class BuildCompat a where
    sizeOfHeader :: Proxy a -> Int
    checkHeader :: Proxy a -> Int -> MutableByteArray -> IO Bool
    serializeHeader :: Proxy a -> Int -> MutableByteArray -> IO Int
    deserializeWithKeys :: Int -> MutableByteArray -> Int -> [Key] -> IO a

litIntegral :: Integral a => a -> Q Exp
litIntegral i = litE (IntegerL (fromIntegral i))

-- +8 if int64
sizeOfHeaderExpr :: DataCon -> Q Exp
sizeOfHeaderExpr (DataCon _ _ _ fields) = litIntegral (sizeOfFields + 1)
  where
    keySize acc (Just tag, _) = acc + length (nameBase tag) + 1
    keySize _ _ = undefined
    sizeOfFields = foldl' keySize (0 :: Int) fields

shiftAdd conv xs =
    foldl' (.|.) zeroBits $
    map (\(j, x) -> shiftL x (j * 8)) $
    zip [(length xs - 1),(length xs - 2) .. 0] $ map conv xs

w64To8 :: Word64 -> Word8
w64To8 = fromIntegral

w8To16 :: Word8 -> Word16
w8To16 = fromIntegral

xorCmp :: [Word8] -> Name -> Name -> Q Exp
xorCmp tag off arr = [|$(go 0) == zeroBits|]
  where
    tagLen = length tag
    go i
        | i >= tagLen = [|zeroBits|]
    go i = do
        let remainingChars = tagLen - i
            ty =
                case remainingChars of
                    x
                        | otherwise -> [t|Word8|]
                        | x < 4 -> [t|Word16|]
                        | x < 8 -> [t|Word32|]
                        | otherwise -> [t|Word64|]
            offInc =
                case remainingChars of
                    x
                        | otherwise -> 1
                        | x < 4 -> 2
                        | x < 8 -> 4
                        | otherwise -> 8
            wIntegral =
                case remainingChars of
                    x
                        | otherwise -> litIntegral (tag !! i)
                        | x < 4 ->
                            litIntegral
                                (shiftAdd w8To16 [tag !! i, tag !! (i + 1)])
                        | x < 8 ->
                            litIntegral
                                (shiftAdd
                                     w8To16
                                     [ tag !! i
                                     , tag !! (i + 1)
                                     , tag !! (i + 2)
                                     , tag !! (i + 3)
                                     ])
                        | otherwise ->
                            litIntegral
                                (shiftAdd
                                     w8To16
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
              ($(wIntegral) :: $(ty)) .|.
          $(go (i + offInc))|]

getHeaderW8 :: DataCon -> [Word8]
getHeaderW8 (DataCon _ _ _ fields) = w8ListComplete
  where
    w8ListComplete = numFields8 ++ concat (map key8 fields)
    key8 (Just tag, _) =
        w64Tow8List (fromIntegral (length (nameBase tag))) ++
        fmap c2w (nameBase tag)
    key8 _ = undefined
    numFields64 = fromIntegral (length fields) :: Word64
    numFields8 = w64Tow8List numFields64
    w64Tow8List :: Word64 -> [Word8]
    -- w64Tow8List x = (\i -> w64To8 (x `shiftR` (i * 7))) <$> [0 .. 7]
    w64Tow8List x = [w64To8 x]

checkHeaderExpr :: Name -> Name -> DataCon -> Q Exp
checkHeaderExpr headerOff arr con = do
    [|pure $(xorCmp (getHeaderW8 con) headerOff arr)|]

serializeHeaderExpr :: Name -> Name -> DataCon -> Q Exp
serializeHeaderExpr headerOff arr con =
    doE (map (go headerOff) (zip [(0 :: Int) ..] w8ListComplete) ++
         [ noBindS
               [|pure
                     ($(varE headerOff) +
                      ($(litIntegral (length w8ListComplete)) :: Int))|]
         ])
  where
    go tOff (i, x) =
        noBindS
            [|void $
              serialize
                  ($(varE tOff) + ($(litIntegral i) :: Int))
                  $(varE arr)
                  ($(litIntegral x) :: Word8)|]
    w8ListComplete = getHeaderW8 con

deserializeWithKeysExpr :: Name -> Name -> Name -> Name -> DataCon -> Q Exp
deserializeWithKeysExpr headerOff arr endOff keys con =
    [|error "Unimplemented"|]

class SerializeCompat a where
    sizeC :: Size a
    serializeC :: Int -> MutableByteArray -> a -> IO Int
    deserializeC :: Int -> MutableByteArray -> Int -> IO (Int, a)

w2c :: Word8 -> Char
w2c = chr . fromIntegral

c2w :: Char -> Word8
c2w = fromIntegral . ord

instance forall a. (Serialize a, BuildCompat a) => SerializeCompat a where
    {-# INLINE sizeC #-}
    sizeC =
        Size $ \i a ->
            case size of
                Size f -> f i a + sizeOfHeader (Proxy :: Proxy a) + 8
    {-# INLINE serializeC #-}
    serializeC off arr val = do
        let off1 = off + 8
        off2 <- serializeHeader (Proxy :: Proxy a) off1 arr
        off3 <- serialize off2 arr val
        Unbox.pokeByteIndex off1 arr off3
        pure off3
    {-# INLINE deserializeC #-}
    deserializeC off arr endOff = do
        (headerOff, finalOff :: Int) <- deserialize off arr endOff
        headerIsMatching <- checkHeader (Proxy :: Proxy a) headerOff arr
        if headerIsMatching
        then
            deserialize (headerOff + sizeOfHeader (Proxy :: Proxy a)) arr endOff
        else do
            (dataOff, (CompactList keys8) :: CompactList (CompactList Word8)) <-
                deserialize headerOff arr endOff
            let keys = map (map w2c . unCompactList) keys8
            val <- deserializeWithKeys dataOff arr endOff keys
            pure (finalOff, val)

{-# INLINE toSkipper #-}
toSkipper :: a -> Skipper a
toSkipper = coerce

{-# INLINE unSkipper #-}
unSkipper :: Skipper a -> a
unSkipper = coerce

--------------------------------------------------------------------------------
-- Code
--------------------------------------------------------------------------------


data Test =
    Test
        { field0 :: Int
        , field2 :: Maybe Char
        }
{-
data Test_253 =
    Test_253
        { field0 :: Skipper Int
        , field2 :: Skipper (Maybe Char)
        }
$(deriveSerialize 'Test_253')

instance SerializeCompat Test
-}


{->
instance SerializeCompat a where
    sizeC
    serializeC
    deserializeC

-- OLD

data Test =
    Test
        { field0 :: Int
        , field2 :: Maybe Char
        }

type TestCompat = Compat Test






data Test =
    Test
        { field0 :: Skipper Int
        , field2 :: Skipper (Maybe Char)
        }

instance BackwardCompatiblize Test where
    emptyVal = Test undefined Nothing undefined undefined
    fromHM off0 arr endOff keys = go off0 keys
        where
        go off (x:xs) acc
            | stringify x == "field0" = do
                (off1, val) <- deserialize off arr endOff
                go off1 xs {field0 = val}
            | stringify x == "field2" = do
                (off1, val) <- deserialize off arr endOff
                go off1 xs {field2 = val}


["field0", "field2"]





data Test =
    Test
        { field0 :: Int
        , field1 :: Maybe Char
        , field2 :: Maybe Char
        }


instance BackwardCompatiblize Test where
    emptyVal = Test undefined Nothing undefined undefined
    fromHM off0 arr endOff keys = go off0 keys
        where
        go off (x:xs) acc
            | stringify x == "field0" = do
                (off1, val) <- deserialize off arr endOff
                go off1 xs {field0 = val}
            | stringify x == "field1" = do
                (off1, val) <- deserialize off arr endOff
                go off1 xs {field1 = val}
            | stringify x == "field2" = do
                (off1, val) <- deserialize off arr endOff
                go off1 xs {field2 = val}
            | otherwize = do
                (off1, val) <- deserialize off arr endOff
                go val xs acc

newtype BackwardCompatible a =
    BackwardCompatible a

instance Serialize a => Serialize (BackwardCompatible a) where
    serialize
-}


deriveBuildCompatInternal :: Cxt -> Type -> [DataCon] -> Q [Dec]
deriveBuildCompatInternal preds headTy [con] = do
    sizeOfHeaderMet <- sizeOfHeaderExpr con

    headerOff <- newName "headerOff"
    arr <- newName "arr"
    endOff <- newName "endOff"
    keys <- newName "keys"

    checkHeaderMet <- checkHeaderExpr headerOff arr con
    serializeHeaderMet <- serializeHeaderExpr headerOff arr con
    deserializeWithKeysMet <-
        deserializeWithKeysExpr headerOff arr endOff keys con

    let methods =
            -- INLINE on sizeOf actually worsens some benchmarks, and improves
            -- none
            [ PragmaD (InlineP 'sizeOfHeader Inlinable FunLike AllPhases)
            , FunD 'sizeOfHeader [Clause [WildP] (NormalB sizeOfHeaderMet) []]
            , PragmaD (InlineP 'checkHeader Inline FunLike AllPhases)
            , FunD
                  'checkHeader
                  [ Clause
                        [WildP, VarP headerOff, VarP arr]
                        (NormalB checkHeaderMet)
                        []
                  ]
            , PragmaD (InlineP 'serializeHeader Inline FunLike AllPhases)
            , FunD
                  'serializeHeader
                  [ Clause
                        [WildP, VarP headerOff, VarP arr]
                        (NormalB serializeHeaderMet)
                        []
                  ]
            , PragmaD (InlineP 'deserializeWithKeys NoInline FunLike AllPhases)
            , FunD
                  'deserializeWithKeys
                  [ Clause
                        [VarP headerOff, VarP arr, VarP endOff, VarP keys]
                        (NormalB deserializeWithKeysMet)
                        []
                  ]
            ]
    return [plainInstanceD preds (AppT (ConT ''BuildCompat) headTy) methods]
deriveBuildCompatInternal preds headTy _ = error "Not 1 constructor"

deriveBuildCompat :: Name -> Q [Dec]
deriveBuildCompat name = do
    dt <- reifyDataType name
    let preds = map (unboxPred . VarT) (dtTvs dt)
        headTy = appsT (ConT name) (map VarT (dtTvs dt))
        cons = dtCons dt
    deriveBuildCompatInternal preds headTy cons

    where

    unboxPred ty =
#if MIN_VERSION_template_haskell(2,10,0)
        AppT (ConT ''Serialize) ty
#else
        ClassP ''Serialize [ty]
#endif
