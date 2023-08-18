{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DuplicateRecordFields #-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

#undef FUSION_CHECK
#ifdef FUSION_CHECK
{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -dsuppress-all #-}
#endif

-- |
-- Module      : Streamly.Benchmark.Data.Serialize
-- Copyright   : (c) 2023 Composewell
-- License     : BSD-3-Clause
-- Maintainer  : streamly@composewell.com

module Main (main) where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

import Data.Word (Word16)
import Control.DeepSeq (NFData(..))
import GHC.Generics (Generic)
import System.Random (randomRIO)
#ifndef USE_UNBOX
import Test.QuickCheck (Arbitrary, arbitrary)
#endif

#ifdef USE_UNBOX
import Data.Proxy (Proxy(..))
import Streamly.Internal.Data.Unbox
#else
import Control.DeepSeq (force)
import Test.QuickCheck (oneof, elements, generate)
import Streamly.Internal.Data.Unbox (newBytes, MutableByteArray)
import Streamly.Internal.Data.Serialize
#endif

#ifdef USE_TH
#ifdef USE_UNBOX
import Streamly.Internal.Data.Unbox.TH
#else
import Streamly.Internal.Data.Serialize.TH
#endif
#endif

import Gauge
import Streamly.Benchmark.Common

#ifdef USE_UNBOX
#define SERIALIZE_CLASS Unbox
#define DERIVE_CLASS deriveUnbox
#define SERIALIZE_OP pokeByteIndex
#define DESERIALIZE_OP peekByteIndex
#else
#define SERIALIZE_CLASS Serialize
#define DERIVE_CLASS deriveSerialize
#define SERIALIZE_OP serialize
#define DESERIALIZE_OP deserialize
#endif

import Data.Time
import Data.Time.Calendar.OrdinalDate
import Data.Time.LocalTime

import qualified Data.Text as T
import qualified Data.Text.Array as TArr (Array(..))

import Data.Text.Internal (Text(..))
import Streamly.Internal.Data.Array (Array(..))
import Streamly.Internal.Data.Unbox (MutableByteArray(..))
import qualified Streamly.Internal.Data.Unbox as Unbox

import GHC.Exts

import GHC.Num.Integer
import GHC.Int
import Data.Proxy (Proxy(..))

import Data.Fixed

import Data.Word (Word8)

import Data.Store.TH
import Data.Store (Store, Poke(..))
import Data.Store.Core
    ( PeekException(..)
    , Poke(..)
    , PokeState
    , unsafeMakePokeState
    )
import qualified Data.Store as Store
import qualified Data.Store.Internal as Store

import           Data.ByteString (ByteString)
import qualified Data.ByteString.Internal as BS

import qualified Streamly.Internal.Data.Serialize.RecordTH as RecordTH
import qualified Streamly.Internal.Data.Serialize.JInternal as JInternal

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data Unit = Unit
    deriving (Generic, Show, Eq)

#ifndef USE_TH
instance SERIALIZE_CLASS Unit
#else
$(DERIVE_CLASS ''Unit)
#endif
-- $(makeStore ''Unit)
instance Store Unit

data Sum2
    = Sum21
    | Sum22
    deriving (Generic, Show, Eq)

#ifndef USE_TH
instance SERIALIZE_CLASS Sum2
#else
$(DERIVE_CLASS ''Sum2)
#endif
$(makeStore ''Sum2)

data Sum25
    = Sum251
    | Sum252
    | Sum253
    | Sum254
    | Sum255
    | Sum256
    | Sum257
    | Sum258
    | Sum259
    | Sum2510
    | Sum2511
    | Sum2512
    | Sum2513
    | Sum2514
    | Sum2515
    | Sum2516
    | Sum2517
    | Sum2518
    | Sum2519
    | Sum2520
    | Sum2521
    | Sum2522
    | Sum2523
    | Sum2524
    | Sum2525
    deriving (Generic, Show, Eq)

#ifndef USE_TH
instance SERIALIZE_CLASS Sum25
#else
$(DERIVE_CLASS ''Sum25)
#endif
$(makeStore ''Sum25)

data Product25
    = Product25
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
        Int
    deriving (Generic, Show)

#ifndef USE_TH
instance SERIALIZE_CLASS Product25
#else
$(DERIVE_CLASS ''Product25)
#endif
$(makeStore ''Product25)

-- XXX derived Eq instance is not inlined
instance Eq Product25 where
    {-# INLINE (==) #-}
    (==)
        (Product25 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25)
        (Product25 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25)
           =   a1  == b1
            && a2  == b2
            && a3  == b3
            && a4  == b4
            && a5  == b5
            && a6  == b6
            && a7  == b7
            && a8  == b8
            && a9  == b9
            && a10 == b10
            && a11 == b11
            && a12 == b12
            && a13 == b13
            && a14 == b14
            && a15 == b15
            && a16 == b16
            && a17 == b17
            && a18 == b18
            && a19 == b19
            && a20 == b20
            && a21 == b21
            && a22 == b22
            && a23 == b23
            && a24 == b24
            && a25 == b25

-------------------------------------------------------------------------------
-- Simple non-recursive ADT
-------------------------------------------------------------------------------

data CustomDT1
    = CDT1C1
    | CDT1C2 Int
    | CDT1C3 Int Int
    deriving (Generic, Show, Eq)

#ifndef USE_TH
instance SERIALIZE_CLASS CustomDT1
#else
$(DERIVE_CLASS ''CustomDT1)
#endif
$(makeStore ''CustomDT1)

-------------------------------------------------------------------------------
-- Recursive ADT
-------------------------------------------------------------------------------

#ifndef USE_UNBOX
data BinTree a
  = Tree (BinTree a) (BinTree a)
  | Leaf a
  deriving (Show, Read, Eq, Generic)

#ifndef USE_TH
instance Serialize (BinTree a)
#else
$(deriveSerialize ''BinTree)
#endif
-- Template haskell derivation of BinTree causes an infinite loop I believe.
-- $(makeStore ''BinTree)
instance Store a => Store (BinTree a)

instance NFData a => NFData (BinTree a) where
  rnf (Leaf a) = rnf a `seq` ()
  rnf (Tree l r) = rnf l `seq` rnf r `seq` ()

instance Arbitrary a => Arbitrary (BinTree a) where
  arbitrary = oneof [Leaf <$> arbitrary, Tree <$> arbitrary <*> arbitrary]

mkBinTree :: (Arbitrary a) => Int -> IO (BinTree a)
mkBinTree = go (generate $ arbitrary)

    where

    go r 0 = Leaf <$> r
    go r n = Tree <$> go r (n - 1) <*> go r (n - 1)

#endif

-------------------------------------------------------------------------------
-- Size helpers
-------------------------------------------------------------------------------

{-# INLINE getSize #-}
getSize :: forall a. SERIALIZE_CLASS a => a -> Int
#ifdef USE_UNBOX
getSize _ = sizeOf (Proxy :: Proxy a)
#else
getSize val =
    case size :: Size a of
        Size f -> f 0 val
#endif

-------------------------------------------------------------------------------
-- Common helpers
-------------------------------------------------------------------------------

-- Parts of "f" that are dependent on val will not be optimized out.
{-# INLINE loop #-}
loop :: Int -> (a -> IO b) -> a -> IO ()
loop count f val = go count val
    where

    go n x = do
        if n > 0
        then f x >> go (n-1) x
        else return ()

-- The first arg of "f" is the environment which is not threaded around in the
-- loop.
{-# INLINE loopWith #-}
loopWith :: Int -> (env -> a -> IO b) -> env -> a -> IO ()
loopWith count f e val = go count val
    where

    go n x = do
        if n > 0
        then f e x >> go (n-1) x
        else return ()

benchSink :: NFData b => String -> Int -> (Int -> IO b) -> Benchmark
benchSink name times f = bench name (nfIO (randomRIO (times, times) >>= f))

-------------------------------------------------------------------------------
-- Serialization Helpers
-------------------------------------------------------------------------------

{-# INLINE pokeWithSize #-}
pokeWithSize :: SERIALIZE_CLASS a => MutableByteArray -> a -> IO ()
pokeWithSize arr val = do
    let n = getSize val
    n `seq` SERIALIZE_OP 0 arr val >> return ()

{-# INLINE pokeTimesWithSize #-}
pokeTimesWithSize :: SERIALIZE_CLASS a => a -> Int -> IO ()
pokeTimesWithSize val times = do
    let n = getSize val
    arr <- newBytes n
    loopWith times pokeWithSize arr val

{-# INLINE poke #-}
poke :: SERIALIZE_CLASS a => MutableByteArray -> a -> IO ()
poke arr val = SERIALIZE_OP 0 arr val >> return ()

{-# INLINE pokeTimes #-}
pokeTimes :: SERIALIZE_CLASS a => a -> Int -> IO ()
pokeTimes val times = do
    let n = getSize val
    arr <- newBytes n
    loopWith times poke arr val

{-# INLINE peek #-}
peek :: forall a. (Eq a, SERIALIZE_CLASS a) => (a, Int) -> MutableByteArray -> IO ()
#ifdef USE_UNBOX
peek (val, _) arr = do
        (val1 :: a) <- DESERIALIZE_OP 0 arr
#else
peek (val, n) arr = do
        (_, val1 :: a) <- DESERIALIZE_OP 0 arr n
#endif
        -- Ensure that we are actually constructing the type and using it. This
        -- is important, otherwise the structure is created and discarded, the
        -- cost of creation of the structure is not accounted. Otherwise we may
        -- just read the values and discard them. The comparison adds to the
        -- cost though. We could use deepseq but then we need to write
        -- instances of NFData and ensure that they are correct and perform
        -- well. Equality check also ensures correctness.
        if (val1 /= val)
        then error "peek: no match"
        else return ()

{-# INLINE peekTimes #-}
peekTimes :: (Eq a, SERIALIZE_CLASS a) => Int -> a -> Int -> IO ()
peekTimes n val times = do
    arr <- newBytes n
    _ <- SERIALIZE_OP 0 arr val
    loopWith times peek (val, n) arr

{-# INLINE trip #-}
trip :: forall a. (Show a, Eq a, SERIALIZE_CLASS a) => a -> IO ()
trip val = do
    let n = getSize val
    arr <- newBytes n
    _ <- SERIALIZE_OP 0 arr val
#ifdef USE_UNBOX
    val1 <- DESERIALIZE_OP 0 arr
#else
    (_, val1) <- DESERIALIZE_OP 0 arr n
#endif
    -- Do not remove this, see the comments in peek.
    if (val1 /= val)
    then error "trip: no match"
    else return ()

{-# INLINE roundtrip #-}
roundtrip :: (Show a, Eq a, SERIALIZE_CLASS a) => a -> Int -> IO ()
roundtrip val times = loop times trip val

-------------------------------------------------------------------------------
-- Store Helpers
-------------------------------------------------------------------------------

{-# INLINE pokeWithSizeStore #-}
pokeWithSizeStore :: forall a. Store a => PokeState -> a -> IO ()
pokeWithSizeStore ps val = do
    let n = Store.getSize val
    n `seq` runPoke (Store.poke val) ps 0 >> return ()

{-# INLINE pokeTimesWithSizeStore #-}
pokeTimesWithSizeStore :: Store a => a -> Int -> IO ()
pokeTimesWithSizeStore val times = do
    let n = Store.getSize val
    BS.create n $ \ptr -> do
        ps <- unsafeMakePokeState ptr (pure ptr)
        loopWith times pokeWithSizeStore ps val
    pure ()

{-# INLINE pokeStore #-}
pokeStore :: Store a => PokeState -> a -> IO ()
pokeStore ps val = do
    runPoke (Store.poke val) ps 0 >> return ()

{-# INLINE pokeTimesStore #-}
pokeTimesStore :: Store a => a -> Int -> IO ()
pokeTimesStore val times = do
    let n = Store.getSize val
    BS.create n $ \ptr -> do
        ps <- unsafeMakePokeState ptr (pure ptr)
        loopWith times pokeStore ps val
    pure ()

{-# INLINE peekStore #-}
peekStore :: forall a. (Eq a, Store a) => a -> ByteString -> IO ()
peekStore val arr = do
        (val1 :: a) <- Store.decodeIO arr
        -- XXX We assert in trip but we don't assert here?
        -- Ensure that we are actually constructing the type and using it.
        -- Otherwise we may just read the values and discard them.
        -- The comparison adds to the cost though.
        --
        if (val1 /= val)
        then error "peekStore: no match"
        else return ()
        return ()

{-# INLINE peekTimesStore #-}
peekTimesStore :: (Eq a, Store a) => Int -> a -> Int -> IO ()
peekTimesStore n val times = do
    arr <-
        BS.create n $ \ptr -> do
            ps <- unsafeMakePokeState ptr (pure ptr)
            runPoke (Store.poke val) ps 0
            return ()
    loopWith times peekStore val arr

{-# INLINE tripStore #-}
tripStore :: forall a. (Show a, Eq a, Store a) => a -> IO ()
tripStore val = do
    let bs = Store.encode val
    val1 <- Store.decodeIO bs
    -- So that the compiler does not optimize it out
    if (val1 /= val)
        then error "tripStore: no match"
        else return ()
    return ()

{-# INLINE roundtripStore #-}
roundtripStore :: (Show a, Eq a, Store a) => a -> Int -> IO ()
roundtripStore val times = loop times tripStore val

-------------------------------------------------------------------------------
-- Record
-------------------------------------------------------------------------------

unpackInt :: Int -> Int#
unpackInt (I# i#) = i#

data LiftedInteger
    = LIS Int
    | LIP (Array Word)
    | LIN (Array Word)

$(deriveSerialize ''LiftedInteger)

-- How costly is the boxing going to be?

liftInteger :: Integer -> LiftedInteger
liftInteger (IS x) = LIS (I# x)
liftInteger (IP x) =
    LIP (Array (MutableByteArray (unsafeCoerce# x)) 0 (I# (sizeofByteArray# x)))
liftInteger (IN x) =
    LIN (Array (MutableByteArray (unsafeCoerce# x)) 0 (I# (sizeofByteArray# x)))

unliftInteger :: LiftedInteger -> Integer
unliftInteger (LIS (I# x)) = IS x
unliftInteger (LIP (Array (MutableByteArray x) _ _)) = IP (unsafeCoerce# x)
unliftInteger (LIN (Array (MutableByteArray x) _ _)) = IN (unsafeCoerce# x)

$(deriveSerialize ''E12)
$(deriveSerialize ''Fixed)

instance Serialize Integer where
    {-# INLINE size #-}
    size =
        Size $ \i a ->
            case size :: Size LiftedInteger of
                Size f -> f i (liftInteger a)

    {-# INLINE deserialize #-}
    deserialize off arr end = fmap unliftInteger <$> deserialize off arr end

    {-# INLINE serialize #-}
    serialize off arr val = serialize off arr (liftInteger val)

$(deriveSerialize ''Maybe)
$(deriveSerialize ''Day)
$(deriveSerialize ''TimeOfDay)
$(deriveSerialize ''LocalTime)

instance Arbitrary Day where
    arbitrary = fromOrdinalDate <$> arbitrary <*> arbitrary

instance Arbitrary TimeOfDay where
    arbitrary =
        TimeOfDay <$> arbitrary <*> arbitrary <*> (MkFixed <$> arbitrary)

instance Arbitrary LocalTime where
    arbitrary = LocalTime <$> arbitrary <*> arbitrary

instance Serialize Text where
    {-# INLINE size #-}
    size =
        Size $ \i a ->
            case size :: Size (Array Word16) of
                Size f -> f i (txtToArr a)

    {-# INLINE deserialize #-}
    deserialize off arr end = fmap arrToTxt <$> deserialize off arr end

    {-# INLINE serialize #-}
    serialize off arr val = serialize off arr (txtToArr val)

-- | Convert a 'Text' to an array of 'Word16'. It can be done in constant time.
{-# INLINE txtToArr #-}
txtToArr :: Text -> Array Word16
txtToArr (Text (TArr.Array _) _ len)
    | len == 0 = Array Unbox.nil 0 0
txtToArr (Text (TArr.Array barr#) off16 len16) =
    let off8 = off16 * 2
        len8 = len16 * 2
    in Array (MutableByteArray (unsafeCoerce# barr#)) off8 (off8 + len8)

{-# INLINE arrToTxt #-}
arrToTxt :: Array Word16 -> Text
arrToTxt Array {..}
    | len8 == 0 = T.empty
    | otherwise = Text (TArr.Array (unsafeCoerce# marr#)) off16 len16

    where

    len8 = arrEnd - arrStart
    off8 = arrStart
    len16 = len8 `div` 2
    off16 = off8 `div` 2
    !(MutableByteArray marr#) = arrContents

instance Arbitrary Text where
    arbitrary = T.pack <$> arbitrary

data TransactionMode
    = IFSC
    | UPI
    deriving (Generic, Show, Eq, Ord, Read, Enum)

instance Arbitrary TransactionMode where
    arbitrary = elements [IFSC, UPI]

$(deriveSerialize ''TransactionMode)
$(makeStore ''TransactionMode)

data TransactionType
    = PAY
    | COLLECT
    deriving (Generic, Show, Eq, Ord, Read, Enum)

instance Arbitrary TransactionType where
    arbitrary = elements [PAY, COLLECT]

$(deriveSerialize ''TransactionType)
$(makeStore ''TransactionType)

data TransactionStatus
    = SUCCESS
    | FAILURE
    | PENDING
    | EXPIRED
    | DECLINED
    | TIMED_OUT
    | DEEMED
    | COLLECT_PAY_INITIATED
    | DECLINE_INITIATED
    | REVERSED
    | NOT_FOUND
    deriving (Generic, Show, Eq, Ord, Read, Enum)

instance Arbitrary TransactionStatus where
    arbitrary =
        elements
            [ SUCCESS
            , FAILURE
            , PENDING
            , EXPIRED
            , DECLINED
            , TIMED_OUT
            , DEEMED
            , COLLECT_PAY_INITIATED
            , DECLINE_INITIATED
            , REVERSED
            , NOT_FOUND
            ]

$(deriveSerialize ''TransactionStatus)
$(makeStore ''TransactionStatus)

data TransactionChannel
    = USSD
    | ANDROID
    | IOS
    | SDK
    deriving (Generic, Show, Eq, Ord, Read, Enum)

instance Arbitrary TransactionChannel where
    arbitrary = elements [USSD, ANDROID, IOS, SDK]

$(deriveSerialize ''TransactionChannel)
$(makeStore ''TransactionChannel)

data TransactionCallbackStatus
    = CALLBACK_SUCCESS
    | CALLBACK_FAILURE
    | CALLBACK_PENDING
    | CALLBACK_UNINITIATED
    | CALLBACK_DEEMED
    deriving (Generic, Show, Eq, Ord, Read, Enum)

instance Arbitrary TransactionCallbackStatus where
    arbitrary =
        elements
            [ CALLBACK_SUCCESS
            , CALLBACK_FAILURE
            , CALLBACK_PENDING
            , CALLBACK_UNINITIATED
            , CALLBACK_DEEMED
            ]

$(deriveSerialize ''TransactionCallbackStatus)
$(makeStore ''TransactionCallbackStatus)

data CollectType
    = TRANSACTION
    | MANDATE
    deriving (Generic, Show, Eq, Ord, Read, Enum)

instance Arbitrary CollectType where
    arbitrary = elements [TRANSACTION, MANDATE]

$(deriveSerialize ''CollectType)
$(makeStore ''CollectType)

-- add more fields if required to PayerInfo
data PayerInfo  =
  PayerInfo
    { _accountNumber :: !(Maybe Text)
    , _accountNumberHash :: !(Maybe Text)
    , _ifsc :: !(Maybe Text)
    , _accountHash :: !(Maybe Text)
    , _bankIIN :: !(Maybe Text)
    , _maskedAccountNumber :: !(Maybe Text)
    , _payerNumber :: !(Maybe Text)
    , _payerNumberHash :: !(Maybe Text)
    , _payerName :: !(Maybe Text)
    , _payerNameHash :: !(Maybe Text)
    , _payerMobileNumber :: !(Maybe Text)
    , _payerMobileNumberHash :: !(Maybe Text)
    , _upiNumber :: !(Maybe Text)
    , _upiNumberHash :: !(Maybe Text)
    , _someDum :: !(Maybe Text)
    } deriving (Show, Eq, Generic, Ord)

$(deriveSerialize ''PayerInfo)
$(makeStore ''PayerInfo)

instance Arbitrary PayerInfo where
    arbitrary =
        PayerInfo <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary

-- add more fields if required to PayeeInfo
data PayeeInfo  =
  PayeeInfo
    { _vpa :: !(Maybe Text)
    , _vpaHash :: !(Maybe Text)
    , _isVerifiedPayee :: !(Maybe Bool)
    , _name :: !(Maybe Text)
    , _nameHash :: !(Maybe Text)
    , _mobileNumber :: !(Maybe Text)
    , _mobileNumberHash :: !(Maybe Text)
    , _isMarkedSpam :: !(Maybe Bool)
    , _upiNumber :: !(Maybe Text)
    , _upiNumberHash :: !(Maybe Text)
    , _maskedAccountNumber :: !(Maybe Text)
    , _bankIIN :: !(Maybe Text)
    } deriving (Show, Eq, Generic, Ord)

$(deriveSerialize ''PayeeInfo)
$(makeStore ''PayeeInfo)

instance Arbitrary PayeeInfo where
    arbitrary =
        PayeeInfo <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary

-- add more fields if required to NpciResponse
data NpciResponse  =
  NpciResponse
    { _error :: !(Maybe Bool)
    , _code :: !(Maybe Text)
    , _result :: !Text
    , _note :: !(Maybe Text)
    , _errCode :: !(Maybe Text)
    , _errorCode :: !(Maybe Text)
    , _userMessage :: !(Maybe Text)
    , _sherlockError :: !(Maybe Bool)
    , _orgErrCode :: !(Maybe Text)
    , _orgStatus :: !(Maybe Text)
    } deriving (Show, Eq, Generic, Ord)

instance Arbitrary NpciResponse where
    arbitrary =
        NpciResponse <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary

$(deriveSerialize ''NpciResponse)
$(makeStore ''NpciResponse)

-- add more fields if required to TxnInfo
data TxnInfo  =
  TxnInfo
    { _payType :: !Text              -- "payType"
    , _udfParameters :: !(Maybe Text)
    , _merchantRequestId :: !(Maybe Text)
    , _merchantCustomerId :: !(Maybe Text)
    -- The following fields are wildly unchecked, and additional
    -- fields may be missing.
    -- (JSON field names from DB are labeled in quotes.)
    , _tiEntity :: !(Maybe Text)         -- "mc"
    , _tiPayeeAddress :: !(Maybe Text)   -- "pa"
    , _tiPayeeAddressHash :: !(Maybe Text)   -- "hashed pa"
    , _tiPayeeName :: !(Maybe Text)      -- "pn"
    , _tiPayeeNameHash :: !(Maybe Text)      -- "hashed pn"
    , _tiPayeeMcc :: !(Maybe Text)       -- "mc"
    , _tiTxnRef :: !(Maybe Text)         -- "tr"
    , _tiTxnNote :: !(Maybe Text)        -- "tn"
    , _tiTxnMinimumAmount :: !(Maybe Text) -- "mam"
    , _tiRefUrl :: !(Maybe Text)         -- "url"
    , _tiPayeeCurency :: !(Maybe Text)   -- "curr"
    , _tiMerchantRequestId :: !(Maybe Text) -- "mr"
    , _tiRiskScore :: !(Maybe Text) -- "riskScore"
    , _tiCode :: !(Maybe Text)
    , _tpvRefFailed :: !(Maybe Bool)
    } deriving (Show, Eq, Generic, Ord)

$(deriveSerialize ''TxnInfo)
$(makeStore ''TxnInfo)

instance Arbitrary TxnInfo where
    arbitrary =
        TxnInfo <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary

data Transaction  = Transaction
  { _id :: !Text
  , _mode :: !TransactionMode
  , __type :: !TransactionType
  , _myval :: !(Maybe Text)
  , _amount :: !Double
  , _expiry :: !(Maybe LocalTime)
  , _status :: !TransactionStatus
  , _channel :: !(Maybe TransactionChannel)
  , _purpose :: !(Maybe Text)
  , _remarks :: !Text
  , _txnInfo :: !(Maybe TxnInfo)
  , _currency :: !Text
  , _payeeVpa :: !(Maybe Text)
  , _payerVpa :: !(Maybe Text)
  , _upiMsgId :: !(Maybe Text)
  , _createdAt :: !LocalTime
  , _payeeInfo :: !(Maybe PayeeInfo)
  , _payerInfo :: !(Maybe PayerInfo)
  , _seqNumber :: !(Maybe Int)
  , _updatedAt :: !LocalTime
  , __MandateId :: !(Maybe Text)
  , __CustomerId :: !(Maybe Text)
  , __MerchantId :: !(Maybe Text)
  , _completedAt :: !(Maybe LocalTime)
  , _callbackSent :: !(Maybe Bool)
  , _npciResponse :: !(Maybe NpciResponse)
  , _payeeVpaHash :: !(Maybe Text)
  , _payerVpaHash :: !(Maybe Text)
  , _upiRequestId :: !Text
  , _selfInitiated :: !(Maybe Bool)
  , _upiResponseId :: !(Maybe Text)
  , _callbackStatus :: !(Maybe TransactionCallbackStatus)
  , _initiationMode :: !(Maybe Text)
  , __MerchantCustomerId :: !(Maybe Text)
  } deriving (Generic, Show, Eq)

$(deriveSerialize ''Transaction)
$(makeStore ''Transaction)

-- $(RecordTH.deriveSerialize ''Transaction)
-- $(JInternal.makeJStore ''Transaction)

instance Arbitrary Transaction where
    arbitrary =
        Transaction <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary


-------------------------------------------------------------------------------
-- Benchmarks
-------------------------------------------------------------------------------

-- XXX Why forall?
{-# INLINE benchConst #-}
benchConst ::
       String
    -> (forall a. (Eq a, SERIALIZE_CLASS a, Store a, Show a) => a -> Int)
    -> (forall a. (Eq a, SERIALIZE_CLASS a, Store a, Show a) => Int -> a -> Int -> IO ())
    -> Int
    -> Benchmark
benchConst gname gtSize f times =
    bgroup gname
       [ let !n = gtSize Unit
          in benchSink "Unit" times (f n Unit)
       , let !n = gtSize CDT1C1
          in benchSink "C1" times (f n CDT1C1)
       , let val = CDT1C2 5
             !n = gtSize val
          in benchSink "C2" (times `div` 2) (f n val)
       , let val = CDT1C3 5 2
             !n = gtSize val
          in benchSink "C3" (times `div` 3) (f n val)
       , let !n = gtSize Sum21
          in benchSink "Sum2" times (f n Sum21)
       , let !n = gtSize Sum2525
          in benchSink "Sum25" times (f n Sum2525)
       , let val = Product25 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25
             !n = gtSize val
          in benchSink "Product25" (times `div` 26) (f n val)
        ]

#ifndef USE_UNBOX
{-# INLINE benchVar #-}
benchVar ::
       String
    -> (forall a. (Eq a, SERIALIZE_CLASS a, Store a, Show a) => a -> Int)
    -> (forall a. (Eq a, SERIALIZE_CLASS a, Store a, Show a) => Int -> a -> Int -> IO ())
    -> BinTree Int
    -> [Int]
    -> Int
    -> Benchmark
benchVar gname gtSize f tInt lInt times =
    bgroup gname
       [ let !n = gtSize tInt
           in benchSink "bintree-int" times (f n tInt)
        , let !n = gtSize lInt
           in benchSink "list-int" times (f n lInt)
        ]

{-# INLINE benchTransaction #-}
benchTransaction ::
       String
    -> (forall a. (Eq a, SERIALIZE_CLASS a, Store a, Show a) => a -> Int)
    -> (forall a. (Eq a, SERIALIZE_CLASS a, Store a, Show a) => Int -> a -> Int -> IO ())
    -> Transaction
    -> Int
    -> Benchmark
benchTransaction gname gtSize f transaction times =
    bgroup gname
        [ let !n = gtSize transaction
           in benchSink "Transaction" times (f n transaction)
        ]
#endif

-- Times is scaled by the number of constructors to normalize
#ifdef USE_UNBOX
allBenchmarks :: Int -> [Benchmark]
allBenchmarks times =
#else
allBenchmarks :: BinTree Int -> [Int] -> Transaction -> Int -> [Benchmark]
allBenchmarks tInt lInt transaction times =
#endif
    [ bgroup "sizeOf"
        [
#ifndef USE_UNBOX
          bench "bintree-int" $ nf getSize tInt
        , bench "list-int" $ nf getSize lInt
#endif
        ]

    , benchConst "poke" getSize (const pokeTimes) times
    , benchConst "pokeStore" Store.getSize (const pokeTimesStore) times
    , benchConst "pokeWithSize" getSize (const pokeTimesWithSize) times
    , benchConst "pokeWithSizeStore" Store.getSize (const pokeTimesWithSizeStore) times
    , benchConst "peek" getSize peekTimes times
    , benchConst "peekStore" Store.getSize peekTimesStore times
    , benchConst "roundtrip" getSize (const roundtrip) times
    , benchConst "roundtripStore" Store.getSize (const roundtripStore) times
#ifndef USE_UNBOX
    , benchVar "poke" getSize (const pokeTimes) tInt lInt 1
    , benchVar "pokeStore" Store.getSize (const pokeTimesStore) tInt lInt 1
    , benchVar "pokeWithSize" getSize (const pokeTimesWithSize) tInt lInt 1
    , benchVar "pokeWithSizeStore" Store.getSize (const pokeTimesWithSizeStore) tInt lInt 1
    , benchVar "peek" getSize peekTimes tInt lInt 1
    , benchVar "peekStore" Store.getSize peekTimesStore tInt lInt 1
    , benchVar "roundtrip" getSize (const roundtrip) tInt lInt 1
    , benchVar "roundtripStore" Store.getSize (const roundtripStore) tInt lInt 1
    , benchTransaction "poke" getSize (const pokeTimes) transaction (times `div` 25)
    , benchTransaction "pokeStore" Store.getSize (const pokeTimesStore) transaction (times `div` 25)
    , benchTransaction "pokeWithSize" getSize (const pokeTimesWithSize) transaction (times `div` 25)
    , benchTransaction "pokeWithSizeStore" Store.getSize (const pokeTimesWithSizeStore) transaction (times `div` 25)
    , benchTransaction "peek" getSize peekTimes transaction (times `div` 25)
    , benchTransaction "peekStore" Store.getSize peekTimesStore transaction (times `div` 25)
    , benchTransaction "roundtrip" getSize (const roundtrip) transaction (times `div` 25)
    , benchTransaction "roundtripStore" Store.getSize (const roundtripStore) transaction (times `div` 25)

#endif
    ]

-------------------------------------------------------------------------------
-- Driver
-------------------------------------------------------------------------------

main :: IO ()
main = do
#ifndef USE_UNBOX
    -- Approximately 100000 constructors
    -- Assuming Leaf nodes constitute two constructors (Leaf, Int) and internal
    -- nodes 1 level = log_2 (100001/3) + 1 = 16
    !(tInt :: BinTree Int) <- force <$> mkBinTree 16

    -- Approximately 100000 constructors, assuming two constructors (Cons, Int)
    -- per element.
    let lInt = [1..50000 :: Int]
    let !len = length lInt -- evaluate the list


    !(transaction :: Transaction) <- generate arbitrary
    -- print transaction
    -- undefined
#endif
#ifndef FUSION_CHECK
    -- This can take too much memory/CPU, need to restrict the test
    -- runQC
#ifdef USE_UNBOX
    runWithCLIOpts defaultStreamSize allBenchmarks
#else
    len `seq` runWithCLIOpts defaultStreamSize (allBenchmarks tInt lInt transaction)
#endif
#else
    -- Enable FUSION_CHECK macro at the beginning of the file
    -- Enable one benchmark below, and run the benchmark
    -- Check the .dump-simpl output
    let value = 100000
    -- print $ getSize (CDT1C3 4 2)
    -- print $ getSize tInt
    -- print $ getSize lInt

    -- pokeTimes tInt 1

    -- peekTimes ((CDT1C2 (5 :: Int)) :: CustomDT1) value
    -- peekTimes (Sum2525) value
    -- peekTimes (Product25 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25) value
    -- peekTimes tInt 1
    let !n = getSize lInt
    peekTimes n lInt 1

    -- roundtrip ((CDT1C2 (5 :: Int)) :: CustomDT1) value
    return ()
#endif
