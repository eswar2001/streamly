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

module Transaction (Transaction) where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

import Data.Word (Word16)
import Control.DeepSeq (NFData(..))
import GHC.Generics (Generic)
import System.Random (randomRIO)
import Test.QuickCheck (Arbitrary, arbitrary)

import Control.DeepSeq (force)
import Test.QuickCheck (oneof, elements, generate)
import Streamly.Internal.Data.Unbox (newBytes, MutableByteArray)
import Streamly.Internal.Data.Serialize
import Streamly.Internal.Data.Serialize.TH
import Streamly.Internal.Data.Serialize.RecordTH2

import Gauge
import Streamly.Benchmark.Common

#define SERIALIZE_CLASS Serialize
#define DERIVE_CLASS deriveSerialize
#define SERIALIZE_OP serialize
#define DESERIALIZE_OP deserialize

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

{-
instance Serialize Text where
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
    -- XXX Use shift instead
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
    -- XXX Use shift instead
    len16 = len8 `div` 2
    off16 = off8 `div` 2
    !(MutableByteArray marr#) = arrContents
-}

instance Serialize Text where
    size =
        Size $ \i (Text (TArr.Array _) _ len16) ->
            i + len16 * 2 + 8 -- XXX sizeof Int

    -- XXX Need to check the bounds here
    {-# INLINE deserialize #-}
    deserialize off arr end = do
        (off1, len16) <- deserialize off arr end :: IO (Int, Int)
        let lenBytes = len16 * 2

        -- XXX Check the available length in input buffer
        if (off1 + lenBytes <= end)
        then do
            newArr <- Unbox.newBytes lenBytes
            -- XXX We can perform an unrolled word copy directly
            Unbox.putSliceUnsafe arr off1 newArr 0 lenBytes
            pure
                ( off1 + lenBytes
                , Text (TArr.Array (unsafeCoerce# (Unbox.getMutableByteArray# newArr))) 0 len16
                )
        else error $ "deserialize: Text: input buffer underflow: off1 = "
                ++ show off1 ++ " lenBytes = " ++ show lenBytes
                ++ " end = " ++ show end

    {-# INLINE serialize #-}
    serialize off arr (Text (TArr.Array barr#) off16 len16) = do
        off1 <- serialize off arr (len16 :: Int)
        let lenBytes = len16 * 2
        Unbox.putSliceUnsafe
            (MutableByteArray (unsafeCoerce# barr#)) (off16 * 2)
            arr off1
            lenBytes
        pure (off1 + lenBytes)

instance Arbitrary Text where
    arbitrary = T.pack <$> arbitrary

data TransactionMode
    = IFSC
    | UPI
    deriving (Generic, Show, Eq, Ord, Read, Enum)

instance NFData TransactionMode where
    {-# INLINE rnf #-}
    rnf _ = ()

instance Arbitrary TransactionMode where
    arbitrary = elements [IFSC, UPI]

$(deriveSerialize ''TransactionMode)
$(makeStore ''TransactionMode)

data TransactionType
    = PAY
    | COLLECT
    deriving (Generic, Show, Eq, Ord, Read, Enum)

instance NFData TransactionType where
    {-# INLINE rnf #-}
    rnf _ = ()

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

instance NFData TransactionStatus where
    {-# INLINE rnf #-}
    rnf _ = ()

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

instance NFData TransactionChannel where
    {-# INLINE rnf #-}
    rnf _ = ()

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

instance NFData TransactionCallbackStatus where
    {-# INLINE rnf #-}
    rnf _ = ()

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

instance NFData CollectType where
    {-# INLINE rnf #-}
    rnf _ = ()

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

instance NFData PayerInfo where
    {-# INLINE rnf #-}
    rnf (PayerInfo {..}) =
        rnf _accountNumber `seq`
        rnf _accountNumberHash `seq`
        rnf _ifsc `seq`
        rnf _accountHash `seq`
        rnf _bankIIN `seq`
        rnf _maskedAccountNumber `seq`
        rnf _payerNumber `seq`
        rnf _payerNumberHash `seq`
        rnf _payerName `seq`
        rnf _payerNameHash `seq`
        rnf _payerMobileNumber `seq`
        rnf _payerMobileNumberHash `seq`
        rnf _upiNumber `seq` rnf _upiNumberHash `seq` rnf _someDum

$(deriveSerialize ''PayerInfo)
$(makeStore ''PayerInfo)

instance Arbitrary PayerInfo where
    arbitrary =
        PayerInfo <$> (Just <$> arbitrary) <*> (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary)

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

instance NFData PayeeInfo where
    {-# INLINE rnf #-}
    rnf (PayeeInfo {..}) =
        rnf _vpa `seq`
        rnf _vpaHash `seq`
        rnf _isVerifiedPayee `seq`
        rnf _name `seq`
        rnf _nameHash `seq`
        rnf _mobileNumber `seq`
        rnf _mobileNumberHash `seq`
        rnf _isMarkedSpam `seq`
        rnf _upiNumber `seq`
        rnf _upiNumberHash `seq` rnf _maskedAccountNumber `seq` rnf _bankIIN

$(deriveSerialize ''PayeeInfo)
$(makeStore ''PayeeInfo)

instance Arbitrary PayeeInfo where
    arbitrary =
        PayeeInfo <$> (Just <$> arbitrary) <*> (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary)

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

instance NFData NpciResponse where
    {-# INLINE rnf #-}
    rnf (NpciResponse {..}) =
        rnf _error `seq`
        rnf _code `seq`
        rnf _result `seq`
        rnf _note `seq`
        rnf _errCode `seq`
        rnf _errorCode `seq`
        rnf _userMessage `seq`
        rnf _sherlockError `seq` rnf _orgErrCode `seq` rnf _orgStatus

instance Arbitrary NpciResponse where
    arbitrary =
        NpciResponse <$> (Just <$> arbitrary) <*> (Just <$> arbitrary) <*>
        arbitrary <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary)

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

instance NFData TxnInfo where
    {-# INLINE rnf #-}
    rnf (TxnInfo {..}) =
        rnf _payType `seq`
        rnf _udfParameters `seq`
        rnf _merchantRequestId `seq`
        rnf _merchantCustomerId `seq`
        rnf _tiEntity `seq`
        rnf _tiPayeeAddress `seq`
        rnf _tiPayeeAddressHash `seq`
        rnf _tiPayeeName `seq`
        rnf _tiPayeeNameHash `seq`
        rnf _tiPayeeMcc `seq`
        rnf _tiTxnRef `seq`
        rnf _tiTxnNote `seq`
        rnf _tiTxnMinimumAmount `seq`
        rnf _tiRefUrl `seq`
        rnf _tiPayeeCurency `seq`
        rnf _tiMerchantRequestId `seq`
        rnf _tiRiskScore `seq` rnf _tiCode `seq` rnf _tpvRefFailed

$(deriveSerialize ''TxnInfo)
$(makeStore ''TxnInfo)

instance Arbitrary TxnInfo where
    arbitrary =
        TxnInfo <$> arbitrary <*> (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary)

data Transaction  = Transaction
  { _id :: !Text
  , _payerVpa :: !(Maybe Text)
  , _payerVpaHash :: !(Maybe Text)
  , _payeeVpa :: !(Maybe Text)
  , _payeeVpaHash :: !(Maybe Text)
  , _payerInfo :: !(Maybe PayerInfo)
  , _payeeInfo :: !(Maybe PayeeInfo)
  , _txnInfo :: !(Maybe TxnInfo)
  , _selfInitiated :: !(Maybe Bool)
  , _mode :: !TransactionMode
  , _amount :: !Double
  , _upiRequestId :: !Text
  , __type :: !TransactionType
  , _status :: !TransactionStatus
  , _upiMsgId :: !(Maybe Text)
  , _npciResponse :: !(Maybe NpciResponse)
  , _remarks :: !Text
  , _expiry :: !(Maybe LocalTime)
  , _currency :: !Text
  , _upiResponseId :: !(Maybe Text)
  , __CustomerId :: !(Maybe Text)
  , __MerchantId :: !(Maybe Text)
  , __MerchantCustomerId :: !(Maybe Text)
  , _channel :: !(Maybe TransactionChannel)
  , _callbackSent :: !(Maybe Bool)
  , _callbackStatus :: !(Maybe TransactionCallbackStatus)
  , _completedAt :: !(Maybe LocalTime)
  , _initiationMode :: !(Maybe Text)
  , _purpose :: !(Maybe Text)
  , __MandateId :: !(Maybe Text)
  , _seqNumber :: !(Maybe Int)
  , _createdAt :: !LocalTime
  , _updatedAt :: !LocalTime
  , _myval :: !(Maybe Text)
  } deriving (Generic, Show, Eq)

$(deriveSerialize ''Transaction)
-- $(makeStore ''Transaction)

-- $(deriveCompatSerialize ''Transaction)
-- $(RecordTH.deriveSerialize ''Transaction)
$(JInternal.makeJStore ''Transaction)

instance Arbitrary Transaction where
    arbitrary =
        Transaction <$> arbitrary <*> (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        arbitrary <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        arbitrary <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        arbitrary <*>
        (Just <$> arbitrary) <*>
        arbitrary <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        (Just <$> arbitrary) <*>
        arbitrary <*>
        arbitrary <*>
        (Just <$> arbitrary)

instance NFData Transaction where
    {-# INLINE rnf #-}
    rnf (Transaction {..}) =
        rnf _id `seq`
        rnf _payerVpa `seq`
        rnf _payerVpaHash `seq`
        rnf _payeeVpa `seq`
        rnf _payeeVpaHash `seq`
        rnf _payerInfo `seq`
        rnf _payeeInfo `seq`
        rnf _txnInfo `seq`
        rnf _selfInitiated `seq`
        rnf _mode `seq`
        rnf _amount `seq`
        rnf _upiRequestId `seq`
        rnf __type `seq`
        rnf _status `seq`
        rnf _upiMsgId `seq`
        rnf _npciResponse `seq`
        rnf _remarks `seq`
        rnf _expiry `seq`
        rnf _currency `seq`
        rnf _upiResponseId `seq`
        rnf __CustomerId `seq`
        rnf __MerchantId `seq`
        rnf __MerchantCustomerId `seq`
        rnf _channel `seq`
        rnf _callbackSent `seq`
        rnf _callbackStatus `seq`
        rnf _completedAt `seq`
        rnf _initiationMode `seq`
        rnf _purpose `seq`
        rnf __MandateId `seq`
        rnf _seqNumber `seq`
        rnf _createdAt `seq` rnf _updatedAt `seq` rnf _myval
