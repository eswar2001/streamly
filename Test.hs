{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where


import Streamly.Internal.Data.Serialize.RecordTH
import Streamly.Internal.Data.Serialize.JInternal
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Streamly.Internal.Data.Serialize hiding (Size, decode, encode, size)

import qualified Streamly.Internal.Data.Serialize as Serialize

import Data.Store

import qualified Streamly.Internal.Data.Unbox as Unbox
import Streamly.Internal.Data.Unbox
    ( MutableByteArray
    , PinnedState(..)
    , Unbox(..)
    )


data RecordDT0 =
    RecordDT0
        { f :: Maybe Int
        }
    deriving (Eq, Show)

$(deriveSerialize ''RecordDT0)
$(makeJStore ''RecordDT0)

{-
{-

data Transaction =
    Transaction
        { _id :: Maybe Int
        , _mode :: Maybe Int
        , __type :: Maybe Int
        , _myval :: Maybe Int
        , _amount :: Maybe Int
        , _expiry :: Maybe Int
        , _status :: Maybe Int
        , _channel :: Maybe Int
        , _purpose :: Maybe Int
        , _remarks :: Maybe Int
        , _txnInfo :: Maybe Int
        , _currency :: Maybe Int
        , _payeeVpa :: Maybe Int
        , _payerVpa :: Maybe Int
        , _upiMsgId :: Maybe Int
        , _createdAt :: Maybe Int
        , _payeeInfo :: Maybe Int
        , _payerInfo :: Maybe Int
        , _seqNumber :: Maybe Int
        , _updatedAt :: Maybe Int
        , __MandateId :: Maybe Int
        , __CustomerId :: Maybe Int
        , __MerchantId :: Maybe Int
        , _completedAt :: Maybe Int
        , _callbackSent :: Maybe Int
        , _npciResponse :: Maybe Int
        , _payeeVpaHash :: Maybe Int
        , _payerVpaHash :: Maybe Int
        , _upiRequestId :: Maybe Int
        , _selfInitiated :: Maybe Int
        , _upiResponseId :: Maybe Int
        , _callbackStatus :: Maybe Int
        , _initiationMode :: Maybe Int
        , __MerchantCustomerId :: Maybe Int
        }
    deriving (Show, Eq)

$(deriveSerialize ''Transaction)
-}

data RecordDT1 =
    RecordDT1
        { field0 :: Maybe Int
        , field2 :: Maybe Char
        , field4 :: Maybe Double
        , field6 :: Maybe Bool
        }
    deriving (Eq, Show)

data RecordDT2 =
    RecordDT2
        { field0 :: Maybe Int
        , field2 :: Maybe Char
        }
    deriving (Eq, Show)

data RecordDT3 =
    RecordDT3
        { field0 :: Maybe Int
        , field4 :: Maybe Double
        }
    deriving (Eq, Show)

data RecordDT4 =
    RecordDT4
        { field4 :: Maybe Double
        , field6 :: Maybe Bool
        }
    deriving (Eq, Show)

data RecordDT5 =
    RecordDT5
        { fld0 :: Maybe Float
        , fld1 :: Maybe Float
        , field0 :: Maybe Int
        , field1 :: Maybe Float
        , field2 :: Maybe Char
        , field3 :: Maybe Float
        , field4 :: Maybe Double
        , field5 :: Maybe Float
        , field6 :: Maybe Bool
        , field7 :: Maybe Float
        , field8 :: Maybe Float
        }
    deriving (Eq, Show)

data RecordDT6 =
    RecordDT6
        { fld0 :: Float
        }
    deriving (Eq, Show)

$(deriveSerialize ''RecordDT1)
$(deriveSerialize ''RecordDT2)
$(deriveSerialize ''RecordDT3)
$(deriveSerialize ''RecordDT4)
$(deriveSerialize ''RecordDT5)
$(deriveSerialize ''RecordDT6)

$(makeJStore ''RecordDT1)
$(makeJStore ''RecordDT2)
$(makeJStore ''RecordDT3)
$(makeJStore ''RecordDT4)
$(makeJStore ''RecordDT5)
$(makeJStore ''RecordDT6)

record = RecordDT1 (Just 3) (Just 'c') (Just 5.5) (Just True)
-- record = RecordDT1 Nothing Nothing Nothing Nothing

test2 = do
    let len =
            case Serialize.size :: Serialize.Size RecordDT1 of
                Serialize.Size f -> f 0 record

    print len
    mbarr <- Unbox.newBytesAs Unpinned len
    off <- serialize 0 mbarr record
    print off

    let encoded = encode record

    putStrLn "----------------"

    (off_, val) <- deserialize 0 mbarr
    print off_
    print (val :: RecordDT1)
    print (decode encoded :: Either PeekException RecordDT1)

    putStrLn "----------------"

    (off_, val) <- deserialize 0 mbarr
    print off_
    print (val :: RecordDT2)
    print (decode encoded :: Either PeekException RecordDT2)

    putStrLn "----------------"

    (off_, val) <- deserialize 0 mbarr
    print off_
    print (val :: RecordDT3)
    print (decode encoded :: Either PeekException RecordDT3)

    putStrLn "----------------"

    (off_, val) <- deserialize 0 mbarr
    print off_
    print (val :: RecordDT4)
    print (decode encoded :: Either PeekException RecordDT4)

    putStrLn "----------------"

    (off_, val) <- deserialize 0 mbarr
    print off_
    print (val :: RecordDT5)
    print (decode encoded :: Either PeekException RecordDT5)

    pure ()

main :: IO ()
main = test2

-}

main = putStrLn "Hi"
