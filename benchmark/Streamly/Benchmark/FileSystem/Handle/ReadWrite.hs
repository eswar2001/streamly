-- |
-- Module      : Streamly.Benchmark.FileSystem.Handle
-- Copyright   : (c) 2019 Composewell Technologies
-- License     : BSD3-3-Clause
-- Maintainer  : streamly@composewell.com
-- Stability   : experimental
-- Portability : GHC

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

#ifdef __HADDOCK_VERSION__
#undef INSPECTION
#endif

#ifdef INSPECTION
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Test.Inspection.Plugin #-}
#endif

module Handle.ReadWrite
    (allBenchmarks)
where

import System.IO (Handle)
import Prelude hiding (last, length)
import Streamly.Internal.System.IO (defaultChunkSize)

import qualified Streamly.FileSystem.Handle as FH
import qualified Streamly.Internal.Data.Unfold as IUF
import qualified Streamly.Internal.FileSystem.Handle as IFH
import qualified Streamly.Data.Array.Unboxed as A
import qualified Streamly.Prelude as S

import Gauge hiding (env)
import Streamly.Benchmark.Common.Handle

#ifdef INSPECTION
import Streamly.Internal.Data.Stream.StreamD.Type (Step(..))

import qualified Streamly.Internal.Data.Stream.StreamD.Type as D
import qualified Streamly.Internal.Data.Tuple.Strict as Strict
import qualified Streamly.Internal.Data.Array.Stream.Mut.Foreign as MAS
import qualified Streamly.Internal.Data.Array.Foreign.Type as AT
import qualified Streamly.Internal.Data.Array.Foreign.Mut.Type as MA

import Test.Inspection
#endif

-------------------------------------------------------------------------------
-- copy chunked
-------------------------------------------------------------------------------

-- | Copy file
copyChunks :: Handle -> Handle -> IO ()
copyChunks inh outh = S.fold (IFH.writeChunks outh) $ IFH.getChunks inh

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'copyChunks
inspect $ 'copyChunks `hasNoType` ''Step
#endif

o_1_space_copy_chunked :: BenchEnv -> [Benchmark]
o_1_space_copy_chunked env =
    [ bgroup "copy/getChunks"
        [ mkBench "toNull" env $ \inH _ ->
            copyChunks inH (nullH env)
        , mkBench "raw" env $ \inH outH ->
            copyChunks inH outH
        ]
    ]

-------------------------------------------------------------------------------
-- copy unfold
-------------------------------------------------------------------------------

-- | Copy file
copyStream :: Handle -> Handle -> IO ()
copyStream inh outh = S.fold (FH.write outh) (S.unfold FH.read inh)

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'copyStream
inspect $ 'copyStream `hasNoType` ''Step -- S.unfold
inspect $ 'copyStream `hasNoType` ''IUF.ConcatState -- FH.read/UF.many
inspect $ 'copyStream `hasNoType` ''MA.ReadUState  -- FH.read/A.read
inspect $ 'copyStream `hasNoType` ''AT.ArrayUnsafe -- FH.write/writeNUnsafe
inspect $ 'copyStream `hasNoType` ''Strict.Tuple3' -- FH.write/chunksOf
#endif

o_1_space_copy_read :: BenchEnv -> [Benchmark]
o_1_space_copy_read env =
    [ bgroup "copy/read"
        [ mkBench "rawToNull" env $ \inh _ ->
            copyStream inh (nullH env)
        , mkBench "rawToFile" env $ \inh outh ->
            copyStream inh outh
        ]
    ]

-------------------------------------------------------------------------------
-- copy stream
-------------------------------------------------------------------------------

-- | Send the file contents to /dev/null
readFromBytesNull :: Handle -> Handle -> IO ()
readFromBytesNull inh devNull = IFH.putBytes devNull $ S.unfold FH.read inh

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'readFromBytesNull
inspect $ 'readFromBytesNull `hasNoType` ''Step
inspect $ 'readFromBytesNull `hasNoType` ''MAS.SpliceState
inspect $ 'readFromBytesNull `hasNoType` ''AT.ArrayUnsafe -- FH.fromBytes/S.arraysOf
inspect $ 'readFromBytesNull `hasNoType` ''D.FoldMany
#endif

-- | Send the file contents ('defaultChunkSize') to /dev/null
readWithFromBytesNull :: Handle -> Handle -> IO ()
readWithFromBytesNull inh devNull =
    IFH.putBytes devNull
        $ S.unfold FH.readWith (defaultChunkSize, inh)

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'readWithFromBytesNull
inspect $ 'readWithFromBytesNull `hasNoType` ''Step
inspect $ 'readWithFromBytesNull `hasNoType` ''MAS.SpliceState
inspect $ 'readWithFromBytesNull `hasNoType` ''AT.ArrayUnsafe -- FH.fromBytes/S.arraysOf
inspect $ 'readWithFromBytesNull `hasNoType` ''D.FoldMany
#endif

-- | Send the chunk content ('defaultChunkSize') to /dev/null
-- Implicitly benchmarked via 'readFromBytesNull'
_readChunks :: Handle -> Handle -> IO ()
_readChunks inh devNull = IUF.fold fld unf inh

    where

    fld = FH.write devNull
    unf = IUF.many A.read FH.readChunks

-- | Send the chunk content to /dev/null
-- Implicitly benchmarked via 'readWithFromBytesNull'
_readChunksWith :: Handle -> Handle -> IO ()
_readChunksWith inh devNull = IUF.fold fld unf (defaultChunkSize, inh)

    where

    fld = FH.write devNull
    unf = IUF.many A.read FH.readChunksWith

o_1_space_copy_fromBytes :: BenchEnv -> [Benchmark]
o_1_space_copy_fromBytes env =
    [ bgroup "copy/putBytes"
        [ mkBench "rawToNull" env $ \inh _ ->
            readFromBytesNull inh (nullH env)
        , mkBench "FH.readWith" env $ \inh _ ->
            readWithFromBytesNull inh (nullH env)
        ]
    ]

-- | Send the file contents ('defaultChunkSize') to /dev/null
writeReadWith :: Handle -> Handle -> IO ()
writeReadWith inh devNull = IUF.fold fld unf (defaultChunkSize, inh)

    where

    fld = FH.writeWith defaultChunkSize devNull
    unf = FH.readWith

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'writeReadWith
inspect $ 'writeReadWith `hasNoType` ''Step
inspect $ 'writeReadWith `hasNoType` ''IUF.ConcatState -- FH.read/UF.many
inspect $ 'writeReadWith `hasNoType` ''MA.ReadUState  -- FH.read/A.read
inspect $ 'writeReadWith `hasNoType` ''AT.ArrayUnsafe -- FH.write/writeNUnsafe
#endif

-- | Send the file contents ('AT.defaultChunkSize') to /dev/null
writeRead :: Handle -> Handle -> IO ()
writeRead inh devNull = IUF.fold fld unf inh

    where

    fld = FH.write devNull
    unf = FH.read

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'writeRead
inspect $ 'writeRead `hasNoType` ''Step
inspect $ 'writeRead `hasNoType` ''IUF.ConcatState -- FH.read/UF.many
inspect $ 'writeRead `hasNoType` ''MA.ReadUState  -- FH.read/A.read
inspect $ 'writeRead `hasNoType` ''AT.ArrayUnsafe -- FH.write/writeNUnsafe
#endif

o_1_space_copy :: BenchEnv -> [Benchmark]
o_1_space_copy env =
    [ bgroup "copy"
        [ mkBench "FH.write . FH.read" env $ \inh _ ->
            writeRead inh (nullH env)
        , mkBench "FH.writeWith . FH.readWith" env $ \inh _ ->
            writeReadWith inh (nullH env)
        ]
    ]

-------------------------------------------------------------------------------
--
-------------------------------------------------------------------------------

allBenchmarks :: BenchEnv -> [Benchmark]
allBenchmarks env = Prelude.concat
    [ o_1_space_copy_chunked env
    , o_1_space_copy_read env
    , o_1_space_copy_fromBytes env
    , o_1_space_copy env
    ]
