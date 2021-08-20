-- |
-- Module      : Serial.Nested
-- Copyright   : (c) 2018 Composewell Technologies
-- License     : BSD-3-Clause
-- Maintainer  : streamly@composewell.com

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

#ifdef __HADDOCK_VERSION__
#undef INSPECTION
#endif

#ifdef INSPECTION
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Test.Inspection.Plugin #-}
#endif

module Serial.Nested (benchmarks)
where

import Control.Monad.Trans.Class (lift)

import qualified Control.Applicative as AP

#ifdef INSPECTION
import GHC.Types (SPEC(..))
import Test.Inspection

import qualified Streamly.Internal.Data.Stream.StreamD as D
#endif

import qualified Streamly.Prelude  as S
import qualified Streamly.Internal.Data.Stream.IsStream as Internal
import qualified Streamly.Internal.Data.Unfold as UF

import Gauge
import Streamly.Prelude (SerialT, fromSerial, serial)
import Streamly.Benchmark.Common
import Streamly.Benchmark.Prelude
import Prelude hiding (concatMap)

-------------------------------------------------------------------------------
-- Iteration/looping utilities
-------------------------------------------------------------------------------

{-# INLINE iterateN #-}
iterateN :: (Int -> a -> a) -> a -> Int -> a
iterateN g initial count = f count initial

    where

    f (0 :: Int) x = x
    f i x = f (i - 1) (g i x)

-- Iterate a transformation over a singleton stream
{-# INLINE iterateSingleton #-}
iterateSingleton :: S.MonadAsync m
    => (Int -> SerialT m Int -> SerialT m Int)
    -> Int
    -> Int
    -> SerialT m Int
iterateSingleton g count n = iterateN g (return n) count

-- XXX need to check why this is slower than the explicit recursion above, even
-- if the above code is written in a foldr like head recursive way. We also
-- need to try this with foldlM' once #150 is fixed.
-- However, it is perhaps best to keep the iteration benchmarks independent of
-- foldrM and any related fusion issues.
{-# INLINE _iterateSingleton #-}
_iterateSingleton ::
       S.MonadAsync m
    => (Int -> SerialT m Int -> SerialT m Int)
    -> Int
    -> Int
    -> SerialT m Int
_iterateSingleton g value n = S.foldrM g (return n) $ sourceIntFromTo value n

-------------------------------------------------------------------------------
-- Multi-Stream
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Appending
-------------------------------------------------------------------------------

{-# INLINE serial2 #-}
serial2 :: Int -> Int -> IO ()
serial2 count n =
    S.drain $
        S.serial (sourceUnfoldrM count n) (sourceUnfoldrM count (n + 1))

{-# INLINE serial4 #-}
serial4 :: Int -> Int -> IO ()
serial4 count n =
    S.drain $
    S.serial
        (S.serial (sourceUnfoldrM count n) (sourceUnfoldrM count (n + 1)))
        (S.serial
              (sourceUnfoldrM count (n + 2))
              (sourceUnfoldrM count (n + 3)))

{-# INLINE append2 #-}
append2 :: Int -> Int -> IO ()
append2 count n =
    S.drain $
    Internal.append (sourceUnfoldrM count n) (sourceUnfoldrM count (n + 1))

{-# INLINE append4 #-}
append4 :: Int -> Int -> IO ()
append4 count n =
    S.drain $
    Internal.append
        (Internal.append
              (sourceUnfoldrM count n)
              (sourceUnfoldrM count (n + 1)))
        (Internal.append
              (sourceUnfoldrM count (n + 2))
              (sourceUnfoldrM count (n + 3)))

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'append2
inspect $ 'append2 `hasNoType` ''SPEC
inspect $ 'append2 `hasNoType` ''D.AppendState
#endif

-------------------------------------------------------------------------------
-- Merging
-------------------------------------------------------------------------------

{-# INLINE mergeBy #-}
mergeBy :: Int -> Int -> IO ()
mergeBy count n =
    S.drain $
    S.mergeBy
        compare
        (sourceUnfoldrM count n)
        (sourceUnfoldrM count (n + 1))

{-# INLINE mergeByM #-}
mergeByM :: Int -> Int -> IO ()
mergeByM count n =
    S.drain $
    S.mergeByM
        (\a b -> return $ compare a b)
        (sourceUnfoldrM count n)
        (sourceUnfoldrM count (n + 1))

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'mergeBy
inspect $ 'mergeBy `hasNoType` ''SPEC
inspect $ 'mergeBy `hasNoType` ''D.Step

inspect $ hasNoTypeClasses 'mergeByM
inspect $ 'mergeByM `hasNoType` ''SPEC
inspect $ 'mergeByM `hasNoType` ''D.Step
#endif

o_1_space_joining :: Int -> [Benchmark]
o_1_space_joining value =
    [ bgroup "joining"
        [ benchIOSrc1 "serial (2,x/2)" (serial2 (value `div` 2))
        , benchIOSrc1 "append (2,x/2)" (append2 (value `div` 2))
        , benchIOSrc1 "serial (2,2,x/4)" (serial4 (value `div` 4))
        , benchIOSrc1 "append (2,2,x/4)" (append4 (value `div` 4))
        , benchIOSrc1 "mergeBy (2,x/2)" (mergeBy (value `div` 2))
        , benchIOSrc1 "mergeByM (2,x/2)" (mergeByM (value `div` 2))
        ]
    ]

-------------------------------------------------------------------------------
-- Concat Foldable containers
-------------------------------------------------------------------------------

o_1_space_concatFoldable :: Int -> [Benchmark]
o_1_space_concatFoldable value =
    [ bgroup "concat-foldable"
        [ benchIOSrc fromSerial "foldMapWith (<>) (List)"
            (sourceFoldMapWith value)
        , benchIOSrc fromSerial "foldMapWith (<>) (Stream)"
            (sourceFoldMapWithStream value)
        , benchIOSrc fromSerial "foldMapWithM (<>) (List)"
            (sourceFoldMapWithM value)
        , benchIOSrc fromSerial "S.concatFoldableWith (<>) (List)"
            (concatFoldableWith value)
        , benchIOSrc fromSerial "S.concatForFoldableWith (<>) (List)"
            (concatForFoldableWith value)
        , benchIOSrc fromSerial "foldMapM (List)" (sourceFoldMapM value)
        ]
    ]

-------------------------------------------------------------------------------
-- Concat
-------------------------------------------------------------------------------

-- concatMap unfoldrM/unfoldrM

{-# INLINE concatMap #-}
concatMap :: Int -> Int -> Int -> IO ()
concatMap outer inner n =
    S.drain $ S.concatMap
        (\_ -> sourceUnfoldrM inner n)
        (sourceUnfoldrM outer n)

{-# INLINE concatMapM #-}
concatMapM :: Int -> Int -> Int -> IO ()
concatMapM outer inner n =
    S.drain $ S.concatMapM
        (\_ -> return $ sourceUnfoldrM inner n)
        (sourceUnfoldrM outer n)

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'concatMap
inspect $ 'concatMap `hasNoType` ''SPEC
#endif

-- concatMap unfoldr/unfoldr

{-# INLINE concatMapPure #-}
concatMapPure :: Int -> Int -> Int -> IO ()
concatMapPure outer inner n =
    S.drain $ S.concatMap
        (\_ -> sourceUnfoldr inner n)
        (sourceUnfoldr outer n)

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'concatMapPure
inspect $ 'concatMapPure `hasNoType` ''SPEC
#endif

-- concatMap replicate/unfoldrM

{-# INLINE concatMapRepl #-}
concatMapRepl :: Int -> Int -> Int -> IO ()
concatMapRepl outer inner n =
    S.drain $ S.concatMap (S.replicate inner) (sourceUnfoldrM outer n)

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'concatMapRepl
inspect $ 'concatMapRepl `hasNoType` ''SPEC
#endif

-- concatMapWith

{-# INLINE concatMapWithSerial #-}
concatMapWithSerial :: Int -> Int -> Int -> IO ()
concatMapWithSerial = concatStreamsWith S.serial

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'concatMapWithSerial
inspect $ 'concatMapWithSerial `hasNoType` ''SPEC
#endif

{-# INLINE concatMapWithAppend #-}
concatMapWithAppend :: Int -> Int -> Int -> IO ()
concatMapWithAppend = concatStreamsWith Internal.append

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'concatMapWithAppend
inspect $ 'concatMapWithAppend `hasNoType` ''SPEC
#endif

-- concatPairWith

{-# INLINE concatPairWithAppend #-}
concatPairWithAppend :: Int -> Int -> Int -> IO ()
concatPairWithAppend = concatPairsWith Internal.append

{-# INLINE concatPairWithInterleave #-}
concatPairWithInterleave :: Int -> Int -> Int -> IO ()
concatPairWithInterleave = concatPairsWith Internal.interleave

{-# INLINE concatPairWithInterleaveSuffix #-}
concatPairWithInterleaveSuffix :: Int -> Int -> Int -> IO ()
concatPairWithInterleaveSuffix = concatPairsWith Internal.interleaveSuffix

{-# INLINE concatPairWithInterleaveInfix #-}
concatPairWithInterleaveInfix :: Int -> Int -> Int -> IO ()
concatPairWithInterleaveInfix = concatPairsWith Internal.interleaveInfix

{-# INLINE concatPairWithInterleaveMin #-}
concatPairWithInterleaveMin :: Int -> Int -> Int -> IO ()
concatPairWithInterleaveMin = concatPairsWith Internal.interleaveMin

{-# INLINE concatPairWithRoundrobin #-}
concatPairWithRoundrobin :: Int -> Int -> Int -> IO ()
concatPairWithRoundrobin = concatPairsWith Internal.roundrobin

-- unfoldMany

-- unfoldMany replicate/unfoldrM

{-# INLINE unfoldManyRepl #-}
unfoldManyRepl :: Int -> Int -> Int -> IO ()
unfoldManyRepl outer inner n =
    S.drain
         $ S.unfoldMany
               (UF.lmap return (UF.replicateM inner))
               (sourceUnfoldrM outer n)

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'unfoldManyRepl
inspect $ 'unfoldManyRepl `hasNoType` ''D.ConcatMapUState
inspect $ 'unfoldManyRepl `hasNoType` ''SPEC
#endif

o_1_space_concat :: Int -> [Benchmark]
o_1_space_concat value = sqrtVal `seq`
    [ bgroup "concat"
        [ benchIOSrc1 "concatMapPure (n of 1)"
            (concatMapPure value 1)
        , benchIOSrc1 "concatMapPure (sqrt n of sqrt n)"
            (concatMapPure sqrtVal sqrtVal)
        , benchIOSrc1 "concatMapPure (1 of n)"
            (concatMapPure 1 value)

        -- This is for comparison with foldMapWith
        , benchIOSrc fromSerial "concatMapId (n of 1) (fromFoldable)"
            (S.concatMap id . sourceConcatMapId value)

        , benchIOSrc1 "concatMap (n of 1)"
            (concatMap value 1)
        , benchIOSrc1 "concatMap (sqrt n of sqrt n)"
            (concatMap sqrtVal sqrtVal)
        , benchIOSrc1 "concatMap (1 of n)"
            (concatMap 1 value)

        , benchIOSrc1 "concatMapM (n of 1)"
            (concatMapM value 1)
        , benchIOSrc1 "concatMapM (sqrt n of sqrt n)"
            (concatMapM sqrtVal sqrtVal)
        , benchIOSrc1 "concatMapM (1 of n)"
            (concatMapM 1 value)

        -- This is for comparison with foldMapWith
        , benchIOSrc fromSerial "concatMapWithId (n of 1) (fromFoldable)"
            (S.concatMapWith serial id . sourceConcatMapId value)

        , benchIOSrc1 "concatMapWith (n of 1)"
            (concatMapWithSerial value 1)
        , benchIOSrc1 "concatMapWith (sqrt n of sqrt n)"
            (concatMapWithSerial sqrtVal sqrtVal)
        , benchIOSrc1 "concatMapWith (1 of n)"
            (concatMapWithSerial 1 value)

        -- quadratic with number of outer streams
        , benchIOSrc1 "concatMapWithAppend (2 of n/2)"
            (concatMapWithAppend 2 (value `div` 2))

        -- concatMap vs unfoldMany
        , benchIOSrc1 "concatMapRepl (sqrt n of sqrt n)"
            (concatMapRepl sqrtVal sqrtVal)
        , benchIOSrc1 "unfoldManyRepl (sqrt n of sqrt n)"
            (unfoldManyRepl sqrtVal sqrtVal)

        -------------------concatPairsWith-----------------

        , benchIOSrc1 "concatPairWithAppend"
            (concatPairWithAppend 2 (value `div` 2))
        , benchIOSrc1 "concatPairWithInterleave"
        (concatPairWithInterleave 2 (value `div` 2))

        , benchIOSrc1 "concatPairWithInterleaveSuffix"
        (concatPairWithInterleaveSuffix 2 (value `div` 2))

        , benchIOSrc1 "concatPairWithInterleaveInfix"
        (concatPairWithInterleaveInfix 2 (value `div` 2))

        , benchIOSrc1 "concatPairWithInterleaveMin"
        (concatPairWithInterleaveMin 2 (value `div` 2))

        , benchIOSrc1 "concatPairWithRoundrobin"
        (concatPairWithRoundrobin 2 (value `div` 2))

        ]
    ]

    where

    sqrtVal = round $ sqrt (fromIntegral value :: Double)

-------------------------------------------------------------------------------
-- Joining streams
-------------------------------------------------------------------------------
toKvMap :: Int -> (Int, Int)
toKvMap p = (p, p)

mkStreamLen :: (S.IsStream t, S.MonadAsync m) => Int -> t m Int
mkStreamLen count = sourceUnfoldrM count 0

{-# INLINE joinInner #-}
joinInner :: Int -> Int -> Int -> IO ()
joinInner val1 val2 _ =
     S.drain $ Internal.joinInner (==) (mkStreamLen val1) $ mkStreamLen val2

{-# INLINE joinInnerHash #-}
joinInnerHash :: Int -> Int -> Int -> IO ()
joinInnerHash val1 val2 _ =
        S.drain $
            Internal.joinInnerHash
            (fmap toKvMap (mkStreamLen val1))
            (fmap toKvMap (mkStreamLen val2))

{-# INLINE joinInnerMerge #-}
joinInnerMerge :: Int -> Int -> Int -> IO ()
joinInnerMerge val1 val2 _ =
    S.drain $
        Internal.joinInnerMerge compare (mkStreamLen val1) $ mkStreamLen val2

{-# INLINE joinLeft #-}
joinLeft :: Int -> Int -> Int -> IO ()
joinLeft val1 val2 _ =
    S.drain $ Internal.joinLeft (==) (mkStreamLen val1) $ mkStreamLen val2

{-# INLINE joinLeftHash #-}
joinLeftHash :: Int -> Int -> Int -> IO ()
joinLeftHash val1 val2 _ =
        S.drain $
            Internal.joinLeftHash
            (fmap toKvMap (mkStreamLen val1))
            (fmap toKvMap (mkStreamLen val2))

{-# INLINE joinLeftMerge #-}
joinLeftMerge :: Int -> Int -> Int -> IO ()
joinLeftMerge val1 val2 _ =
    S.drain $
        Internal.joinLeftMerge compare (mkStreamLen val1) $ mkStreamLen val2

{-# INLINE joinOuter #-}
joinOuter :: Int -> Int -> Int -> IO ()
joinOuter val1 val2 _ =
    S.drain $ Internal.joinOuter (==) (mkStreamLen val1) $ mkStreamLen val2

{-# INLINE joinOuterHash #-}
joinOuterHash :: Int -> Int -> Int -> IO ()
joinOuterHash val1 val2 _ =
        S.drain $
            Internal.joinOuterHash
            (fmap toKvMap (mkStreamLen val1))
            (fmap toKvMap (mkStreamLen val2))

{-# INLINE joinOuterMerge #-}
joinOuterMerge :: Int -> Int -> Int -> IO ()
joinOuterMerge val1 val2 _ =
    S.drain $
        Internal.joinOuterMerge compare (mkStreamLen val1) $ mkStreamLen val2

{-# INLINE unionBySorted #-}
unionBySorted :: Int -> Int -> Int -> IO ()
unionBySorted val1 val2 _ =
    S.drain $
        Internal.unionBySorted compare (mkStreamLen val1) $ mkStreamLen val2

{-# INLINE differenceBySorted #-}
differenceBySorted :: Int -> Int -> Int -> IO ()
differenceBySorted val1 val2 _ =
    S.drain $
        Internal.differenceBySorted
        compare
        (mkStreamLen val1)
        (mkStreamLen val2)

{-# INLINE intersectBySorted #-}
intersectBySorted :: Int -> Int -> Int -> IO ()
intersectBySorted val1 val2 _ =
    S.drain $
        Internal.intersectBySorted
        compare
        (mkStreamLen val1)
        (mkStreamLen val2)

o_n_heap_buffering :: Int -> [Benchmark]
o_n_heap_buffering value =
    [ bgroup "join"
        [
          benchIOSrc1 "joinInner[Sqrt]" (joinInner value sqrtVal)
        , benchIOSrc1 "joinInnerHash" (joinInnerHash value value)
        , benchIOSrc1 "joinInnerHash[Sqrt]" (joinInnerHash value sqrtVal)
        , benchIOSrc1 "joinInnerMerge" (joinInnerMerge value value)
        , benchIOSrc1 "joinInnerMerge[Sqrt]" (joinInnerMerge value sqrtVal)
        , benchIOSrc1 "joinLeft[Sqrt]" (joinLeft value sqrtVal)
        , benchIOSrc1 "joinLeftHash" (joinLeftHash value value)
        , benchIOSrc1 "joinLeftHash[Sqrt]" (joinLeftHash value sqrtVal)
        , benchIOSrc1 "joinLeftMerge" (joinLeftMerge value value)
        , benchIOSrc1 "joinLeftMerge[Sqrt]" (joinLeftMerge value sqrtVal)
        , benchIOSrc1 "joinOuter[Sqrt]" (joinOuter value sqrtVal)
        , benchIOSrc1 "joinOuterHash" (joinOuterHash value value)
        , benchIOSrc1 "joinOuterHash[Sqrt]" (joinOuterHash value sqrtVal)
        , benchIOSrc1 "joinOuterMerge" (joinOuterMerge value value)
        , benchIOSrc1 "joinOuterMerge[Sqrt]" (joinOuterMerge value sqrtVal)
        , benchIOSrc1 "differenceBySorted" (differenceBySorted value value)
        , benchIOSrc1 "differenceBySorted[Sqrt]" (differenceBySorted value sqrtVal)
        , benchIOSrc1 "unionBySorted" (unionBySorted value value)
        , benchIOSrc1 "unionBySorted[Sqrt]" (unionBySorted value sqrtVal)
        , benchIOSrc1 "intersectBySorted" (intersectBySorted value value)
        , benchIOSrc1 "intersectBySorted[Sqrt]" (intersectBySorted value sqrtVal)
        ]
    ]

    where

    sqrtVal = round $ sqrt (fromIntegral value :: Double)

-------------------------------------------------------------------------------
-- Applicative
-------------------------------------------------------------------------------

o_1_space_applicative :: Int -> [Benchmark]
o_1_space_applicative value =
    [ bgroup "Applicative"
        [ benchIO "(*>) (sqrt n x sqrt n)" $ apDiscardFst value fromSerial
        , benchIO "(<*) (sqrt n x sqrt n)" $ apDiscardSnd value fromSerial
        , benchIO "(<*>) (sqrt n x sqrt n)" $ toNullAp value fromSerial
        , benchIO "liftA2 (sqrt n x sqrt n)" $ apLiftA2 value fromSerial
        ]
    ]

o_n_space_applicative :: Int -> [Benchmark]
o_n_space_applicative value =
    [ bgroup "Applicative"
        [ benchIOSrc fromSerial "(*>) (n times)" $
            iterateSingleton ((*>) . pure) value
        , benchIOSrc fromSerial "(<*) (n times)" $
            iterateSingleton (\x xs -> xs <* pure x) value
        , benchIOSrc fromSerial "(<*>) (n times)" $
            iterateSingleton (\x xs -> pure (+ x) <*> xs) value
        , benchIOSrc fromSerial "liftA2 (n times)" $
            iterateSingleton (AP.liftA2 (+) . pure) value
        ]
    ]

-------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

o_1_space_monad :: Int -> [Benchmark]
o_1_space_monad value =
    [ bgroup "Monad"
        [ benchIO "(>>) (sqrt n x sqrt n)" $ monadThen value fromSerial
        , benchIO "(>>=) (sqrt n x sqrt n)" $ toNullM value fromSerial
        , benchIO "(>>=) (sqrt n x sqrt n) (filterAllOut)" $
            filterAllOutM value fromSerial
        , benchIO "(>>=) (sqrt n x sqrt n) (filterAllIn)" $
            filterAllInM value fromSerial
        , benchIO "(>>=) (sqrt n x sqrt n) (filterSome)" $
            filterSome value fromSerial
        , benchIO "(>>=) (sqrt n x sqrt n) (breakAfterSome)" $
            breakAfterSome value fromSerial
        , benchIO "(>>=) (cubert n x cubert n x cubert n)" $
            toNullM3 value fromSerial
        ]
    ]

-- This is a good benchmark but inefficient way to compute primes. As we see a
-- new prime we keep appending a division filter for all the future numbers.
{-# INLINE sieve #-}
sieve :: Monad m => SerialT m Int -> SerialT m Int
sieve s = do
    r <- lift $ S.uncons s
    case r of
        Just (prime, rest) ->
            prime `S.cons` sieve (S.filter (\n -> n `mod` prime /= 0) rest)
        Nothing -> S.nil

o_n_space_monad :: Int -> [Benchmark]
o_n_space_monad value =
    [ bgroup "Monad"
        [ benchIOSrc fromSerial "(>>) (n times)" $
            iterateSingleton ((>>) . pure) value
        , benchIOSrc fromSerial "(>>=) (n times)" $
            iterateSingleton (\x xs -> xs >>= \y -> return (x + y)) value
        , benchIO "(>>=) (sqrt n x sqrt n) (toList)" $
            toListM value fromSerial
        , benchIO "(>>=) (sqrt n x sqrt n) (toListSome)" $
            toListSome value fromSerial
        , benchIO "naive prime sieve (n/4)"
            (\n -> S.sum $ sieve $ S.enumerateFromTo 2 (value `div` 4 + n))
        ]
    ]

-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------

-- In addition to gauge options, the number of elements in the stream can be
-- passed using the --stream-size option.
--
benchmarks :: String -> Int -> [Benchmark]
benchmarks moduleName size =
        [ bgroup (o_1_space_prefix moduleName) $ Prelude.concat
            [
            -- multi-stream
              o_1_space_joining size
            , o_1_space_concatFoldable size
            , o_1_space_concat size

            , o_1_space_applicative size
            , o_1_space_monad size

            ]
        , bgroup (o_n_space_prefix moduleName) $ Prelude.concat
            [
            -- multi-stream
              o_n_space_applicative size
            , o_n_space_monad size
            ]
        , bgroup (o_n_heap_prefix moduleName) $
            -- multi-stream
            o_n_heap_buffering size
        ]
