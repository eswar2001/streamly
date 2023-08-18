-- |
-- Module      : Streamly.Benchmark.Data.Stream
-- Copyright   : (c) 2018 Composewell Technologies
--
-- License     : BSD3
-- Maintainer  : streamly@composewell.com

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

#ifdef __HADDOCK_VERSION__
#undef INSPECTION
#endif

#ifdef INSPECTION
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Test.Inspection.Plugin #-}
#endif

module Main (main) where

import Control.Applicative (liftA2)
import Control.Monad (when)
import Data.Maybe (isJust)
import Gauge (bench, nfIO, bgroup, Benchmark, defaultMain)
import System.Random (randomRIO)
import Prelude hiding (tail, mapM_, foldl, last, map, mapM, concatMap, zip)

import qualified Prelude as P
import qualified Streamly.Internal.Data.Stream as S
import qualified Streamly.Internal.Data.Unfold as UF
import qualified Streamly.Internal.Data.Fold as FL

import Streamly.Benchmark.Common

#ifdef INSPECTION
import GHC.Types (SPEC(..))
import Test.Inspection
#endif

-- We try to keep the total number of iterations same irrespective of nesting
-- of the loops so that the overhead is easy to compare.
value, value2, value3, value16, maxValue :: Int
value = 100000
value2 = round (P.fromIntegral value**(1/2::P.Double)) -- double nested loop
value3 = round (P.fromIntegral value**(1/3::P.Double)) -- triple nested loop
value16 = round (P.fromIntegral value**(1/16::P.Double)) -- triple nested loop
maxValue = value

-------------------------------------------------------------------------------
-- Stream generation and elimination
-------------------------------------------------------------------------------

type Stream m a = S.Stream m a

{-# INLINE sourceUnfoldr #-}
sourceUnfoldr :: Monad m => Int -> Stream m Int
sourceUnfoldr n = S.unfoldr step n
    where
    step cnt =
        if cnt > n + value
        then Nothing
        else Just (cnt, cnt + 1)

{-# INLINE sourceUnfoldrN #-}
sourceUnfoldrN :: Monad m => Int -> Int -> Stream m Int
sourceUnfoldrN m n = S.unfoldr step n
    where
    step cnt =
        if cnt > n + m
        then Nothing
        else Just (cnt, cnt + 1)

{-# INLINE sourceUnfoldrMN #-}
sourceUnfoldrMN :: Monad m => Int -> Int -> Stream m Int
sourceUnfoldrMN m n = S.unfoldrM step n
    where
    step cnt =
        if cnt > n + m
        then return Nothing
        else return (Just (cnt, cnt + 1))

{-# INLINE sourceUnfoldrM #-}
sourceUnfoldrM :: Monad m => Int -> Stream m Int
sourceUnfoldrM n = S.unfoldrM step n
    where
    step cnt =
        if cnt > n + value
        then return Nothing
        else return (Just (cnt, cnt + 1))

{-# INLINE sourceIntFromTo #-}
sourceIntFromTo :: Monad m => Int -> Stream m Int
sourceIntFromTo n = S.enumerateFromToIntegral n (n + value)

{-# INLINE sourceFromList #-}
sourceFromList :: Monad m => Int -> Stream m Int
sourceFromList n = S.fromList [n..n+value]

-------------------------------------------------------------------------------
-- Elimination
-------------------------------------------------------------------------------

{-# INLINE runStream #-}
runStream :: Monad m => Stream m a -> m ()
runStream = S.drain

{-# INLINE mapM_ #-}
mapM_ :: Monad m => Stream m a -> m ()
mapM_ = S.mapM_ (\_ -> return ())

{-# INLINE toNull #-}
toNull :: Monad m => Stream m Int -> m ()
toNull = runStream

{-# INLINE uncons #-}
{-# INLINE nullTail #-}
{-# INLINE headTail #-}
uncons, nullTail, headTail
    :: Monad m
    => Stream m Int -> m ()

uncons s = do
    r <- S.uncons s
    case r of
        Nothing -> return ()
        Just (_, t) -> uncons t

{-# INLINE foldBreak #-}
foldBreak :: Monad m => Stream m Int -> m ()
foldBreak s = do
    (r, s1) <- S.foldBreak (FL.take 1 FL.length) s
    when (r /= 0) $ foldBreak s1

{-# INLINE tail #-}
tail :: Monad m => Stream m a -> m ()
tail s = S.tail s >>= P.mapM_ tail

nullTail s = do
    r <- S.null s
    when (not r) $ S.tail s >>= P.mapM_ nullTail

headTail s = do
    h <- S.head s
    when (isJust h) $ S.tail s >>= P.mapM_ headTail

{-# INLINE toList #-}
toList :: Monad m => Stream m Int -> m [Int]
toList = S.toList

{-# INLINE foldl #-}
foldl :: Monad m => Stream m Int -> m Int
foldl  = S.foldl' (+) 0

{-# INLINE last #-}
last :: Monad m => Stream m Int -> m (Maybe Int)
last   = S.last

-------------------------------------------------------------------------------
-- Transformation
-------------------------------------------------------------------------------

{-# INLINE transform #-}
transform :: Monad m => Stream m a -> m ()
transform = runStream

{-# INLINE composeN #-}
composeN
    :: Monad m
    => Int -> (Stream m Int -> Stream m Int) -> Stream m Int -> m ()
composeN n f =
    case n of
        1 -> transform . f
        2 -> transform . f . f
        3 -> transform . f . f . f
        4 -> transform . f . f . f . f
        _ -> undefined

{-# INLINE scan #-}
{-# INLINE map #-}
{-# INLINE fmapD #-}
{-# INLINE mapM #-}
{-# INLINE mapMaybe #-}
{-# INLINE mapMaybeM #-}
{-# INLINE filterEven #-}
{-# INLINE filterAllOut #-}
{-# INLINE filterAllIn #-}
{-# INLINE _takeOne #-}
{-# INLINE takeAll #-}
{-# INLINE takeWhileTrue #-}
{-# INLINE _takeWhileMTrue #-}
{-# INLINE dropOne #-}
{-# INLINE dropAll #-}
{-# INLINE dropWhileTrue #-}
{-# INLINE _dropWhileMTrue #-}
{-# INLINE dropWhileFalse #-}
{-# INLINE _foldrS #-}
{-# INLINE _foldlS #-}
{-# INLINE intersperse #-}
scan, map, fmapD, mapM, mapMaybe, mapMaybeM, filterEven, filterAllOut,
    filterAllIn, _takeOne, takeAll, takeWhileTrue, _takeWhileMTrue, dropOne,
    dropAll, dropWhileTrue, _dropWhileMTrue, dropWhileFalse, _foldrS, _foldlS,
    intersperse
    :: Monad m
    => Int -> Stream m Int -> m ()

scan          n = composeN n $ S.scanl' (+) 0
fmapD         n = composeN n $ Prelude.fmap (+1)
map           n = composeN n $ S.map (+1)
mapM          n = composeN n $ S.mapM return
mapMaybe      n = composeN n $ S.mapMaybe
    (\x -> if Prelude.odd x then Nothing else Just x)
mapMaybeM     n = composeN n $ S.mapMaybeM
    (\x -> if Prelude.odd x then return Nothing else return $ Just x)
filterEven    n = composeN n $ S.filter even
filterAllOut  n = composeN n $ S.filter (> maxValue)
filterAllIn   n = composeN n $ S.filter (<= maxValue)
_takeOne      n = composeN n $ S.take 1
takeAll       n = composeN n $ S.take maxValue
takeWhileTrue n = composeN n $ S.takeWhile (<= maxValue)
_takeWhileMTrue n = composeN n $ S.takeWhileM (return . (<= maxValue))
dropOne        n = composeN n $ S.drop 1
dropAll        n = composeN n $ S.drop maxValue
dropWhileTrue  n = composeN n $ S.dropWhile (<= maxValue)
_dropWhileMTrue n = composeN n $ S.dropWhileM (return . (<= maxValue))
dropWhileFalse n = composeN n $ S.dropWhile (> maxValue)
_foldrS        n = composeN n $ S.foldrS S.cons S.nil
_foldlS         n = composeN n $ S.foldlS (flip S.cons) S.nil
intersperse    n = composeN n $ S.intersperse maxValue

-------------------------------------------------------------------------------
-- Iteration
-------------------------------------------------------------------------------

iterStreamLen, maxIters :: Int
iterStreamLen = 10
maxIters = 10000

{-# INLINE iterateSource #-}
iterateSource
    :: Monad m
    => (Stream m Int -> Stream m Int) -> Int -> Int -> Stream m Int
iterateSource g i n = f i (sourceUnfoldrMN iterStreamLen n)
    where
        f (0 :: Int) m = g m
        f x m = g (f (x P.- 1) m)

{-# INLINE iterateMapM #-}
{-# INLINE iterateScan #-}
{-# INLINE iterateFilterEven #-}
{-# INLINE iterateTakeAll #-}
{-# INLINE iterateDropOne #-}
{-# INLINE iterateDropWhileFalse #-}
{-# INLINE iterateDropWhileTrue #-}
iterateMapM, iterateScan, iterateFilterEven, iterateTakeAll, iterateDropOne,
    iterateDropWhileFalse, iterateDropWhileTrue
    :: Monad m
    => Int -> Stream m Int

-- this is quadratic
iterateScan            = iterateSource (S.scanl' (+) 0) (maxIters `div` 10)
iterateDropWhileFalse  = iterateSource (S.dropWhile (> maxValue))
                                       (maxIters `div` 10)

iterateMapM            = iterateSource (S.mapM return) maxIters
iterateFilterEven      = iterateSource (S.filter even) maxIters
iterateTakeAll         = iterateSource (S.take maxValue) maxIters
iterateDropOne         = iterateSource (S.drop 1) maxIters
iterateDropWhileTrue   = iterateSource (S.dropWhile (<= maxValue)) maxIters

{-# INLINE iterateM #-}
iterateM :: Monad m => Int -> Stream m Int
iterateM i = S.take maxIters (S.iterateM (\x -> return (x + 1)) (return i))

-------------------------------------------------------------------------------
-- Zipping
-------------------------------------------------------------------------------

{-# INLINE eqBy #-}
eqBy :: (Monad m, P.Eq a) => S.Stream m a -> m P.Bool
eqBy src = S.eqBy (==) src src

{-# INLINE cmpBy #-}
cmpBy :: (Monad m, P.Ord a) => S.Stream m a -> m P.Ordering
cmpBy src = S.cmpBy P.compare src src

{-# INLINE zip #-}
zip :: Monad m => Stream m Int -> m ()
zip src = transform $ S.zipWith (,) src src

-------------------------------------------------------------------------------
-- Mixed Composition
-------------------------------------------------------------------------------

{-# INLINE scanMap #-}
{-# INLINE dropMap #-}
{-# INLINE dropScan #-}
{-# INLINE takeDrop #-}
{-# INLINE takeScan #-}
{-# INLINE takeMap #-}
{-# INLINE filterDrop #-}
{-# INLINE filterTake #-}
{-# INLINE filterScan #-}
{-# INLINE filterMap #-}
scanMap, dropMap, dropScan, takeDrop, takeScan, takeMap, filterDrop,
    filterTake, filterScan, filterMap
    :: Monad m => Int -> Stream m Int -> m ()

scanMap    n = composeN n $ S.map (subtract 1) . S.scanl' (+) 0
dropMap    n = composeN n $ S.map (subtract 1) . S.drop 1
dropScan   n = composeN n $ S.scanl' (+) 0 . S.drop 1
takeDrop   n = composeN n $ S.drop 1 . S.take maxValue
takeScan   n = composeN n $ S.scanl' (+) 0 . S.take maxValue
takeMap    n = composeN n $ S.map (subtract 1) . S.take maxValue
filterDrop n = composeN n $ S.drop 1 . S.filter (<= maxValue)
filterTake n = composeN n $ S.take maxValue . S.filter (<= maxValue)
filterScan n = composeN n $ S.scanl' (+) 0 . S.filter (<= maxBound)
filterMap  n = composeN n $ S.map (subtract 1) . S.filter (<= maxValue)

-------------------------------------------------------------------------------
-- Nested Composition
-------------------------------------------------------------------------------

instance Monad f => Applicative (S.Stream f) where
    {-# INLINE pure #-}
    pure = S.fromPure

    {-# INLINE (<*>) #-}
    (<*>) = S.crossApply

    {-# INLINE liftA2 #-}
    liftA2 f x = (<*>) (fmap f x)

    {-# INLINE (*>) #-}
    (*>) = S.crossApplySnd

    {-# INLINE (<*) #-}
    (<*) = S.crossApplyFst

-- NOTE: even though concatMap for StreamD is 4x faster compared to StreamK,
-- the monad instance does not seem to be significantly faster.
instance Monad m => Monad (S.Stream m) where
    {-# INLINE return #-}
    return = pure

    {-# INLINE (>>=) #-}
    (>>=) = flip S.concatMap

    {-# INLINE (>>) #-}
    (>>) = (*>)

{-# INLINE toNullApNested #-}
toNullApNested :: Monad m => Stream m Int -> m ()
toNullApNested s = runStream $ do
    (+) <$> s <*> s

{-# INLINE toNullNested #-}
toNullNested :: Monad m => Stream m Int -> m ()
toNullNested s = runStream $ do
    x <- s
    y <- s
    return $ x + y

{-# INLINE toNullNested3 #-}
toNullNested3 :: Monad m => Stream m Int -> m ()
toNullNested3 s = runStream $ do
    x <- s
    y <- s
    z <- s
    return $ x + y + z

{-# INLINE filterAllOutNested #-}
filterAllOutNested
    :: Monad m
    => Stream m Int -> m ()
filterAllOutNested str = runStream $ do
    x <- str
    y <- str
    let s = x + y
    if s < 0
    then return s
    else S.nil

{-# INLINE filterAllInNested #-}
filterAllInNested
    :: Monad m
    => Stream m Int -> m ()
filterAllInNested str = runStream $ do
    x <- str
    y <- str
    let s = x + y
    if s > 0
    then return s
    else S.nil

-------------------------------------------------------------------------------
-- ConcatMap
-------------------------------------------------------------------------------

-- concatMap unfoldrM/unfoldrM

{-# INLINE concatMap #-}
concatMap :: Int -> Int -> Int -> IO ()
concatMap outer inner n =
    S.drain $ S.concatMap
        (\_ -> sourceUnfoldrMN inner n)
        (sourceUnfoldrMN outer n)

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'concatMap
inspect $ 'concatMap `hasNoType` ''SPEC
#endif

-- concatMap unfoldr/unfoldr

{-# INLINE concatMapPure #-}
concatMapPure :: Int -> Int -> Int -> IO ()
concatMapPure outer inner n =
    S.drain $ S.concatMap
        (\_ -> sourceUnfoldrN inner n)
        (sourceUnfoldrN outer n)

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'concatMapPure
inspect $ 'concatMapPure `hasNoType` ''SPEC
#endif

-- concatMap replicate/unfoldrM

{-# INLINE concatMapRepl #-}
concatMapRepl :: Int -> Int -> Int -> IO ()
concatMapRepl outer inner n =
    S.drain $ S.concatMap (S.replicate inner) (sourceUnfoldrMN outer n)

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'concatMapRepl
inspect $ 'concatMapRepl `hasNoType` ''SPEC
#endif

-- unfoldMany replicate/unfoldrM

{-# INLINE unfoldManyRepl #-}
unfoldManyRepl :: Int -> Int -> Int -> IO ()
unfoldManyRepl outer inner n =
    S.drain
         $ S.unfoldMany
               UF.replicateM
               (S.map ((inner,) . return) (sourceUnfoldrMN outer n))

#ifdef INSPECTION
inspect $ hasNoTypeClasses 'unfoldManyRepl
inspect $ 'unfoldManyRepl `hasNoType` ''S.ConcatMapUState
inspect $ 'unfoldManyRepl `hasNoType` ''SPEC
#endif

-------------------------------------------------------------------------------
-- Benchmarks
-------------------------------------------------------------------------------

moduleName :: String
moduleName = "Data.Stream"

o_1_space :: [Benchmark]
o_1_space =
    [ bgroup (o_1_space_prefix moduleName)
      [ bgroup "generation"
        [ benchFold "unfoldr"      toNull sourceUnfoldr
        , benchFold "unfoldrM"     toNull sourceUnfoldrM
        , benchFold "intFromTo"    toNull sourceIntFromTo

        , benchFold "fromList" toNull sourceFromList
        ]
      , bgroup "elimination"
        [ benchFold "toNull"   toNull   sourceUnfoldrM
        , benchFold "mapM_"    mapM_    sourceUnfoldrM
        , benchFold "uncons"   uncons   sourceUnfoldrM
        , benchFold "foldBreak" foldBreak sourceUnfoldrM
        , benchFold "foldl'" foldl    sourceUnfoldrM
        , benchFold "last"   last     sourceUnfoldrM
        ]
      , bgroup "nested"
        [ benchFold "toNullAp" toNullApNested (sourceUnfoldrMN value2)
        , benchFold "toNull"   toNullNested   (sourceUnfoldrMN value2)
        , benchFold "toNull3"  toNullNested3  (sourceUnfoldrMN value3)
        , benchFold "filterAllIn"  filterAllInNested  (sourceUnfoldrMN value2)
        , benchFold "filterAllOut"  filterAllOutNested  (sourceUnfoldrMN value2)
        , benchFold "toNullApPure" toNullApNested (sourceUnfoldrN value2)
        , benchFold "toNullPure"   toNullNested   (sourceUnfoldrN value2)
        , benchFold "toNull3Pure"  toNullNested3  (sourceUnfoldrN value3)
        , benchFold "filterAllInPure"  filterAllInNested  (sourceUnfoldrN value2)
        , benchFold "filterAllOutPure"  filterAllOutNested  (sourceUnfoldrN value2)
        ]
      , bgroup "transformation"
        [ benchFold "scan"      (scan      1) sourceUnfoldrM
        , benchFold "map"       (map       1) sourceUnfoldrM
        , benchFold "fmap"      (fmapD     1) sourceUnfoldrM
        , benchFold "mapM"      (mapM      1) sourceUnfoldrM
        , benchFold "mapMaybe"  (mapMaybe  1) sourceUnfoldrM
        , benchFold "mapMaybeM" (mapMaybeM 1) sourceUnfoldrM
        ]
      , bgroup "transformationX4"
        [ benchFold "scan"      (scan      4) sourceUnfoldrM
        , benchFold "map"       (map       4) sourceUnfoldrM
        , benchFold "fmap"      (fmapD     4) sourceUnfoldrM
        , benchFold "mapM"      (mapM      4) sourceUnfoldrM
        , benchFold "mapMaybe"  (mapMaybe  4) sourceUnfoldrM
        , benchFold "mapMaybeM" (mapMaybeM 4) sourceUnfoldrM
        -- XXX this is horribly slow
        -- , benchFold "concatMap" (concatMap 4) (sourceUnfoldrMN value16)
        ]

      , bgroup "concat"
        [ benchIOSrc1 "concatMapPure (n of 1)"
            (concatMapPure value 1)
        , benchIOSrc1 "concatMapPure (sqrt n of sqrt n)"
            (concatMapPure value2 value2)
        , benchIOSrc1 "concatMapPure (1 of n)"
            (concatMapPure 1 value)

        , benchIOSrc1 "concatMap (n of 1)"
            (concatMap value 1)
        , benchIOSrc1 "concatMap (sqrt n of sqrt n)"
            (concatMap value2 value2)
        , benchIOSrc1 "concatMap (1 of n)"
            (concatMap 1 value)

        -- concatMap vs unfoldMany
        , benchIOSrc1 "concatMapRepl (sqrt n of sqrt n)"
            (concatMapRepl value2 value2)
        , benchIOSrc1 "unfoldManyRepl (sqrt n of sqrt n)"
            (unfoldManyRepl value2 value2)
        ]
      , bgroup "filtering"
        [ benchFold "filter-even"     (filterEven     1) sourceUnfoldrM
        , benchFold "filter-all-out"  (filterAllOut   1) sourceUnfoldrM
        , benchFold "filter-all-in"   (filterAllIn    1) sourceUnfoldrM
        , benchFold "take-all"        (takeAll        1) sourceUnfoldrM
        , benchFold "takeWhile-true"  (takeWhileTrue  1) sourceUnfoldrM
        , benchFold "drop-one"        (dropOne        1) sourceUnfoldrM
        , benchFold "drop-all"        (dropAll        1) sourceUnfoldrM
        , benchFold "dropWhile-true"  (dropWhileTrue  1) sourceUnfoldrM
        , benchFold "dropWhile-false" (dropWhileFalse 1) sourceUnfoldrM
        ]
      , bgroup "filteringX4"
        [ benchFold "filter-even"     (filterEven     4) sourceUnfoldrM
        , benchFold "filter-all-out"  (filterAllOut   4) sourceUnfoldrM
        , benchFold "filter-all-in"   (filterAllIn    4) sourceUnfoldrM
        , benchFold "take-all"        (takeAll        4) sourceUnfoldrM
        , benchFold "takeWhile-true"  (takeWhileTrue  4) sourceUnfoldrM
        , benchFold "drop-one"        (dropOne        4) sourceUnfoldrM
        , benchFold "drop-all"        (dropAll        4) sourceUnfoldrM
        , benchFold "dropWhile-true"  (dropWhileTrue  4) sourceUnfoldrM
        , benchFold "dropWhile-false" (dropWhileFalse 4) sourceUnfoldrM
        ]
      , bgroup "zipping"
        [ benchFold "eqBy"  eqBy  sourceUnfoldrM
        , benchFold "cmpBy" cmpBy sourceUnfoldrM
        , benchFold   "zip"   zip   sourceUnfoldrM
        ]
      , bgroup "mixed"
        [ benchFold "scan-map"    (scanMap    1) sourceUnfoldrM
        , benchFold "drop-map"    (dropMap    1) sourceUnfoldrM
        , benchFold "drop-scan"   (dropScan   1) sourceUnfoldrM
        , benchFold "take-drop"   (takeDrop   1) sourceUnfoldrM
        , benchFold "take-scan"   (takeScan   1) sourceUnfoldrM
        , benchFold "take-map"    (takeMap    1) sourceUnfoldrM
        , benchFold "filter-drop" (filterDrop 1) sourceUnfoldrM
        , benchFold "filter-take" (filterTake 1) sourceUnfoldrM
        , benchFold "filter-scan" (filterScan 1) sourceUnfoldrM
        , benchFold "filter-map"  (filterMap  1) sourceUnfoldrM
        ]
      , bgroup "mixedX2"
        [ benchFold "scan-map"    (scanMap    2) sourceUnfoldrM
        , benchFold "drop-map"    (dropMap    2) sourceUnfoldrM
        , benchFold "drop-scan"   (dropScan   2) sourceUnfoldrM
        , benchFold "take-drop"   (takeDrop   2) sourceUnfoldrM
        , benchFold "take-scan"   (takeScan   2) sourceUnfoldrM
        , benchFold "take-map"    (takeMap    2) sourceUnfoldrM
        , benchFold "filter-drop" (filterDrop 2) sourceUnfoldrM
        , benchFold "filter-take" (filterTake 2) sourceUnfoldrM
        , benchFold "filter-scan" (filterScan 2) sourceUnfoldrM
        , benchFold "filter-map"  (filterMap  2) sourceUnfoldrM
        ]
      , bgroup "mixedX4"
        [ benchFold "scan-map"    (scanMap    4) sourceUnfoldrM
        , benchFold "drop-map"    (dropMap    4) sourceUnfoldrM
        , benchFold "drop-scan"   (dropScan   4) sourceUnfoldrM
        , benchFold "take-drop"   (takeDrop   4) sourceUnfoldrM
        , benchFold "take-scan"   (takeScan   4) sourceUnfoldrM
        , benchFold "take-map"    (takeMap    4) sourceUnfoldrM
        , benchFold "filter-drop" (filterDrop 4) sourceUnfoldrM
        , benchFold "filter-take" (filterTake 4) sourceUnfoldrM
        , benchFold "filter-scan" (filterScan 4) sourceUnfoldrM
        , benchFold "filter-map"  (filterMap  4) sourceUnfoldrM
        ]
      ]
    ]

-- | Takes a source, and uses it with a default drain/fold method.
{-# INLINE benchD #-}
benchD :: P.String -> (Int -> Stream P.IO Int) -> Benchmark
benchD name f = bench name $ nfIO $ randomRIO (1,1) >>= toNull . f

o_n_stack :: [Benchmark]
o_n_stack =
    [ bgroup (o_n_stack_prefix moduleName)
      [ bgroup "elimination"
        [ benchFold "tail"   tail     sourceUnfoldrM
        , benchFold "nullTail" nullTail sourceUnfoldrM
        , benchFold "headTail" headTail sourceUnfoldrM
        ]
      , bgroup "transformation"
        [
          -- this is horribly slow
          -- benchFold "foldrS"    (_foldrS    1) sourceUnfoldrM
          -- XXX why do these need so much stack
          benchFold "intersperse" (intersperse 1) (sourceUnfoldrMN value2)
        , benchFold "interspersePure" (intersperse 1) (sourceUnfoldrN value2)
        ]
      , bgroup "transformationX4"
        [
          benchFold "intersperse" (intersperse 4) (sourceUnfoldrMN value16)
        ]
      , bgroup "iterated"
        [ benchD "mapM"                 iterateMapM
        , benchD "scan(1/10)"           iterateScan
        , benchD "filterEven"           iterateFilterEven
        , benchD "takeAll"              iterateTakeAll
        , benchD "dropOne"              iterateDropOne
        , benchD "dropWhileFalse(1/10)" iterateDropWhileFalse
        , benchD "dropWhileTrue"        iterateDropWhileTrue
        , benchD "iterateM"             iterateM
        ]
      ]
    ]

o_n_space :: [Benchmark]
o_n_space =
    [ bgroup (o_n_space_prefix moduleName)
      [ bgroup "elimination"
        [ benchFold "toList" toList   sourceUnfoldrM
        ]
      , bgroup "transformation"
        [

        -- This is horribly slow, never finishes
        -- benchFold "foldlS"    (_foldlS    1) sourceUnfoldrM
        ]
      ]
    ]

main :: IO ()
main = defaultMain $ concat [o_1_space, o_n_stack, o_n_space]
