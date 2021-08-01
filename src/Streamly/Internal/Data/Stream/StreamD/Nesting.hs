-- |-- We use fromStreamK/toStreamK to convert the direct style stream to CPS
-- Module      : Streamly.Internal.Data.Stream.StreamD.Nesting-- style. In the first phase we try fusing the fromStreamK/toStreamK using:
---- Copyright   : (c) 2018 Composewell Technologies
-- {-# RULES "fromStreamK/toStreamK fusion"--               (c) Roman Leshchinskiy 2008-2010
-- License     : BSD-3-Clause--     forall s. toStreamK (fromStreamK s) = s #-}
---- Maintainer  : streamly@composewell.com
-- Stability   : experimental-- If for some reason some of the operations could not be fused then we have
-- Portability : GHC-- fallback rules in the second phase. For example:
----
-- {-# INLINE_EARLY unfoldr #-}-- This module contains transformations involving multiple streams, unfolds or
-- unfoldr :: (Monad m, IsStream t) => (b -> Maybe (a, b)) -> b -> t m a-- folds. There are two types of transformations generational or eliminational.
-- unfoldr step seed = fromStreamS (S.unfoldr step seed)-- Generational transformations are like the "Generate" module but they
-- {-# RULES "unfoldr fallback to StreamK" [1]-- generate a stream by combining streams instead of elements. Eliminational
--     forall a b. S.toStreamK (S.unfoldr a b) = K.unfoldr a b #-}```-- transformations are like the "Eliminate" module but they transform a stream
---- by eliminating parts of the stream instead of eliminating the whole stream.
---- Then, fromStreamK/toStreamK are inlined in the last phase:
---- These combinators involve transformation, generation, elimination so can be
-- {-# INLINE_LATE toStreamK #-}-- classified under any of those.
---- toStreamK :: Monad m => Stream m a -> K.Stream m a```
---- Ultimately these operations should be supported by Unfolds, Pipes and Folds,
-- and this module may become redundant.-- The fallback rules make sure that if we could not fuse the direct style
-- operations then better use the CPS style operation, because unfused direct
-- style would have worse performance than the CPS style ops.-- The zipWithM combinator in this module has been adapted from the vector
-- package (c) Roman Leshchinskiy.
--
module Streamly.Internal.Data.Stream.StreamD.Nesting
    (
    -- * Generate
    -- | Combining streams to generate streams.

    -- ** Combine Two Streams
    -- | Functions ending in the shape:
    --
    -- @t m a -> t m a -> t m a@.

    -- *** Appending
    -- | Append a stream after another. A special case of concatMap or
    -- unfoldMany.
      AppendState(..)
    , append

    -- *** Interleaving
    -- | Interleave elements from two streams alternately. A special case of
    -- unfoldManyInterleave.
    , InterleaveState(..)
    , interleave
    , interleaveMin
    , interleaveSuffix
    , interleaveInfix

    -- *** Scheduling
    -- | Execute streams alternately irrespective of whether they generate
    -- elements or not. Note 'interleave' would execute a stream until it
    -- yields an element. A special case of unfoldManyRoundRobin.
    , roundRobin -- interleaveFair?/ParallelFair

    -- *** Zipping
    -- | Zip corresponding elements of two streams.
    , zipWith
    , zipWithM

    -- *** Merging
    -- | Interleave elements from two streams based on a condition.
    , mergeBy
    , mergeByM

    -- ** Combine N Streams
    -- | Functions generally ending in these shapes:
    --
    -- @
    -- concat: f (t m a) -> t m a
    -- concatMap: (a -> t m b) -> t m a -> t m b
    -- unfoldMany: Unfold m a b -> t m a -> t m b
    -- @

    -- *** ConcatMap
    -- | Generate streams by mapping a stream generator on each element of an
    -- input stream, append the resulting streams and flatten.
    , concatMap
    , concatMapM

    -- *** ConcatUnfold
    -- | Generate streams by using an unfold on each element of an input
    -- stream, append the resulting streams and flatten. A special case of
    -- gintercalate.
    , unfoldMany
    , ConcatUnfoldInterleaveState (..)
    , unfoldManyInterleave
    , unfoldManyRoundRobin

    -- *** Interpose
    -- | Like unfoldMany but intersperses an effect between the streams. A
    -- special case of gintercalate.
    , interpose
    , interposeSuffix

    -- *** Intercalate
    -- | Like unfoldMany but intersperses streams from another source between
    -- the streams from the first source.
    , gintercalate
    , gintercalateSuffix

    -- * Eliminate
    -- | Folding and Parsing chunks of streams to eliminate nested streams.
    -- Functions generally ending in these shapes:
    --
    -- @
    -- f (Fold m a b) -> t m a -> t m b
    -- f (Parser m a b) -> t m a -> t m b
    -- @

    -- ** Folding
    -- | Apply folds on a stream.
    , foldMany
    , foldIterateM

    -- ** Parsing
    -- | Parsing is opposite to flattening. 'parseMany' is dual to concatMap or
    -- unfoldMany. concatMap generates a stream from single values in a
    -- stream and flattens, parseMany does the opposite of flattening by
    -- splitting the stream and then folds each such split to single value in
    -- the output stream.
    , parseMany
    , parseIterate

    -- ** Grouping
    -- | Group segments of a stream and fold. Special case of parsing.
    , chunksOf
    , groupsOf2
    , groupsBy
    , groupsRollingBy

    -- ** Splitting
    -- | A special case of parsing.
    , wordsBy
    , splitOnSeq
    , splitOnSuffixSeq

    -- * Transform (Nested Containers)
    -- | Opposite to compact in ArrayStream
    , splitInnerBy
    , splitInnerBySuffix
    , joinInnerMerge
    , joinLeftMerge
    , joinRightMerge
    , differenceBySorted
    , removeDupsAll
    , joinOuterMerge
    , intersectBySorted
    )
where



import Control.Exception (assert)
import Control.Monad.Catch (MonadThrow, throwM)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Bits (shiftR, shiftL, (.|.), (.&.))

import Data.Functor.Identity ( Identity )

import Data.Word (Word32)
import Foreign.Storable (Storable(..))
import Fusion.Plugin.Types (Fuse(..))
import GHC.Types (SPEC(..))

import Streamly.Internal.Data.Array.Foreign.Type (Array(..))
import Streamly.Internal.Data.Fold.Type (Fold(..))
import Streamly.Internal.Data.Parser (ParseError(..))
import Streamly.Internal.Data.SVar.Type (adaptState)
import Streamly.Internal.Data.Unfold.Type (Unfold(..))

import qualified Streamly.Internal.Data.Array.Foreign.Type as A
import qualified Streamly.Internal.Data.Fold.Type as FL
import qualified Streamly.Internal.Data.Parser as PR
import qualified Streamly.Internal.Data.Parser.ParserD as PRD
import qualified Streamly.Internal.Ring.Foreign as RB

import Streamly.Internal.Data.Stream.StreamD.Type

import Prelude hiding (concatMap, mapM, zipWith)
import Data.Maybe
import Data.IORef


------------------------------------------------------------------------------
-- Appending
------------------------------------------------------------------------------

data AppendState s1 s2 = AppendFirst s1 | AppendSecond s2

-- Note that this could be much faster compared to the CPS stream. However, as
-- the number of streams being composed increases this may become expensive.
-- Need to see where the breaking point is between the two.
--
{-# INLINE [1] append #-}
append :: Monad m => Stream m a -> Stream m a -> Stream m a
append (Stream step1 state1) (Stream step2 state2) =
    Stream step (AppendFirst state1)

    where

    {-# INLINE [0] step #-}
    step gst (AppendFirst st) = do
        r <- step1 gst st
        return $ case r of
            Yield a s -> Yield a (AppendFirst s)
            Skip s -> Skip (AppendFirst s)
            Stop -> Skip (AppendSecond state2)

    step gst (AppendSecond st) = do
        r <- step2 gst st
        return $ case r of
            Yield a s -> Yield a (AppendSecond s)
            Skip s -> Skip (AppendSecond s)
            Stop -> Stop

------------------------------------------------------------------------------
-- Interleaving
------------------------------------------------------------------------------

data InterleaveState s1 s2 = InterleaveFirst s1 s2 | InterleaveSecond s1 s2
    | InterleaveSecondOnly s2 | InterleaveFirstOnly s1

{-# INLINE [1] interleave #-}
interleave :: Monad m => Stream m a -> Stream m a -> Stream m a
interleave (Stream step1 state1) (Stream step2 state2) =
    Stream step (InterleaveFirst state1 state2)

    where

    {-# INLINE [0] step #-}
    step gst (InterleaveFirst st1 st2) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield a (InterleaveSecond s st2)
            Skip s -> Skip (InterleaveFirst s st2)
            Stop -> Skip (InterleaveSecondOnly st2)

    step gst (InterleaveSecond st1 st2) = do
        r <- step2 gst st2
        return $ case r of
            Yield a s -> Yield a (InterleaveFirst st1 s)
            Skip s -> Skip (InterleaveSecond st1 s)
            Stop -> Skip (InterleaveFirstOnly st1)

    step gst (InterleaveFirstOnly st1) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield a (InterleaveFirstOnly s)
            Skip s -> Skip (InterleaveFirstOnly s)
            Stop -> Stop

    step gst (InterleaveSecondOnly st2) = do
        r <- step2 gst st2
        return $ case r of
            Yield a s -> Yield a (InterleaveSecondOnly s)
            Skip s -> Skip (InterleaveSecondOnly s)
            Stop -> Stop

{-# INLINE [1] interleaveMin #-}
interleaveMin :: Monad m => Stream m a -> Stream m a -> Stream m a
interleaveMin (Stream step1 state1) (Stream step2 state2) =
    Stream step (InterleaveFirst state1 state2)

    where

    {-# INLINE [0] step #-}
    step gst (InterleaveFirst st1 st2) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield a (InterleaveSecond s st2)
            Skip s -> Skip (InterleaveFirst s st2)
            Stop -> Stop

    step gst (InterleaveSecond st1 st2) = do
        r <- step2 gst st2
        return $ case r of
            Yield a s -> Yield a (InterleaveFirst st1 s)
            Skip s -> Skip (InterleaveSecond st1 s)
            Stop -> Stop

    step _ (InterleaveFirstOnly _) =  undefined
    step _ (InterleaveSecondOnly _) =  undefined

{-# INLINE [1] interleaveSuffix #-}
interleaveSuffix :: Monad m => Stream m a -> Stream m a -> Stream m a
interleaveSuffix (Stream step1 state1) (Stream step2 state2) =
    Stream step (InterleaveFirst state1 state2)

    where

    {-# INLINE [0] step #-}
    step gst (InterleaveFirst st1 st2) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield a (InterleaveSecond s st2)
            Skip s -> Skip (InterleaveFirst s st2)
            Stop -> Stop

    step gst (InterleaveSecond st1 st2) = do
        r <- step2 gst st2
        return $ case r of
            Yield a s -> Yield a (InterleaveFirst st1 s)
            Skip s -> Skip (InterleaveSecond st1 s)
            Stop -> Skip (InterleaveFirstOnly st1)

    step gst (InterleaveFirstOnly st1) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield a (InterleaveFirstOnly s)
            Skip s -> Skip (InterleaveFirstOnly s)
            Stop -> Stop

    step _ (InterleaveSecondOnly _) =  undefined

data InterleaveInfixState s1 s2 a
    = InterleaveInfixFirst s1 s2
    | InterleaveInfixSecondBuf s1 s2
    | InterleaveInfixSecondYield s1 s2 a
    | InterleaveInfixFirstYield s1 s2 a
    | InterleaveInfixFirstOnly s1

{-# INLINE [1] interleaveInfix #-}
interleaveInfix :: Monad m => Stream m a -> Stream m a -> Stream m a
interleaveInfix (Stream step1 state1) (Stream step2 state2) =
    Stream step (InterleaveInfixFirst state1 state2)

    where

    {-# INLINE [0] step #-}
    step gst (InterleaveInfixFirst st1 st2) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield a (InterleaveInfixSecondBuf s st2)
            Skip s -> Skip (InterleaveInfixFirst s st2)
            Stop -> Stop

    step gst (InterleaveInfixSecondBuf st1 st2) = do
        r <- step2 gst st2
        return $ case r of
            Yield a s -> Skip (InterleaveInfixSecondYield st1 s a)
            Skip s -> Skip (InterleaveInfixSecondBuf st1 s)
            Stop -> Skip (InterleaveInfixFirstOnly st1)

    step gst (InterleaveInfixSecondYield st1 st2 x) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield x (InterleaveInfixFirstYield s st2 a)
            Skip s -> Skip (InterleaveInfixSecondYield s st2 x)
            Stop -> Stop

    step _ (InterleaveInfixFirstYield st1 st2 x) =
        return $ Yield x (InterleaveInfixSecondBuf st1 st2)

    step gst (InterleaveInfixFirstOnly st1) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield a (InterleaveInfixFirstOnly s)
            Skip s -> Skip (InterleaveInfixFirstOnly s)
            Stop -> Stop

------------------------------------------------------------------------------
-- Scheduling
------------------------------------------------------------------------------

{-# INLINE [1] roundRobin #-}
roundRobin :: Monad m => Stream m a -> Stream m a -> Stream m a
roundRobin (Stream step1 state1) (Stream step2 state2) =
    Stream step (InterleaveFirst state1 state2)

    where

    {-# INLINE [0] step #-}
    step gst (InterleaveFirst st1 st2) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield a (InterleaveSecond s st2)
            Skip s -> Skip (InterleaveSecond s st2)
            Stop -> Skip (InterleaveSecondOnly st2)

    step gst (InterleaveSecond st1 st2) = do
        r <- step2 gst st2
        return $ case r of
            Yield a s -> Yield a (InterleaveFirst st1 s)
            Skip s -> Skip (InterleaveFirst st1 s)
            Stop -> Skip (InterleaveFirstOnly st1)

    step gst (InterleaveSecondOnly st2) = do
        r <- step2 gst st2
        return $ case r of
            Yield a s -> Yield a (InterleaveSecondOnly s)
            Skip s -> Skip (InterleaveSecondOnly s)
            Stop -> Stop

    step gst (InterleaveFirstOnly st1) = do
        r <- step1 gst st1
        return $ case r of
            Yield a s -> Yield a (InterleaveFirstOnly s)
            Skip s -> Skip (InterleaveFirstOnly s)
            Stop -> Stop

------------------------------------------------------------------------------
-- Zipping
------------------------------------------------------------------------------

{-# INLINE [1] zipWithM #-}
zipWithM :: Monad m
    => (a -> b -> m c) -> Stream m a -> Stream m b -> Stream m c
zipWithM f (Stream stepa ta) (Stream stepb tb) = Stream step (ta, tb, Nothing)
  where
    {-# INLINE [0] step #-}
    step gst (sa, sb, Nothing) = do
        r <- stepa (adaptState gst) sa
        return $
          case r of
            Yield x sa' -> Skip (sa', sb, Just x)
            Skip sa'    -> Skip (sa', sb, Nothing)
            Stop        -> Stop

    step gst (sa, sb, Just x) = do
        r <- stepb (adaptState gst) sb
        case r of
            Yield y sb' -> do
                z <- f x y
                return $ Yield z (sa, sb', Nothing)
            Skip sb' -> return $ Skip (sa, sb', Just x)
            Stop     -> return Stop


{-# RULES "zipWithM xs xs"
    forall f xs. zipWithM @Identity f xs xs = mapM (\x -> f x x) xs #-}


{-# INLINE zipWith #-}
zipWith :: Monad m => (a -> b -> c) -> Stream m a -> Stream m b -> Stream m c
zipWith f = zipWithM (\a b -> return (f a b))

------------------------------------------------------------------------------
-- Merging
------------------------------------------------------------------------------

{-# INLINE [1] mergeByM #-}
mergeByM
    :: (Monad m)
    => (a -> a -> m Ordering) -> Stream m a -> Stream m a -> Stream m a
mergeByM cmp (Stream stepa ta) (Stream stepb tb) =
    Stream step (Just ta, Just tb, Nothing, Nothing)
  where
    {-# INLINE [0] step #-}

    -- one of the values is missing, and the corresponding stream is running
    step gst (Just sa, sb, Nothing, b) = do
        r <- stepa gst sa
        return $ case r of
            Yield a sa' -> Skip (Just sa', sb, Just a, b)
            Skip sa'    -> Skip (Just sa', sb, Nothing, b)
            Stop        -> Skip (Nothing, sb, Nothing, b)

    step gst (sa, Just sb, a, Nothing) = do
        r <- stepb gst sb
        return $ case r of
            Yield b sb' -> Skip (sa, Just sb', a, Just b)
            Skip sb'    -> Skip (sa, Just sb', a, Nothing)
            Stop        -> Skip (sa, Nothing, a, Nothing)

    -- both the values are available
    step _ (sa, sb, Just a, Just b) = do
        res <- cmp a b
        return $ case res of
            GT -> Yield b (sa, sb, Just a, Nothing)
            _  -> Yield a (sa, sb, Nothing, Just b)

    -- one of the values is missing, corresponding stream is done
    step _ (Nothing, sb, Nothing, Just b) =
            return $ Yield b (Nothing, sb, Nothing, Nothing)

    step _ (sa, Nothing, Just a, Nothing) =
            return $ Yield a (sa, Nothing, Nothing, Nothing)

    step _ (Nothing, Nothing, Nothing, Nothing) = return Stop

{-# INLINE mergeBy #-}
mergeBy
    :: (Monad m)
    => (a -> a -> Ordering) -> Stream m a -> Stream m a -> Stream m a
mergeBy cmp = mergeByM (\a b -> return $ cmp a b)

{-# INLINE [1] joinInnerMerge #-}
joinInnerMerge
    :: (MonadIO m,  Eq a, Eq b)
    => (a -> b -> Ordering) -> Stream m a -> Stream m b -> Stream m (a, b)
joinInnerMerge cmp (Stream stepa ta) (Stream stepb tb) =

    Stream step
    (Just ta, Just tb, Nothing, Nothing, Nothing, Nothing, Nothing, NM, 0)
  where
    {-# INLINE [0] step #-}

    -- step 1 when left stream could be  empty
    step gst (Just sa, sb, Nothing, Nothing, pa, pb, _, NM, idx) = do
        ref <- liftIO $ newIORef []
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Skip
                (Just sa', sb, Just a', Nothing, pa, pb, Just ref, MR, idx)
            Skip sa' ->
                Skip
                (Just sa', sb, Nothing, Nothing, pa, pb, Just ref, NM, idx)
            Stop -> Stop

    --  step 2 both stream has data pull from right stream and
    --  compare a and b
    step gst (Just sa, Just sb, a, b, pa, pb, buff, MR, idx) = do
        r <- stepb (adaptState gst) sb
        return $ case r of
            Yield b' sb' ->
                Skip
                (Just sa, Just sb', a, Just b', pa, pb, buff, MC, idx) -- go to step 5
            Skip sb' ->
                Skip
                (Nothing, Just sb', Nothing, b, pa, Nothing, buff, NM, idx)
            Stop -> Stop

    -- step 3 both stream has data pull from right stream and in next step
    -- compare b with previous b to remove mismatched duplicates from right stream
    step gst (Just sa, Just sb, a, b, pa, pb, buff, MRD, idx) = do
        r <- stepb (adaptState gst) sb
        return $ case r of
            Yield b' sb' ->
                Skip
                (Just sa, Just sb', a, Just b', pa, pb, buff, MCD, idx) -- step 4
            Skip sb' ->
                Skip
                (Nothing, Just sb', Nothing, b, pa, Nothing, buff, NM, idx)
            Stop -> Stop

    -- step 4 compare b with previous b to remove mismatched duplicates from right stream
    step _ (Just sa, sb, Just a, Just b, pa, Just pb, buff, MCD, idx) =
        return $
        if b == pb
        then
            Skip
            (Just sa,  sb, Just a, Just b, pa, Just pb, buff, MRD, idx) -- step 3
        else Skip (Just sa, sb, Just a,Just b, pa, Just b, buff, MC, idx) -- step 5

    -- step 5 compare left stream data with right stream
    step _ (sa, sb, Just a, Just b, pa, pb, Just buff, MC, idx) = do
        let res = cmp a b
        return $ case res of
            LT ->
                Skip (sa, sb, Just a, Just b, pa, pb, Just buff, ML, idx) -- skip a step 9
            EQ ->
                Skip (sa, sb, Just a, Just b, Just a, pb, Just buff, BUFF, idx) -- step 6
            GT ->
                Skip (sa, sb, Just a, Just b, pa, Just b, Just buff, MRD, idx) -- skip b step 3

    -- step 6 b in list initial step
    step _ (Just sa, Just sb, Just a, Just b, pa, _, Just buff, BUFF, idx) = do
        liftIO $ modifyIORef'  buff (b : )
        return $
            Skip                                    -- step 7
            ( Just sa
            , Just sb
            , Just a
            , Just b
            , pa
            , Just b
            , Just buff
            , BUFFB
            , idx
            )

    -- step 7 buffer repeated data
    step gst (Just sa, Just sb, a, b, pa, Just pb, Just buff, BUFFB, idx) = do
        r <- stepb (adaptState gst) sb
        case r of
            Yield b' sb' -> do
                if b' == pb
                then do
                    liftIO $ modifyIORef'  buff (b' : )
                    return $
                        Skip                                -- step 7
                        ( Just sa
                        , Just sb'
                        , a
                        , Just b'
                        , pa
                        , Just b'
                        , Just buff
                        , BUFFB
                        , idx
                        )
                else return $
                    Skip                                    -- step 8
                    ( Just sa
                    , Just sb'
                    , a
                    , Just b'
                    , pa
                    , Just b'
                    , Just buff
                    , YLD
                    , 0
                    )
            Skip sb' ->
                return $
                    Skip
                    ( Nothing
                    , Just sb'
                    , Nothing
                    , b
                    , pa
                    , Nothing
                    , Just buff
                    , NM
                    , idx
                    )
            Stop ->
                return $
                Skip (Just sa, Just sb, a, b, pa, Just pb, Just buff, YLD, 0)  -- step 8

    -- step 8 do pairing with buff (only when repeatation is over)
    step
        _
        ( Just sa
        , Just sb
        , Just a
        , Just b
        , pa
        , Just pb
        , Just buff
        , YLD
        , idx
        )
        = do
        bl <- liftIO $ readIORef buff
        if idx < length bl
        then return $
            Yield
            (a, bl !! idx)
            ( Just sa
            , Just sb
            , Just a
            , Just b
            , pa
            , Just pb
            , Just buff
            , YLD
            , idx+1
            )
        else return $
            Skip                                    -- step 11
            ( Just sa
            , Just sb
            , Just a
            , Just b
            , Just a
            , Just pb
            , Just buff
            , ALD
            , 0
            )

    -- step 9 pull the data from left stream to compare next data from right stream
    step gst (Just sa, Just sb, Just a, Just b, pa, pb, buff, ML, idx) = do
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Skip                                -- step 5
                ( Just sa'
                , Just sb
                , Just a'
                , Just b
                , Just a
                , pb
                , buff
                , MC
                , idx
                )
            Skip sa' ->
                Skip
                (Just sa', Just sb, Nothing, Nothing, pa, pb, buff, MR, idx)
            Stop -> Stop

    -- step 10 pull the data from left stream to compare next data from right stream
    step gst (Just sa, sb, Just _, Just b, pa, pb, buff, MLD, idx) = do
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Skip (Just sa', sb, Just a', Just b, pa, pb, buff, MC, idx) -- step 5
            Skip sa' ->
                Skip (Just sa', sb, Nothing, Nothing, pa, pb, buff, MR, idx)
            Stop -> Stop

    -- step 11 pull the data from left stream to compare next data from right stream
    step gst
        (Just sa, sb, Just _, Just b, Just pa, pb, Just buff, ALD, idx) = do
        r <- stepa (adaptState gst) sa
        case r of
            Yield a' sa' -> do
                if a' == pa
                then return $
                    Skip                                -- step 8
                    ( Just sa'
                    , sb
                    , Just a'
                    , Just b
                    , Just a'
                    , pb
                    , Just buff
                    , YLD
                    , idx
                    )
                else do
                    -- clear buff
                    liftIO $ writeIORef buff []
                    return $
                        Skip                            -- step 5
                        ( Just sa'
                        , sb
                        , Just a'
                        , Just b
                        , Just a'
                        , pb
                        , Just buff
                        , MC
                        , idx
                        )
            Skip sa' ->
                return $
                    Skip
                    ( Just sa'
                    , sb
                    , Nothing
                    , Nothing
                    , Just pa
                    , pb
                    , Just buff
                    , MR
                    , idx
                    )
            Stop -> return Stop

    step _ (_, _, _, _, _, _, _, _, _) = return Stop


{-# INLINE [1] intersectBySorted #-}
intersectBySorted
    :: (MonadIO m, Eq a)
    => (a -> a -> Ordering) -> Stream m a -> Stream m a -> Stream m a
intersectBySorted cmp (Stream stepa ta) (Stream stepb tb) =
    Stream step (Just ta, Just tb, Nothing, Nothing, Nothing)

    where
    {-# INLINE [0] step #-}

    -- step 1
    step gst (Just sa, sb, Nothing, b, Nothing) = do
        liftIO $ print "p1"
        r <- stepa gst sa
        return $ case r of
            Yield a sa' -> Skip (Just sa', sb, Just a, b, Nothing)
            Skip sa'    -> Skip (Just sa', sb, Nothing, b, Nothing)
            Stop        -> Stop

    -- step 2
    step gst (sa, Just sb, a, Nothing, Nothing) = do
        liftIO $ print "p2"
        r <- stepb gst sb
        return $ case r of
            Yield b sb' -> Skip (sa, Just sb', a, Just b, Nothing)
            Skip sb'    -> Skip (sa, Just sb', a, Nothing, Nothing)
            Stop        -> Stop

    -- step 3
    -- both the values are available compare it
    step _ (sa, sb, Just a, Just b, Nothing) = do
        liftIO $ print "p3"
        let res = cmp a b
        return $ case res of
            GT -> Skip (sa, sb, Just a, Nothing, Nothing)
            LT -> Skip (sa, sb, Nothing, Just b, Nothing)
            EQ -> Yield a (sa, sb, Nothing, Just a, Just b) -- step 4

    -- step 4
    -- Matching element
    step gst (Just sa, Just sb, Nothing, Just _, Just b) = do
        liftIO $ print "p4"
        r1 <- stepa gst sa
        return $ case r1 of
            Yield a' sa' -> do
                if a' == b -- match with prev a
                then Yield a' (Just sa', Just sb, Nothing, Just b, Just b)  --step 1
                else Skip (Just sa', Just sb, Just a', Nothing, Nothing)

            Skip sa'    -> Skip (Just sa', Just sb, Nothing, Nothing, Nothing)
            Stop        -> Stop

    step _ (_, _, _, _, _) = return Stop


{-# INLINE [1] joinLeftMerge #-}
joinLeftMerge
    :: (MonadIO m,  Eq a, Eq b)
    => (a -> b -> Ordering)
    -> Stream m a -> Stream m b
    -> Stream m (a, Maybe b)
joinLeftMerge cmp (Stream stepa ta) (Stream stepb tb) =
    Stream
        step
        (Just ta, Just tb, Nothing, Nothing, Nothing, Nothing, Nothing, NM, 0)
    where
    {-# INLINE [0] step #-}

    -- step 1 when left stream could be  empty
    step gst (Just sa, sb, Nothing, Nothing, pa, pb, _, NM, idx) = do
        ref <- liftIO $ newIORef []
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Skip
                (Just sa', sb, Just a', Nothing, pa, pb, Just ref, MR, idx)
            Skip sa' ->
                Skip
                (Just sa', sb, Nothing, Nothing, pa, pb, Just ref, NM, idx)
            Stop -> Stop

    --  step 2 both stream has data pull from right stream and
    --  compare a and b
    step gst (Just sa, Just sb, Just a, b, pa, pb, buff, MR, idx) = do
        r <- stepb (adaptState gst) sb
        return $ case r of
            Yield b' sb' ->
                Skip
                (Just sa, Just sb', Just a, Just b', pa, pb, buff, MC, idx) -- go to step 5
            Skip sb' ->
                Skip
                (Nothing, Just sb', Nothing, b, pa, Nothing, buff, NM, idx)
            Stop ->
                Yield
                (a, Nothing)
                ( Just sa
                , Nothing
                , Just a
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )

    -- step 3 both stream has data pull from right stream and in next step
    -- compare b with previous b to remove mismatched duplicates from right stream
    step gst (Just sa, Just sb, Just a, b, pa, pb, buff, MRD, idx) = do
        r <- stepb (adaptState gst) sb
        return $ case r of
            Yield b' sb' ->
                Skip
                (Just sa, Just sb', Just a, Just b', pa, pb, buff, MCD, idx) -- step 4
            Skip sb' ->
                Skip
                (Nothing, Just sb', Nothing, b, pa, Nothing, buff, NM, idx)
            Stop ->
                Yield
                (a, Nothing)
                ( Just sa
                , Nothing
                , Just a
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )

    -- step 4 compare b with previous b to remove mismatched duplicates from right stream
    step _ (Just sa, sb, Just a, Just b, pa, Just pb, buff, MCD, idx) =
        return $
        if b == pb
        then
            Skip
            (Just sa,  sb, Just a, Just b, pa, Just pb, buff, MRD, idx) -- step 3
        else
            Skip
            (Just sa, sb, Just a,Just b, pa, Just b, buff, MC, idx)     -- step 5

    -- step 5 compare left stream data with right stream
    step _ (sa, sb, Just a, Just b, pa, pb, Just buff, MC, idx) = do
        let res = cmp a b
        return $ case res of
            LT ->
                Yield
                (a, Nothing)
                (sa, sb, Just a, Just b, pa, pb, Just buff, ML, idx) -- skip a step 9
            EQ ->
                Skip
                (sa, sb, Just a, Just b, Just a, pb, Just buff, BUFF, idx) -- step 6
            GT ->
                Skip
                (sa, sb, Just a, Just b, pa, Just b, Just buff, MRD, idx) -- skip b  step 3

    -- step 6 b in list initial step
    step _ (Just sa, Just sb, Just a, Just b, pa, _, Just buff, BUFF, idx) = do
        liftIO $ modifyIORef'  buff (b : )
        return $
            Skip                            -- step 7 pull next b
            ( Just sa
            , Just sb
            , Just a
            , Just b
            , pa
            , Just b
            , Just buff
            , BUFFB
            , idx
            )

    -- step 7 buffer repeated data
    step gst (Just sa, Just sb, a, b, pa, Just pb, Just buff, BUFFB, idx) = do
        r <- stepb (adaptState gst) sb
        case r of
            Yield b' sb' -> do
                if b' == pb
                then do
                    liftIO $ modifyIORef'  buff (b' : )
                    return $
                        Skip                            -- step 7
                        ( Just sa
                        , Just sb'
                        , a
                        , Just b'
                        , pa
                        , Just b'
                        , Just buff
                        , BUFFB
                        , idx
                        )
                else
                    return $
                    Skip                        -- step 8
                    ( Just sa
                    , Just sb'
                    , a
                    , Just b'
                    , pa
                    , Just b'
                    , Just buff
                    , YLD
                    , 0
                    )
            Skip sb' ->
                return $
                    Skip
                    ( Nothing
                    , Just sb'
                    , Nothing
                    , b
                    , pa
                    , Nothing
                    , Just buff
                    , NM
                    , idx
                    )
            Stop ->
                return $
                    Skip
                    (Just sa, Just sb, a, b, pa, Just pb, Just buff, YLD, 0)    -- go to step 8

    -- step 8 do pairing with buff (only when repeatation is over)
    step _
        (Just sa, Just sb, Just a, Just b, pa, Just pb, Just buff, YLD, idx)
        = do
            bl <- liftIO $ readIORef buff
            if idx < length bl
            then return $
                Yield
                (a, Just (bl !! idx))
                ( Just sa
                , Just sb
                , Just a
                , Just b
                , pa
                , Just pb
                , Just buff
                , YLD
                , idx+1
                )
            else return $
                Skip                                -- step 11
                ( Just sa
                , Just sb
                , Just a
                , Just b
                , Just a
                , Just pb
                , Just buff
                , ALD
                , 0
                )

    -- step 9 pull the data from left stream to compare next data from right stream
    step gst (Just sa, Just sb, Just a, Just b, pa, pb, buff, ML, idx) = do
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Skip                            -- step 5
                ( Just sa'
                , Just sb
                , Just a'
                , Just b
                , Just a
                , pb
                , buff
                , MC
                , idx
                )
            Skip sa' ->
                Skip
                (Just sa', Just sb, Nothing, Nothing, pa, pb, buff, MR, idx)
            Stop -> Stop

    -- step 10 pull the data from left stream to compare next data from right stream
    step gst (Just sa, sb, Just _, Just b, pa, pb, buff, MLD, idx) = do
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Skip
                (Just sa', sb, Just a', Just b, pa, pb, buff, MC, idx) -- step 5
            Skip sa' ->
                Skip
                (Just sa', sb, Nothing, Nothing, pa, pb, buff, MR, idx)
            Stop -> Stop

    -- step 11 pull the data from left stream to compare next data from right stream
    step gst (Just sa, sb, Just _, Just b, Just pa, pb, Just buff, ALD, idx) = do
        r <- stepa (adaptState gst) sa
        case r of
            Yield a' sa' -> do
                if a' == pa
                then return $
                    Skip                                -- step 8
                    ( Just sa'
                    , sb
                    , Just a'
                    , Just b
                    , Just a'
                    , pb
                    , Just buff
                    , YLD
                    , idx
                    )
                else do
                    -- clear buff
                    liftIO $ writeIORef buff []
                    return $
                        Skip                        -- step 5
                        ( Just sa'
                        , sb
                        , Just a'
                        , Just b
                        , Just a'
                        , pb
                        , Just buff
                        , MC
                        , idx
                        )
            Skip sa' ->
                return $
                    Skip
                    ( Just sa'
                    , sb
                    , Nothing
                    , Nothing
                    , Just pa
                    , pb
                    , Just buff
                    , MR
                    , idx
                    )
            Stop -> return Stop

    --  step 12 b stream has finished yield remaining a
    step
        gst
        (Just sa, Nothing, Just a, Nothing, Nothing, Nothing, Nothing, NM, idx)
        = do
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Yield                           -- step 5
                (a', Nothing)
                ( Just sa'
                , Nothing
                , Just a'
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )
            Skip sa' ->
                Skip
                ( Just sa'
                , Nothing
                , Just a
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )
            Stop -> Stop

    step _ (_, _, _, _, _, _, _, _, _) = return Stop

{-# INLINE [1] joinRightMerge #-}
joinRightMerge
    :: (MonadIO m,  Eq a, Eq b)
    => (a -> b -> Ordering) -> Stream m b -> Stream m a -> Stream m (Maybe b, a)
joinRightMerge cmp s1 s2 = fmap (\(a,b) -> (b,a)) (joinLeftMerge cmp s2 s1)


{-# INLINE [1] differenceBySorted #-}
differenceBySorted
    :: (Monad m)
    => (a -> a -> Ordering) -> Stream m a -> Stream m a -> Stream m a
differenceBySorted cmp (Stream stepa ta) (Stream stepb tb) =
    Stream step (Just ta, Just tb, Nothing, Nothing, Nothing)
    where
    {-# INLINE [0] step #-}

    -- one of the values is missing, and the corresponding stream is running
    step gst (Just sa, sb, Nothing, b, Nothing) = do
        r <- stepa gst sa
        return $ case r of
            Yield a sa' -> Skip (Just sa', sb, Just a, b, Nothing)
            Skip sa'    -> Skip (Just sa', sb, Nothing, b, Nothing)
            Stop        -> Skip (Nothing, sb, Nothing, b, Nothing)

    step gst (sa, Just sb, a, Nothing, Nothing) = do
        r <- stepb gst sb
        return $ case r of
            Yield b sb' -> Skip (sa, Just sb', a, Just b, Nothing)
            Skip sb'    -> Skip (sa, Just sb', a, Nothing, Nothing)
            Stop        -> Skip (sa, Nothing, a, Nothing, Nothing)

    -- Matching element
    step gst (Just sa, Just sb, Nothing, _, Just _) = do
        r1 <- stepa gst sa
        r2 <- stepb gst sb
        return $ case r1 of
            Yield a sa' -> case r2 of
                            Yield c sb' -> Skip (Just sa', Just sb', Just a, Just c, Nothing)
                            Skip sb' -> Skip (Just sa', Just sb', Just a, Just a, Nothing)
                            Stop -> Yield a (Just sa', Just sb, Nothing, Nothing, Just a)
            Skip sa'    -> case r2 of
                            Yield c sb' -> Skip (Just sa', Just sb', Just c, Just c, Nothing)
                            Skip sb' -> Skip (Just sa', Just sb', Nothing, Nothing, Nothing)
                            Stop -> Stop
            Stop        -> Stop

    -- both the values are available
    step _ (sa, sb, Just a, Just b, Nothing) = do
        let res = cmp a b
        return $ case res of
            GT -> Skip (sa, sb, Just a, Nothing, Nothing)
            LT -> Yield a (sa, sb, Nothing, Just b, Nothing)
            EQ -> Skip (sa, sb, Nothing, Just b, Just b)

    -- one of the values is missing, corresponding stream is done
    step _ (sa, Nothing, Just a, Nothing, Nothing) =
        return $ Yield a (sa, Nothing, Nothing, Nothing , Nothing)
    step _ (_, _, _, _, _) = return Stop

data Dir = ALD|BUFF|BUFFB|ML|MR|MC|MLD|MRD|MCD|NM|YLD

{-# INLINE removeDupsAll #-}
removeDupsAll
    :: (MonadIO m)
    => (a -> a -> Ordering) -> Stream m a -> Stream m a -> Stream m a
removeDupsAll cmp = removeDupsAllM (\a b -> return $ cmp a b)

{-# INLINE [1] removeDupsAllM #-}
removeDupsAllM
    ::(MonadIO m)
    => (a -> a -> m Ordering) -> Stream m a -> Stream m a -> Stream m a
removeDupsAllM cmp (Stream stepa ta) (Stream stepb tb) =
    Stream step (Just ta, Just tb, Nothing, Nothing, Nothing, Nothing, NM)
    where
    {-# INLINE [0] step #-}
    -- step 1 when left stream could be  empty
    step gst (Just sa, sb, Nothing, Nothing, pa, pb, NM) = do
        liftIO $ print "p1"
        r <- stepa gst sa
        return $ case r of
            Yield a' sa' -> Skip (Just sa', sb, Just a', Nothing, Just a', pb, MR)
            Skip sa' -> Skip (Just sa', sb, Nothing, Nothing, pa, pb, MR)
            Stop -> Skip (Nothing, sb, Nothing, Nothing, pa, pb, NM)

    --  step 2 both stream has data pull from right stream and
    --  compare a and b
    step gst (Just sa, Just sb, a, b, pa, _, MR) = do
        liftIO $ print "p2"
        r <- stepb gst sb
        return $ case r of
            Yield b' sb' -> Skip (Just sa, Just sb', a, Just b', pa, Just b', MC) -- go to step 8
            Skip sb' -> Skip (Nothing, Just sb', Nothing, b, pa, Nothing, NM)
            Stop -> Stop

    -- step 3 left stream is finished
    step gst(Nothing, Just sb, Nothing, b, pa, Nothing, NM)= do
        liftIO $ print "p3"
        r <- stepb gst sb
        return $ case r of
            Yield b' sb' -> Yield b' (Nothing, Just sb', Nothing, Just b', pa, Just b', MR)
            Skip sb' -> Skip (Nothing, Just sb', Nothing, b, pa, Nothing, NM)
            Stop -> Stop

    -- step 4 left stream is finished
    step gst (Nothing, Just sb, a, b, pa, pb, MR) = do
        liftIO $ print "p4"
        r <- stepb gst sb
        return $ case r of
            Yield b' sb' -> Skip (Nothing, Just sb', a, Just b', pa, pb, MC) --go step 7
            Skip sb' -> Skip (Nothing, Just sb', Nothing, b, pa, Nothing, NM)
            Stop -> Stop

    -- step 5 both stream has data pull from right stream and in next step
    -- compare b with previous b to remove duplicates from right stream
    step gst (Just sa, Just sb, a, b, pa, pb, MRD) = do
        liftIO $ print "p5"
        r <- stepb gst sb
        return $ case r of
            Yield b' sb' -> Skip(Just sa, Just sb', a, Just b', pa, pb, MCD)
            Skip sb' -> Skip (Nothing, Just sb', Nothing, b, pa, Nothing, NM)
            Stop -> Stop

    -- step 6 compare b with previous b to remove duplicates from right stream
    step _ (Just sa, sb, Just a, Just b, pa, Just pb, MCD) = do
        liftIO $ print "p6"
        res <- cmp b pb
        return $ case res of
            EQ -> Skip (Just sa,  sb, Just a, Just b, pa, Just pb, MRD)
            _ -> Skip (Just sa, sb, Just a,Just b, pa, Just b, MC)

    -- step 7 compare consecutive data from right stream
    step _ (Nothing, sb, Nothing, Just b, pa, Just pb, MC) = do
        liftIO $ print "p7"
        res <- cmp b pb
        return $ case res of
            EQ -> Skip (Nothing, sb, Nothing, Just b, pa, Just b, MR)
            _ -> Yield b (Nothing, sb, Nothing,Just b, pa, Just b, MR)

    -- step 8 compare left stream data with right stream
    step _ (sa, sb, Just a, Just b, pa, pb, MC) = do
        liftIO $ print "p8"
        res <- cmp a b
        return $ case res of
            LT -> Skip (sa, sb, Just a, Just b, pa, pb, ML) -- step 9
            EQ -> Skip (sa, sb, Just a, Just b, pa, pb, MR) -- step 2
            GT -> Yield b (sa, sb, Just a, Just b, pa, Just b, MRD) -- print b & step 5

    -- step 9 pull the data from left stream to compare next data from right stream
    step gst (Just sa, Just sb, Just a, Just b, pa, pb, ML) = do
        liftIO $ print "p9"
        r <- stepa gst sa
        return $ case r of
            Yield a' sa' -> Skip(Just sa', Just sb, Just a', Just b, Just a, pb, MC) -- step 8
            Skip sa' -> Skip (Just sa', Just sb, Nothing, Nothing, pa, pb, MR)
            Stop -> Yield b (Nothing, Just sb, Nothing, Nothing,  pa, pb, MR) -- a is empty go step 4

    step _ (_, _, _, _, _, _, _) = do
        liftIO $ print "p10"
        return Stop

------------------------------------------------------------------------------
-- Combine N Streams - unfoldMany
------------------------------------------------------------------------------

data ConcatUnfoldInterleaveState o i =
      ConcatUnfoldInterleaveOuter o [i]
    | ConcatUnfoldInterleaveInner o [i]
    | ConcatUnfoldInterleaveInnerL [i] [i]
    | ConcatUnfoldInterleaveInnerR [i] [i]

-- XXX use arrays to store state instead of lists.
-- XXX In general we can use different scheduling strategies e.g. how to
-- schedule the outer vs inner loop or assigning weights to different streams
-- or outer and inner loops.

-- After a yield, switch to the next stream. Do not switch streams on Skip.
-- Yield from outer stream switches to the inner stream.
--
-- There are two choices here, (1) exhaust the outer stream first and then
-- start yielding from the inner streams, this is much simpler to implement,
-- (2) yield at least one element from an inner stream before going back to
-- outer stream and opening the next stream from it.
--
-- Ideally, we need some scheduling bias to inner streams vs outer stream.
-- Maybe we can configure the behavior.
--
{-# INLINE [1] unfoldManyInterleave #-}
unfoldManyInterleave :: Monad m => Unfold m a b -> Stream m a -> Stream m b
unfoldManyInterleave (Unfold istep inject) (Stream ostep ost) =
    Stream step (ConcatUnfoldInterleaveOuter ost [])
  where
    {-# INLINE [0] step #-}
    step gst (ConcatUnfoldInterleaveOuter o ls) = do
        r <- ostep (adaptState gst) o
        case r of
            Yield a o' -> do
                i <- inject a
                i `seq` return (Skip (ConcatUnfoldInterleaveInner o' (i : ls)))
            Skip o' -> return $ Skip (ConcatUnfoldInterleaveOuter o' ls)
            Stop -> return $ Skip (ConcatUnfoldInterleaveInnerL ls [])

    step _ (ConcatUnfoldInterleaveInner _ []) = undefined
    step _ (ConcatUnfoldInterleaveInner o (st:ls)) = do
        r <- istep st
        return $ case r of
            Yield x s -> Yield x (ConcatUnfoldInterleaveOuter o (s:ls))
            Skip s    -> Skip (ConcatUnfoldInterleaveInner o (s:ls))
            Stop      -> Skip (ConcatUnfoldInterleaveOuter o ls)

    step _ (ConcatUnfoldInterleaveInnerL [] []) = return Stop
    step _ (ConcatUnfoldInterleaveInnerL [] rs) =
        return $ Skip (ConcatUnfoldInterleaveInnerR [] rs)

    step _ (ConcatUnfoldInterleaveInnerL (st:ls) rs) = do
        r <- istep st
        return $ case r of
            Yield x s -> Yield x (ConcatUnfoldInterleaveInnerL ls (s:rs))
            Skip s    -> Skip (ConcatUnfoldInterleaveInnerL (s:ls) rs)
            Stop      -> Skip (ConcatUnfoldInterleaveInnerL ls rs)

    step _ (ConcatUnfoldInterleaveInnerR [] []) = return Stop
    step _ (ConcatUnfoldInterleaveInnerR ls []) =
        return $ Skip (ConcatUnfoldInterleaveInnerL ls [])

    step _ (ConcatUnfoldInterleaveInnerR ls (st:rs)) = do
        r <- istep st
        return $ case r of
            Yield x s -> Yield x (ConcatUnfoldInterleaveInnerR (s:ls) rs)
            Skip s    -> Skip (ConcatUnfoldInterleaveInnerR ls (s:rs))
            Stop      -> Skip (ConcatUnfoldInterleaveInnerR ls rs)

-- XXX In general we can use different scheduling strategies e.g. how to
-- schedule the outer vs inner loop or assigning weights to different streams
-- or outer and inner loops.
--
-- This could be inefficient if the tasks are too small.
--
-- Compared to unfoldManyInterleave this one switches streams on Skips.
--
{-# INLINE [1] unfoldManyRoundRobin #-}
unfoldManyRoundRobin :: Monad m => Unfold m a b -> Stream m a -> Stream m b
unfoldManyRoundRobin (Unfold istep inject) (Stream ostep ost) =
    Stream step (ConcatUnfoldInterleaveOuter ost [])
  where
    {-# INLINE [0] step #-}
    step gst (ConcatUnfoldInterleaveOuter o ls) = do
        r <- ostep (adaptState gst) o
        case r of
            Yield a o' -> do
                i <- inject a
                i `seq` return (Skip (ConcatUnfoldInterleaveInner o' (i : ls)))
            Skip o' -> return $ Skip (ConcatUnfoldInterleaveInner o' ls)
            Stop -> return $ Skip (ConcatUnfoldInterleaveInnerL ls [])

    step _ (ConcatUnfoldInterleaveInner o []) =
            return $ Skip (ConcatUnfoldInterleaveOuter o [])

    step _ (ConcatUnfoldInterleaveInner o (st:ls)) = do
        r <- istep st
        return $ case r of
            Yield x s -> Yield x (ConcatUnfoldInterleaveOuter o (s:ls))
            Skip s    -> Skip (ConcatUnfoldInterleaveOuter o (s:ls))
            Stop      -> Skip (ConcatUnfoldInterleaveOuter o ls)

    step _ (ConcatUnfoldInterleaveInnerL [] []) = return Stop
    step _ (ConcatUnfoldInterleaveInnerL [] rs) =
        return $ Skip (ConcatUnfoldInterleaveInnerR [] rs)

    step _ (ConcatUnfoldInterleaveInnerL (st:ls) rs) = do
        r <- istep st
        return $ case r of
            Yield x s -> Yield x (ConcatUnfoldInterleaveInnerL ls (s:rs))
            Skip s    -> Skip (ConcatUnfoldInterleaveInnerL ls (s:rs))
            Stop      -> Skip (ConcatUnfoldInterleaveInnerL ls rs)

    step _ (ConcatUnfoldInterleaveInnerR [] []) = return Stop
    step _ (ConcatUnfoldInterleaveInnerR ls []) =
        return $ Skip (ConcatUnfoldInterleaveInnerL ls [])

    step _ (ConcatUnfoldInterleaveInnerR ls (st:rs)) = do
        r <- istep st
        return $ case r of
            Yield x s -> Yield x (ConcatUnfoldInterleaveInnerR (s:ls) rs)
            Skip s    -> Skip (ConcatUnfoldInterleaveInnerR (s:ls) rs)
            Stop      -> Skip (ConcatUnfoldInterleaveInnerR ls rs)

------------------------------------------------------------------------------
-- Combine N Streams - interpose
------------------------------------------------------------------------------

{-# ANN type InterposeSuffixState Fuse #-}
data InterposeSuffixState s1 i1 =
      InterposeSuffixFirst s1
    -- | InterposeSuffixFirstYield s1 i1
    | InterposeSuffixFirstInner s1 i1
    | InterposeSuffixSecond s1

-- Note that if an unfolded layer turns out to be nil we still emit the
-- separator effect. An alternate behavior could be to emit the separator
-- effect only if at least one element has been yielded by the unfolding.
-- However, that becomes a bit complicated, so we have chosen the former
-- behvaior for now.
{-# INLINE [1] interposeSuffix #-}
interposeSuffix
    :: Monad m
    => m c -> Unfold m b c -> Stream m b -> Stream m c
interposeSuffix
    action
    (Unfold istep1 inject1) (Stream step1 state1) =
    Stream step (InterposeSuffixFirst state1)

    where

    {-# INLINE [0] step #-}
    step gst (InterposeSuffixFirst s1) = do
        r <- step1 (adaptState gst) s1
        case r of
            Yield a s -> do
                i <- inject1 a
                i `seq` return (Skip (InterposeSuffixFirstInner s i))
                -- i `seq` return (Skip (InterposeSuffixFirstYield s i))
            Skip s -> return $ Skip (InterposeSuffixFirst s)
            Stop -> return Stop

    {-
    step _ (InterposeSuffixFirstYield s1 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Yield x (InterposeSuffixFirstInner s1 i')
            Skip i'    -> Skip (InterposeSuffixFirstYield s1 i')
            Stop       -> Skip (InterposeSuffixFirst s1)
    -}

    step _ (InterposeSuffixFirstInner s1 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Yield x (InterposeSuffixFirstInner s1 i')
            Skip i'    -> Skip (InterposeSuffixFirstInner s1 i')
            Stop       -> Skip (InterposeSuffixSecond s1)

    step _ (InterposeSuffixSecond s1) = do
        r <- action
        return $ Yield r (InterposeSuffixFirst s1)

{-# ANN type InterposeState Fuse #-}
data InterposeState s1 i1 a =
      InterposeFirst s1
    -- | InterposeFirstYield s1 i1
    | InterposeFirstInner s1 i1
    | InterposeFirstInject s1
    -- | InterposeFirstBuf s1 i1
    | InterposeSecondYield s1 i1
    -- -- | InterposeSecondYield s1 i1 a
    -- -- | InterposeFirstResume s1 i1 a

-- Note that this only interposes the pure values, we may run many effects to
-- generate those values as some effects may not generate anything (Skip).
{-# INLINE [1] interpose #-}
interpose :: Monad m => m c -> Unfold m b c -> Stream m b -> Stream m c
interpose
    action
    (Unfold istep1 inject1) (Stream step1 state1) =
    Stream step (InterposeFirst state1)

    where

    {-# INLINE [0] step #-}
    step gst (InterposeFirst s1) = do
        r <- step1 (adaptState gst) s1
        case r of
            Yield a s -> do
                i <- inject1 a
                i `seq` return (Skip (InterposeFirstInner s i))
                -- i `seq` return (Skip (InterposeFirstYield s i))
            Skip s -> return $ Skip (InterposeFirst s)
            Stop -> return Stop

    {-
    step _ (InterposeFirstYield s1 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Yield x (InterposeFirstInner s1 i')
            Skip i'    -> Skip (InterposeFirstYield s1 i')
            Stop       -> Skip (InterposeFirst s1)
    -}

    step _ (InterposeFirstInner s1 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Yield x (InterposeFirstInner s1 i')
            Skip i'    -> Skip (InterposeFirstInner s1 i')
            Stop       -> Skip (InterposeFirstInject s1)

    step gst (InterposeFirstInject s1) = do
        r <- step1 (adaptState gst) s1
        case r of
            Yield a s -> do
                i <- inject1 a
                -- i `seq` return (Skip (InterposeFirstBuf s i))
                i `seq` return (Skip (InterposeSecondYield s i))
            Skip s -> return $ Skip (InterposeFirstInject s)
            Stop -> return Stop

    {-
    step _ (InterposeFirstBuf s1 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Skip (InterposeSecondYield s1 i' x)
            Skip i'    -> Skip (InterposeFirstBuf s1 i')
            Stop       -> Stop
    -}

    {-
    step _ (InterposeSecondYield s1 i1 v) = do
        r <- action
        return $ Yield r (InterposeFirstResume s1 i1 v)
    -}
    step _ (InterposeSecondYield s1 i1) = do
        r <- action
        return $ Yield r (InterposeFirstInner s1 i1)

    {-
    step _ (InterposeFirstResume s1 i1 v) = do
        return $ Yield v (InterposeFirstInner s1 i1)
    -}

------------------------------------------------------------------------------
-- Combine N Streams - intercalate
------------------------------------------------------------------------------

data ICUState s1 s2 i1 i2 =
      ICUFirst s1 s2
    | ICUSecond s1 s2
    | ICUSecondOnly s2
    | ICUFirstOnly s1
    | ICUFirstInner s1 s2 i1
    | ICUSecondInner s1 s2 i2
    | ICUFirstOnlyInner s1 i1
    | ICUSecondOnlyInner s2 i2

-- | Interleave streams (full streams, not the elements) unfolded from two
-- input streams and concat. Stop when the first stream stops. If the second
-- stream ends before the first one then first stream still keeps running alone
-- without any interleaving with the second stream.
--
--    [a1, a2, ... an]                   [b1, b2 ...]
-- => [streamA1, streamA2, ... streamAn] [streamB1, streamB2, ...]
-- => [streamA1, streamB1, streamA2...StreamAn, streamBn]
-- => [a11, a12, ...a1j, b11, b12, ...b1k, a21, a22, ...]
--
{-# INLINE [1] gintercalateSuffix #-}
gintercalateSuffix
    :: Monad m
    => Unfold m a c -> Stream m a -> Unfold m b c -> Stream m b -> Stream m c
gintercalateSuffix
    (Unfold istep1 inject1) (Stream step1 state1)
    (Unfold istep2 inject2) (Stream step2 state2) =
    Stream step (ICUFirst state1 state2)

    where

    {-# INLINE [0] step #-}
    step gst (ICUFirst s1 s2) = do
        r <- step1 (adaptState gst) s1
        case r of
            Yield a s -> do
                i <- inject1 a
                i `seq` return (Skip (ICUFirstInner s s2 i))
            Skip s -> return $ Skip (ICUFirst s s2)
            Stop -> return Stop

    step gst (ICUFirstOnly s1) = do
        r <- step1 (adaptState gst) s1
        case r of
            Yield a s -> do
                i <- inject1 a
                i `seq` return (Skip (ICUFirstOnlyInner s i))
            Skip s -> return $ Skip (ICUFirstOnly s)
            Stop -> return Stop

    step _ (ICUFirstInner s1 s2 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Yield x (ICUFirstInner s1 s2 i')
            Skip i'    -> Skip (ICUFirstInner s1 s2 i')
            Stop       -> Skip (ICUSecond s1 s2)

    step _ (ICUFirstOnlyInner s1 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Yield x (ICUFirstOnlyInner s1 i')
            Skip i'    -> Skip (ICUFirstOnlyInner s1 i')
            Stop       -> Skip (ICUFirstOnly s1)

    step gst (ICUSecond s1 s2) = do
        r <- step2 (adaptState gst) s2
        case r of
            Yield a s -> do
                i <- inject2 a
                i `seq` return (Skip (ICUSecondInner s1 s i))
            Skip s -> return $ Skip (ICUSecond s1 s)
            Stop -> return $ Skip (ICUFirstOnly s1)

    step _ (ICUSecondInner s1 s2 i2) = do
        r <- istep2 i2
        return $ case r of
            Yield x i' -> Yield x (ICUSecondInner s1 s2 i')
            Skip i'    -> Skip (ICUSecondInner s1 s2 i')
            Stop       -> Skip (ICUFirst s1 s2)

    step _ (ICUSecondOnly _s2) = undefined
    step _ (ICUSecondOnlyInner _s2 _i2) = undefined

data ICALState s1 s2 i1 i2 a =
      ICALFirst s1 s2
    -- | ICALFirstYield s1 s2 i1
    | ICALFirstInner s1 s2 i1
    | ICALFirstOnly s1
    | ICALFirstOnlyInner s1 i1
    | ICALSecondInject s1 s2
    | ICALFirstInject s1 s2 i2
    -- | ICALFirstBuf s1 s2 i1 i2
    | ICALSecondInner s1 s2 i1 i2
    -- -- | ICALSecondInner s1 s2 i1 i2 a
    -- -- | ICALFirstResume s1 s2 i1 i2 a

-- | Interleave streams (full streams, not the elements) unfolded from two
-- input streams and concat. Stop when the first stream stops. If the second
-- stream ends before the first one then first stream still keeps running alone
-- without any interleaving with the second stream.
--
--    [a1, a2, ... an]                   [b1, b2 ...]
-- => [streamA1, streamA2, ... streamAn] [streamB1, streamB2, ...]
-- => [streamA1, streamB1, streamA2...StreamAn, streamBn]
-- => [a11, a12, ...a1j, b11, b12, ...b1k, a21, a22, ...]
--
{-# INLINE [1] gintercalate #-}
gintercalate
    :: Monad m
    => Unfold m a c -> Stream m a -> Unfold m b c -> Stream m b -> Stream m c
gintercalate
    (Unfold istep1 inject1) (Stream step1 state1)
    (Unfold istep2 inject2) (Stream step2 state2) =
    Stream step (ICALFirst state1 state2)

    where

    {-# INLINE [0] step #-}
    step gst (ICALFirst s1 s2) = do
        r <- step1 (adaptState gst) s1
        case r of
            Yield a s -> do
                i <- inject1 a
                i `seq` return (Skip (ICALFirstInner s s2 i))
                -- i `seq` return (Skip (ICALFirstYield s s2 i))
            Skip s -> return $ Skip (ICALFirst s s2)
            Stop -> return Stop

    {-
    step _ (ICALFirstYield s1 s2 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Yield x (ICALFirstInner s1 s2 i')
            Skip i'    -> Skip (ICALFirstYield s1 s2 i')
            Stop       -> Skip (ICALFirst s1 s2)
    -}

    step _ (ICALFirstInner s1 s2 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Yield x (ICALFirstInner s1 s2 i')
            Skip i'    -> Skip (ICALFirstInner s1 s2 i')
            Stop       -> Skip (ICALSecondInject s1 s2)

    step gst (ICALFirstOnly s1) = do
        r <- step1 (adaptState gst) s1
        case r of
            Yield a s -> do
                i <- inject1 a
                i `seq` return (Skip (ICALFirstOnlyInner s i))
            Skip s -> return $ Skip (ICALFirstOnly s)
            Stop -> return Stop

    step _ (ICALFirstOnlyInner s1 i1) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Yield x (ICALFirstOnlyInner s1 i')
            Skip i'    -> Skip (ICALFirstOnlyInner s1 i')
            Stop       -> Skip (ICALFirstOnly s1)

    -- We inject the second stream even before checking if the first stream
    -- would yield any more elements. There is no clear choice whether we
    -- should do this before or after that. Doing it after may make the state
    -- machine a bit simpler though.
    step gst (ICALSecondInject s1 s2) = do
        r <- step2 (adaptState gst) s2
        case r of
            Yield a s -> do
                i <- inject2 a
                i `seq` return (Skip (ICALFirstInject s1 s i))
            Skip s -> return $ Skip (ICALSecondInject s1 s)
            Stop -> return $ Skip (ICALFirstOnly s1)

    step gst (ICALFirstInject s1 s2 i2) = do
        r <- step1 (adaptState gst) s1
        case r of
            Yield a s -> do
                i <- inject1 a
                i `seq` return (Skip (ICALSecondInner s s2 i i2))
                -- i `seq` return (Skip (ICALFirstBuf s s2 i i2))
            Skip s -> return $ Skip (ICALFirstInject s s2 i2)
            Stop -> return Stop

    {-
    step _ (ICALFirstBuf s1 s2 i1 i2) = do
        r <- istep1 i1
        return $ case r of
            Yield x i' -> Skip (ICALSecondInner s1 s2 i' i2 x)
            Skip i'    -> Skip (ICALFirstBuf s1 s2 i' i2)
            Stop       -> Stop

    step _ (ICALSecondInner s1 s2 i1 i2 v) = do
        r <- istep2 i2
        return $ case r of
            Yield x i' -> Yield x (ICALSecondInner s1 s2 i1 i' v)
            Skip i'    -> Skip (ICALSecondInner s1 s2 i1 i' v)
            Stop       -> Skip (ICALFirstResume s1 s2 i1 i2 v)
    -}

    step _ (ICALSecondInner s1 s2 i1 i2) = do
        r <- istep2 i2
        return $ case r of
            Yield x i' -> Yield x (ICALSecondInner s1 s2 i1 i')
            Skip i'    -> Skip (ICALSecondInner s1 s2 i1 i')
            Stop       -> Skip (ICALFirstInner s1 s2 i1)
            -- Stop       -> Skip (ICALFirstResume s1 s2 i1 i2)

    {-
    step _ (ICALFirstResume s1 s2 i1 i2 x) = do
        return $ Yield x (ICALFirstInner s1 s2 i1 i2)
    -}

------------------------------------------------------------------------------
-- Folding
------------------------------------------------------------------------------

{-# ANN type FIterState Fuse #-}
data FIterState s f m a b
    = FIterInit s f
    | forall fs. FIterStream s (fs -> a -> m (FL.Step fs b)) fs (fs -> m b)
    | FIterYield b (FIterState s f m a b)
    | FIterStop

{-# INLINE [1] foldIterateM #-}
foldIterateM ::
       Monad m => (b -> m (FL.Fold m a b)) -> b -> Stream m a -> Stream m b
foldIterateM func seed0 (Stream step state) =
    Stream stepOuter (FIterInit state seed0)

    where

    {-# INLINE iterStep #-}
    iterStep from st fstep extract = do
        res <- from
        return
            $ Skip
            $ case res of
                  FL.Partial fs -> FIterStream st fstep fs extract
                  FL.Done fb -> FIterYield fb $ FIterInit st fb

    {-# INLINE [0] stepOuter #-}
    stepOuter _ (FIterInit st seed) = do
        (FL.Fold fstep initial extract) <- func seed
        iterStep initial st fstep extract
    stepOuter gst (FIterStream st fstep fs extract) = do
        r <- step (adaptState gst) st
        case r of
            Yield x s ->
                iterStep (fstep fs x) s fstep extract
            Skip s -> return $ Skip $ FIterStream s fstep fs extract
            Stop -> do
                b <- extract fs
                return $ Skip $ FIterYield b FIterStop
    stepOuter _ (FIterYield a next) = return $ Yield a next
    stepOuter _ FIterStop = return Stop

------------------------------------------------------------------------------
-- Parsing
------------------------------------------------------------------------------

{-# ANN type ParseChunksState Fuse #-}
data ParseChunksState x inpBuf st pst =
      ParseChunksInit inpBuf st
    | ParseChunksInitLeftOver inpBuf
    | ParseChunksStream st inpBuf !pst
    | ParseChunksBuf inpBuf st inpBuf !pst
    | ParseChunksYield x (ParseChunksState x inpBuf st pst)

{-# INLINE [1] parseMany #-}
parseMany
    :: MonadThrow m
    => PRD.Parser m a b
    -> Stream m a
    -> Stream m b
parseMany (PRD.Parser pstep initial extract) (Stream step state) =
    Stream stepOuter (ParseChunksInit [] state)

    where

    {-# INLINE [0] stepOuter #-}
    -- Buffer is empty, get the first element from the stream, initialize the
    -- fold and then go to stream processing loop.
    stepOuter gst (ParseChunksInit [] st) = do
        r <- step (adaptState gst) st
        case r of
            Yield x s -> do
                res <- initial
                case res of
                    PRD.IPartial ps ->
                        return $ Skip $ ParseChunksBuf [x] s [] ps
                    PRD.IDone pb ->
                        let next = ParseChunksInit [x] s
                         in return $ Skip $ ParseChunksYield pb next
                    PRD.IError err -> throwM $ ParseError err
            Skip s -> return $ Skip $ ParseChunksInit [] s
            Stop   -> return Stop

    -- Buffer is not empty, go to buffered processing loop
    stepOuter _ (ParseChunksInit src st) = do
        res <- initial
        case res of
            PRD.IPartial ps ->
                return $ Skip $ ParseChunksBuf src st [] ps
            PRD.IDone pb ->
                let next = ParseChunksInit src st
                 in return $ Skip $ ParseChunksYield pb next
            PRD.IError err -> throwM $ ParseError err

    -- XXX we just discard any leftover input at the end
    stepOuter _ (ParseChunksInitLeftOver _) = return Stop

    -- Buffer is empty, process elements from the stream
    stepOuter gst (ParseChunksStream st buf pst) = do
        r <- step (adaptState gst) st
        case r of
            Yield x s -> do
                pRes <- pstep pst x
                case pRes of
                    PR.Partial 0 pst1 ->
                        return $ Skip $ ParseChunksStream s [] pst1
                    PR.Partial n pst1 -> do
                        assert (n <= length (x:buf)) (return ())
                        let src0 = Prelude.take n (x:buf)
                            src  = Prelude.reverse src0
                        return $ Skip $ ParseChunksBuf src s [] pst1
                    PR.Continue 0 pst1 ->
                        return $ Skip $ ParseChunksStream s (x:buf) pst1
                    PR.Continue n pst1 -> do
                        assert (n <= length (x:buf)) (return ())
                        let (src0, buf1) = splitAt n (x:buf)
                            src  = Prelude.reverse src0
                        return $ Skip $ ParseChunksBuf src s buf1 pst1
                    PR.Done 0 b ->
                        return $ Skip $
                        ParseChunksYield b (ParseChunksInit [] s)
                    PR.Done n b -> do
                        assert (n <= length (x:buf)) (return ())
                        let src = Prelude.reverse (Prelude.take n (x:buf))
                        return $ Skip $
                            ParseChunksYield b (ParseChunksInit src s)
                    PR.Error err -> throwM $ ParseError err
            Skip s -> return $ Skip $ ParseChunksStream s buf pst
            Stop   -> do
                b <- extract pst
                let src = Prelude.reverse buf
                return $ Skip $
                    ParseChunksYield b (ParseChunksInitLeftOver src)

    -- go back to stream processing mode
    stepOuter _ (ParseChunksBuf [] s buf pst) =
        return $ Skip $ ParseChunksStream s buf pst

    -- buffered processing loop
    stepOuter _ (ParseChunksBuf (x:xs) s buf pst) = do
        pRes <- pstep pst x
        case pRes of
            PR.Partial 0 pst1 ->
                return $ Skip $ ParseChunksBuf xs s [] pst1
            PR.Partial n pst1 -> do
                assert (n <= length (x:buf)) (return ())
                let src0 = Prelude.take n (x:buf)
                    src  = Prelude.reverse src0 <> xs
                return $ Skip $ ParseChunksBuf src s [] pst1
            PR.Continue 0 pst1 ->
                return $ Skip $ ParseChunksBuf xs s (x:buf) pst1
            PR.Continue n pst1 -> do
                assert (n <= length (x:buf)) (return ())
                let (src0, buf1) = splitAt n (x:buf)
                    src  = Prelude.reverse src0 <> xs
                return $ Skip $ ParseChunksBuf src s buf1 pst1
            PR.Done 0 b ->
                return $ Skip $ ParseChunksYield b (ParseChunksInit xs s)
            PR.Done n b -> do
                assert (n <= length (x:buf)) (return ())
                let src = Prelude.reverse (Prelude.take n (x:buf)) <> xs
                return $ Skip $ ParseChunksYield b (ParseChunksInit src s)
            PR.Error err -> throwM $ ParseError err

    stepOuter _ (ParseChunksYield a next) = return $ Yield a next

{-# ANN type ConcatParseState Fuse #-}
data ConcatParseState b inpBuf st p m a =
      ConcatParseInit inpBuf st p
    | ConcatParseInitLeftOver inpBuf
    | forall s. ConcatParseStream st inpBuf (s -> a -> m (PRD.Step s b)) s (s -> m b)
    | forall s. ConcatParseBuf inpBuf st inpBuf (s -> a -> m (PRD.Step s b)) s (s -> m b)
    | ConcatParseYield b (ConcatParseState b inpBuf st p m a)

{-# INLINE [1] parseIterate #-}
parseIterate
    :: MonadThrow m
    => (b -> PRD.Parser m a b)
    -> b
    -> Stream m a
    -> Stream m b
parseIterate func seed (Stream step state) =
    Stream stepOuter (ConcatParseInit [] state (func seed))

    where

    {-# INLINE [0] stepOuter #-}
    -- Buffer is empty, go to stream processing loop
    stepOuter _ (ConcatParseInit [] st (PRD.Parser pstep initial extract)) = do
        res <- initial
        case res of
            PRD.IPartial ps ->
                return $ Skip $ ConcatParseStream st [] pstep ps extract
            PRD.IDone pb ->
                let next = ConcatParseInit [] st (func pb)
                 in return $ Skip $ ConcatParseYield pb next
            PRD.IError err -> throwM $ ParseError err

    -- Buffer is not empty, go to buffered processing loop
    stepOuter _ (ConcatParseInit src st
                    (PRD.Parser pstep initial extract)) = do
        res <- initial
        case res of
            PRD.IPartial ps ->
                return $ Skip $ ConcatParseBuf src st [] pstep ps extract
            PRD.IDone pb ->
                let next = ConcatParseInit src st (func pb)
                 in return $ Skip $ ConcatParseYield pb next
            PRD.IError err -> throwM $ ParseError err

    -- XXX we just discard any leftover input at the end
    stepOuter _ (ConcatParseInitLeftOver _) = return Stop

    -- Buffer is empty process elements from the stream
    stepOuter gst (ConcatParseStream st buf pstep pst extract) = do
        r <- step (adaptState gst) st
        case r of
            Yield x s -> do
                pRes <- pstep pst x
                case pRes of
                    PR.Partial 0 pst1 ->
                        return $ Skip $ ConcatParseStream s [] pstep pst1 extract
                    PR.Partial n pst1 -> do
                        assert (n <= length (x:buf)) (return ())
                        let src0 = Prelude.take n (x:buf)
                            src  = Prelude.reverse src0
                        return $ Skip $ ConcatParseBuf src s [] pstep pst1 extract
                    -- PR.Continue 0 pst1 ->
                    --     return $ Skip $ ConcatParseStream s (x:buf) pst1
                    PR.Continue n pst1 -> do
                        assert (n <= length (x:buf)) (return ())
                        let (src0, buf1) = splitAt n (x:buf)
                            src  = Prelude.reverse src0
                        return $ Skip $ ConcatParseBuf src s buf1 pstep pst1 extract
                    -- XXX Specialize for Stop 0 common case?
                    PR.Done n b -> do
                        assert (n <= length (x:buf)) (return ())
                        let src = Prelude.reverse (Prelude.take n (x:buf))
                        return $ Skip $
                            ConcatParseYield b (ConcatParseInit src s (func b))
                    PR.Error err -> throwM $ ParseError err
            Skip s -> return $ Skip $ ConcatParseStream s buf pstep pst extract
            Stop   -> do
                b <- extract pst
                let src = Prelude.reverse buf
                return $ Skip $ ConcatParseYield b (ConcatParseInitLeftOver src)

    -- go back to stream processing mode
    stepOuter _ (ConcatParseBuf [] s buf pstep ps extract) =
        return $ Skip $ ConcatParseStream s buf pstep ps extract

    -- buffered processing loop
    stepOuter _ (ConcatParseBuf (x:xs) s buf pstep pst extract) = do
        pRes <- pstep pst x
        case pRes of
            PR.Partial 0 pst1 ->
                return $ Skip $ ConcatParseBuf xs s [] pstep pst1 extract
            PR.Partial n pst1 -> do
                assert (n <= length (x:buf)) (return ())
                let src0 = Prelude.take n (x:buf)
                    src  = Prelude.reverse src0 <> xs
                return $ Skip $ ConcatParseBuf src s [] pstep pst1 extract
         -- PR.Continue 0 pst1 -> return $ Skip $ ConcatParseBuf xs s (x:buf) pst1
            PR.Continue n pst1 -> do
                assert (n <= length (x:buf)) (return ())
                let (src0, buf1) = splitAt n (x:buf)
                    src  = Prelude.reverse src0 <> xs
                return $ Skip $ ConcatParseBuf src s buf1 pstep pst1 extract
            -- XXX Specialize for Stop 0 common case?
            PR.Done n b -> do
                assert (n <= length (x:buf)) (return ())
                let src = Prelude.reverse (Prelude.take n (x:buf)) <> xs
                return $ Skip $ ConcatParseYield b
                                    (ConcatParseInit src s (func b))
            PR.Error err -> throwM $ ParseError err

    stepOuter _ (ConcatParseYield a next) = return $ Yield a next

------------------------------------------------------------------------------
-- Grouping
------------------------------------------------------------------------------

data GroupByState st fs a b
    = GroupingInit st
    | GroupingDo st !fs
    | GroupingInitWith st !a
    | GroupingDoWith st !fs !a
    | GroupingYield !b (GroupByState st fs a b)
    | GroupingDone

{-# INLINE [1] groupsBy #-}
groupsBy :: Monad m
    => (a -> a -> Bool)
    -> Fold m a b
    -> Stream m a
    -> Stream m b
{-
groupsBy eq fld = parseMany (PRD.groupBy eq fld)
-}
groupsBy cmp (Fold fstep initial done) (Stream step state) =
    Stream stepOuter (GroupingInit state)

    where

    {-# INLINE [0] stepOuter #-}
    stepOuter _ (GroupingInit st) = do
        -- XXX Note that if the stream stops without yielding a single element
        -- in the group we discard the "initial" effect.
        res <- initial
        return
            $ case res of
                  FL.Partial s -> Skip $ GroupingDo st s
                  FL.Done b -> Yield b $ GroupingInit st
    stepOuter gst (GroupingDo st fs) = do
        res <- step (adaptState gst) st
        case res of
            Yield x s -> do
                r <- fstep fs x
                case r of
                    FL.Partial fs1 -> go SPEC x s fs1
                    FL.Done b -> return $ Yield b (GroupingInit s)
            Skip s -> return $ Skip $ GroupingDo s fs
            Stop -> return Stop

        where

        go !_ prev stt !acc = do
            res <- step (adaptState gst) stt
            case res of
                Yield x s -> do
                    if cmp x prev
                    then do
                        r <- fstep acc x
                        case r of
                            FL.Partial fs1 -> go SPEC prev s fs1
                            FL.Done b -> return $ Yield b (GroupingInit s)
                    else do
                        r <- done acc
                        return $ Yield r (GroupingInitWith s x)
                Skip s -> go SPEC prev s acc
                Stop -> done acc >>= \r -> return $ Yield r GroupingDone
    stepOuter _ (GroupingInitWith st x) = do
        res <- initial
        return
            $ case res of
                  FL.Partial s -> Skip $ GroupingDoWith st s x
                  FL.Done b -> Yield b $ GroupingInitWith st x
    stepOuter gst (GroupingDoWith st fs prev) = do
        res <- fstep fs prev
        case res of
            FL.Partial fs1 -> go SPEC st fs1
            FL.Done b -> return $ Yield b (GroupingInit st)

        where

        -- XXX code duplicated from the previous equation
        go !_ stt !acc = do
            res <- step (adaptState gst) stt
            case res of
                Yield x s -> do
                    if cmp x prev
                    then do
                        r <- fstep acc x
                        case r of
                            FL.Partial fs1 -> go SPEC s fs1
                            FL.Done b -> return $ Yield b (GroupingInit s)
                    else do
                        r <- done acc
                        return $ Yield r (GroupingInitWith s x)
                Skip s -> go SPEC s acc
                Stop -> done acc >>= \r -> return $ Yield r GroupingDone
    stepOuter _ (GroupingYield _ _) = error "groupsBy: Unreachable"
    stepOuter _ GroupingDone = return Stop

{-# INLINE [1] groupsRollingBy #-}
groupsRollingBy :: Monad m
    => (a -> a -> Bool)
    -> Fold m a b
    -> Stream m a
    -> Stream m b
{-
groupsRollingBy eq fld = parseMany (PRD.groupByRolling eq fld)
-}
groupsRollingBy cmp (Fold fstep initial done) (Stream step state) =
    Stream stepOuter (GroupingInit state)

    where

    {-# INLINE [0] stepOuter #-}
    stepOuter _ (GroupingInit st) = do
        -- XXX Note that if the stream stops without yielding a single element
        -- in the group we discard the "initial" effect.
        res <- initial
        return
            $ case res of
                  FL.Partial fs -> Skip $ GroupingDo st fs
                  FL.Done fb -> Yield fb $ GroupingInit st
    stepOuter gst (GroupingDo st fs) = do
        res <- step (adaptState gst) st
        case res of
            Yield x s -> do
                r <- fstep fs x
                case r of
                    FL.Partial fs1 -> go SPEC x s fs1
                    FL.Done fb -> return $ Yield fb (GroupingInit s)
            Skip s -> return $ Skip $ GroupingDo s fs
            Stop -> return Stop

        where

        go !_ prev stt !acc = do
            res <- step (adaptState gst) stt
            case res of
                Yield x s -> do
                    if cmp prev x
                    then do
                        r <- fstep acc x
                        case r of
                            FL.Partial fs1 -> go SPEC x s fs1
                            FL.Done b -> return $ Yield b (GroupingInit s)
                    else do
                        r <- done acc
                        return $ Yield r (GroupingInitWith s x)
                Skip s -> go SPEC prev s acc
                Stop -> done acc >>= \r -> return $ Yield r GroupingDone
    stepOuter _ (GroupingInitWith st x) = do
        res <- initial
        return
            $ case res of
                  FL.Partial s -> Skip $ GroupingDoWith st s x
                  FL.Done b -> Yield b $ GroupingInitWith st x
    stepOuter gst (GroupingDoWith st fs previous) = do
        res <- fstep fs previous
        case res of
            FL.Partial s -> go SPEC previous st s
            FL.Done b -> return $ Yield b (GroupingInit st)

        where

        -- XXX GHC: groupsBy has one less parameter in this go loop and it
        -- fuses. However, groupsRollingBy does not fuse, removing the prev
        -- parameter makes it fuse. Something needs to be fixed in GHC. The
        -- workaround for this is noted in the comments below.
        go !_ prev !stt !acc = do
            res <- step (adaptState gst) stt
            case res of
                Yield x s -> do
                    if cmp prev x
                    then do
                        r <- fstep acc x
                        case r of
                            FL.Partial fs1 -> go SPEC x s fs1
                            FL.Done b -> return $ Yield b (GroupingInit st)
                    else do
                        {-
                        r <- done acc
                        return $ Yield r (GroupingInitWith s x)
                        -}
                        -- The code above does not let groupBy fuse. We use the
                        -- alternative code below instead.  Instead of jumping
                        -- to GroupingInitWith state, we unroll the code of
                        -- GroupingInitWith state here to help GHC with stream
                        -- fusion.
                        result <- initial
                        r <- done acc
                        return
                            $ Yield r
                            $ case result of
                                  FL.Partial fsi -> GroupingDoWith s fsi x
                                  FL.Done b -> GroupingYield b (GroupingInit s)
                Skip s -> go SPEC prev s acc
                Stop -> done acc >>= \r -> return $ Yield r GroupingDone
    stepOuter _ (GroupingYield r next) = return $ Yield r next
    stepOuter _ GroupingDone = return Stop

------------------------------------------------------------------------------
-- Splitting - by a predicate
------------------------------------------------------------------------------

data WordsByState st fs b
    = WordsByInit st
    | WordsByDo st !fs
    | WordsByDone
    | WordsByYield !b (WordsByState st fs b)

{-# INLINE [1] wordsBy #-}
wordsBy :: Monad m => (a -> Bool) -> Fold m a b -> Stream m a -> Stream m b
wordsBy predicate (Fold fstep initial done) (Stream step state) =
    Stream stepOuter (WordsByInit state)

    where

    {-# INLINE [0] stepOuter #-}
    stepOuter _ (WordsByInit st) = do
        res <- initial
        return
            $ case res of
                  FL.Partial s -> Skip $ WordsByDo st s
                  FL.Done b -> Yield b (WordsByInit st)

    stepOuter gst (WordsByDo st fs) = do
        res <- step (adaptState gst) st
        case res of
            Yield x s -> do
                if predicate x
                then do
                    resi <- initial
                    return
                        $ case resi of
                              FL.Partial fs1 -> Skip $ WordsByDo s fs1
                              FL.Done b -> Yield b (WordsByInit s)
                else do
                    r <- fstep fs x
                    case r of
                        FL.Partial fs1 -> go SPEC s fs1
                        FL.Done b -> return $ Yield b (WordsByInit s)
            Skip s    -> return $ Skip $ WordsByDo s fs
            Stop      -> return Stop

        where

        go !_ stt !acc = do
            res <- step (adaptState gst) stt
            case res of
                Yield x s -> do
                    if predicate x
                    then do
                        {-
                        r <- done acc
                        return $ Yield r (WordsByInit s)
                        -}
                        -- The above code does not fuse well. Need to check why
                        -- GHC is not able to simplify it well.  Using the code
                        -- below, instead of jumping through the WordsByInit
                        -- state always, we directly go to WordsByDo state in
                        -- the common case of Partial.
                        resi <- initial
                        r <- done acc
                        return
                            $ Yield r
                            $ case resi of
                                  FL.Partial fs1 -> WordsByDo s fs1
                                  FL.Done b -> WordsByYield b (WordsByInit s)
                    else do
                        r <- fstep acc x
                        case r of
                            FL.Partial fs1 -> go SPEC s fs1
                            FL.Done b -> return $ Yield b (WordsByInit s)
                Skip s -> go SPEC s acc
                Stop -> done acc >>= \r -> return $ Yield r WordsByDone

    stepOuter _ WordsByDone = return Stop

    stepOuter _ (WordsByYield b next) = return $ Yield b next

------------------------------------------------------------------------------
-- Splitting on a sequence
------------------------------------------------------------------------------

-- String search algorithms:
-- http://www-igm.univ-mlv.fr/~lecroq/string/index.html

{-
-- TODO can we unify the splitting operations using a splitting configuration
-- like in the split package.
--
data SplitStyle = Infix | Suffix | Prefix deriving (Eq, Show)
data SplitOptions = SplitOptions
    { style    :: SplitStyle
    , withSep  :: Bool  -- ^ keep the separators in output
    -- , compact  :: Bool  -- ^ treat multiple consecutive separators as one
    -- , trimHead :: Bool  -- ^ drop blank at head
    -- , trimTail :: Bool  -- ^ drop blank at tail
    }
-}

-- XXX using "fs" as the last arg in Constructors may simplify the code a bit,
-- because we can use the constructor directly without having to create "jump"
-- functions.
{-# ANN type SplitOnSeqState Fuse #-}
data SplitOnSeqState rb rh ck w fs s b x =
      SplitOnSeqInit
    | SplitOnSeqYield b (SplitOnSeqState rb rh ck w fs s b x)
    | SplitOnSeqDone

    | SplitOnSeqEmpty !fs s

    | SplitOnSeqSingle !fs s x

    | SplitOnSeqWordInit !fs s
    | SplitOnSeqWordLoop !w s !fs
    | SplitOnSeqWordDone Int !fs !w

    | SplitOnSeqKRInit Int !fs s rb !rh
    | SplitOnSeqKRLoop fs s rb !rh !ck
    | SplitOnSeqKRCheck fs s rb !rh
    | SplitOnSeqKRDone Int !fs rb !rh

    | SplitOnSeqReinit (fs -> SplitOnSeqState rb rh ck w fs s b x)

{-# INLINE [1] splitOnSeq #-}
splitOnSeq
    :: forall m a b. (MonadIO m, Storable a, Enum a, Eq a)
    => Array a
    -> Fold m a b
    -> Stream m a
    -> Stream m b
splitOnSeq patArr (Fold fstep initial done) (Stream step state) =
    Stream stepOuter SplitOnSeqInit

    where

    patLen = A.length patArr
    maxIndex = patLen - 1
    elemBits = sizeOf (undefined :: a) * 8

    -- For word pattern case
    wordMask :: Word
    wordMask = 1 `shiftL` (elemBits * patLen) - 1

    elemMask :: Word
    elemMask = 1 `shiftL` elemBits - 1

    wordPat :: Word
    wordPat = wordMask .&. A.foldl' addToWord 0 patArr

    addToWord wd a = wd `shiftL` elemBits .|. fromIntegral (fromEnum a)

    -- For Rabin-Karp search
    k = 2891336453 :: Word32
    coeff = k ^ patLen

    addCksum cksum a = cksum * k + fromIntegral (fromEnum a)

    deltaCksum cksum old new =
        addCksum cksum new - coeff * fromIntegral (fromEnum old)

    -- XXX shall we use a random starting hash or 1 instead of 0?
    patHash = A.foldl' addCksum 0 patArr

    skip = return . Skip

    nextAfterInit nextGen stepRes =
        case stepRes of
            FL.Partial s -> nextGen s
            FL.Done b -> SplitOnSeqYield b (SplitOnSeqReinit nextGen)

    {-# INLINE yieldProceed #-}
    yieldProceed nextGen fs =
        initial >>= skip . SplitOnSeqYield fs . nextAfterInit nextGen

    {-# INLINE [0] stepOuter #-}
    stepOuter _ SplitOnSeqInit = do
        res <- initial
        case res of
            FL.Partial acc ->
                if patLen == 0
                then return $ Skip $ SplitOnSeqEmpty acc state
                else if patLen == 1
                     then do
                         pat <- liftIO $ A.unsafeIndexIO patArr 0
                         return $ Skip $ SplitOnSeqSingle acc state pat
                     else if sizeOf (undefined :: a) * patLen
                               <= sizeOf (undefined :: Word)
                          then return $ Skip $ SplitOnSeqWordInit acc state
                          else do
                              (rb, rhead) <- liftIO $ RB.new patLen
                              skip $ SplitOnSeqKRInit 0 acc state rb rhead
            FL.Done b -> skip $ SplitOnSeqYield b SplitOnSeqInit

    stepOuter _ (SplitOnSeqYield x next) = return $ Yield x next

    ---------------------------
    -- Checkpoint
    ---------------------------

    stepOuter _ (SplitOnSeqReinit nextGen) =
        initial >>= skip . nextAfterInit nextGen

    ---------------------------
    -- Empty pattern
    ---------------------------

    stepOuter gst (SplitOnSeqEmpty acc st) = do
        res <- step (adaptState gst) st
        case res of
            Yield x s -> do
                r <- fstep acc x
                b1 <-
                    case r of
                        FL.Partial acc1 -> done acc1
                        FL.Done b -> return b
                let jump c = SplitOnSeqEmpty c s
                 in yieldProceed jump b1
            Skip s -> skip (SplitOnSeqEmpty acc s)
            Stop -> return Stop

    -----------------
    -- Done
    -----------------

    stepOuter _ SplitOnSeqDone = return Stop

    -----------------
    -- Single Pattern
    -----------------

    stepOuter gst (SplitOnSeqSingle fs st pat) = do
        res <- step (adaptState gst) st
        case res of
            Yield x s -> do
                let jump c = SplitOnSeqSingle c s pat
                if pat == x
                then done fs >>= yieldProceed jump
                else do
                    r <- fstep fs x
                    case r of
                        FL.Partial fs1 -> skip $ jump fs1
                        FL.Done b -> yieldProceed jump b
            Skip s -> return $ Skip $ SplitOnSeqSingle fs s pat
            Stop -> do
                r <- done fs
                return $ Skip $ SplitOnSeqYield r SplitOnSeqDone

    ---------------------------
    -- Short Pattern - Shift Or
    ---------------------------

    stepOuter _ (SplitOnSeqWordDone 0 fs _) = do
        r <- done fs
        skip $ SplitOnSeqYield r SplitOnSeqDone
    stepOuter _ (SplitOnSeqWordDone n fs wrd) = do
        let old = elemMask .&. wrd `shiftR` (elemBits * (n - 1))
        r <- fstep fs (toEnum $ fromIntegral old)
        case r of
            FL.Partial fs1 -> skip $ SplitOnSeqWordDone (n - 1) fs1 wrd
            FL.Done b -> do
                 let jump c = SplitOnSeqWordDone (n - 1) c wrd
                 yieldProceed jump b

    stepOuter gst (SplitOnSeqWordInit fs st0) =
        go SPEC 0 0 st0

        where

        {-# INLINE go #-}
        go !_ !idx !wrd !st = do
            res <- step (adaptState gst) st
            case res of
                Yield x s -> do
                    let wrd1 = addToWord wrd x
                    if idx == maxIndex
                    then do
                        if wrd1 .&. wordMask == wordPat
                        then do
                            let jump c = SplitOnSeqWordInit c s
                            done fs >>= yieldProceed jump
                        else skip $ SplitOnSeqWordLoop wrd1 s fs
                    else go SPEC (idx + 1) wrd1 s
                Skip s -> go SPEC idx wrd s
                Stop -> do
                    if idx /= 0
                    then skip $ SplitOnSeqWordDone idx fs wrd
                    else do
                        r <- done fs
                        skip $ SplitOnSeqYield r SplitOnSeqDone

    stepOuter gst (SplitOnSeqWordLoop wrd0 st0 fs0) =
        go SPEC wrd0 st0 fs0

        where

        {-# INLINE go #-}
        go !_ !wrd !st !fs = do
            res <- step (adaptState gst) st
            case res of
                Yield x s -> do
                    let jump c = SplitOnSeqWordInit c s
                        wrd1 = addToWord wrd x
                        old = (wordMask .&. wrd)
                                `shiftR` (elemBits * (patLen - 1))
                    r <- fstep fs (toEnum $ fromIntegral old)
                    case r of
                        FL.Partial fs1 -> do
                            if wrd1 .&. wordMask == wordPat
                            then done fs1 >>= yieldProceed jump
                            else go SPEC wrd1 s fs1
                        FL.Done b -> yieldProceed jump b
                Skip s -> go SPEC wrd s fs
                Stop -> skip $ SplitOnSeqWordDone patLen fs wrd

    -------------------------------
    -- General Pattern - Karp Rabin
    -------------------------------

    stepOuter gst (SplitOnSeqKRInit idx fs st rb rh) = do
        res <- step (adaptState gst) st
        case res of
            Yield x s -> do
                rh1 <- liftIO $ RB.unsafeInsert rb rh x
                if idx == maxIndex
                then do
                    let fld = RB.unsafeFoldRing (RB.ringBound rb)
                    let !ringHash = fld addCksum 0 rb
                    if ringHash == patHash
                    then skip $ SplitOnSeqKRCheck fs s rb rh1
                    else skip $ SplitOnSeqKRLoop fs s rb rh1 ringHash
                else skip $ SplitOnSeqKRInit (idx + 1) fs s rb rh1
            Skip s -> skip $ SplitOnSeqKRInit idx fs s rb rh
            Stop ->
                skip $ SplitOnSeqKRDone idx fs rb (RB.startOf rb)

    -- XXX The recursive "go" is more efficient than the state based recursion
    -- code commented out below. Perhaps its more efficient because of
    -- factoring out "rb" outside the loop.
    --
    stepOuter gst (SplitOnSeqKRLoop fs0 st0 rb rh0 cksum0) =
        go SPEC fs0 st0 rh0 cksum0

        where

        go !_ !fs !st !rh !cksum = do
            res <- step (adaptState gst) st
            case res of
                Yield x s -> do
                    old <- liftIO $ peek rh
                    let cksum1 = deltaCksum cksum old x
                    r <- fstep fs old
                    case r of
                        FL.Partial fs1 -> do
                            rh1 <- liftIO (RB.unsafeInsert rb rh x)
                            if cksum1 == patHash
                            then skip $ SplitOnSeqKRCheck fs1 s rb rh1
                            else go SPEC fs1 s rh1 cksum1
                        FL.Done b -> do
                            let rst = RB.startOf rb
                                jump c = SplitOnSeqKRInit 0 c s rb rst
                            yieldProceed jump b
                Skip s -> go SPEC fs s rh cksum
                Stop -> skip $ SplitOnSeqKRDone patLen fs rb rh

    -- XXX The following code is 5 times slower compared to the recursive loop
    -- based code above. Need to investigate why. One possibility is that the
    -- go loop above does not thread around the ring buffer (rb). This code may
    -- be causing the state to bloat and getting allocated on each iteration.
    -- We can check the cmm/asm code to confirm.  If so a good GHC solution to
    -- such problem is needed. One way to avoid this could be to use unboxed
    -- mutable state?
    {-
    stepOuter gst (SplitOnSeqKRLoop fs st rb rh cksum) = do
            res <- step (adaptState gst) st
            case res of
                Yield x s -> do
                    old <- liftIO $ peek rh
                    let cksum1 = deltaCksum cksum old x
                    fs1 <- fstep fs old
                    if (cksum1 == patHash)
                    then do
                        r <- done fs1
                        skip $ SplitOnSeqYield r $ SplitOnSeqKRInit 0 s rb rh
                    else do
                        rh1 <- liftIO (RB.unsafeInsert rb rh x)
                        skip $ SplitOnSeqKRLoop fs1 s rb rh1 cksum1
                Skip s -> skip $ SplitOnSeqKRLoop fs s rb rh cksum
                Stop -> skip $ SplitOnSeqKRDone patLen fs rb rh
    -}

    stepOuter _ (SplitOnSeqKRCheck fs st rb rh) =
        if RB.unsafeEqArray rb rh patArr
        then do
            r <- done fs
            let rst = RB.startOf rb
                jump c = SplitOnSeqKRInit 0 c st rb rst
            yieldProceed jump r
        else skip $ SplitOnSeqKRLoop fs st rb rh patHash

    stepOuter _ (SplitOnSeqKRDone 0 fs _ _) = do
        r <- done fs
        skip $ SplitOnSeqYield r SplitOnSeqDone
    stepOuter _ (SplitOnSeqKRDone n fs rb rh) = do
        old <- liftIO $ peek rh
        let rh1 = RB.advance rb rh
        r <- fstep fs old
        case r of
            FL.Partial fs1 -> skip $ SplitOnSeqKRDone (n - 1) fs1 rb rh1
            FL.Done b -> do
                 let jump c = SplitOnSeqKRDone (n - 1) c rb rh1
                 yieldProceed jump b

{-# ANN type SplitOnSuffixSeqState Fuse #-}
data SplitOnSuffixSeqState rb rh ck w fs s b x =
      SplitOnSuffixSeqInit
    | SplitOnSuffixSeqYield b (SplitOnSuffixSeqState rb rh ck w fs s b x)
    | SplitOnSuffixSeqDone

    | SplitOnSuffixSeqEmpty !fs s

    | SplitOnSuffixSeqSingleInit !fs s x
    | SplitOnSuffixSeqSingle !fs s x

    | SplitOnSuffixSeqWordInit !fs s
    | SplitOnSuffixSeqWordLoop !w s !fs
    | SplitOnSuffixSeqWordDone Int !fs !w

    | SplitOnSuffixSeqKRInit Int !fs s rb !rh
    | SplitOnSuffixSeqKRInit1 !fs s rb !rh
    | SplitOnSuffixSeqKRLoop fs s rb !rh !ck
    | SplitOnSuffixSeqKRCheck fs s rb !rh
    | SplitOnSuffixSeqKRDone Int !fs rb !rh

    | SplitOnSuffixSeqReinit
          (fs -> SplitOnSuffixSeqState rb rh ck w fs s b x)

{-# INLINE [1] splitOnSuffixSeq #-}
splitOnSuffixSeq
    :: forall m a b. (MonadIO m, Storable a, Enum a, Eq a)
    => Bool
    -> Array a
    -> Fold m a b
    -> Stream m a
    -> Stream m b
splitOnSuffixSeq withSep patArr (Fold fstep initial done) (Stream step state) =
    Stream stepOuter SplitOnSuffixSeqInit

    where

    patLen = A.length patArr
    maxIndex = patLen - 1
    elemBits = sizeOf (undefined :: a) * 8

    -- For word pattern case
    wordMask :: Word
    wordMask = 1 `shiftL` (elemBits * patLen) - 1

    elemMask :: Word
    elemMask = 1 `shiftL` elemBits - 1

    wordPat :: Word
    wordPat = wordMask .&. A.foldl' addToWord 0 patArr

    addToWord wd a = wd `shiftL` elemBits .|. fromIntegral (fromEnum a)

    nextAfterInit nextGen stepRes =
        case stepRes of
            FL.Partial s -> nextGen s
            FL.Done b ->
                SplitOnSuffixSeqYield b (SplitOnSuffixSeqReinit nextGen)

    {-# INLINE yieldProceed #-}
    yieldProceed nextGen fs =
        initial >>= skip . SplitOnSuffixSeqYield fs . nextAfterInit nextGen

    -- For single element pattern case
    {-# INLINE processYieldSingle #-}
    processYieldSingle pat x s fs = do
        let jump c = SplitOnSuffixSeqSingleInit c s pat
        if pat == x
        then do
            r <- if withSep then fstep fs x else return $ FL.Partial fs
            b1 <-
                case r of
                    FL.Partial fs1 -> done fs1
                    FL.Done b -> return b
            yieldProceed jump b1
        else do
            r <- fstep fs x
            case r of
                FL.Partial fs1 -> skip $ SplitOnSuffixSeqSingle fs1 s pat
                FL.Done b -> yieldProceed jump b

    -- For Rabin-Karp search
    k = 2891336453 :: Word32
    coeff = k ^ patLen

    addCksum cksum a = cksum * k + fromIntegral (fromEnum a)

    deltaCksum cksum old new =
        addCksum cksum new - coeff * fromIntegral (fromEnum old)

    -- XXX shall we use a random starting hash or 1 instead of 0?
    patHash = A.foldl' addCksum 0 patArr

    skip = return . Skip

    {-# INLINE [0] stepOuter #-}
    stepOuter _ SplitOnSuffixSeqInit = do
        res <- initial
        case res of
            FL.Partial fs ->
                if patLen == 0
                then skip $ SplitOnSuffixSeqEmpty fs state
                else if patLen == 1
                     then do
                         pat <- liftIO $ A.unsafeIndexIO patArr 0
                         skip $ SplitOnSuffixSeqSingleInit fs state pat
                     else if sizeOf (undefined :: a) * patLen
                               <= sizeOf (undefined :: Word)
                          then skip $ SplitOnSuffixSeqWordInit fs state
                          else do
                              (rb, rhead) <- liftIO $ RB.new patLen
                              skip $ SplitOnSuffixSeqKRInit 0 fs state rb rhead
            FL.Done fb -> skip $ SplitOnSuffixSeqYield fb SplitOnSuffixSeqInit

    stepOuter _ (SplitOnSuffixSeqYield x next) = return $ Yield x next

    ---------------------------
    -- Reinit
    ---------------------------

    stepOuter _ (SplitOnSuffixSeqReinit nextGen) =
        initial >>= skip . nextAfterInit nextGen

    ---------------------------
    -- Empty pattern
    ---------------------------

    stepOuter gst (SplitOnSuffixSeqEmpty acc st) = do
        res <- step (adaptState gst) st
        case res of
            Yield x s -> do
                let jump c = SplitOnSuffixSeqEmpty c s
                r <- fstep acc x
                b1 <-
                    case r of
                        FL.Partial fs -> done fs
                        FL.Done b -> return b
                yieldProceed jump b1
            Skip s -> skip (SplitOnSuffixSeqEmpty acc s)
            Stop -> return Stop

    -----------------
    -- Done
    -----------------

    stepOuter _ SplitOnSuffixSeqDone = return Stop

    -----------------
    -- Single Pattern
    -----------------

    stepOuter gst (SplitOnSuffixSeqSingleInit fs st pat) = do
        res <- step (adaptState gst) st
        case res of
            Yield x s -> processYieldSingle pat x s fs
            Skip s -> skip $ SplitOnSuffixSeqSingleInit fs s pat
            Stop -> return Stop

    stepOuter gst (SplitOnSuffixSeqSingle fs st pat) = do
        res <- step (adaptState gst) st
        case res of
            Yield x s -> processYieldSingle pat x s fs
            Skip s -> skip $ SplitOnSuffixSeqSingle fs s pat
            Stop -> do
                r <- done fs
                skip $ SplitOnSuffixSeqYield r SplitOnSuffixSeqDone

    ---------------------------
    -- Short Pattern - Shift Or
    ---------------------------

    stepOuter _ (SplitOnSuffixSeqWordDone 0 fs _) = do
        r <- done fs
        skip $ SplitOnSuffixSeqYield r SplitOnSuffixSeqDone
    stepOuter _ (SplitOnSuffixSeqWordDone n fs wrd) = do
        let old = elemMask .&. wrd `shiftR` (elemBits * (n - 1))
        r <- fstep fs (toEnum $ fromIntegral old)
        case r of
            FL.Partial fs1 -> skip $ SplitOnSuffixSeqWordDone (n - 1) fs1 wrd
            FL.Done b -> do
                let jump c = SplitOnSuffixSeqWordDone (n - 1) c wrd
                yieldProceed jump b

    stepOuter gst (SplitOnSuffixSeqWordInit fs0 st0) = do
        res <- step (adaptState gst) st0
        case res of
            Yield x s -> do
                let wrd = addToWord 0 x
                r <- if withSep then fstep fs0 x else return $ FL.Partial fs0
                case r of
                    FL.Partial fs1 -> go SPEC 1 wrd s fs1
                    FL.Done b -> do
                        let jump c = SplitOnSuffixSeqWordInit c s
                        yieldProceed jump b
            Skip s -> skip (SplitOnSuffixSeqWordInit fs0 s)
            Stop -> return Stop

        where

        {-# INLINE go #-}
        go !_ !idx !wrd !st !fs = do
            res <- step (adaptState gst) st
            case res of
                Yield x s -> do
                    let jump c = SplitOnSuffixSeqWordInit c s
                    let wrd1 = addToWord wrd x
                    r <- if withSep then fstep fs x else return $ FL.Partial fs
                    case r of
                        FL.Partial fs1 ->
                            if idx /= maxIndex
                            then go SPEC (idx + 1) wrd1 s fs1
                            else if wrd1 .&. wordMask /= wordPat
                            then skip $ SplitOnSuffixSeqWordLoop wrd1 s fs1
                            else done fs >>= yieldProceed jump
                        FL.Done b -> yieldProceed jump b
                Skip s -> go SPEC idx wrd s fs
                Stop -> skip $ SplitOnSuffixSeqWordDone idx fs wrd

    stepOuter gst (SplitOnSuffixSeqWordLoop wrd0 st0 fs0) =
        go SPEC wrd0 st0 fs0

        where

        {-# INLINE go #-}
        go !_ !wrd !st !fs = do
            res <- step (adaptState gst) st
            case res of
                Yield x s -> do
                    let jump c = SplitOnSuffixSeqWordInit c s
                        wrd1 = addToWord wrd x
                        old = (wordMask .&. wrd)
                                `shiftR` (elemBits * (patLen - 1))
                    r <-
                        if withSep
                        then fstep fs x
                        else fstep fs (toEnum $ fromIntegral old)
                    case r of
                        FL.Partial fs1 ->
                            if wrd1 .&. wordMask == wordPat
                            then done fs1 >>= yieldProceed jump
                            else go SPEC wrd1 s fs1
                        FL.Done b -> yieldProceed jump b
                Skip s -> go SPEC wrd s fs
                Stop ->
                    if wrd .&. wordMask == wordPat
                    then return Stop
                    else if withSep
                    then do
                        r <- done fs
                        skip $ SplitOnSuffixSeqYield r SplitOnSuffixSeqDone
                    else skip $ SplitOnSuffixSeqWordDone patLen fs wrd

    -------------------------------
    -- General Pattern - Karp Rabin
    -------------------------------

    stepOuter gst (SplitOnSuffixSeqKRInit idx0 fs st0 rb rh0) = do
        res <- step (adaptState gst) st0
        case res of
            Yield x s -> do
                rh1 <- liftIO $ RB.unsafeInsert rb rh0 x
                r <- if withSep then fstep fs x else return $ FL.Partial fs
                case r of
                    FL.Partial fs1 ->
                        skip $ SplitOnSuffixSeqKRInit1 fs1 s rb rh1
                    FL.Done b -> do
                        let rst = RB.startOf rb
                            jump c = SplitOnSuffixSeqKRInit 0 c s rb rst
                        yieldProceed jump b
            Skip s -> skip $ SplitOnSuffixSeqKRInit idx0 fs s rb rh0
            Stop -> return Stop

    stepOuter gst (SplitOnSuffixSeqKRInit1 fs0 st0 rb rh0) =
        go SPEC 1 rh0 st0 fs0

        where

        go !_ !idx !rh st !fs = do
            res <- step (adaptState gst) st
            case res of
                Yield x s -> do
                    rh1 <- liftIO (RB.unsafeInsert rb rh x)
                    r <- if withSep then fstep fs x else return $ FL.Partial fs
                    case r of
                        FL.Partial fs1 ->
                            if idx /= maxIndex
                            then go SPEC (idx + 1) rh1 s fs1
                            else skip $
                                let fld = RB.unsafeFoldRing (RB.ringBound rb)
                                    !ringHash = fld addCksum 0 rb
                                 in if ringHash == patHash
                                    then SplitOnSuffixSeqKRCheck fs1 s rb rh1
                                    else SplitOnSuffixSeqKRLoop
                                            fs1 s rb rh1 ringHash
                        FL.Done b -> do
                            let rst = RB.startOf rb
                                jump c = SplitOnSuffixSeqKRInit 0 c s rb rst
                            yieldProceed jump b
                Skip s -> go SPEC idx rh s fs
                Stop -> do
                    -- do not issue a blank segment when we end at pattern
                    if idx == maxIndex && RB.unsafeEqArray rb rh patArr
                    then return Stop
                    else if withSep
                    then do
                        r <- done fs
                        skip $ SplitOnSuffixSeqYield r SplitOnSuffixSeqDone
                    else skip $ SplitOnSuffixSeqKRDone idx fs rb (RB.startOf rb)

    stepOuter gst (SplitOnSuffixSeqKRLoop fs0 st0 rb rh0 cksum0) =
        go SPEC fs0 st0 rh0 cksum0

        where

        go !_ !fs !st !rh !cksum = do
            res <- step (adaptState gst) st
            case res of
                Yield x s -> do
                    old <- liftIO $ peek rh
                    rh1 <- liftIO (RB.unsafeInsert rb rh x)
                    let cksum1 = deltaCksum cksum old x
                    r <- if withSep then fstep fs x else fstep fs old
                    case r of
                        FL.Partial fs1 ->
                            if cksum1 /= patHash
                            then go SPEC fs1 s rh1 cksum1
                            else skip $ SplitOnSuffixSeqKRCheck fs1 s rb rh1
                        FL.Done b -> do
                            let rst = RB.startOf rb
                                jump c = SplitOnSuffixSeqKRInit 0 c s rb rst
                            yieldProceed jump b
                Skip s -> go SPEC fs s rh cksum
                Stop ->
                    if RB.unsafeEqArray rb rh patArr
                    then return Stop
                    else if withSep
                    then do
                        r <- done fs
                        skip $ SplitOnSuffixSeqYield r SplitOnSuffixSeqDone
                    else skip $ SplitOnSuffixSeqKRDone patLen fs rb rh

    stepOuter _ (SplitOnSuffixSeqKRCheck fs st rb rh) =
        if RB.unsafeEqArray rb rh patArr
        then do
            r <- done fs
            let rst = RB.startOf rb
                jump c = SplitOnSuffixSeqKRInit 0 c st rb rst
            yieldProceed jump r
        else skip $ SplitOnSuffixSeqKRLoop fs st rb rh patHash

    stepOuter _ (SplitOnSuffixSeqKRDone 0 fs _ _) = do
        r <- done fs
        skip $ SplitOnSuffixSeqYield r SplitOnSuffixSeqDone
    stepOuter _ (SplitOnSuffixSeqKRDone n fs rb rh) = do
        old <- liftIO $ peek rh
        let rh1 = RB.advance rb rh
        r <- fstep fs old
        case r of
            FL.Partial fs1 -> skip $ SplitOnSuffixSeqKRDone (n - 1) fs1 rb rh1
            FL.Done b -> do
                let jump c = SplitOnSuffixSeqKRDone (n - 1) c rb rh1
                yieldProceed jump b

------------------------------------------------------------------------------
-- Nested Container Transformation
------------------------------------------------------------------------------

{-# ANN type SplitState Fuse #-}
data SplitState s arr
    = SplitInitial s
    | SplitBuffering s arr
    | SplitSplitting s arr
    | SplitYielding arr (SplitState s arr)
    | SplitFinishing

-- XXX An alternative approach would be to use a partial fold (Fold m a b) to
-- split using a splitBy like combinator. The Fold would consume upto the
-- separator and return any leftover which can then be fed to the next fold.
--
-- We can revisit this once we have partial folds/parsers.
--
-- | Performs infix separator style splitting.
{-# INLINE [1] splitInnerBy #-}
splitInnerBy
    :: Monad m
    => (f a -> m (f a, Maybe (f a)))  -- splitter
    -> (f a -> f a -> m (f a))        -- joiner
    -> Stream m (f a)
    -> Stream m (f a)
splitInnerBy splitter joiner (Stream step1 state1) =
    Stream step (SplitInitial state1)

    where

    {-# INLINE [0] step #-}
    step gst (SplitInitial st) = do
        r <- step1 gst st
        case r of
            Yield x s -> do
                (x1, mx2) <- splitter x
                return $ case mx2 of
                    Nothing -> Skip (SplitBuffering s x1)
                    Just x2 -> Skip (SplitYielding x1 (SplitSplitting s x2))
            Skip s -> return $ Skip (SplitInitial s)
            Stop -> return Stop

    step gst (SplitBuffering st buf) = do
        r <- step1 gst st
        case r of
            Yield x s -> do
                (x1, mx2) <- splitter x
                buf' <- joiner buf x1
                return $ case mx2 of
                    Nothing -> Skip (SplitBuffering s buf')
                    Just x2 -> Skip (SplitYielding buf' (SplitSplitting s x2))
            Skip s -> return $ Skip (SplitBuffering s buf)
            Stop -> return $ Skip (SplitYielding buf SplitFinishing)

    step _ (SplitSplitting st buf) = do
        (x1, mx2) <- splitter buf
        return $ case mx2 of
                Nothing -> Skip $ SplitBuffering st x1
                Just x2 -> Skip $ SplitYielding x1 (SplitSplitting st x2)

    step _ (SplitYielding x next) = return $ Yield x next
    step _ SplitFinishing = return Stop

-- | Performs infix separator style splitting.
{-# INLINE [1] splitInnerBySuffix #-}
splitInnerBySuffix
    :: (Monad m, Eq (f a), Monoid (f a))
    => (f a -> m (f a, Maybe (f a)))  -- splitter
    -> (f a -> f a -> m (f a))        -- joiner
    -> Stream m (f a)
    -> Stream m (f a)
splitInnerBySuffix splitter joiner (Stream step1 state1) =
    Stream step (SplitInitial state1)

    where

    {-# INLINE [0] step #-}
    step gst (SplitInitial st) = do
        r <- step1 gst st
        case r of
            Yield x s -> do
                (x1, mx2) <- splitter x
                return $ case mx2 of
                    Nothing -> Skip (SplitBuffering s x1)
                    Just x2 -> Skip (SplitYielding x1 (SplitSplitting s x2))
            Skip s -> return $ Skip (SplitInitial s)
            Stop -> return Stop

    step gst (SplitBuffering st buf) = do
        r <- step1 gst st
        case r of
            Yield x s -> do
                (x1, mx2) <- splitter x
                buf' <- joiner buf x1
                return $ case mx2 of
                    Nothing -> Skip (SplitBuffering s buf')
                    Just x2 -> Skip (SplitYielding buf' (SplitSplitting s x2))
            Skip s -> return $ Skip (SplitBuffering s buf)
            Stop -> return $
                if buf == mempty
                then Stop
                else Skip (SplitYielding buf SplitFinishing)

    step _ (SplitSplitting st buf) = do
        (x1, mx2) <- splitter buf
        return $ case mx2 of
                Nothing -> Skip $ SplitBuffering st x1
                Just x2 -> Skip $ SplitYielding x1 (SplitSplitting st x2)

    step _ (SplitYielding x next) = return $ Yield x next
    step _ SplitFinishing = return Stop
{-
{-# INLINE joinOuterMerge #-}
joinOuterMerge
    :: (MonadIO m,  Eq a, Eq b)
    => (a -> b -> Ordering)
    -> Stream m a
    -> Stream m b
    -> Stream m (Maybe a, Maybe b)
joinOuterMerge cmp = mergeOuterJoinM (\a b -> return $ cmp a b)
-}

{-# INLINE [1] joinOuterMerge #-}
joinOuterMerge
    :: (MonadIO m,  Eq a, Eq b)
    => (a -> b -> Ordering)
    -> Stream m a
    -> Stream m b
    -> Stream m (Maybe a, Maybe b)
joinOuterMerge cmp (Stream stepa ta) (Stream stepb tb) =
    Stream
        step
        (Just ta, Just tb, Nothing, Nothing, Nothing, Nothing, Nothing, NM, 0)

    where
    {-# INLINE [0] step #-}

    -- step 1 when left stream could be  empty
    step gst (Just sa, sb, Nothing, Nothing, pa, pb, _, NM, idx) = do
        ref <- liftIO $ newIORef []
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Skip
                (Just sa', sb, Just a', Nothing, pa, pb, Just ref, MR, idx)
            Skip sa' ->
                Skip
                (Just sa', sb, Nothing, Nothing, pa, pb, Just ref, NM, idx)
            Stop ->
                Skip                        --step 13
                ( Nothing
                , sb
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )

    --  step 2 both stream has data pull from right stream and
    --  compare a and b
    step gst (Just sa, Just sb, Just a, b, pa, pb, buff, MR, idx) = do
        r <- stepb (adaptState gst) sb
        return $ case r of
            Yield b' sb' ->
                Skip
                (Just sa, Just sb', Just a, Just b', pa, pb, buff, MC, idx) -- go to step 5
            Skip sb' ->
                Skip
                (Nothing, Just sb', Nothing, b, pa, Nothing, buff, NM, idx)
            Stop ->
                Yield                                       -- step 12
                (Just a, Nothing)
                ( Just sa
                , Nothing
                , Just a
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )

    -- step 3 both stream has data pull from right stream and in next step
    -- compare b with previous b to remove mismatched duplicates from right stream
    step gst (Just sa, Just sb, Just a, b, pa, pb, buff, MRD, idx) = do
        r <- stepb (adaptState gst) sb
        return $ case r of
            Yield b' sb' ->
                Skip
                (Just sa, Just sb', Just a, Just b', pa, pb, buff, MCD, idx) -- step 4
            Skip sb' ->
                Skip
                (Nothing, Just sb', Nothing, b, pa, Nothing, buff, NM, idx)
            Stop ->
                Yield                               -- step 12
                (Just a, Nothing)
                ( Just sa
                , Nothing
                , Just a
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )

    -- step 4 compare b with previous b to remove mismatched duplicates from right stream
    step _ (Just sa, sb, Just a, Just b, pa, Just pb, buff, MCD, idx) =
        return $
        if b == pb
        then
            Yield                                   -- step 3
            (Nothing, Just b)
            (Just sa,  sb, Just a, Just b, pa, Just pb, buff, MRD, idx)
        else
            Skip (Just sa, sb, Just a,Just b, pa, Just b, buff, MC, idx)   -- step 5


    -- step 5 compare left stream data with right stream
    step _ (sa, sb, Just a, Just b, pa, pb, Just buff, MC, idx) = do
        liftIO $ print "p5"
        let res = cmp a b
        return $ case res of
            LT ->
                Yield
                (Just a, Nothing)
                (sa, sb, Just a, Just b, pa, pb, Just buff, ML, idx) -- skip a step 9
            EQ ->
                Skip
                (sa, sb, Just a, Just b, Just a, pb, Just buff, BUFF, idx) -- step 6
            GT ->
                Yield
                (Nothing, Just b)
                (sa, sb, Just a, Just b, pa, Just b, Just buff, MRD, idx) -- skip b  step 3

    -- step 6 b in list initial step
    step _ (Just sa, Just sb, Just a, Just b, pa, _, Just buff, BUFF, idx) = do
        liftIO $ print "p6"
        liftIO $ modifyIORef'  buff (b : )
        return $
            Skip                            -- step 7 pull next b
            ( Just sa
            , Just sb
            , Just a
            , Just b
            , pa
            , Just b
            , Just buff
            , BUFFB
            , idx
            )

    -- step 7 buffer repeated data
    step gst (Just sa, Just sb, a, b, pa, Just pb, Just buff, BUFFB, idx) = do
        liftIO $ print "p7"
        r <- stepb (adaptState gst) sb
        case r of
            Yield b' sb' -> do
                if b' == pb
                then do
                    liftIO $ modifyIORef'  buff (b' : )
                    return $
                        Skip                        -- go to 7
                        ( Just sa
                        , Just sb'
                        , a
                        , Just b'
                        , pa
                        , Just b'
                        , Just buff
                        , BUFFB
                        , idx
                        )
                else
                    return $
                    Skip                        -- go to step 8
                    ( Just sa
                    , Just sb'
                    , a
                    , Just b'
                    , pa
                    , Just b'
                    , Just buff
                    , YLD
                    , 0
                    )
            Skip sb' ->
                return $
                Skip
                ( Nothing
                , Just sb'
                , Nothing
                , b
                , pa
                , Nothing
                , Just buff
                , NM
                , idx
                )
            Stop ->
                return $
                Skip                        -- go to step 8
                ( Just sa
                , Just sb
                , a
                , Nothing
                , pa
                , Just pb
                , Just buff
                , YLD
                , 0
                )

    -- step 8 do pairing with buff (only when repeatation is over)
    step _ (Just sa, Just sb, Just a, b, pa, Just pb, Just buff, YLD, idx) = do
        liftIO $ print "p8"
        bl <- liftIO $ readIORef buff
        if idx < length bl
        then
            return $
            Yield
            (Just a, Just (bl !! idx))
            ( Just sa
            , Just sb
            , Just a
            , b
            , pa
            , Just pb
            , Just buff
            , YLD
            , idx+1
            )
        else
            return $
            Skip                            -- step 11
            ( Just sa
            , Just sb
            , Just a
            , b
            , Just a
            , Just pb
            , Just buff
            , ALD
            , 0
            )

    -- step 9 pull the data from left stream to compare next data from right stream
    step gst (Just sa, Just sb, Just a, Just b, pa, pb, buff, ML, idx) = do
        liftIO $ print "p9"
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Skip                        -- step 5
                (Just sa', Just sb, Just a', Just b, Just a, pb, buff, MC, idx)
            Skip sa' ->
                Skip
                (Just sa', Just sb, Nothing, Nothing, pa, pb, buff, MR, idx)
            Stop ->
                Yield                       --step 13
                (Nothing, Just b)
                ( Nothing
                , Just sb
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )

    -- step 10 pull the data from left stream to compare next data from right stream
    step gst (Just sa, sb, Just _, Just b, pa, pb, buff, MLD, idx) = do
        liftIO $ print "p10"
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Skip                        -- step 5
                ( Just sa', sb, Just a', Just b, pa, pb, buff, MC, idx)
            Skip sa' ->
                Skip
                (Just sa', sb, Nothing, Nothing, pa, pb, buff, MR, idx)
            Stop ->
                Yield                       --step 13
                (Nothing, Just b)
                ( Nothing
                , sb
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )

    -- step 11 pull the data from left stream to compare next data from right stream
    step gst (Just sa, sb, Just _, b, Just pa, pb, Just buff, ALD, idx) = do
        liftIO $ print "p11"
        r <- stepa (adaptState gst) sa
        case r of
            Yield a' sa' -> do
                if a' == pa
                then
                    return $
                    Skip                    -- step 8
                    ( Just sa'
                    , sb
                    , Just a'
                    , b
                    , Just a'
                    , pb
                    , Just buff
                    , YLD
                    , idx
                    )
                else do
                    -- clear buff
                    liftIO $ writeIORef buff []
                    return $
                        if isJust b
                        then
                            Skip                    -- step 5
                            ( Just sa'
                            , sb
                            , Just a'
                            , b
                            , Just a'
                            , pb
                            , Just buff
                            , MC
                            , idx
                            )
                        else
                            Yield                           -- step 12
                            (Just a', Nothing)
                            ( Just sa'
                            , Nothing
                            , Just a'
                            , Nothing
                            , Nothing, Nothing
                            , Nothing
                            , NM
                            , idx
                            )
            Skip sa' ->
                return $
                Skip
                ( Just sa'
                , sb
                , Nothing
                , Nothing
                , Just pa
                , pb
                , Just buff
                , MR
                , idx
                )
            Stop ->
                return $
                Skip                --step 13
                ( Nothing
                , sb
                , Nothing
                , b
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )

    --  step 12 b stream has finished yield remaining a
    step
        gst
        (Just sa, Nothing, Just a, Nothing, Nothing, Nothing, Nothing, NM, idx)
         = do
        liftIO $ print "p12"
        r <- stepa (adaptState gst) sa
        return $ case r of
            Yield a' sa' ->
                Yield                           -- go to step 5
                (Just a', Nothing)
                ( Just sa'
                , Nothing
                , Just a'
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )
            Skip sa' ->
                Skip
                ( Just sa'
                , Nothing
                , Just a
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )
            Stop -> Stop

    --  step 13 a stream has finished yield remaining b
    step
        gst
        ( Nothing
        , Just sb
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        , NM
        , idx
        ) = do
        liftIO $ print "p13"
        r <- stepb (adaptState gst) sb
        return $ case r of
            Yield b' sb' ->
                Yield                   -- go to step 5
                (Nothing, Just b')
                ( Nothing
                , Just sb'
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )
            Skip sb' ->
                Skip
                ( Nothing
                , Just sb'
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , Nothing
                , NM
                , idx
                )
            Stop -> Stop

    --  step 13.1 a stream has finished yield remaining b
    step
        _
        (Nothing, Just sb, Nothing, b, Nothing, Nothing, Nothing, NM, idx) = do
        liftIO $ print "p13.1"
        return $
            Yield                       -- go to step 5
            (Nothing, b)
            (Nothing, Just sb, Nothing, Nothing, Nothing, Nothing, Nothing, NM, idx)

    step _ (_, _, _, _, _, _, _, _, _) = return Stop
 