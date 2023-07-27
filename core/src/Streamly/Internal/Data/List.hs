{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Streamly.Internal.Data.List
-- Copyright   : (c) 2018 Composewell Technologies
--
-- License     : BSD3
-- Maintainer  : streamly@composewell.com
-- Portability : GHC
--
-- Lists are just a special case of monadic streams. The stream type @Stream
-- Identity a@ can be used as a replacement for @[a]@.  The 'List' type in this
-- module is just a newtype wrapper around @Stream Identity@ for better type
-- inference when using the 'OverloadedLists' GHC extension. @List a@ provides
-- better performance compared to @[a]@. Standard list, string and list
-- comprehension syntax can be used with the 'List' type by enabling
-- 'OverloadedLists', 'OverloadedStrings' and 'MonadComprehensions' GHC
-- extensions.  There would be a slight difference in the 'Show' and 'Read'
-- strings of streamly list as compared to regular lists.
--
-- Conversion to stream types is free, any stream combinator can be used on
-- lists by converting them to streams.  However, for convenience, this module
-- provides combinators that work directly on the 'List' type.
--
--
-- @
-- List $ S.map (+ 1) $ toStream (1 \`Cons\` Nil)
-- @
--
-- To convert a 'List' to regular lists, you can use any of the following:
--
-- * @toList . toStream@ and @toStream . fromList@
-- * 'Data.Foldable.toList' from "Data.Foldable"
-- * 'GHC.Exts.toList' and 'GHC.Exts.fromList' from 'IsList' in "GHC.Exts"
--
-- If you have made use of 'Nil' and 'Cons' constructors in the code and you
-- want to replace streamly lists with standard lists, all you need to do is
-- import these definitions:
--
-- @
-- type List = []
-- pattern Nil <- [] where Nil = []
-- pattern Cons x xs = x : xs
-- infixr 5 `Cons`
-- {-\# COMPLETE Cons, Nil #-}
-- @
--
-- See <src/docs/streamly-vs-lists.md> for more details and
-- <src/test/PureStreams.hs> for comprehensive usage examples.
--
module Streamly.Internal.Data.List
    (
    List (Nil, Cons)

    , toStream
    , fromStream

    -- XXX we may want to use rebindable syntax for variants instead of using
    -- different types (applicative do and apWith).
    , ZipList (..)
    , fromZipList
    , toZipList
    )
where

import Control.Arrow (second)
import Data.Functor.Identity (Identity, runIdentity)
import GHC.Exts (IsList(..), IsString(..))
import Streamly.Internal.Data.Stream.StreamD.Type
    ( CrossStream
    , mkCross
    , unCross
    )
import Streamly.Internal.Data.Stream.StreamD.Type (Stream)
import Text.Read
       ( Lexeme(Ident), lexP, parens, prec, readPrec, readListPrec
       , readListPrecDefault)

import qualified Streamly.Internal.Data.Stream.StreamK.Type as K
import qualified Streamly.Internal.Data.Stream.StreamD.Type as Stream
import qualified Streamly.Internal.Data.Stream.StreamD.Generate as Stream

-- XXX Rename to PureStream.

-- | @List a@ is a replacement for @[a]@.
--
-- /Pre-release/
newtype List a = List { toCrossStream :: CrossStream Identity a }
    deriving
    ( Eq, Ord
    , Functor, Foldable
    , Applicative, Monad, IsList)

toStream :: List a -> Stream Identity a
toStream = unCross . toCrossStream

fromStream :: Stream Identity a -> List a
fromStream xs = List (mkCross xs)

instance (a ~ Char) => IsString (List a) where
    {-# INLINE fromString #-}
    fromString = List . fromList

instance Show a => Show (List a) where
    show (List x) = show $ unCross x

instance Read a => Read (List a) where
    readPrec = fromStream <$> readPrec

------------------------------------------------------------------------------
-- Patterns
------------------------------------------------------------------------------

-- Note: When using the OverloadedLists extension we should be able to pattern
-- match using the regular list contructors. OverloadedLists uses 'toList' to
-- perform the pattern match, it should not be too bad as it works lazily in
-- the Identity monad. We need these patterns only when not using that
-- extension.

-- | An empty list constructor and pattern that matches an empty 'List'.
-- Corresponds to '[]' for Haskell lists.
--
pattern Nil :: List a
pattern Nil <- (runIdentity . K.null . Stream.toStreamK . toStream -> True)

    where

    Nil = List $ mkCross (Stream.fromStreamK K.nil)

infixr 5 `Cons`

-- | A list constructor and pattern that deconstructs a 'List' into its head
-- and tail. Corresponds to ':' for Haskell lists.
--
pattern Cons :: a -> List a -> List a
pattern Cons x xs <-
    (fmap (second (List . mkCross . Stream.fromStreamK))
        . runIdentity . K.uncons . Stream.toStreamK . toStream
            -> Just (x, xs)
    )

    where

    Cons x xs = List $ mkCross $ Stream.cons x (toStream xs)

{-# COMPLETE Nil, Cons #-}

------------------------------------------------------------------------------
-- ZipStream
------------------------------------------------------------------------------

-- $setup
-- >>> import qualified Streamly.Data.Fold as Fold
-- >>> import qualified Streamly.Data.Stream as Stream
-- >>> import qualified Streamly.Internal.Data.Stream.Zip as Stream

------------------------------------------------------------------------------
-- Serially Zipping Streams
------------------------------------------------------------------------------

-- | For 'ZipStream':
--
-- @
-- (<>) = 'Streamly.Data.Stream.append'
-- (\<*>) = 'Streamly.Data.Stream.zipWith' id
-- @
--
-- Applicative evaluates the streams being zipped serially:
--
-- >>> s1 = Stream.ZipStream $ Stream.fromFoldable [1, 2]
-- >>> s2 = Stream.ZipStream $ Stream.fromFoldable [3, 4]
-- >>> s3 = Stream.ZipStream $ Stream.fromFoldable [5, 6]
-- >>> s = (,,) <$> s1 <*> s2 <*> s3
-- >>> Stream.fold Fold.toList (Stream.unZipStream s)
-- [(1,3,5),(2,4,6)]
--
newtype ZipStream m a = ZipStream {unZipStream :: Stream m a}
        deriving (Functor)

deriving instance IsList (ZipStream Identity a)
deriving instance (a ~ Char) => IsString (ZipStream Identity a)
deriving instance Eq a => Eq (ZipStream Identity a)
deriving instance Ord a => Ord (ZipStream Identity a)
deriving instance (Foldable m, Monad m) => Foldable (ZipStream m)

instance Show a => Show (ZipStream Identity a) where
    showsPrec p dl = showParen (p > 10) $
        showString "fromList " . shows (toList dl)

instance Read a => Read (ZipStream Identity a) where
    readPrec = parens $ prec 10 $ do
        Ident "fromList" <- lexP
        fromList <$> readPrec
    readListPrec = readListPrecDefault

type ZipSerialM = ZipStream

-- | An IO stream whose applicative instance zips streams serially.
--
type ZipSerial = ZipSerialM IO

instance Monad m => Applicative (ZipStream m) where
    pure = ZipStream . Stream.repeat

    {-# INLINE (<*>) #-}
    ZipStream m1 <*> ZipStream m2 = ZipStream $ Stream.zipWith id m1 m2

------------------------------------------------------------------------------
-- ZipList
------------------------------------------------------------------------------

-- | Just like 'List' except that it has a zipping 'Applicative' instance
-- and no 'Monad' instance.
--
newtype ZipList a = ZipList { toZipStream :: ZipStream Identity a }
    deriving
    ( Show, Read, Eq, Ord
    , Functor, Foldable
    , Applicative, IsList
    )

instance (a ~ Char) => IsString (ZipList a) where
    {-# INLINE fromString #-}
    fromString = ZipList . fromList

-- | Convert a 'ZipList' to a regular 'List'
--
fromZipList :: ZipList a -> List a
fromZipList (ZipList zs) = List $ mkCross (unZipStream zs)

-- | Convert a regular 'List' to a 'ZipList'
--
toZipList :: List a -> ZipList a
toZipList = ZipList . ZipStream . toStream
