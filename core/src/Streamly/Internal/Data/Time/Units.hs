-- |
-- Module      : Streamly.Internal.Data.Time.Units
-- Copyright   : (c) 2019 Composewell Technologies
-- License     : BSD-3-Clause
-- Maintainer  : streamly@composewell.com
-- Stability   : pre-release
-- Portability : GHC
--
-- Fast time manipulation.
--
-- = Representing Time
--
-- Numbers along with an associated unit (e.g. 'MilliSecond64') are used to
-- represent durations and points in time.  Durations are relative but points
-- are absolute and defined with respect to some fixed or well known point in
-- time e.g. the Unix epoch (01-Jan-1970).  Absolute and relative times are
-- numbers that can be represented and manipulated like 'Num'.
--
-- = Fixed Precision 64-bit Units
--
-- * 'NanoSecond64': 292 years at nanosecond precision.
-- * 'MicroSecond64': 292K years at nanosecond precision.
-- * 'MilliSecond64': 292M years at nanosecond precision.
--
-- These units are 'Integral' 'Num' types. We can use 'fromIntegral' to convert
-- any integral type to/from these types.
--
-- = TimeSpec
--
-- * 'TimeSpec': 292G years at nanosecond precision
--
-- = RelTime64
--
-- Relative time, not relative to any specific epoch.  Represented using
-- 'NanoSecond64'. 'fromRelTime64' and 'toRelTime64' can be used to convert a
-- time unit to/from RelTime. Note that a larger unit e.g. 'MicroSecond64' may
-- get truncated if it is larger than 292 years. RelTime64 is also generated by
-- diffing two AbsTime.
--
-- RelTime is a 'Num', we can do number arithmetic on RelTime, and use
-- 'fromInteger' to convert an 'Integer' nanoseconds to 'RelTime'.
--
-- = AbsTime
--
-- Time measured relative to the POSIX epoch i.e. 01-Jan-1970. Represented
-- using 'TimeSpec'. 'fromAbsTime' and 'toAbsTime' can be used to convert a
-- time unit to/from AbsTime.
--
-- AbsTime is not a 'Num'. We can use 'diffAbsTime' to diff abstimes to get
-- a 'RelTime'. We can add RelTime to AbsTime to get another AbsTime.
--
-- = TimeSpec vs 64-bit Units
--
-- TimeSpec can represent up to 292 billion years of time at nanosecond
-- precision while 64-bit units can represent only 292 years at the same
-- precision. However, 64-bit units are much faster to manipulate. In high
-- performance code it is recommended to use the 64-bit units if possible.
--
-- = Working with the "time" package
--
-- AbsTime is essentially the same as 'SystemTime' from the time package. We
-- can use 'SystemTime' to interconvert between time package and this module.
--
-- = Alternative Representations
--
-- Double or Fixed would be a much better representation so that we do not lose
-- information between conversions. However, for faster arithmetic operations
-- we use an 'Int64' here. When we need convservation of values we can use a
-- different system of units with a Fixed precision.
--
-- = TODO
--
--  Split the Timespec/TimeUnit in a separate module?
--  Keep *64/TimeUnit64 in this module, remove the 64 suffix because these are
--  common units.
--  Rename TimeUnit to IsTimeSpec, TimeUnit64 to IsTimeUnit.
--
-- Time (default double precision). Fast Time (64-bit), Wide Time (TimeSpec).
-- Timezone, UTC/Local/System/User-defined.
--
-- Fast (UTC Time), Wide (Local Time) etc.
--
-- Units? Can be module specific or wrappers around them.
-- e.g. NanoSecond (Fast (UTC Time)) or NanoSecond Time.
--

module Streamly.Internal.Data.Time.Units
    (
    -- * Time Unit Conversions
      TimeUnit()
    -- , TimeUnitWide()
    , TimeUnit64()

    -- * Time Units
    , TimeSpec(..)
    , NanoSecond64(..)
    , MicroSecond64(..)
    , MilliSecond64(..)
    , showNanoSecond64

    -- * Absolute times (using TimeSpec)
    , AbsTime(..)
    , toAbsTime
    , fromAbsTime

    -- * Relative times (using TimeSpec)
    , RelTime
    , toRelTime
    , fromRelTime
    , diffAbsTime
    , addToAbsTime

    -- * Relative times (using NanoSecond64)
    , RelTime64
    , toRelTime64
    , fromRelTime64
    , diffAbsTime64
    , addToAbsTime64
    , showRelTime64
    )
where

#include "inline.hs"

import Text.Printf (printf)

import Data.Int
import Foreign.Storable (Storable)
import Streamly.Internal.Data.Unbox (Unbox)
import Streamly.Internal.Data.Time.TimeSpec

-------------------------------------------------------------------------------
-- Some constants
-------------------------------------------------------------------------------

{-# INLINE tenPower3 #-}
tenPower3 :: Int64
tenPower3 = 1000

{-# INLINE tenPower6 #-}
tenPower6 :: Int64
tenPower6 = 1000000

{-# INLINE tenPower9 #-}
tenPower9 :: Int64
tenPower9 = 1000000000


-------------------------------------------------------------------------------
-- Time Unit Representations
-------------------------------------------------------------------------------

-- XXX We should be able to use type families to use different represenations
-- for a unit.
--
-- Second Rational
-- Second Double
-- Second Int64
-- Second Integer
-- NanoSecond Int64
-- ...

-------------------------------------------------------------------------------
-- Integral Units
-------------------------------------------------------------------------------

-- | An 'Int64' time representation with a nanosecond resolution. It can
-- represent time up to ~292 years.
newtype NanoSecond64 = NanoSecond64 Int64
    deriving ( Eq
             , Read
             , Show
             , Enum
             , Bounded
             , Num
             , Real
             , Integral
             , Ord
             , Storable
             , Unbox
             )

-- XXX timed

timed :: IO a -> IO (NanoSecond64, a)
timed = undefined

-- ghcStats :: IO a -> IO (GHCStats, a)
-- measuredBy :: Diff s => IO s -> IO a -> IO (s, a)
-- timed = measuredBy (getTime Monotonic)

-- | An 'Int64' time representation with a microsecond resolution.
-- It can represent time up to ~292,000 years.
newtype MicroSecond64 = MicroSecond64 Int64
    deriving ( Eq
             , Read
             , Show
             , Enum
             , Bounded
             , Num
             , Real
             , Integral
             , Ord
             , Storable
             , Unbox
             )

-- | An 'Int64' time representation with a millisecond resolution.
-- It can represent time up to ~292 million years.
newtype MilliSecond64 = MilliSecond64 Int64
    deriving ( Eq
             , Read
             , Show
             , Enum
             , Bounded
             , Num
             , Real
             , Integral
             , Ord
             , Storable
             , Unbox
             )

-------------------------------------------------------------------------------
-- Fractional Units
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Time unit conversions
-------------------------------------------------------------------------------

-- TODO: compare whether using TimeSpec instead of Integer provides significant
-- performance boost. If not then we can just use Integer nanoseconds and get
-- rid of TimeUnitWide.
--
{-
-- | A type class for converting between time units using 'Integer' as the
-- intermediate and the widest representation with a nanosecond resolution.
-- This system of units can represent arbitrarily large times but provides
-- least efficient arithmetic operations due to 'Integer' arithmetic.
--
-- NOTE: Converting to and from units may truncate the value depending on the
-- original value and the size and resolution of the destination unit.
class TimeUnitWide a where
    toTimeInteger   :: a -> Integer
    fromTimeInteger :: Integer -> a
-}

-- XXX Rename to IsTimeUnit?
--
-- | A type class for converting between units of time using 'TimeSpec' as the
-- intermediate representation.  This system of units can represent up to ~292
-- billion years at nanosecond resolution with reasonably efficient arithmetic
-- operations.
--
-- NOTE: Converting to and from units may truncate the value depending on the
-- original value and the size and resolution of the destination unit.
class TimeUnit a where
    toTimeSpec   :: a -> TimeSpec
    fromTimeSpec :: TimeSpec -> a

-- XXX we can use a fromNanoSecond64 for conversion with overflow check and
-- fromNanoSecond64Unsafe for conversion without overflow check.
--
-- | A type class for converting between units of time using 'Int64' as the
-- intermediate representation with a nanosecond resolution.  This system of
-- units can represent up to ~292 years at nanosecond resolution with fast
-- arithmetic operations.
--
-- NOTE: Converting to and from units may truncate the value depending on the
-- original value and the size and resolution of the destination unit.
class TimeUnit64 a where
    toNanoSecond64   :: a -> NanoSecond64
    fromNanoSecond64 :: NanoSecond64 -> a

-------------------------------------------------------------------------------
-- Time units
-------------------------------------------------------------------------------

instance TimeUnit TimeSpec where
    toTimeSpec = id
    fromTimeSpec = id

-- XXX Remove 64 suffix, regular units should be considered 64 bit.

instance TimeUnit NanoSecond64 where
    {-# INLINE toTimeSpec #-}
    toTimeSpec (NanoSecond64 t) = TimeSpec s ns
        where (s, ns) = t `divMod` tenPower9

    {-# INLINE fromTimeSpec #-}
    fromTimeSpec (TimeSpec s ns) =
        NanoSecond64 $ s * tenPower9 + ns

instance TimeUnit64 NanoSecond64 where
    {-# INLINE toNanoSecond64 #-}
    toNanoSecond64 = id

    {-# INLINE fromNanoSecond64 #-}
    fromNanoSecond64 = id

instance TimeUnit MicroSecond64 where
    {-# INLINE toTimeSpec #-}
    toTimeSpec (MicroSecond64 t) = TimeSpec s (us * tenPower3)
        where (s, us) = t `divMod` tenPower6

    {-# INLINE fromTimeSpec #-}
    fromTimeSpec (TimeSpec s ns) =
        -- XXX round ns to nearest microsecond?
        MicroSecond64 $ s * tenPower6 + (ns `div` tenPower3)

instance TimeUnit64 MicroSecond64 where
    {-# INLINE toNanoSecond64 #-}
    toNanoSecond64 (MicroSecond64 us) = NanoSecond64 $ us * tenPower3

    {-# INLINE fromNanoSecond64 #-}
    -- XXX round ns to nearest microsecond?
    fromNanoSecond64 (NanoSecond64 ns) = MicroSecond64 $ ns `div` tenPower3

instance TimeUnit MilliSecond64 where
    {-# INLINE toTimeSpec #-}
    toTimeSpec (MilliSecond64 t) = TimeSpec s (ms * tenPower6)
        where (s, ms) = t `divMod` tenPower3

    {-# INLINE fromTimeSpec #-}
    fromTimeSpec (TimeSpec s ns) =
        -- XXX round ns to nearest millisecond?
        MilliSecond64 $ s * tenPower3 + (ns `div` tenPower6)

instance TimeUnit64 MilliSecond64 where
    {-# INLINE toNanoSecond64 #-}
    toNanoSecond64 (MilliSecond64 ms) = NanoSecond64 $ ms * tenPower6

    {-# INLINE fromNanoSecond64 #-}
    -- XXX round ns to nearest millisecond?
    fromNanoSecond64 (NanoSecond64 ns) = MilliSecond64 $ ns `div` tenPower6

-------------------------------------------------------------------------------
-- Absolute time
-------------------------------------------------------------------------------

-- Have a Fixed64 type with an Int64 as underlying type
-- XXX Use AbsTime64 for faster arithmetic on AbsTimes?
--
-- data Epoch = Posix | UTC | Rel
--
-- XXX data Time epoch = Time TimeSpec
--
-- | Absolute times are relative to a predefined epoch in time. 'AbsTime'
-- represents times using 'TimeSpec' which can represent times up to ~292
-- billion years at a nanosecond resolution.
newtype AbsTime = AbsTime TimeSpec
    deriving (Eq, Ord, Show)

-- | Convert a 'TimeUnit' representing relative time from the Unix epoch to an
-- absolute time.
{-# INLINE_NORMAL toAbsTime #-}
toAbsTime :: TimeUnit a => a -> AbsTime
toAbsTime = AbsTime . toTimeSpec

-- | Convert absolute time to a relative 'TimeUnit' representing time relative
-- to the Unix epoch.
{-# INLINE_NORMAL fromAbsTime #-}
fromAbsTime :: TimeUnit a => AbsTime -> a
fromAbsTime (AbsTime t) = fromTimeSpec t

-- XXX We can also write rewrite rules to simplify divisions multiplications
-- and additions when manipulating units. Though, that might get simplified at
-- the assembly (llvm) level as well. Note to/from conversions may be lossy and
-- therefore this equation may not hold, but that's ok.
{-# RULES "fromAbsTime/toAbsTime" forall a. toAbsTime (fromAbsTime a) = a #-}
{-# RULES "toAbsTime/fromAbsTime" forall a. fromAbsTime (toAbsTime a) = a #-}

-------------------------------------------------------------------------------
-- Relative time using NaonoSecond64 as the underlying representation
-------------------------------------------------------------------------------

-- XXX Use NanoSecond etc. instead of RelTime. They already denote relative
-- time.  Maybe its a good idea to keep RelTime as a wrapper around time units
-- so that we can switch the underlying representation any time. we can use
-- Double or Int64 or Fixed or TimeSpec.
--
-- Can we design it such that we can switch to Double as the underlying
-- representation any time if we want?  We can just switch the module to switch
-- the impl.
--
-- We can use AbsTime and RelTime as generic types so that we have the ability
-- to switch the underlying repr.
--
-- Use "Time" for AbsTime relative to Posix epoch, basically the system
-- time. For Time, use a 64-bit value or 64+64? A fixed epoch + relative time.
-- For relative times in a stream we can use rollingMap (-). As long as the
-- epoch is fixed we only need to diff the reltime which should be efficient.
--
-- We can do the same to paths as well. As long as the root is fixed we can
-- diff only the relative components.
--
-- Also type Time = PosixTime
--      newtype PosixTime = AbsTime Posix days ns
--      newtype UTCTime = AbsTime UTC days ns
--      newtype RelTime = AbsTime Rel days ns
--
-- The max value of ns won't be limited to 10^9 so we can keep the epoch fixed
-- and only manipulate ns.
--
-- We use a separate type to represent relative time for safety and speed.
-- RelTime has a Num instance, absolute time doesn't.  Relative times are
-- usually shorter and for our purposes an Int64 nanoseconds can hold close to
-- thousand year duration. It is also faster to manipulate. We do not check for
-- overflows during manipulations so use it only when you know the time cannot
-- be too big. If you need a bigger RelTime representation then use RelTime.

-- This is the same as the DiffTime in time package.
--
-- | Relative times are relative to some arbitrary point of time. Unlike
-- 'AbsTime' they are not relative to a predefined epoch.
newtype RelTime64 = RelTime64 NanoSecond64
    deriving ( Eq
             , Read
             , Show
             , Enum
             , Bounded
             , Num
             , Real
             , Integral
             , Ord
             )

-- | Convert a 'TimeUnit' to a relative time.
{-# INLINE_NORMAL toRelTime64 #-}
toRelTime64 :: TimeUnit64 a => a -> RelTime64
toRelTime64 = RelTime64 . toNanoSecond64

-- | Convert relative time to a 'TimeUnit'.
{-# INLINE_NORMAL fromRelTime64 #-}
fromRelTime64 :: TimeUnit64 a => RelTime64 -> a
fromRelTime64 (RelTime64 t) = fromNanoSecond64 t

{-# RULES "fromRelTime64/toRelTime64" forall a .
          toRelTime64 (fromRelTime64 a) = a #-}

{-# RULES "toRelTime64/fromRelTime64" forall a .
          fromRelTime64 (toRelTime64 a) = a #-}

-- | Difference between two absolute points of time.
{-# INLINE diffAbsTime64 #-}
diffAbsTime64 :: AbsTime -> AbsTime -> RelTime64
diffAbsTime64 (AbsTime (TimeSpec s1 ns1)) (AbsTime (TimeSpec s2 ns2)) =
    RelTime64 $ NanoSecond64 $ ((s1 - s2) * tenPower9) + (ns1 - ns2)

{-# INLINE addToAbsTime64 #-}
addToAbsTime64 :: AbsTime -> RelTime64 -> AbsTime
addToAbsTime64 (AbsTime (TimeSpec s1 ns1)) (RelTime64 (NanoSecond64 ns2)) =
    AbsTime $ TimeSpec (s1 + s) ns
    where (s, ns) = (ns1 + ns2) `divMod` tenPower9

-------------------------------------------------------------------------------
-- Relative time using TimeSpec as the underlying representation
-------------------------------------------------------------------------------

newtype RelTime = RelTime TimeSpec
    deriving ( Eq
             , Read
             , Show
             -- , Enum
             -- , Bounded
             , Num
             -- , Real
             -- , Integral
             , Ord
             )

{-# INLINE_NORMAL toRelTime #-}
toRelTime :: TimeUnit a => a -> RelTime
toRelTime = RelTime . toTimeSpec

{-# INLINE_NORMAL fromRelTime #-}
fromRelTime :: TimeUnit a => RelTime -> a
fromRelTime (RelTime t) = fromTimeSpec t

{-# RULES "fromRelTime/toRelTime" forall a. toRelTime (fromRelTime a) = a #-}
{-# RULES "toRelTime/fromRelTime" forall a. fromRelTime (toRelTime a) = a #-}

-- XXX rename to diffAbsTimes?
-- SemigroupR?
{-# INLINE diffAbsTime #-}
diffAbsTime :: AbsTime -> AbsTime -> RelTime
diffAbsTime (AbsTime t1) (AbsTime t2) = RelTime (t1 - t2)

-- SemigroupR?
{-# INLINE addToAbsTime #-}
addToAbsTime :: AbsTime -> RelTime -> AbsTime
addToAbsTime (AbsTime t1) (RelTime t2) = AbsTime $ t1 + t2

-------------------------------------------------------------------------------
-- Formatting and printing
-------------------------------------------------------------------------------

-- | Convert nanoseconds to a string showing time in an appropriate unit.
showNanoSecond64 :: NanoSecond64 -> String
showNanoSecond64 time@(NanoSecond64 ns)
    | time < 0    = '-' : showNanoSecond64 (-time)
    | ns < 1000 = fromIntegral ns `with` "ns"
#ifdef mingw32_HOST_OS
    | ns < 1000000 = (fromIntegral ns / 1000) `with` "us"
#else
    | ns < 1000000 = (fromIntegral ns / 1000) `with` "μs"
#endif
    | ns < 1000000000 = (fromIntegral ns / 1000000) `with` "ms"
    | ns < (60 * 1000000000) = (fromIntegral ns / 1000000000) `with` "s"
    | ns < (60 * 60 * 1000000000) =
        (fromIntegral ns / (60 * 1000000000)) `with` "min"
    | ns < (24 * 60 * 60 * 1000000000) =
        (fromIntegral ns / (60 * 60 * 1000000000)) `with` "hr"
    | ns < (365 * 24 * 60 * 60 * 1000000000) =
        (fromIntegral ns / (24 * 60 * 60 * 1000000000)) `with` "days"
    | otherwise =
        (fromIntegral ns / (365 * 24 * 60 * 60 * 1000000000)) `with` "years"
     where with (t :: Double) (u :: String)
               | t >= 1e9  = printf "%.4g %s" t u
               | t >= 1e3  = printf "%.0f %s" t u
               | t >= 1e2  = printf "%.1f %s" t u
               | t >= 1e1  = printf "%.2f %s" t u
               | otherwise = printf "%.3f %s" t u

-- The unit Second may be implicit. We can then use modifiers to convert it
-- e.g. Nano 1 for 1 nanosec, Micro 1 for 1 microsec. These can work in general
-- for any unit.
--
-- We can also use Minute x for 60x, and Hour x for 3600x etc.
--
-- In general we should be able to show the time in a specified unit, if we
-- omit the unit we can show it in an automatically chosen one.
{-
data UnitName =
      Nano
    | Micro
    | Milli
    | Sec
-}

showRelTime64 :: RelTime64 -> String
showRelTime64 = showNanoSecond64 . fromRelTime64
