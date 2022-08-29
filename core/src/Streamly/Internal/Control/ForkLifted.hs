-- |
-- Module      : Streamly.Internal.Control.ForkLifted
-- Copyright   : (c) 2017 Composewell Technologies
-- License     : BSD-3-Clause
-- Maintainer  : streamly@composewell.com
-- Stability   : experimental
-- Portability : GHC

module Streamly.Internal.Control.ForkLifted
    (
      doFork
    , forkManaged
    )
where

import Control.Concurrent (ThreadId, forkIO)
import Control.Exception (SomeException(..), catch, mask)
import Data.Functor (void)
-- import Streamly.Internal.Control.Concurrent (MonadRunInIO, RunInIO(..), withRunInIO, withRunInIONoRestore)
import Streamly.Internal.Control.ForkIO (rawForkIO, forkManagedWith)

-- | Fork a thread to run the given computation, installing the provided
-- exception handler. Lifted to any monad with 'MonadRunInIO m'
-- capability.
--
-- TODO: the RunInIO argument can be removed, we can directly pass the action
-- as "mrun action" instead.
{-# INLINE doFork #-}
doFork ::
       IO ()
    -> (IO () -> IO ())
    -> (SomeException -> IO ())
    -> IO ThreadId
doFork action mrun exHandler =
        mask $ \restore -> do
            rawForkIO $ catch (restore $ void $ mrun action) exHandler

-- | Fork a thread that is automatically killed as soon as the reference to the
-- returned threadId is garbage collected.
--
{-# INLINABLE forkManaged #-}
forkManaged :: IO () -> IO ThreadId
forkManaged = forkManagedWith forkIO
