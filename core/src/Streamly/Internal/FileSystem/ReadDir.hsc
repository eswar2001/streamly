-- |
-- Module      : Streamly.Internal.FileSystem.Dir
-- Copyright   : (c) 2018 Composewell Technologies
--
-- License     : BSD3
-- Maintainer  : streamly@composewell.com
-- Portability : GHC

module Streamly.Internal.FileSystem.ReadDir
    (
      openDirStream
    , readDirStreamEither
    , readEitherChunks
    )
where

import Control.Monad.IO.Class (MonadIO(..))
import Data.Char (ord)
import Foreign (Ptr, Word8, nullPtr, peek, peekByteOff, castPtr)
import Foreign.C 
    (resetErrno, Errno(..), getErrno, eINTR, throwErrno, CString, CChar)
import Fusion.Plugin.Types (Fuse(..))
import Streamly.Internal.Data.Array (Array)
import Streamly.Internal.FileSystem.Path (Path)
import System.Posix.Directory (closeDirStream)
import System.Posix.Directory.Internals (DirStream(..), CDir, CDirent)
import System.Posix.Error (throwErrnoPathIfNullRetry)
import Streamly.Internal.Data.Stream (Stream(..), Step(..))

import qualified Streamly.Internal.Data.Array as Array
import qualified Streamly.Internal.FileSystem.Path as Path

#include <dirent.h>

foreign import capi unsafe "dirent.h opendir"
    c_opendir :: CString  -> IO (Ptr CDir)

foreign import ccall unsafe "dirent.h readdir"
    c_readdir  :: Ptr CDir -> IO (Ptr CDirent)

foreign import ccall unsafe "__hscore_d_name"
    d_name :: Ptr CDirent -> IO CString

-- XXX Use openat instead of open so that we do not have to build and resolve
-- absolute paths.
--
-- XXX Path is not null terminated therefore we need to make a copy even if the
-- array is pinned.
-- {-# INLINE openDirStream #-}
openDirStream :: Path -> IO DirStream
openDirStream p =
  Array.asCStringUnsafe (Path.toChunk p) $ \s -> do
    -- XXX is toString always creating another copy or only in case of error?
    dirp <- throwErrnoPathIfNullRetry (Path.toString p) "openDirStream" $ c_opendir s
    return (DirStream dirp)

isMetaDir :: Ptr CChar -> IO Bool
isMetaDir dname = do
    -- XXX Assuming an encoding that maps "." to ".", this is true for
    -- UTF8.
    c1 <- peek dname
    if (c1 /= fromIntegral (ord '.'))
    then return False
    else do
        c2 :: Word8 <- peekByteOff dname 1
        if (c2 == 0)
        then return True
        else if (c2 /= fromIntegral (ord '.'))
        then return False
        else do
            c3 :: Word8 <- peekByteOff dname 2
            if (c3 == 0)
            then return True
            else return False

-- XXX We can use getdents64 directly so that we can use array slices from the
-- same buffer that we passed to the OS. That way we can also avoid any
-- overhead of bracket.
-- XXX Make this as Unfold to avoid returning Maybe
-- XXX Or NOINLINE some parts and inline the rest to fuse it
-- {-# INLINE readDirStreamEither #-}
readDirStreamEither ::
    -- DirStream -> IO (Either (Rel (Dir Path)) (Rel (File Path)))
    DirStream -> IO (Maybe (Either Path Path))
readDirStreamEither (DirStream dirp) = loop

  where

  -- mkPath :: IsPath (Rel (a Path)) => Array Word8 -> Rel (a Path)
  -- {-# INLINE mkPath #-}
  mkPath :: Array Word8 -> Path
  mkPath = Path.unsafeFromPath . Path.unsafeFromChunk

  loop = do
    resetErrno
    ptr <- c_readdir dirp
    if (ptr /= nullPtr)
    then do
        dname <- d_name ptr
        dtype :: #{type unsigned char} <- #{peek struct dirent, d_type} ptr
        -- dreclen :: #{type unsigned short} <- #{peek struct dirent, d_reclen} ptr
        -- It is possible to find the name length using dreclen and then use
        -- fromPtrN, but it is not straightforward because the reclen is
        -- padded to 8-byte boundary.
        let !name = Array.fromByteStr (castPtr dname)
        if (dtype == #const DT_DIR)
        then do
            isMeta <- isMetaDir dname
            if isMeta
            then loop
            else return (Just (Left (mkPath name)))
        else return (Just (Right (mkPath name)))
    else do
        errno <- getErrno
        if (errno == eINTR)
        then loop
        else do
            let (Errno n) = errno
            if (n == 0)
            -- then return (Left (mkPath (Array.fromList [46])))
            then return Nothing
            else throwErrno "readDirStreamEither"

{-# ANN type ChunkStreamState Fuse #-}
data ChunkStreamState =
      ChunkStreamInit [Path] [Path] Int [Path] Int
    | ChunkStreamLoop
        Path -- current dir path
        [Path]  -- remaining dirs
        (Ptr CDir) -- current dir
        [Path] -- dirs buffered
        Int    -- dir count
        [Path] -- files buffered
        Int -- file count

-- XXX We can use a fold for collecting files and dirs.
-- XXX We can write a two fold scan to buffer and yield whichever fills first
-- like foldMany, it would be foldEither.
{-# INLINE readEitherChunks #-}
readEitherChunks :: MonadIO m => [Path] -> Stream m (Either [Path] [Path])
readEitherChunks alldirs =
    Stream step (ChunkStreamInit alldirs [] 0 [] 0)

    where

    -- We want to keep the dir batching as low as possible for better
    -- concurrency esp when the number of dirs is low.
    dirMax = 4
    fileMax = 1000

    mkPath :: Array Word8 -> Path
    mkPath = Path.unsafeFromPath . Path.unsafeFromChunk

    step _ (ChunkStreamInit (x:xs) dirs ndirs files nfiles) = do
        DirStream dirp <- liftIO $ openDirStream x
        return $ Skip (ChunkStreamLoop x xs dirp dirs ndirs files nfiles)

    step _ (ChunkStreamInit [] [] _ [] _) =
        return Stop

    step _ (ChunkStreamInit [] [] _ files _) =
        return $ Yield (Right files) (ChunkStreamInit [] [] 0 [] 0)

    step _ (ChunkStreamInit [] dirs _ files _) =
        return $ Yield (Left dirs) (ChunkStreamInit [] [] 0 files 0)

    step _ st@(ChunkStreamLoop curdir xs dirp dirs ndirs files nfiles) = do
        liftIO resetErrno
        dentPtr <- liftIO $ c_readdir dirp
        if (dentPtr /= nullPtr)
        then do
            dname <- liftIO $ d_name dentPtr
            dtype :: #{type unsigned char} <-
                liftIO $ #{peek struct dirent, d_type} dentPtr

            let !name = Array.fromByteStr (castPtr dname)
                path = Path.append curdir (mkPath name)

            if (dtype == (#const DT_DIR))
            then do
                isMeta <- liftIO $ isMetaDir dname
                if isMeta
                then return $ Skip st
                else let dirs1 = path : dirs
                         ndirs1 = ndirs + 1
                      in if ndirs1 >= dirMax
                         then return $ Yield (Left dirs1)
                            (ChunkStreamLoop curdir xs dirp [] 0 files nfiles)
                         else return $ Skip
                            (ChunkStreamLoop curdir xs dirp dirs1 ndirs1 files nfiles)
            else let files1 = path : files
                     nfiles1 = nfiles + 1
                  in if nfiles1 >= fileMax
                     then return $ Yield (Right files1)
                        (ChunkStreamLoop curdir xs dirp dirs ndirs [] 0)
                     else return $ Skip
                        (ChunkStreamLoop curdir xs dirp dirs ndirs files1 nfiles1)
        else do
            errno <- liftIO getErrno
            if (errno == eINTR)
            then return $ Skip st
            else do
                let (Errno n) = errno
                liftIO $ closeDirStream (DirStream dirp)
                if (n == 0)
                then return $ Skip (ChunkStreamInit xs dirs ndirs files nfiles)
                else liftIO $ throwErrno "readEitherChunks"