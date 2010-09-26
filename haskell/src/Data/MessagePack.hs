--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack
-- Copyright : (c) Hideyuki Tanaka, 2009-2010
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- Simple interface to pack and unpack MessagePack data.
--
--------------------------------------------------------------------

module Data.MessagePack(
  module Data.MessagePack.Pack,
  module Data.MessagePack.Unpack,
  module Data.MessagePack.Object,
  module Data.MessagePack.Iteratee,
  module Data.MessagePack.Derive,
  
  -- * Pack functions
  packToString,
  packToHandle,
  packToHandle',
  packToFile,
  
  -- * Unpack functions
  unpackFromString,
  unpackFromHandle,
  unpackFromFile,
  unpackFromStringI,
  unpackFromHandleI,
  unpackFromFileI,
  
  ) where

import qualified Control.Monad.CatchIO as CIO
import Control.Monad.IO.Class
import qualified Data.Attoparsec as A
import Data.Binary.Put
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as L
import qualified Data.Iteratee as I
import System.IO

import Data.MessagePack.Pack
import Data.MessagePack.Unpack
import Data.MessagePack.Object
import Data.MessagePack.Iteratee
import Data.MessagePack.Derive

bufferSize :: Int
bufferSize = 4 * 1024

-- | Pack to ByteString.
packToString :: Put -> L.ByteString
packToString = runPut

-- | Pack to Handle
packToHandle :: Handle -> Put -> IO ()
packToHandle h = L.hPutStr h . packToString

-- | Pack to Handle and Flush Handle
packToHandle' :: Handle -> Put -> IO ()
packToHandle' h p = packToHandle h p >> hFlush h

-- | Pack to File
packToFile :: FilePath -> Put -> IO ()
packToFile path = L.writeFile path . packToString

-- | Unpack from ByteString
unpackFromString :: (Monad m, IsByteString s) => s -> A.Parser a -> m a
unpackFromString bs =
  unpackFromStringI bs . parserToIteratee

-- | Unpack from Handle
unpackFromHandle :: CIO.MonadCatchIO m => Handle -> A.Parser a -> m a
unpackFromHandle h =
  unpackFromHandleI h .parserToIteratee

-- | Unpack from File
unpackFromFile :: CIO.MonadCatchIO m => FilePath -> A.Parser a -> m a
unpackFromFile path =
  unpackFromFileI path . parserToIteratee

-- | Iteratee interface to unpack from ByteString
unpackFromStringI :: (Monad m, IsByteString s) => s -> I.Iteratee B.ByteString m a -> m a
unpackFromStringI bs =
  I.run . I.joinIM . I.enumPure1Chunk (toBS bs)

-- | Iteratee interface to unpack from Handle
unpackFromHandleI :: CIO.MonadCatchIO m => Handle -> I.Iteratee B.ByteString m a -> m a
unpackFromHandleI h =
  I.run . I.joinIM . enumHandleNonBlocking bufferSize h

-- | Iteratee interface to unpack from File
unpackFromFileI :: CIO.MonadCatchIO m => FilePath -> I.Iteratee B.ByteString m a -> m a
unpackFromFileI path p =
  CIO.bracket
  (liftIO $ openBinaryFile path ReadMode)
  (liftIO . hClose)
  (flip unpackFromHandleI p)
