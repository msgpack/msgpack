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
  module Data.MessagePack.Object,
  module Data.MessagePack.Put,
  module Data.MessagePack.Parser,
  module Data.MessagePack.Iteratee,
  
  -- * Simple functions of Pack and Unpack
  pack,
  unpack,
  
  -- * Pack functions
  packToString,
  packToHandle,
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
import Data.Functor.Identity
import qualified Data.Iteratee as I
import qualified Data.Iteratee.IO as I
import System.IO

import Data.MessagePack.Object
import Data.MessagePack.Put
import Data.MessagePack.Parser
import Data.MessagePack.Iteratee

bufferSize :: Int
bufferSize = 4 * 1024

class IsByteString s where
  toBS :: s -> B.ByteString

instance IsByteString B.ByteString where
  toBS = id

instance IsByteString L.ByteString where
  toBS = B.concat . L.toChunks

-- | Pack Haskell data to MessagePack string.
pack :: ObjectPut a => a -> L.ByteString
pack = packToString . put

-- | Unpack MessagePack string to Haskell data.
unpack :: (ObjectGet a, IsByteString s) => s -> a
unpack bs =
  runIdentity $ I.run $ I.joinIM $ I.enumPure1Chunk (toBS bs) getI

-- TODO: tryUnpack

-- | Pack to ByteString.
packToString :: Put -> L.ByteString
packToString = runPut

-- | Pack to Handle
packToHandle :: Handle -> Put -> IO ()
packToHandle h = L.hPutStr h . packToString

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
  I.run . I.joinIM . I.enumHandle bufferSize h

-- | Iteratee interface to unpack from File
unpackFromFileI :: CIO.MonadCatchIO m => FilePath -> I.Iteratee B.ByteString m a -> m a
unpackFromFileI path p =
  CIO.bracket
  (liftIO $ openBinaryFile path ReadMode)
  (liftIO . hClose)
  (flip unpackFromHandleI p)
