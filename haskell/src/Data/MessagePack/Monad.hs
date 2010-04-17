--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Monad
-- Copyright : (c) Hideyuki Tanaka, 2009
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- Monadic Stream Serializers and Deserializers
--
--------------------------------------------------------------------

module Data.MessagePack.Monad(
  -- * Classes
  MonadPacker(..),
  MonadUnpacker(..),
  
  -- * Packer and Unpacker type
  PackerT(..),
  UnpackerT(..),
  
  -- * Packers
  packToString,
  packToHandle,
  packToFile,
  
  -- * Unpackers
  unpackFrom,
  unpackFromString,
  unpackFromHandle,
  unpackFromFile,
  ) where

import Control.Monad
import Control.Monad.Trans
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import System.IO

import Data.MessagePack.Base hiding (Unpacker)
import qualified Data.MessagePack.Base as Base
import Data.MessagePack.Class
import Data.MessagePack.Feed

class Monad m => MonadPacker m where
  -- | Serialize a object
  put :: OBJECT a => a -> m ()

class Monad m => MonadUnpacker m where
  -- | Deserialize a object
  get :: OBJECT a => m a

-- | Serializer Type
newtype PackerT m r = PackerT { runPackerT :: Base.Packer -> m r }

instance Monad m => Monad (PackerT m) where
  a >>= b =
    PackerT $ \pc -> do
      r <- runPackerT a pc
      runPackerT (b r) pc
  
  return r =
    PackerT $ \_ -> return r

instance MonadTrans PackerT where
  lift m = PackerT $ \_ -> m

instance MonadIO m => MonadIO (PackerT m) where
  liftIO = lift . liftIO

instance MonadIO m => MonadPacker (PackerT m) where
  put v = PackerT $ \pc -> liftIO $ do
    pack pc v

-- | Execute given serializer and returns byte sequence.
packToString :: MonadIO m => PackerT m r -> m ByteString
packToString m = do
  sb <- liftIO $ newSimpleBuffer
  pc <- liftIO $ newPacker sb
  runPackerT m pc
  liftIO $ simpleBufferData sb

-- | Execcute given serializer and write byte sequence to Handle.
packToHandle :: MonadIO m => Handle -> PackerT m r -> m ()
packToHandle h m = do
  sb <- packToString m
  liftIO $ BS.hPut h sb
  liftIO $ hFlush h

-- | Execute given serializer and write byte sequence to file.
packToFile :: MonadIO m => FilePath -> PackerT m r -> m ()
packToFile p m = do
  sb <- packToString m
  liftIO $ BS.writeFile p sb

-- | Deserializer type
newtype UnpackerT m r = UnpackerT { runUnpackerT :: Base.Unpacker -> Feeder -> m r }

instance Monad m => Monad (UnpackerT m) where
  a >>= b =
    UnpackerT $ \up feed -> do
      r <- runUnpackerT a up feed
      runUnpackerT (b r) up feed
  
  return r =
    UnpackerT $ \_ _ -> return r

instance MonadTrans UnpackerT where
  lift m = UnpackerT $ \_ _ -> m

instance MonadIO m => MonadIO (UnpackerT m) where
  liftIO = lift . liftIO

instance MonadIO m => MonadUnpacker (UnpackerT m) where
  get = UnpackerT $ \up feed -> liftIO $ do
    resp <- unpackerExecute up
    guard $ resp>=0
    when (resp==0) $ do
      Just bs <- feed
      unpackerFeed up bs
      resp2 <- unpackerExecute up
      guard $ resp2==1
    obj <- unpackerData up
    freeZone =<< unpackerReleaseZone up
    unpackerReset up
    let Right r = fromObject obj
    return r

-- | Execute deserializer using given feeder.
unpackFrom :: MonadIO m => Feeder -> UnpackerT m r -> m r
unpackFrom f m = do
  up <- liftIO $ newUnpacker defaultInitialBufferSize
  runUnpackerT m up f

-- | Execute deserializer using given handle.
unpackFromHandle :: MonadIO m => Handle -> UnpackerT m r -> m r
unpackFromHandle h m =
  flip unpackFrom m =<< liftIO (feederFromHandle h)

-- | Execute deserializer using given file content.
unpackFromFile :: MonadIO m => FilePath -> UnpackerT m r -> m r
unpackFromFile p m = do
  h <- liftIO $ openFile p ReadMode
  r <- flip unpackFrom m =<< liftIO (feederFromHandle h)
  liftIO $ hClose h
  return r

-- | Execute deserializer from given byte sequence.
unpackFromString :: MonadIO m => ByteString -> UnpackerT m r -> m r
unpackFromString bs m = do
  flip unpackFrom m =<< liftIO (feederFromString bs)
