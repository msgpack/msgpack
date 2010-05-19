--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Stream
-- Copyright : (c) Hideyuki Tanaka, 2009
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- Lazy Stream Serializers and Deserializers
--
--------------------------------------------------------------------

module Data.MessagePack.Stream(
  unpackObjects,
  unpackObjectsFromFile,
  unpackObjectsFromHandle,
  unpackObjectsFromString,
  ) where

import Data.ByteString (ByteString)
import System.IO
import System.IO.Unsafe

import Data.MessagePack.Base
import Data.MessagePack.Feed

-- | Unpack objects using given feeder.
unpackObjects :: Feeder -> IO [Object]
unpackObjects feeder = do
  up <- newUnpacker defaultInitialBufferSize
  f up
  where
  f up = unsafeInterleaveIO $ do
    mbo <- unpackOnce up
    case mbo of
      Just o -> do
        os <- f up
        return $ o:os
      Nothing ->
        return []

  unpackOnce up = do
    resp <- unpackerExecute up
    case resp of
      0 -> do
        r <- feedOnce up
        if r
          then unpackOnce up
          else return Nothing
      1 -> do
        obj <- unpackerData up
        freeZone =<< unpackerReleaseZone up
        unpackerReset up
        return $ Just obj
      _ ->
        error $ "unpackerExecute fails: " ++ show resp

  feedOnce up = do
    dat <- feeder
    case dat of
      Nothing ->
        return False
      Just bs -> do
        unpackerFeed up bs
        return True

-- | Unpack objects from file.
unpackObjectsFromFile :: FilePath -> IO [Object]
unpackObjectsFromFile fname =
  unpackObjects =<< feederFromFile fname

-- | Unpack objects from handle.
unpackObjectsFromHandle :: Handle -> IO [Object]
unpackObjectsFromHandle h =
  unpackObjects =<< feederFromHandle h
  
-- | Unpack oobjects from given byte sequence.
unpackObjectsFromString :: ByteString -> IO [Object]
unpackObjectsFromString bs =
  unpackObjects =<< feederFromString bs
