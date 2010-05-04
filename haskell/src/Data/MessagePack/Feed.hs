--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Feed
-- Copyright : (c) Hideyuki Tanaka, 2009
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- Feeders for Stream Deserializers
--
--------------------------------------------------------------------

module Data.MessagePack.Feed(
  -- * Feeder type
  Feeder,
  -- * Feeders
  feederFromHandle,
  feederFromFile,
  feederFromString,
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.IORef
import System.IO

-- | Feeder returns Just ByteString when bytes remains, otherwise Nothing.
type Feeder = IO (Maybe ByteString)

-- | Feeder from Handle
feederFromHandle :: Handle -> IO Feeder
feederFromHandle h = return $ do
  bs <- BS.hGetNonBlocking h bufSize
  if BS.length bs > 0
    then do return $ Just bs
    else do
    c <- BS.hGet h 1
    if BS.length c > 0
      then do return $ Just c
      else do
      hClose h
      return Nothing
  where
    bufSize = 4096

-- | Feeder from File
feederFromFile :: FilePath -> IO Feeder
feederFromFile path =
  openFile path ReadMode >>= feederFromHandle

-- | Feeder from ByteString
feederFromString :: ByteString -> IO Feeder
feederFromString bs = do
  r <- newIORef (Just bs)
  return $ f r
  where
    f r = do
      mb <- readIORef r
      writeIORef r Nothing
      return mb
