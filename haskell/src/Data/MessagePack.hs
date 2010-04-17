--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack
-- Copyright : (c) Hideyuki Tanaka, 2009
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
  module Data.MessagePack.Base,
  module Data.MessagePack.Class,
  module Data.MessagePack.Feed,
  module Data.MessagePack.Monad,
  module Data.MessagePack.Stream,
  
  -- * Pack and Unpack
  packb,
  unpackb,
  
  -- * Pure version of Pack and Unpack
  packb',
  unpackb',
  ) where

import Data.ByteString (ByteString)
import System.IO.Unsafe

import Data.MessagePack.Base
import Data.MessagePack.Class
import Data.MessagePack.Feed
import Data.MessagePack.Monad
import Data.MessagePack.Stream

-- | Pack Haskell data to MessagePack string.
packb :: OBJECT a => a -> IO ByteString
packb dat = do
  sb <- newSimpleBuffer
  pc <- newPacker sb
  pack pc dat
  simpleBufferData sb

-- | Unpack MessagePack string to Haskell data.
unpackb :: OBJECT a => ByteString -> IO (Result a)
unpackb bs = do
  withZone $ \z -> do
    r <- unpackObject z bs
    return $ case r of
      Left err -> Left (show err)
      Right (_, dat) -> fromObject dat

-- | Pure version of 'packb'.
packb' :: OBJECT a => a -> ByteString
packb' dat = unsafePerformIO $ packb dat

-- | Pure version of 'unpackb'.
unpackb' :: OBJECT a => ByteString -> Result a
unpackb' bs = unsafePerformIO $ unpackb bs
