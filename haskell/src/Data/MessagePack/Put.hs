{-# Language FlexibleInstances #-}
{-# Language IncoherentInstances #-}
{-# Language OverlappingInstances #-}

--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Put
-- Copyright : (c) Hideyuki Tanaka, 2009-2010
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- MessagePack Serializer using @Data.Binary.Put@
--
--------------------------------------------------------------------

module Data.MessagePack.Put(
  -- * Serializable class
  ObjectPut(..),
  ) where

import Data.Binary.Put
import Data.Binary.IEEE754
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.Vector as V

import Data.MessagePack.Object

-- | Serializable class
class ObjectPut a where
  -- | Serialize a value
  put :: a -> Put

instance ObjectPut Object where
  put obj =
    case obj of
      ObjectInteger n ->
        put n
      ObjectNil ->
        put ()
      ObjectBool b ->
        put b
      ObjectDouble d ->
        put d
      ObjectRAW raw ->
        put raw
      ObjectArray arr ->
        put arr
      ObjectMap m ->
        put m

instance ObjectPut Int where
  put n =
    case n of
      _ | n >= 0 && n <= 127 ->
        putWord8 $ fromIntegral n
      _ | n >= -32 && n <= -1 ->
        putWord8 $ fromIntegral n
      _ | n >= 0 && n < 0x100 -> do
        putWord8 0xCC
        putWord8 $ fromIntegral n
      _ | n >= 0 && n < 0x10000 -> do
        putWord8 0xCD
        putWord16be $ fromIntegral n
      _ | n >= 0 && n < 0x100000000 -> do
        putWord8 0xCE
        putWord32be $ fromIntegral n
      _ | n >= 0 -> do
        putWord8 0xCF
        putWord64be $ fromIntegral n
      _ | n >= -0x80 -> do
        putWord8 0xD0
        putWord8 $ fromIntegral n
      _ | n >= -0x8000 -> do
        putWord8 0xD1
        putWord16be $ fromIntegral n
      _ | n >= -0x80000000 -> do
        putWord8 0xD2
        putWord32be $ fromIntegral n
      _ -> do
        putWord8 0xD3
        putWord64be $ fromIntegral n

instance ObjectPut () where
  put _ = 
    putWord8 0xC0

instance ObjectPut Bool where
  put True = putWord8 0xC3
  put False = putWord8 0xC2

instance ObjectPut Double where
  put d = do
    putWord8 0xCB
    putFloat64be d

instance ObjectPut B.ByteString where
  put bs = do
    case len of
      _ | len <= 31 -> do
        putWord8 $ 0xA0 .|. fromIntegral len
      _ | len < 0x10000 -> do
        putWord8 0xDA
        putWord16be $ fromIntegral len
      _ -> do
        putWord8 0xDB
        putWord32be $ fromIntegral len
    putByteString bs
    where
      len = B.length bs

instance ObjectPut a => ObjectPut [a] where
  put = putArray length (mapM_ put)

instance ObjectPut a => ObjectPut (V.Vector a) where
  put = putArray V.length (V.mapM_ put)

putArray :: (a -> Int) -> (a -> Put) -> a -> Put
putArray lf pf arr = do
  case lf arr of
    len | len <= 15 ->
      putWord8 $ 0x90 .|. fromIntegral len
    len | len < 0x10000 -> do
      putWord8 0xDC
      putWord16be $ fromIntegral len
    len -> do
      putWord8 0xDD
      putWord32be $ fromIntegral len
  pf arr

instance (ObjectPut k, ObjectPut v) => ObjectPut [(k, v)] where
  put = putMap length (mapM_ putPair)

instance (ObjectPut k, ObjectPut v) => ObjectPut (V.Vector (k, v)) where
  put = putMap V.length (V.mapM_ putPair)

putPair :: (ObjectPut a, ObjectPut b) => (a, b) -> Put
putPair (a, b) = put a >> put b

putMap :: (a -> Int) -> (a -> Put) -> a -> Put
putMap lf pf m = do
  case lf m of
    len | len <= 15 ->
      putWord8 $ 0x80 .|. fromIntegral len
    len | len < 0x10000 -> do
      putWord8 0xDE
      putWord16be $ fromIntegral len
    len -> do
      putWord8 0xDF
      putWord32be $ fromIntegral len
  pf m
