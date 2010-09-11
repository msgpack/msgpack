{-# Language FlexibleInstances #-}
{-# Language IncoherentInstances #-}
{-# Language OverlappingInstances #-}
{-# Language TypeSynonymInstances #-}

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
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as L
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

instance ObjectPut String where
  put = putString length (putByteString . B8.pack)

instance ObjectPut B.ByteString where
  put = putString B.length putByteString

instance ObjectPut L.ByteString where
  put = putString (fromIntegral . L.length) putLazyByteString

putString :: (s -> Int) -> (s -> Put) -> s -> Put
putString lf pf str = do
  case lf str of
    len | len <= 31 -> do
      putWord8 $ 0xA0 .|. fromIntegral len
    len | len < 0x10000 -> do
      putWord8 0xDA
      putWord16be $ fromIntegral len
    len -> do
      putWord8 0xDB
      putWord32be $ fromIntegral len
  pf str

instance ObjectPut a => ObjectPut [a] where
  put = putArray length (mapM_ put)

instance ObjectPut a => ObjectPut (V.Vector a) where
  put = putArray V.length (V.mapM_ put)

instance (ObjectPut a1, ObjectPut a2) => ObjectPut (a1, a2) where
  put = putArray (const 2) f where
    f (a1, a2) = put a1 >> put a2

instance (ObjectPut a1, ObjectPut a2, ObjectPut a3) => ObjectPut (a1, a2, a3) where
  put = putArray (const 3) f where
    f (a1, a2, a3) = put a1 >> put a2 >> put a3

instance (ObjectPut a1, ObjectPut a2, ObjectPut a3, ObjectPut a4) => ObjectPut (a1, a2, a3, a4) where
  put = putArray (const 4) f where
    f (a1, a2, a3, a4) = put a1 >> put a2 >> put a3 >> put a4

instance (ObjectPut a1, ObjectPut a2, ObjectPut a3, ObjectPut a4, ObjectPut a5) => ObjectPut (a1, a2, a3, a4, a5) where
  put = putArray (const 5) f where
    f (a1, a2, a3, a4, a5) = put a1 >> put a2 >> put a3 >> put a4 >> put a5

instance (ObjectPut a1, ObjectPut a2, ObjectPut a3, ObjectPut a4, ObjectPut a5, ObjectPut a6) => ObjectPut (a1, a2, a3, a4, a5, a6) where
  put = putArray (const 6) f where
    f (a1, a2, a3, a4, a5, a6) = put a1 >> put a2 >> put a3 >> put a4 >> put a5 >> put a6

instance (ObjectPut a1, ObjectPut a2, ObjectPut a3, ObjectPut a4, ObjectPut a5, ObjectPut a6, ObjectPut a7) => ObjectPut (a1, a2, a3, a4, a5, a6, a7) where
  put = putArray (const 7) f where
    f (a1, a2, a3, a4, a5, a6, a7) = put a1 >> put a2 >> put a3 >> put a4 >> put a5 >> put a6 >> put a7

instance (ObjectPut a1, ObjectPut a2, ObjectPut a3, ObjectPut a4, ObjectPut a5, ObjectPut a6, ObjectPut a7, ObjectPut a8) => ObjectPut (a1, a2, a3, a4, a5, a6, a7, a8) where
  put = putArray (const 8) f where
    f (a1, a2, a3, a4, a5, a6, a7, a8) = put a1 >> put a2 >> put a3 >> put a4 >> put a5 >> put a6 >> put a7 >> put a8

instance (ObjectPut a1, ObjectPut a2, ObjectPut a3, ObjectPut a4, ObjectPut a5, ObjectPut a6, ObjectPut a7, ObjectPut a8, ObjectPut a9) => ObjectPut (a1, a2, a3, a4, a5, a6, a7, a8, a9) where
  put = putArray (const 9) f where
    f (a1, a2, a3, a4, a5, a6, a7, a8, a9) = put a1 >> put a2 >> put a3 >> put a4 >> put a5 >> put a6 >> put a7 >> put a8 >> put a9

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
