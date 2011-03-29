{-# Language FlexibleInstances #-}
{-# Language IncoherentInstances #-}
{-# Language TypeSynonymInstances #-}

--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Pack
-- Copyright : (c) Hideyuki Tanaka, 2009-2010
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- MessagePack Serializer using @Data.Binary.Pack@
--
--------------------------------------------------------------------

module Data.MessagePack.Pack (
  -- * Serializable class
  Packable(..),
  -- * Simple function to pack a Haskell value
  pack,
  ) where

import Data.Binary.Put
import Data.Binary.IEEE754
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TL
import qualified Data.Vector as V

import Data.MessagePack.Assoc
import Data.MessagePack.Internal.Utf8

-- | Serializable class
class Packable a where
  -- | Serialize a value
  put :: a -> Put

-- | Pack Haskell data to MessagePack string.
pack :: Packable a => a -> BL.ByteString
pack = runPut . put

instance Packable Int where
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

instance Packable () where
  put _ = 
    putWord8 0xC0

instance Packable Bool where
  put True = putWord8 0xC3
  put False = putWord8 0xC2

instance Packable Float where
  put f = do
    putWord8 0xCA
    putFloat32be f

instance Packable Double where
  put d = do
    putWord8 0xCB
    putFloat64be d

instance Packable String where
  put = putString encodeUtf8 B.length putByteString

instance Packable B.ByteString where
  put = putString id B.length putByteString

instance Packable BL.ByteString where
  put = putString id (fromIntegral . BL.length) putLazyByteString

instance Packable T.Text where
  put = putString T.encodeUtf8 B.length putByteString

instance Packable TL.Text where
  put = putString TL.encodeUtf8 (fromIntegral . BL.length) putLazyByteString

putString :: (s -> t) -> (t -> Int) -> (t -> Put) -> s -> Put
putString cnv lf pf str = do
  let bs = cnv str
  case lf bs of
    len | len <= 31 -> do
      putWord8 $ 0xA0 .|. fromIntegral len
    len | len < 0x10000 -> do
      putWord8 0xDA
      putWord16be $ fromIntegral len
    len -> do
      putWord8 0xDB
      putWord32be $ fromIntegral len
  pf bs

instance Packable a => Packable [a] where
  put = putArray length (mapM_ put)

instance Packable a => Packable (V.Vector a) where
  put = putArray V.length (V.mapM_ put)

instance (Packable a1, Packable a2) => Packable (a1, a2) where
  put = putArray (const 2) f where
    f (a1, a2) = put a1 >> put a2

instance (Packable a1, Packable a2, Packable a3) => Packable (a1, a2, a3) where
  put = putArray (const 3) f where
    f (a1, a2, a3) = put a1 >> put a2 >> put a3

instance (Packable a1, Packable a2, Packable a3, Packable a4) => Packable (a1, a2, a3, a4) where
  put = putArray (const 4) f where
    f (a1, a2, a3, a4) = put a1 >> put a2 >> put a3 >> put a4

instance (Packable a1, Packable a2, Packable a3, Packable a4, Packable a5) => Packable (a1, a2, a3, a4, a5) where
  put = putArray (const 5) f where
    f (a1, a2, a3, a4, a5) = put a1 >> put a2 >> put a3 >> put a4 >> put a5

instance (Packable a1, Packable a2, Packable a3, Packable a4, Packable a5, Packable a6) => Packable (a1, a2, a3, a4, a5, a6) where
  put = putArray (const 6) f where
    f (a1, a2, a3, a4, a5, a6) = put a1 >> put a2 >> put a3 >> put a4 >> put a5 >> put a6

instance (Packable a1, Packable a2, Packable a3, Packable a4, Packable a5, Packable a6, Packable a7) => Packable (a1, a2, a3, a4, a5, a6, a7) where
  put = putArray (const 7) f where
    f (a1, a2, a3, a4, a5, a6, a7) = put a1 >> put a2 >> put a3 >> put a4 >> put a5 >> put a6 >> put a7

instance (Packable a1, Packable a2, Packable a3, Packable a4, Packable a5, Packable a6, Packable a7, Packable a8) => Packable (a1, a2, a3, a4, a5, a6, a7, a8) where
  put = putArray (const 8) f where
    f (a1, a2, a3, a4, a5, a6, a7, a8) = put a1 >> put a2 >> put a3 >> put a4 >> put a5 >> put a6 >> put a7 >> put a8

instance (Packable a1, Packable a2, Packable a3, Packable a4, Packable a5, Packable a6, Packable a7, Packable a8, Packable a9) => Packable (a1, a2, a3, a4, a5, a6, a7, a8, a9) where
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

instance (Packable k, Packable v) => Packable (Assoc [(k,v)]) where
  put = putMap length (mapM_ putPair) . unAssoc

instance (Packable k, Packable v) => Packable (Assoc (V.Vector (k,v))) where
  put = putMap V.length (V.mapM_ putPair) . unAssoc

putPair :: (Packable a, Packable b) => (a, b) -> Put
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

instance Packable a => Packable (Maybe a) where
  put Nothing = put ()
  put (Just a) = put a

