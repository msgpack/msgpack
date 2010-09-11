{-# Language FlexibleInstances #-}
{-# Language IncoherentInstances #-}
{-# Language OverlappingInstances #-}
{-# Language TypeSynonymInstances #-}

--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Parser
-- Copyright : (c) Hideyuki Tanaka, 2009-2010
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- MessagePack Deserializer using @Data.Attoparsec@
--
--------------------------------------------------------------------

module Data.MessagePack.Parser(
  -- * MessagePack deserializer
  ObjectGet(..),
  ) where

import Control.Monad
import qualified Data.Attoparsec as A
import Data.Binary.Get
import Data.Binary.IEEE754
import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as L
import Data.Int
import qualified Data.Vector as V
import Data.Word
import Text.Printf

import Data.MessagePack.Object

-- | Deserializable class
class ObjectGet a where
  -- | Deserialize a value
  get :: A.Parser a

instance ObjectGet Object where
  get =
    A.choice
    [ liftM ObjectInteger get
    , liftM (\() -> ObjectNil) get
    , liftM ObjectBool get
    , liftM ObjectDouble get
    , liftM ObjectRAW get
    , liftM ObjectArray get
    , liftM ObjectMap get
    ]

instance ObjectGet Int where
  get = do
    c <- A.anyWord8
    case c of
      _ | c .&. 0x80 == 0x00 ->
        return $ fromIntegral c
      _ | c .&. 0xE0 == 0xE0 ->
        return $ fromIntegral (fromIntegral c :: Int8)
      0xCC ->
        return . fromIntegral =<< A.anyWord8
      0xCD ->
        return . fromIntegral =<< parseUint16
      0xCE ->
        return . fromIntegral =<< parseUint32
      0xCF ->
        return . fromIntegral =<< parseUint64
      0xD0 ->
        return . fromIntegral =<< parseInt8
      0xD1 ->
        return . fromIntegral =<< parseInt16
      0xD2 ->
        return . fromIntegral =<< parseInt32
      0xD3 ->
        return . fromIntegral =<< parseInt64
      _ ->
        fail $ printf "invlid integer tag: 0x%02X" c

instance ObjectGet () where
  get = do
    c <- A.anyWord8
    case c of
      0xC0 ->
        return ()
      _ ->
        fail $ printf "invlid nil tag: 0x%02X" c

instance ObjectGet Bool where
  get = do
    c <- A.anyWord8
    case c of
      0xC3 ->
        return True
      0xC2 ->
        return False
      _ ->
        fail $ printf "invlid bool tag: 0x%02X" c

instance ObjectGet Double where
  get = do
    c <- A.anyWord8
    case c of
      0xCA ->
        return . realToFrac . runGet getFloat32be . toLBS =<< A.take 4
      0xCB ->
        return . runGet getFloat64be . toLBS =<< A.take 8
      _ ->
        fail $ printf "invlid double tag: 0x%02X" c

instance ObjectGet String where
  get = parseString (\n -> return . B8.unpack =<< A.take n)

instance ObjectGet B.ByteString where
  get = parseString A.take

instance ObjectGet L.ByteString where
  get = parseString (\n -> do bs <- A.take n; return $ L.fromChunks [bs])

parseString :: (Int -> A.Parser a) -> A.Parser a
parseString aget = do
  c <- A.anyWord8
  case c of
    _ | c .&. 0xE0 == 0xA0 ->
      aget . fromIntegral $ c .&. 0x1F
    0xDA ->
      aget . fromIntegral =<< parseUint16
    0xDB ->
      aget . fromIntegral =<< parseUint32
    _ ->
      fail $ printf "invlid raw tag: 0x%02X" c

instance ObjectGet a => ObjectGet [a] where
  get = parseArray (flip replicateM get)

instance ObjectGet a => ObjectGet (V.Vector a) where
  get = parseArray (flip V.replicateM get)

instance (ObjectGet a1, ObjectGet a2) => ObjectGet (a1, a2) where
  get = parseArray f where
    f 2 = get >>= \a1 -> get >>= \a2 -> return (a1, a2)
    f n = fail $ printf "wrong tupple size: expected 2 but got " n

instance (ObjectGet a1, ObjectGet a2, ObjectGet a3) => ObjectGet (a1, a2, a3) where
  get = parseArray f where
    f 3 = get >>= \a1 -> get >>= \a2 -> get >>= \a3 -> return (a1, a2, a3)
    f n = fail $ printf "wrong tupple size: expected 3 but got " n

instance (ObjectGet a1, ObjectGet a2, ObjectGet a3, ObjectGet a4) => ObjectGet (a1, a2, a3, a4) where
  get = parseArray f where
    f 4 = get >>= \a1 -> get >>= \a2 -> get >>= \a3 -> get >>= \a4 -> return (a1, a2, a3, a4)
    f n = fail $ printf "wrong tupple size: expected 4 but got " n

instance (ObjectGet a1, ObjectGet a2, ObjectGet a3, ObjectGet a4, ObjectGet a5) => ObjectGet (a1, a2, a3, a4, a5) where
  get = parseArray f where
    f 5 = get >>= \a1 -> get >>= \a2 -> get >>= \a3 -> get >>= \a4 -> get >>= \a5 -> return (a1, a2, a3, a4, a5)
    f n = fail $ printf "wrong tupple size: expected 5 but got " n

instance (ObjectGet a1, ObjectGet a2, ObjectGet a3, ObjectGet a4, ObjectGet a5, ObjectGet a6) => ObjectGet (a1, a2, a3, a4, a5, a6) where
  get = parseArray f where
    f 6 = get >>= \a1 -> get >>= \a2 -> get >>= \a3 -> get >>= \a4 -> get >>= \a5 -> get >>= \a6 -> return (a1, a2, a3, a4, a5, a6)
    f n = fail $ printf "wrong tupple size: expected 6 but got " n

instance (ObjectGet a1, ObjectGet a2, ObjectGet a3, ObjectGet a4, ObjectGet a5, ObjectGet a6, ObjectGet a7) => ObjectGet (a1, a2, a3, a4, a5, a6, a7) where
  get = parseArray f where
    f 7 = get >>= \a1 -> get >>= \a2 -> get >>= \a3 -> get >>= \a4 -> get >>= \a5 -> get >>= \a6 -> get >>= \a7 -> return (a1, a2, a3, a4, a5, a6, a7)
    f n = fail $ printf "wrong tupple size: expected 7 but got " n

instance (ObjectGet a1, ObjectGet a2, ObjectGet a3, ObjectGet a4, ObjectGet a5, ObjectGet a6, ObjectGet a7, ObjectGet a8) => ObjectGet (a1, a2, a3, a4, a5, a6, a7, a8) where
  get = parseArray f where
    f 8 = get >>= \a1 -> get >>= \a2 -> get >>= \a3 -> get >>= \a4 -> get >>= \a5 -> get >>= \a6 -> get >>= \a7 -> get >>= \a8 -> return (a1, a2, a3, a4, a5, a6, a7, a8)
    f n = fail $ printf "wrong tupple size: expected 8 but got " n

instance (ObjectGet a1, ObjectGet a2, ObjectGet a3, ObjectGet a4, ObjectGet a5, ObjectGet a6, ObjectGet a7, ObjectGet a8, ObjectGet a9) => ObjectGet (a1, a2, a3, a4, a5, a6, a7, a8, a9) where
  get = parseArray f where
    f 9 = get >>= \a1 -> get >>= \a2 -> get >>= \a3 -> get >>= \a4 -> get >>= \a5 -> get >>= \a6 -> get >>= \a7 -> get >>= \a8 -> get >>= \a9 -> return (a1, a2, a3, a4, a5, a6, a7, a8, a9)
    f n = fail $ printf "wrong tupple size: expected 9 but got " n

parseArray :: (Int -> A.Parser a) -> A.Parser a
parseArray aget = do
  c <- A.anyWord8
  case c of
    _ | c .&. 0xF0 == 0x90 ->
      aget . fromIntegral $ c .&. 0x0F
    0xDC ->
      aget . fromIntegral =<< parseUint16
    0xDD ->
      aget . fromIntegral =<< parseUint32
    _ ->
      fail $ printf "invlid array tag: 0x%02X" c

instance (ObjectGet k, ObjectGet v) => ObjectGet [(k, v)] where
  get = parseMap (flip replicateM parsePair)

instance (ObjectGet k, ObjectGet v) => ObjectGet (V.Vector (k, v)) where
  get = parseMap (flip V.replicateM parsePair)

parsePair :: (ObjectGet k, ObjectGet v) => A.Parser (k, v)
parsePair = do
  a <- get
  b <- get
  return (a, b)

parseMap :: (Int -> A.Parser a) -> A.Parser a
parseMap aget = do
  c <- A.anyWord8
  case c of
    _ | c .&. 0xF0 == 0x80 ->
      aget . fromIntegral $ c .&. 0x0F
    0xDE ->
      aget . fromIntegral =<< parseUint16
    0xDF ->
      aget . fromIntegral =<< parseUint32
    _ ->
      fail $ printf "invlid map tag: 0x%02X" c

parseUint16 :: A.Parser Word16
parseUint16 = do
  b0 <- A.anyWord8
  b1 <- A.anyWord8
  return $ (fromIntegral b0 `shiftL` 8) .|. fromIntegral b1

parseUint32 :: A.Parser Word32
parseUint32 = do
  b0 <- A.anyWord8
  b1 <- A.anyWord8
  b2 <- A.anyWord8
  b3 <- A.anyWord8
  return $ (fromIntegral b0 `shiftL` 24) .|.
           (fromIntegral b1 `shiftL` 16) .|.
           (fromIntegral b2 `shiftL` 8) .|.
           fromIntegral b3

parseUint64 :: A.Parser Word64
parseUint64 = do
  b0 <- A.anyWord8
  b1 <- A.anyWord8
  b2 <- A.anyWord8
  b3 <- A.anyWord8
  b4 <- A.anyWord8
  b5 <- A.anyWord8
  b6 <- A.anyWord8
  b7 <- A.anyWord8
  return $ (fromIntegral b0 `shiftL` 56) .|.
           (fromIntegral b1 `shiftL` 48) .|.
           (fromIntegral b2 `shiftL` 40) .|.
           (fromIntegral b3 `shiftL` 32) .|.
           (fromIntegral b4 `shiftL` 24) .|.
           (fromIntegral b5 `shiftL` 16) .|.
           (fromIntegral b6 `shiftL` 8) .|.
           fromIntegral b7

parseInt8 :: A.Parser Int8
parseInt8 = return . fromIntegral =<< A.anyWord8

parseInt16 :: A.Parser Int16
parseInt16 = return . fromIntegral =<< parseUint16

parseInt32 :: A.Parser Int32
parseInt32 = return . fromIntegral =<< parseUint32

parseInt64 :: A.Parser Int64
parseInt64 = return . fromIntegral =<< parseUint64

toLBS :: B.ByteString -> L.ByteString
toLBS bs = L.fromChunks [bs]
