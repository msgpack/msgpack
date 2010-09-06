{-# Language FlexibleInstances #-}
{-# Language IncoherentInstances #-}
{-# Language OverlappingInstances #-}

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

instance ObjectGet Int where
  get = parseInt

instance ObjectGet () where
  get = parseNil

instance ObjectGet Bool where
  get = parseBool

instance ObjectGet Double where
  get = parseDouble

instance ObjectGet B.ByteString where
  get = parseRAW

instance ObjectGet a => ObjectGet [a] where
  get = parseArray

instance ObjectGet a => ObjectGet (V.Vector a) where
  get = parseArrayVector

instance (ObjectGet k, ObjectGet v) => ObjectGet [(k, v)] where
  get = parseMap

instance (ObjectGet k, ObjectGet v) => ObjectGet (V.Vector (k, v)) where
  get = parseMapVector

instance ObjectGet Object where
  get = parseObject

parseInt :: A.Parser Int
parseInt = do
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

parseNil :: A.Parser ()
parseNil = do
  _ <- A.word8 0xC0
  return ()

parseBool :: A.Parser Bool
parseBool = do
  c <- A.anyWord8
  case c of
    0xC3 ->
      return True
    0xC2 ->
      return False
    _ ->
      fail $ printf "invlid bool tag: 0x%02X" c

parseDouble :: A.Parser Double
parseDouble = do
  c <- A.anyWord8
  case c of
    0xCA ->
      return . realToFrac . runGet getFloat32be . toLBS =<< A.take 4
    0xCB ->
      return . runGet getFloat64be . toLBS =<< A.take 8
    _ ->
      fail $ printf "invlid double tag: 0x%02X" c

parseRAW :: A.Parser B.ByteString
parseRAW = do
  c <- A.anyWord8
  case c of
    _ | c .&. 0xE0 == 0xA0 ->
      A.take . fromIntegral $ c .&. 0x1F
    0xDA ->
      A.take . fromIntegral =<< parseUint16
    0xDB ->
      A.take . fromIntegral =<< parseUint32
    _ ->
      fail $ printf "invlid raw tag: 0x%02X" c
  
parseArray :: ObjectGet a => A.Parser [a]
parseArray = do
  c <- A.anyWord8
  case c of
    _ | c .&. 0xF0 == 0x90 ->
      flip replicateM get . fromIntegral $ c .&. 0x0F
    0xDC ->
      flip replicateM get . fromIntegral =<< parseUint16
    0xDD ->
      flip replicateM get . fromIntegral =<< parseUint32
    _ ->
      fail $ printf "invlid array tag: 0x%02X" c

parseArrayVector :: ObjectGet a => A.Parser (V.Vector a)
parseArrayVector = do
  c <- A.anyWord8
  case c of
    _ | c .&. 0xF0 == 0x90 ->
      flip V.replicateM get . fromIntegral $ c .&. 0x0F
    0xDC ->
      flip V.replicateM get . fromIntegral =<< parseUint16
    0xDD ->
      flip V.replicateM get . fromIntegral =<< parseUint32
    _ ->
      fail $ printf "invlid array tag: 0x%02X" c

parseMap :: (ObjectGet k, ObjectGet v) => A.Parser [(k, v)]
parseMap = do
  c <- A.anyWord8
  case c of
    _ | c .&. 0xF0 == 0x80 ->
      flip replicateM parsePair . fromIntegral $ c .&. 0x0F
    0xDE ->
      flip replicateM parsePair . fromIntegral =<< parseUint16
    0xDF ->
      flip replicateM parsePair . fromIntegral =<< parseUint32
    _ ->
      fail $ printf "invlid map tag: 0x%02X" c

parseMapVector :: (ObjectGet k, ObjectGet v) => A.Parser (V.Vector (k, v))
parseMapVector = do
  c <- A.anyWord8
  case c of
    _ | c .&. 0xF0 == 0x80 ->
      flip V.replicateM parsePair . fromIntegral $ c .&. 0x0F
    0xDE ->
      flip V.replicateM parsePair . fromIntegral =<< parseUint16
    0xDF ->
      flip V.replicateM parsePair . fromIntegral =<< parseUint32
    _ ->
      fail $ printf "invlid map tag: 0x%02X" c

parseObject :: A.Parser Object
parseObject =
  A.choice
  [ liftM ObjectInteger parseInt
  , liftM (const ObjectNil) parseNil
  , liftM ObjectBool parseBool
  , liftM ObjectDouble parseDouble
  , liftM ObjectRAW parseRAW
  , liftM ObjectArray parseArray
  , liftM ObjectMap parseMap
  ]

parsePair :: (ObjectGet k, ObjectGet v) => A.Parser (k, v)
parsePair = do
  a <- get
  b <- get
  return (a, b)

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
