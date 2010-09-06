--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Iteratee
-- Copyright : (c) Hideyuki Tanaka, 2009-2010
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- MessagePack Deserializer interface to @Data.Iteratee@
--
--------------------------------------------------------------------

module Data.MessagePack.Iteratee(
  -- * Iteratee version of deserializer
  getI,
  -- * Non Blocking Enumerator
  enumHandleNonBlocking,
  -- * Convert Parser to Iteratee
  parserToIteratee,
  ) where

import Control.Exception
import Control.Monad.IO.Class
import qualified Data.Attoparsec as A
import qualified Data.ByteString as B
import qualified Data.Iteratee as I
import System.IO

import Data.MessagePack.Parser

-- | Deserialize a value
getI :: (Monad m, ObjectGet a) => I.Iteratee B.ByteString m a
getI = parserToIteratee get

-- | Enumerator
enumHandleNonBlocking :: MonadIO m => Int -> Handle -> I.Enumerator B.ByteString m a
enumHandleNonBlocking bufSize h =
  I.enumFromCallback $ readSome bufSize h

readSome :: MonadIO m => Int -> Handle -> m (Either SomeException (Bool, B.ByteString))
readSome bufSize h = liftIO $ do
  ebs <- try $ hGetSome bufSize h
  case ebs of
    Left exc ->
      return $ Left (exc :: SomeException)
    Right bs | B.null bs ->
      return $ Right (False, B.empty)
    Right bs ->
      return $ Right (True, bs)

hGetSome :: Int -> Handle -> IO B.ByteString
hGetSome bufSize h = do
  bs <- B.hGetNonBlocking h bufSize
  if B.null bs
    then do
    hd <- B.hGet h 1
    if B.null hd
      then do
      return B.empty
      else do
      rest <- B.hGetNonBlocking h (bufSize - 1)
      return $ B.cons (B.head hd) rest
    else do
    return bs

-- | Convert Parser to Iteratee
parserToIteratee :: Monad m => A.Parser a -> I.Iteratee B.ByteString m a
parserToIteratee p = I.icont (itr (A.parse p)) Nothing
  where
    itr pcont s = case s of
      I.EOF _ ->
        I.throwErr (I.setEOF s)
      I.Chunk bs ->
        case pcont bs of
          A.Fail _ _ msg ->
            I.throwErr (I.iterStrExc msg)
          A.Partial cont ->
            I.icont (itr cont) Nothing
          A.Done remain ret ->
            I.idone ret (I.Chunk remain)
