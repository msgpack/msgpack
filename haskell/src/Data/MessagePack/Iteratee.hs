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
  -- * Convert Parser to Iteratee
  parserToIteratee,
  ) where

import qualified Data.Attoparsec as A
import qualified Data.ByteString as B
import qualified Data.Iteratee as I

import Data.MessagePack.Parser

-- | Deserialize a value
getI :: (Monad m, ObjectGet a) => I.Iteratee B.ByteString m a
getI = parserToIteratee get

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
