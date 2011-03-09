{-# Language DeriveDataTypeable #-}
{-# Language GeneralizedNewtypeDeriving #-}

--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Assoc
-- Copyright : (c) Daiki Handa, 2010
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- MessagePack map labeling type
--
--------------------------------------------------------------------

module Data.MessagePack.Assoc (
  Assoc(..)
  ) where

import Control.DeepSeq
import Data.Typeable

-- not defined for general Functor for performance reason.
-- (ie. you would want to write custom instances for each type using specialized mapM-like functions)
newtype Assoc a=Assoc{unAssoc :: a} deriving(Show,Eq,Ord,Typeable,NFData)

