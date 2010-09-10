{-# Language TypeSynonymInstances #-}
{-# Language FlexibleInstances #-}
{-# Language OverlappingInstances #-}
{-# Language DeriveDataTypeable #-}

--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Object
-- Copyright : (c) Hideyuki Tanaka, 2009-2010
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- MessagePack object definition
--
--------------------------------------------------------------------

module Data.MessagePack.Object(
  -- * MessagePack Object
  Object(..),
  
  -- * Serialization to and from Object
  OBJECT(..),
  Result,
  ) where

import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans.Error ()
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C8
import Data.Typeable

-- | Object Representation of MessagePack data.
data Object =
  ObjectNil
  | ObjectBool Bool
  | ObjectInteger Int
  | ObjectDouble Double
  | ObjectRAW B.ByteString
  | ObjectArray [Object]
  | ObjectMap [(Object, Object)]
  deriving (Show, Eq, Ord, Typeable)

instance NFData Object where
  rnf obj =
    case obj of
      ObjectNil -> ()
      ObjectBool b -> rnf b
      ObjectInteger n -> rnf n
      ObjectDouble d -> rnf d
      ObjectRAW bs -> bs `seq` ()
      ObjectArray a -> rnf a
      ObjectMap m -> rnf m

-- | The class of types serializable to and from MessagePack object
class OBJECT a where
  -- | Encode a value to MessagePack object
  toObject :: a -> Object
  -- | Decode a value from MessagePack object
  fromObject :: Object -> Result a

-- | A type for parser results
type Result a = Either String a

instance OBJECT Object where
  toObject = id
  fromObject = Right

fromObjectError :: String
fromObjectError = "fromObject: cannot cast"

instance OBJECT () where
  toObject = const ObjectNil
  fromObject ObjectNil = Right ()
  fromObject _ = Left fromObjectError

instance OBJECT Int where
  toObject = ObjectInteger
  fromObject (ObjectInteger n) = Right n
  fromObject _ = Left fromObjectError

instance OBJECT Bool where
  toObject = ObjectBool
  fromObject (ObjectBool b) = Right b
  fromObject _ = Left fromObjectError

instance OBJECT Double where
  toObject = ObjectDouble
  fromObject (ObjectDouble d) = Right d
  fromObject _ = Left fromObjectError

instance OBJECT B.ByteString where
  toObject = ObjectRAW
  fromObject (ObjectRAW bs) = Right bs
  fromObject _ = Left fromObjectError

instance OBJECT String where
  toObject = toObject . C8.pack
  fromObject obj = liftM C8.unpack $ fromObject obj

instance OBJECT a => OBJECT [a] where
  toObject = ObjectArray . map toObject
  fromObject (ObjectArray arr) =
    mapM fromObject arr
  fromObject _ =
    Left fromObjectError

instance (OBJECT a, OBJECT b) => OBJECT [(a, b)] where
  toObject =
    ObjectMap . map (\(a, b) -> (toObject a, toObject b))
  fromObject (ObjectMap mem) = do
    mapM (\(a, b) -> liftM2 (,) (fromObject a) (fromObject b)) mem
  fromObject _ =
    Left fromObjectError

instance OBJECT a => OBJECT (Maybe a) where
  toObject (Just a) = toObject a
  toObject Nothing = ObjectNil
  
  fromObject ObjectNil = return Nothing
  fromObject obj = liftM Just $ fromObject obj
