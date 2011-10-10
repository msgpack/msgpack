{-# Language TypeSynonymInstances #-}
{-# Language FlexibleInstances #-}
{-# Language IncoherentInstances #-}
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
  -- Result,
  ) where

import Control.DeepSeq
import Control.Exception
import Control.Monad
import qualified Data.Attoparsec as A
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TL
import Data.Typeable

import Data.MessagePack.Assoc
import Data.MessagePack.Pack
import Data.MessagePack.Unpack
import Data.MessagePack.Internal.Utf8

-- | Object Representation of MessagePack data.
data Object
  = ObjectNil
  | ObjectBool Bool
  | ObjectInteger Int
  | ObjectFloat Float
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
      ObjectFloat f -> rnf f
      ObjectDouble d -> rnf d
      ObjectRAW bs -> bs `seq` ()
      ObjectArray a -> rnf a
      ObjectMap m -> rnf m


instance Unpackable Object where
  get =
    A.choice
    [ liftM ObjectInteger get
    , liftM (\() -> ObjectNil) get
    , liftM ObjectBool get
    , liftM ObjectFloat get
    , liftM ObjectDouble get
    , liftM ObjectRAW get
    , liftM ObjectArray get
    , liftM (ObjectMap . unAssoc) get
    ]

instance Packable Object where
  put obj =
    case obj of
      ObjectInteger n ->
        put n
      ObjectNil ->
        put ()
      ObjectBool b ->
        put b
      ObjectFloat f ->
        put f
      ObjectDouble d ->
        put d
      ObjectRAW raw ->
        put raw
      ObjectArray arr ->
        put arr
      ObjectMap m ->
        put $ Assoc m

-- | The class of types serializable to and from MessagePack object
class (Unpackable a, Packable a) => OBJECT a where
  -- | Encode a value to MessagePack object
  toObject :: a -> Object
  toObject = unpack . pack
  
  -- | Decode a value from MessagePack object
  fromObject :: Object -> a
  fromObject a =
    case tryFromObject a of
      Left err ->
        throw $ UnpackError err
      Right ret ->
        ret

  -- | Decode a value from MessagePack object
  tryFromObject :: Object -> Either String a
  tryFromObject = tryUnpack . pack

instance OBJECT Object where
  toObject = id
  tryFromObject = Right

tryFromObjectError :: Either String a
tryFromObjectError = Left "tryFromObject: cannot cast"

instance OBJECT () where
  toObject = const ObjectNil
  tryFromObject ObjectNil = Right ()
  tryFromObject _ = tryFromObjectError

instance OBJECT Int where
  toObject = ObjectInteger
  tryFromObject (ObjectInteger n) = Right n
  tryFromObject _ = tryFromObjectError

instance OBJECT Bool where
  toObject = ObjectBool
  tryFromObject (ObjectBool b) = Right b
  tryFromObject _ = tryFromObjectError

instance OBJECT Double where
  toObject = ObjectDouble
  tryFromObject (ObjectDouble d) = Right d
  tryFromObject _ = tryFromObjectError

instance OBJECT Float where
  toObject = ObjectFloat
  tryFromObject (ObjectFloat f) = Right f
  tryFromObject _ = tryFromObjectError

instance OBJECT String where
  toObject = toObject . encodeUtf8
  tryFromObject obj = liftM decodeUtf8 $ tryFromObject obj

instance OBJECT B.ByteString where
  toObject = ObjectRAW
  tryFromObject (ObjectRAW bs) = Right bs
  tryFromObject _ = tryFromObjectError

instance OBJECT BL.ByteString where
  toObject = ObjectRAW . fromLBS
  tryFromObject (ObjectRAW bs) = Right $ toLBS bs
  tryFromObject _ = tryFromObjectError

instance OBJECT T.Text where
  toObject = ObjectRAW . T.encodeUtf8
  tryFromObject (ObjectRAW bs) = Right $ T.decodeUtf8With skipChar bs
  tryFromObject _ = tryFromObjectError

instance OBJECT TL.Text where
  toObject = ObjectRAW . fromLBS . TL.encodeUtf8
  tryFromObject (ObjectRAW bs) = Right $ TL.decodeUtf8With skipChar $ toLBS bs
  tryFromObject _ = tryFromObjectError

instance OBJECT a => OBJECT [a] where
  toObject = ObjectArray . map toObject
  tryFromObject (ObjectArray arr) =
    mapM tryFromObject arr
  tryFromObject _ =
    tryFromObjectError

instance (OBJECT a1, OBJECT a2) => OBJECT (a1, a2) where
  toObject (a1, a2) = ObjectArray [toObject a1, toObject a2]
  tryFromObject (ObjectArray arr) =
    case arr of
      [o1, o2] -> do
        v1 <- tryFromObject o1
        v2 <- tryFromObject o2
        return (v1, v2)
      _ ->
        tryFromObjectError
  tryFromObject _ =
    tryFromObjectError

instance (OBJECT a1, OBJECT a2, OBJECT a3) => OBJECT (a1, a2, a3) where
  toObject (a1, a2, a3) = ObjectArray [toObject a1, toObject a2, toObject a3]
  tryFromObject (ObjectArray arr) =
    case arr of
      [o1, o2, o3] -> do
        v1 <- tryFromObject o1
        v2 <- tryFromObject o2
        v3 <- tryFromObject o3
        return (v1, v2, v3)
      _ ->
        tryFromObjectError
  tryFromObject _ =
    tryFromObjectError

instance (OBJECT a1, OBJECT a2, OBJECT a3, OBJECT a4) => OBJECT (a1, a2, a3, a4) where
  toObject (a1, a2, a3, a4) = ObjectArray [toObject a1, toObject a2, toObject a3, toObject a4]
  tryFromObject (ObjectArray arr) =
    case arr of
      [o1, o2, o3, o4] -> do
        v1 <- tryFromObject o1
        v2 <- tryFromObject o2
        v3 <- tryFromObject o3
        v4 <- tryFromObject o4
        return (v1, v2, v3, v4)
      _ ->
        tryFromObjectError
  tryFromObject _ =
    tryFromObjectError

instance (OBJECT a1, OBJECT a2, OBJECT a3, OBJECT a4, OBJECT a5) => OBJECT (a1, a2, a3, a4, a5) where
  toObject (a1, a2, a3, a4, a5) = ObjectArray [toObject a1, toObject a2, toObject a3, toObject a4, toObject a5]
  tryFromObject (ObjectArray arr) =
    case arr of
      [o1, o2, o3, o4, o5] -> do
        v1 <- tryFromObject o1
        v2 <- tryFromObject o2
        v3 <- tryFromObject o3
        v4 <- tryFromObject o4
        v5 <- tryFromObject o5
        return (v1, v2, v3, v4, v5)
      _ ->
        tryFromObjectError
  tryFromObject _ =
    tryFromObjectError

instance (OBJECT a1, OBJECT a2, OBJECT a3, OBJECT a4, OBJECT a5, OBJECT a6) => OBJECT (a1, a2, a3, a4, a5, a6) where
  toObject (a1, a2, a3, a4, a5, a6) = ObjectArray [toObject a1, toObject a2, toObject a3, toObject a4, toObject a5, toObject a6]
  tryFromObject (ObjectArray arr) =
    case arr of
      [o1, o2, o3, o4, o5, o6] -> do
        v1 <- tryFromObject o1
        v2 <- tryFromObject o2
        v3 <- tryFromObject o3
        v4 <- tryFromObject o4
        v5 <- tryFromObject o5
        v6 <- tryFromObject o6
        return (v1, v2, v3, v4, v5, v6)
      _ ->
        tryFromObjectError
  tryFromObject _ =
    tryFromObjectError

instance (OBJECT a1, OBJECT a2, OBJECT a3, OBJECT a4, OBJECT a5, OBJECT a6, OBJECT a7) => OBJECT (a1, a2, a3, a4, a5, a6, a7) where
  toObject (a1, a2, a3, a4, a5, a6, a7) = ObjectArray [toObject a1, toObject a2, toObject a3, toObject a4, toObject a5, toObject a6, toObject a7]
  tryFromObject (ObjectArray arr) =
    case arr of
      [o1, o2, o3, o4, o5, o6, o7] -> do
        v1 <- tryFromObject o1
        v2 <- tryFromObject o2
        v3 <- tryFromObject o3
        v4 <- tryFromObject o4
        v5 <- tryFromObject o5
        v6 <- tryFromObject o6
        v7 <- tryFromObject o7
        return (v1, v2, v3, v4, v5, v6, v7)
      _ ->
        tryFromObjectError
  tryFromObject _ =
    tryFromObjectError

instance (OBJECT a1, OBJECT a2, OBJECT a3, OBJECT a4, OBJECT a5, OBJECT a6, OBJECT a7, OBJECT a8) => OBJECT (a1, a2, a3, a4, a5, a6, a7, a8) where
  toObject (a1, a2, a3, a4, a5, a6, a7, a8) = ObjectArray [toObject a1, toObject a2, toObject a3, toObject a4, toObject a5, toObject a6, toObject a7, toObject a8]
  tryFromObject (ObjectArray arr) =
    case arr of
      [o1, o2, o3, o4, o5, o6, o7, o8] -> do
        v1 <- tryFromObject o1
        v2 <- tryFromObject o2
        v3 <- tryFromObject o3
        v4 <- tryFromObject o4
        v5 <- tryFromObject o5
        v6 <- tryFromObject o6
        v7 <- tryFromObject o7
        v8 <- tryFromObject o8
        return (v1, v2, v3, v4, v5, v6, v7, v8)
      _ ->
        tryFromObjectError
  tryFromObject _ =
    tryFromObjectError

instance (OBJECT a1, OBJECT a2, OBJECT a3, OBJECT a4, OBJECT a5, OBJECT a6, OBJECT a7, OBJECT a8, OBJECT a9) => OBJECT (a1, a2, a3, a4, a5, a6, a7, a8, a9) where
  toObject (a1, a2, a3, a4, a5, a6, a7, a8, a9) = ObjectArray [toObject a1, toObject a2, toObject a3, toObject a4, toObject a5, toObject a6, toObject a7, toObject a8, toObject a9]
  tryFromObject (ObjectArray arr) =
    case arr of
      [o1, o2, o3, o4, o5, o6, o7, o8, o9] -> do
        v1 <- tryFromObject o1
        v2 <- tryFromObject o2
        v3 <- tryFromObject o3
        v4 <- tryFromObject o4
        v5 <- tryFromObject o5
        v6 <- tryFromObject o6
        v7 <- tryFromObject o7
        v8 <- tryFromObject o8
        v9 <- tryFromObject o9
        return (v1, v2, v3, v4, v5, v6, v7, v8, v9)
      _ ->
        tryFromObjectError
  tryFromObject _ =
    tryFromObjectError

instance (OBJECT a, OBJECT b) => OBJECT (Assoc [(a,b)]) where
  toObject =
    ObjectMap . map (\(a, b) -> (toObject a, toObject b)) . unAssoc
  tryFromObject (ObjectMap mem) = do
    liftM Assoc $ mapM (\(a, b) -> liftM2 (,) (tryFromObject a) (tryFromObject b)) mem
  tryFromObject _ =
    tryFromObjectError

instance OBJECT a => OBJECT (Maybe a) where
  toObject (Just a) = toObject a
  toObject Nothing = ObjectNil
  
  tryFromObject ObjectNil = return Nothing
  tryFromObject obj = liftM Just $ tryFromObject obj

