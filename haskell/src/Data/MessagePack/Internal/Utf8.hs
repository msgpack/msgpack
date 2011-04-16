module Data.MessagePack.Internal.Utf8 (
  encodeUtf8,
  decodeUtf8,
  skipChar,
  toLBS,
  fromLBS,
  ) where

import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Encoding.Error as T

encodeUtf8 :: String -> B.ByteString
encodeUtf8 = T.encodeUtf8 . T.pack

decodeUtf8 :: B.ByteString -> String
decodeUtf8 = T.unpack . T.decodeUtf8With skipChar

skipChar :: T.OnDecodeError
skipChar _ _ = Nothing

toLBS :: B.ByteString -> BL.ByteString
toLBS bs = BL.fromChunks [bs]

fromLBS :: BL.ByteString -> B.ByteString
fromLBS = B.concat . BL.toChunks
