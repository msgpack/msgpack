{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}

--------------------------------------------------------------------
-- |
-- Module    : Data.MessagePack.Base
-- Copyright : (c) Hideyuki Tanaka, 2009
-- License   : BSD3
--
-- Maintainer:  tanaka.hideyuki@gmail.com
-- Stability :  experimental
-- Portability: portable
--
-- Low Level Interface to MessagePack C API
--
--------------------------------------------------------------------

module Data.MessagePack.Base(
  -- * Simple Buffer
  SimpleBuffer,
  newSimpleBuffer,
  simpleBufferData,
  
  -- * Serializer
  Packer,
  newPacker,
  
  packU8,
  packU16,
  packU32,
  packU64,  
  packS8,
  packS16,
  packS32,
  packS64,
  
  packTrue,
  packFalse,
  
  packInt,
  packDouble,
  packNil,
  packBool,
  
  packArray,
  packMap,
  packRAW,
  packRAWBody,
  packRAW',
  
  -- * Stream Deserializer
  Unpacker,
  defaultInitialBufferSize,
  newUnpacker,
  unpackerReserveBuffer,
  unpackerBuffer,
  unpackerBufferCapacity,
  unpackerBufferConsumed,
  unpackerFeed,
  unpackerExecute,
  unpackerData,
  unpackerReleaseZone,
  unpackerResetZone,
  unpackerReset,
  unpackerMessageSize,
  
  -- * MessagePack Object
  Object(..),
  packObject,
  
  UnpackReturn(..),
  unpackObject,
  
  -- * Memory Zone
  Zone,
  newZone,
  freeZone,
  withZone,
  ) where

import Control.Exception
import Control.Monad
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS hiding (pack, unpack)
import Data.Int
import Data.Word
import Foreign.C
import Foreign.Concurrent
import Foreign.ForeignPtr hiding (newForeignPtr)
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable

#include <msgpack.h>

type SimpleBuffer = ForeignPtr ()

type WriteCallback = Ptr () -> CString -> CUInt -> IO CInt

-- | Create a new Simple Buffer. It will be deleted automatically.
newSimpleBuffer :: IO SimpleBuffer
newSimpleBuffer = do
  ptr <- mallocBytes (#size msgpack_sbuffer)
  fptr <- newForeignPtr ptr $ do
    msgpack_sbuffer_destroy ptr
    free ptr
  withForeignPtr fptr $ \p ->
    msgpack_sbuffer_init p
  return fptr

-- | Get data of Simple Buffer.
simpleBufferData :: SimpleBuffer -> IO ByteString
simpleBufferData sb =
  withForeignPtr sb $ \ptr -> do
    size <- (#peek msgpack_sbuffer, size) ptr
    dat  <- (#peek msgpack_sbuffer, data) ptr
    BS.packCStringLen (dat, fromIntegral (size :: CSize))

foreign import ccall "msgpack_sbuffer_init_wrap" msgpack_sbuffer_init ::
  Ptr () -> IO ()

foreign import ccall "msgpack_sbuffer_destroy_wrap" msgpack_sbuffer_destroy ::
  Ptr () -> IO ()

foreign import ccall "msgpack_sbuffer_write_wrap" msgpack_sbuffer_write ::
  WriteCallback

type Packer = ForeignPtr ()

-- | Create new Packer. It will be deleted automatically.
newPacker :: SimpleBuffer -> IO Packer
newPacker sbuf = do
  cb <- wrap_callback msgpack_sbuffer_write
  ptr <- withForeignPtr sbuf $ \ptr ->
    msgpack_packer_new ptr cb
  fptr <- newForeignPtr ptr $ do
    msgpack_packer_free ptr
  return fptr

foreign import ccall "msgpack_packer_new_wrap" msgpack_packer_new ::
  Ptr () -> FunPtr WriteCallback -> IO (Ptr ())

foreign import ccall "msgpack_packer_free_wrap" msgpack_packer_free ::
  Ptr () -> IO ()

foreign import ccall "wrapper" wrap_callback ::
  WriteCallback -> IO (FunPtr WriteCallback)

packU8 :: Packer -> Word8 -> IO Int
packU8 pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_uint8 ptr n

foreign import ccall "msgpack_pack_uint8_wrap" msgpack_pack_uint8 ::
  Ptr () -> Word8 -> IO CInt

packU16 :: Packer -> Word16 -> IO Int
packU16 pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_uint16 ptr n

foreign import ccall "msgpack_pack_uint16_wrap" msgpack_pack_uint16 ::
  Ptr () -> Word16 -> IO CInt

packU32 :: Packer -> Word32 -> IO Int
packU32 pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_uint32 ptr n

foreign import ccall "msgpack_pack_uint32_wrap" msgpack_pack_uint32 ::
  Ptr () -> Word32 -> IO CInt

packU64 :: Packer -> Word64 -> IO Int
packU64 pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_uint64 ptr n

foreign import ccall "msgpack_pack_uint64_wrap" msgpack_pack_uint64 ::
  Ptr () -> Word64 -> IO CInt

packS8 :: Packer -> Int8 -> IO Int
packS8 pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_int8 ptr n

foreign import ccall "msgpack_pack_int8_wrap" msgpack_pack_int8 ::
  Ptr () -> Int8 -> IO CInt

packS16 :: Packer -> Int16 -> IO Int
packS16 pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_int16 ptr n

foreign import ccall "msgpack_pack_int16_wrap" msgpack_pack_int16 ::
  Ptr () -> Int16 -> IO CInt

packS32 :: Packer -> Int32 -> IO Int
packS32 pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_int32 ptr n

foreign import ccall "msgpack_pack_int32_wrap" msgpack_pack_int32 ::
  Ptr () -> Int32 -> IO CInt

packS64 :: Packer -> Int64 -> IO Int
packS64 pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_int64 ptr n

foreign import ccall "msgpack_pack_int64_wrap" msgpack_pack_int64 ::
  Ptr () -> Int64 -> IO CInt

-- | Pack an integral data.
packInt :: Integral a => Packer -> a -> IO Int
packInt pc n = packS64 pc $ fromIntegral n

-- | Pack a double data.
packDouble :: Packer -> Double -> IO Int
packDouble pc d =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_double ptr (realToFrac d)

foreign import ccall "msgpack_pack_double_wrap" msgpack_pack_double ::
  Ptr () -> CDouble -> IO CInt

-- | Pack a nil.
packNil :: Packer -> IO Int
packNil pc =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_nil ptr

foreign import ccall "msgpack_pack_nil_wrap" msgpack_pack_nil ::
  Ptr () -> IO CInt

packTrue :: Packer -> IO Int
packTrue pc =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_true ptr

foreign import ccall "msgpack_pack_true_wrap" msgpack_pack_true ::
  Ptr () -> IO CInt

packFalse :: Packer -> IO Int
packFalse pc =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_false ptr

foreign import ccall "msgpack_pack_false_wrap" msgpack_pack_false ::
  Ptr () -> IO CInt

-- | Pack a bool data.
packBool :: Packer -> Bool -> IO Int
packBool pc True  = packTrue pc
packBool pc False = packFalse pc

-- | 'packArray' @p n@ starts packing an array. 
-- Next @n@ data will consist this array.
packArray :: Packer -> Int -> IO Int
packArray pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_array ptr (fromIntegral n)

foreign import ccall "msgpack_pack_array_wrap" msgpack_pack_array ::
  Ptr () -> CUInt -> IO CInt

-- | 'packMap' @p n@ starts packing a map. 
-- Next @n@ pairs of data (2*n data) will consist this map.
packMap :: Packer -> Int -> IO Int
packMap pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_map ptr (fromIntegral n)

foreign import ccall "msgpack_pack_map_wrap" msgpack_pack_map ::
  Ptr () -> CUInt -> IO CInt

-- | 'packRAW' @p n@ starts packing a byte sequence. 
-- Next total @n@ bytes of 'packRAWBody' call will consist this sequence.
packRAW :: Packer -> Int -> IO Int
packRAW pc n =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
    msgpack_pack_raw ptr (fromIntegral n)

foreign import ccall "msgpack_pack_raw_wrap" msgpack_pack_raw ::
  Ptr () -> CSize -> IO CInt

-- | Pack a byte sequence.
packRAWBody :: Packer -> ByteString -> IO Int
packRAWBody pc bs =
  liftM fromIntegral $ withForeignPtr pc $ \ptr ->
  BS.useAsCStringLen bs $ \(str, len) ->
    msgpack_pack_raw_body ptr (castPtr str) (fromIntegral len)

foreign import ccall "msgpack_pack_raw_body_wrap" msgpack_pack_raw_body ::
  Ptr () -> Ptr () -> CSize -> IO CInt

-- | Pack a single byte stream. It calls 'packRAW' and 'packRAWBody'.
packRAW' :: Packer -> ByteString -> IO Int
packRAW' pc bs = do
  packRAW pc (BS.length bs)
  packRAWBody pc bs

type Unpacker = ForeignPtr ()

defaultInitialBufferSize :: Int
defaultInitialBufferSize = 32 * 1024 -- #const MSGPACK_UNPACKER_DEFAULT_INITIAL_BUFFER_SIZE

-- | 'newUnpacker' @initialBufferSize@ creates a new Unpacker. It will be deleted automatically.
newUnpacker :: Int -> IO Unpacker
newUnpacker initialBufferSize = do
  ptr <- msgpack_unpacker_new (fromIntegral initialBufferSize)
  fptr <- newForeignPtr ptr $ do
    msgpack_unpacker_free ptr
  return fptr

foreign import ccall "msgpack_unpacker_new" msgpack_unpacker_new ::
  CSize -> IO (Ptr ())

foreign import ccall "msgpack_unpacker_free" msgpack_unpacker_free ::
  Ptr() -> IO ()

-- | 'unpackerReserveBuffer' @up size@ reserves at least @size@ bytes of buffer.
unpackerReserveBuffer :: Unpacker -> Int -> IO Bool
unpackerReserveBuffer up size =
  withForeignPtr up $ \ptr ->
  liftM (/=0) $ msgpack_unpacker_reserve_buffer ptr (fromIntegral size)

foreign import ccall "msgpack_unpacker_reserve_buffer_wrap" msgpack_unpacker_reserve_buffer ::
  Ptr () -> CSize -> IO CChar

-- | Get a pointer of unpacker buffer.
unpackerBuffer :: Unpacker -> IO (Ptr CChar)
unpackerBuffer up =
  withForeignPtr up $ \ptr ->
  msgpack_unpacker_buffer ptr

foreign import ccall "msgpack_unpacker_buffer_wrap" msgpack_unpacker_buffer ::
  Ptr () -> IO (Ptr CChar)

-- | Get size of allocated buffer.
unpackerBufferCapacity :: Unpacker -> IO Int
unpackerBufferCapacity up =
  withForeignPtr up $ \ptr ->
  liftM fromIntegral $ msgpack_unpacker_buffer_capacity ptr

foreign import ccall "msgpack_unpacker_buffer_capacity_wrap" msgpack_unpacker_buffer_capacity ::
  Ptr () -> IO CSize

-- | 'unpackerBufferConsumed' @up size@ notices that writed @size@ bytes to buffer.
unpackerBufferConsumed :: Unpacker -> Int -> IO ()
unpackerBufferConsumed up size =
  withForeignPtr up $ \ptr ->
  msgpack_unpacker_buffer_consumed ptr (fromIntegral size)

foreign import ccall "msgpack_unpacker_buffer_consumed_wrap" msgpack_unpacker_buffer_consumed ::
  Ptr () -> CSize -> IO ()

-- | Write byte sequence to Unpacker. It is utility funciton, calls 'unpackerReserveBuffer', 'unpackerBuffer' and 'unpackerBufferConsumed'.
unpackerFeed :: Unpacker -> ByteString -> IO ()
unpackerFeed up bs =
  BS.useAsCStringLen bs $ \(str, len) -> do
    True <- unpackerReserveBuffer up len
    ptr <- unpackerBuffer up
    copyArray ptr str len
    unpackerBufferConsumed up len

-- | Execute deserializing. It returns 0 when buffer contains not enough bytes, returns 1 when succeeded, returns negative value when it failed.
unpackerExecute :: Unpacker -> IO Int
unpackerExecute up =
  withForeignPtr up $ \ptr ->
  liftM fromIntegral $ msgpack_unpacker_execute ptr

foreign import ccall "msgpack_unpacker_execute" msgpack_unpacker_execute ::
  Ptr () -> IO CInt

-- | Returns a deserialized object when 'unpackerExecute' returned 1.
unpackerData :: Unpacker -> IO Object
unpackerData up =
  withForeignPtr up $ \ptr ->
  allocaBytes (#size msgpack_object) $ \pobj -> do
    msgpack_unpacker_data ptr pobj
    peekObject pobj

foreign import ccall "msgpack_unpacker_data_wrap" msgpack_unpacker_data ::
  Ptr () -> Ptr () -> IO ()

-- | Release memory zone. The returned zone must be freed by calling 'freeZone'.
unpackerReleaseZone :: Unpacker -> IO Zone
unpackerReleaseZone up =
  withForeignPtr up $ \ptr ->
  msgpack_unpacker_release_zone ptr

foreign import ccall "msgpack_unpacker_release_zone" msgpack_unpacker_release_zone ::
  Ptr () -> IO (Ptr ())

-- | Free memory zone used by Unapcker.
unpackerResetZone :: Unpacker -> IO ()
unpackerResetZone up =
  withForeignPtr up $ \ptr ->
  msgpack_unpacker_reset_zone ptr

foreign import ccall "msgpack_unpacker_reset_zone" msgpack_unpacker_reset_zone ::
  Ptr () -> IO ()

-- | Reset Unpacker state except memory zone.
unpackerReset :: Unpacker -> IO ()
unpackerReset up =
  withForeignPtr up $ \ptr ->
  msgpack_unpacker_reset ptr

foreign import ccall "msgpack_unpacker_reset" msgpack_unpacker_reset ::
  Ptr () -> IO ()

-- | Returns number of bytes of sequence of deserializing object.
unpackerMessageSize :: Unpacker -> IO Int
unpackerMessageSize up =
  withForeignPtr up $ \ptr ->
  liftM fromIntegral $ msgpack_unpacker_message_size ptr

foreign import ccall "msgpack_unpacker_message_size_wrap" msgpack_unpacker_message_size ::
  Ptr () -> IO CSize

type Zone = Ptr ()

-- | Create a new memory zone. It must be freed manually.
newZone :: IO Zone
newZone =
  msgpack_zone_new (#const MSGPACK_ZONE_CHUNK_SIZE)

-- | Free a memory zone.
freeZone :: Zone -> IO ()
freeZone z =
  msgpack_zone_free z

-- | Create a memory zone, then execute argument, then free memory zone.
withZone :: (Zone -> IO a) -> IO a
withZone z =
  bracket newZone freeZone z

foreign import ccall "msgpack_zone_new" msgpack_zone_new ::
  CSize -> IO Zone

foreign import ccall "msgpack_zone_free" msgpack_zone_free ::
  Zone -> IO ()

-- | Object Representation of MessagePack data.
data Object =
  ObjectNil
  | ObjectBool Bool
  | ObjectInteger Int
  | ObjectDouble Double
  | ObjectRAW ByteString
  | ObjectArray [Object]
  | ObjectMap [(Object, Object)]
  deriving (Show)

peekObject :: Ptr a -> IO Object
peekObject ptr = do
  typ <- (#peek msgpack_object, type) ptr
  case (typ :: CInt) of
    (#const MSGPACK_OBJECT_NIL) ->
      return ObjectNil
    (#const MSGPACK_OBJECT_BOOLEAN) ->
      peekObjectBool ptr
    (#const MSGPACK_OBJECT_POSITIVE_INTEGER) ->
      peekObjectPositiveInteger ptr
    (#const MSGPACK_OBJECT_NEGATIVE_INTEGER) ->
      peekObjectNegativeInteger ptr
    (#const MSGPACK_OBJECT_DOUBLE) ->
      peekObjectDouble ptr
    (#const MSGPACK_OBJECT_RAW) ->
      peekObjectRAW ptr
    (#const MSGPACK_OBJECT_ARRAY) ->
      peekObjectArray ptr
    (#const MSGPACK_OBJECT_MAP) ->
      peekObjectMap ptr
    _ ->
      fail "peekObject: unknown object type"

peekObjectBool :: Ptr a -> IO Object
peekObjectBool ptr = do
  b <- (#peek msgpack_object, via.boolean) ptr
  return $ ObjectBool $ (b :: CUChar) /= 0

peekObjectPositiveInteger :: Ptr a -> IO Object
peekObjectPositiveInteger ptr = do
  n <- (#peek msgpack_object, via.u64) ptr
  return $ ObjectInteger $ fromIntegral (n :: Word64)

peekObjectNegativeInteger :: Ptr a -> IO Object
peekObjectNegativeInteger ptr = do
  n <- (#peek msgpack_object, via.i64) ptr
  return $ ObjectInteger $ fromIntegral (n :: Int64)

peekObjectDouble :: Ptr a -> IO Object
peekObjectDouble ptr = do
  d <- (#peek msgpack_object, via.dec) ptr
  return $ ObjectDouble $ realToFrac (d :: CDouble)

peekObjectRAW :: Ptr a -> IO Object
peekObjectRAW ptr = do
  size <- (#peek msgpack_object, via.raw.size) ptr
  p    <- (#peek msgpack_object, via.raw.ptr) ptr
  bs   <- BS.packCStringLen (p, fromIntegral (size :: Word32))
  return $ ObjectRAW bs

peekObjectArray :: Ptr a -> IO Object
peekObjectArray ptr = do
  size <- (#peek msgpack_object, via.array.size) ptr
  p    <- (#peek msgpack_object, via.array.ptr) ptr
  objs <- mapM (\i -> peekObject $ p `plusPtr`
                      ((#size msgpack_object) * i))
          [0..size-1]
  return $ ObjectArray objs

peekObjectMap :: Ptr a -> IO Object
peekObjectMap ptr = do
  size <- (#peek msgpack_object, via.map.size) ptr
  p    <- (#peek msgpack_object, via.map.ptr) ptr
  dat  <- mapM (\i -> peekObjectKV $ p `plusPtr`
                      ((#size msgpack_object_kv) * i))
          [0..size-1]
  return $ ObjectMap dat

peekObjectKV :: Ptr a -> IO (Object, Object)
peekObjectKV ptr = do
  k <- peekObject $ ptr `plusPtr` (#offset msgpack_object_kv, key)
  v <- peekObject $ ptr `plusPtr` (#offset msgpack_object_kv, val)
  return (k, v)

-- | Pack a Object.
packObject :: Packer -> Object -> IO ()
packObject pc ObjectNil = packNil pc >> return ()

packObject pc (ObjectBool b) = packBool pc b >> return ()

packObject pc (ObjectInteger n) = packInt pc n >> return ()

packObject pc (ObjectDouble d) = packDouble pc d >> return ()

packObject pc (ObjectRAW bs) = packRAW' pc bs >> return ()

packObject pc (ObjectArray ls) = do
  packArray pc (length ls)
  mapM_ (packObject pc) ls

packObject pc (ObjectMap ls) = do
  packMap pc (length ls)
  mapM_ (\(a, b) -> packObject pc a >> packObject pc b) ls

data UnpackReturn =
  UnpackContinue     -- ^ not enough bytes to unpack object
  | UnpackParseError -- ^ got invalid bytes
  | UnpackError      -- ^ other error
  deriving (Eq, Show)

-- | Unpack a single MessagePack object from byte sequence.
unpackObject :: Zone -> ByteString -> IO (Either UnpackReturn (Int, Object))
unpackObject z dat =
  allocaBytes (#size msgpack_object) $ \ptr ->
  BS.useAsCStringLen dat $ \(str, len) ->
  alloca $ \poff -> do
    ret <- msgpack_unpack str (fromIntegral len) poff z ptr
    case ret of
      (#const MSGPACK_UNPACK_SUCCESS) -> do
        off <- peek poff
        obj <- peekObject ptr
        return $ Right (fromIntegral off, obj)
      (#const MSGPACK_UNPACK_EXTRA_BYTES) -> do
        off <- peek poff
        obj <- peekObject ptr
        return $ Right (fromIntegral off, obj)
      (#const MSGPACK_UNPACK_CONTINUE) ->
        return $ Left UnpackContinue
      (#const MSGPACK_UNPACK_PARSE_ERROR) ->
        return $ Left UnpackParseError
      _ ->
        return $ Left UnpackError

foreign import ccall "msgpack_unpack" msgpack_unpack ::
  Ptr CChar -> CSize -> Ptr CSize -> Zone -> Ptr () -> IO CInt
