#include <msgpack.h>

void msgpack_sbuffer_init_wrap(msgpack_sbuffer* sbuf)
{
  msgpack_sbuffer_init(sbuf);
}

void msgpack_sbuffer_destroy_wrap(msgpack_sbuffer* sbuf)
{
  msgpack_sbuffer_destroy(sbuf);
}

int msgpack_sbuffer_write_wrap(void* data, const char* buf, unsigned int len)
{
  return msgpack_sbuffer_write(data, buf, len);
}

msgpack_packer* msgpack_packer_new_wrap(void *data, msgpack_packer_write callback)
{
  return msgpack_packer_new(data, callback);
}

void msgpack_packer_free_wrap(msgpack_packer* pk)
{
  msgpack_packer_free(pk);
}

int msgpack_pack_uint8_wrap(msgpack_packer* pk, uint8_t d)
{
  return msgpack_pack_uint8(pk, d);
}

int msgpack_pack_uint16_wrap(msgpack_packer* pk, uint16_t d)
{
  return msgpack_pack_uint16(pk, d);
}

int msgpack_pack_uint32_wrap(msgpack_packer* pk, uint32_t d)
{
  return msgpack_pack_uint32(pk, d);
}

int msgpack_pack_uint64_wrap(msgpack_packer* pk, uint64_t d)
{
  return msgpack_pack_uint64(pk, d);
}

int msgpack_pack_int8_wrap(msgpack_packer* pk, int8_t d)
{
  return msgpack_pack_int8(pk, d);
}

int msgpack_pack_int16_wrap(msgpack_packer* pk, int16_t d)
{
  return msgpack_pack_int16(pk, d);
}

int msgpack_pack_int32_wrap(msgpack_packer* pk, int32_t d)
{
  return msgpack_pack_int32(pk, d);
}

int msgpack_pack_int64_wrap(msgpack_packer* pk, int64_t d)
{
  return msgpack_pack_int64(pk, d);
}

int msgpack_pack_double_wrap(msgpack_packer* pk, double d)
{
  return msgpack_pack_double(pk, d);
}

int msgpack_pack_nil_wrap(msgpack_packer* pk)
{
  return msgpack_pack_nil(pk);
}

int msgpack_pack_true_wrap(msgpack_packer* pk)
{
  return msgpack_pack_true(pk);
}

int msgpack_pack_false_wrap(msgpack_packer* pk)
{
  return msgpack_pack_false(pk);
}

int msgpack_pack_array_wrap(msgpack_packer* pk, unsigned int n)
{
  return msgpack_pack_array(pk, n);
}

int msgpack_pack_map_wrap(msgpack_packer* pk, unsigned int n)
{
  return msgpack_pack_map(pk, n);
}

int msgpack_pack_raw_wrap(msgpack_packer* pk, size_t l)
{
  return msgpack_pack_raw(pk, l);
}

int msgpack_pack_raw_body_wrap(msgpack_packer* pk, const void *b, size_t l)
{
  return msgpack_pack_raw_body(pk, b, l);
}

bool msgpack_unpacker_reserve_buffer_wrap(msgpack_unpacker *mpac, size_t size)
{
  return msgpack_unpacker_reserve_buffer(mpac, size);
}

char *msgpack_unpacker_buffer_wrap(msgpack_unpacker *mpac)
{
  return msgpack_unpacker_buffer(mpac);
}

size_t msgpack_unpacker_buffer_capacity_wrap(const msgpack_unpacker *mpac)
{
  return msgpack_unpacker_buffer_capacity(mpac);
}

void msgpack_unpacker_buffer_consumed_wrap(msgpack_unpacker *mpac, size_t size)
{
  msgpack_unpacker_buffer_consumed(mpac, size);
}

void msgpack_unpacker_data_wrap(msgpack_unpacker *mpac, msgpack_object *obj)
{
  *obj=msgpack_unpacker_data(mpac);
}

size_t msgpack_unpacker_message_size_wrap(const msgpack_unpacker *mpac)
{
  return msgpack_unpacker_message_size(mpac);
}

