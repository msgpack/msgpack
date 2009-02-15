#ifndef MSGPACK_PACK_H__
#define MSGPACK_PACK_H__

#include <stddef.h>
#include <stdint.h>

typedef void (*msgpack_pack_callback_t)(void* data, const unsigned char* b, unsigned int i);

typedef struct {
	void* data;
	msgpack_pack_callback_t callback;
} msgpack_pack_t;

msgpack_pack_t* msgpack_pack_new(void* data, msgpack_pack_callback_t callback);
void msgpack_pack_free(msgpack_pack_t* ctx);

void msgpack_pack_int(msgpack_pack_t* ctx, int d);
void msgpack_pack_unsigned_int(msgpack_pack_t* ctx, unsigned int d);
void msgpack_pack_unsigned_int_8(msgpack_pack_t* ctx, uint8_t d);
void msgpack_pack_unsigned_int_16(msgpack_pack_t* ctx, uint16_t d);
void msgpack_pack_unsigned_int_32(msgpack_pack_t* ctx, uint32_t d);
void msgpack_pack_unsigned_int_64(msgpack_pack_t* ctx, uint64_t d);
void msgpack_pack_signed_int_8(msgpack_pack_t* ctx, int8_t d);
void msgpack_pack_signed_int_16(msgpack_pack_t* ctx, int16_t d);
void msgpack_pack_signed_int_32(msgpack_pack_t* ctx, int32_t d);
void msgpack_pack_signed_int_64(msgpack_pack_t* ctx, int64_t d);
void msgpack_pack_float(msgpack_pack_t* ctx, float d);
void msgpack_pack_double(msgpack_pack_t* ctx, double d);
void msgpack_pack_nil(msgpack_pack_t* ctx);
void msgpack_pack_true(msgpack_pack_t* ctx);
void msgpack_pack_false(msgpack_pack_t* ctx);
void msgpack_pack_array(msgpack_pack_t* ctx, unsigned int n);
void msgpack_pack_map(msgpack_pack_t* ctx, unsigned int n);
void msgpack_pack_string(msgpack_pack_t* ctx, const char* b);
void msgpack_pack_raw(msgpack_pack_t* ctx, const void* b, size_t l);

#endif /* msgpack/pack.h */

