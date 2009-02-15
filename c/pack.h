/*
 * MessagePack packing routine for C
 *
 * Copyright (C) 2008 FURUHASHI Sadayuki
 *
 *    Licensed under the Apache License, Version 2.0 (the "License");
 *    you may not use this file except in compliance with the License.
 *    You may obtain a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 *    Unless required by applicable law or agreed to in writing, software
 *    distributed under the License is distributed on an "AS IS" BASIS,
 *    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *    See the License for the specific language governing permissions and
 *    limitations under the License.
 */
#ifndef MSGPACK_PACK_H__
#define MSGPACK_PACK_H__

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif


typedef void (*msgpack_pack_append_buffer_t)(void* data, const char* b, unsigned int i);

typedef struct {
	void* data;
	msgpack_pack_append_buffer_t callback;
} msgpack_pack_t;

msgpack_pack_t* msgpack_pack_new(void* data, msgpack_pack_append_buffer_t callback);

void msgpack_pack_free(msgpack_pack_t* ctx);

void msgpack_pack_int(msgpack_pack_t* ctx, int d);
void msgpack_pack_unsigned_int(msgpack_pack_t* ctx, unsigned int d);
void msgpack_pack_uint8(msgpack_pack_t* ctx, uint8_t d);
void msgpack_pack_uint16(msgpack_pack_t* ctx, uint16_t d);
void msgpack_pack_uint32(msgpack_pack_t* ctx, uint32_t d);
void msgpack_pack_uint64(msgpack_pack_t* ctx, uint64_t d);
void msgpack_pack_int8(msgpack_pack_t* ctx, int8_t d);
void msgpack_pack_int16(msgpack_pack_t* ctx, int16_t d);
void msgpack_pack_int32(msgpack_pack_t* ctx, int32_t d);
void msgpack_pack_int64(msgpack_pack_t* ctx, int64_t d);
void msgpack_pack_float(msgpack_pack_t* ctx, float d);
void msgpack_pack_double(msgpack_pack_t* ctx, double d);
void msgpack_pack_nil(msgpack_pack_t* ctx);
void msgpack_pack_true(msgpack_pack_t* ctx);
void msgpack_pack_false(msgpack_pack_t* ctx);
void msgpack_pack_array(msgpack_pack_t* ctx, unsigned int n);
void msgpack_pack_map(msgpack_pack_t* ctx, unsigned int n);
void msgpack_pack_string(msgpack_pack_t* ctx, const char* b);
void msgpack_pack_raw(msgpack_pack_t* ctx, const void* b, size_t l);


#ifdef __cplusplus
}
#endif

#endif /* msgpack/pack.h */

