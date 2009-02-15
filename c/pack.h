/*
 * MessagePack for C packing routine
 *
 * Copyright (C) 2008-2009 FURUHASHI Sadayuki
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
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif


typedef int (*msgpack_pack_write_t)(void* data, const char* buf, unsigned int len);

typedef struct {
	void* data;
	msgpack_pack_write_t callback;
} msgpack_pack_t;

void msgpack_pack_init(msgpack_pack_t* ctx, void* data, msgpack_pack_write_t callback);

msgpack_pack_t* msgpack_pack_new(void* data, msgpack_pack_write_t callback);
void msgpack_pack_free(msgpack_pack_t* ctx);

int msgpack_pack_short(msgpack_pack_t* ctx, short d);
int msgpack_pack_int(msgpack_pack_t* ctx, int d);
int msgpack_pack_long(msgpack_pack_t* ctx, long d);
int msgpack_pack_long_long(msgpack_pack_t* ctx, long long d);
int msgpack_pack_unsigned_short(msgpack_pack_t* ctx, unsigned short d);
int msgpack_pack_unsigned_int(msgpack_pack_t* ctx, unsigned int d);
int msgpack_pack_unsigned_long(msgpack_pack_t* ctx, unsigned long d);
int msgpack_pack_unsigned_long_long(msgpack_pack_t* ctx, unsigned long long d);

int msgpack_pack_uint8(msgpack_pack_t* ctx, uint8_t d);
int msgpack_pack_uint16(msgpack_pack_t* ctx, uint16_t d);
int msgpack_pack_uint32(msgpack_pack_t* ctx, uint32_t d);
int msgpack_pack_uint64(msgpack_pack_t* ctx, uint64_t d);
int msgpack_pack_int8(msgpack_pack_t* ctx, int8_t d);
int msgpack_pack_int16(msgpack_pack_t* ctx, int16_t d);
int msgpack_pack_int32(msgpack_pack_t* ctx, int32_t d);
int msgpack_pack_int64(msgpack_pack_t* ctx, int64_t d);

int msgpack_pack_float(msgpack_pack_t* ctx, float d);
int msgpack_pack_double(msgpack_pack_t* ctx, double d);

int msgpack_pack_nil(msgpack_pack_t* ctx);
int msgpack_pack_true(msgpack_pack_t* ctx);
int msgpack_pack_false(msgpack_pack_t* ctx);

int msgpack_pack_array(msgpack_pack_t* ctx, unsigned int n);

int msgpack_pack_map(msgpack_pack_t* ctx, unsigned int n);

int msgpack_pack_raw(msgpack_pack_t* ctx, size_t l);
int msgpack_pack_raw_body(msgpack_pack_t* ctx, const void* b, size_t l);



#define msgpack_pack_inline_func(name) \
	inline int msgpack_pack ## name

#define msgpack_pack_inline_func_cint(name) \
	inline int msgpack_pack ## name

#define msgpack_pack_user msgpack_pack_t*

#define msgpack_pack_append_buffer(user, buf, len) \
	return (*(user)->callback)((user)->data, (const char*)buf, len)

#include "msgpack/pack_template.h"

inline void msgpack_pack_init(msgpack_pack_t* ctx, void* data, msgpack_pack_write_t callback)
{
	ctx->data = data;
	ctx->callback = callback;
}

inline msgpack_pack_t* msgpack_pack_new(void* data, msgpack_pack_write_t callback)
{
	msgpack_pack_t* ctx = (msgpack_pack_t*)calloc(1, sizeof(msgpack_pack_t));
	if(!ctx) { return NULL; }
	msgpack_pack_init(ctx, data, callback);
	return ctx;
}

inline void msgpack_pack_free(msgpack_pack_t* ctx)
{
	free(ctx);
}


#ifdef __cplusplus
}
#endif

#endif /* msgpack/pack.h */

