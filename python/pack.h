/*
 * MessagePack for Python packing routine
 *
 * Copyright (C) 2009 Naoki INADA
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

#if _MSC_VER
typedef signed char uint8_t;
typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int32_t;
typedef unsigned int uint32_t;
typedef long long int64_t;
typedef unsigned long long uint64_t;
#elif
#include <stdint.h>
#endif

#include <stddef.h>
#include <stdlib.h>
#include "msgpack/pack_define.h"
#include "msgpack/object.h"

#ifdef __cplusplus
extern "C" {
#endif


typedef int (*msgpack_packer_write)(void* data, const char* buf, unsigned int len);

typedef struct msgpack_packer {
	void* data;
	msgpack_packer_write callback;
} msgpack_packer;

static void msgpack_packer_init(msgpack_packer* pk, void* data, msgpack_packer_write callback);

static msgpack_packer* msgpack_packer_new(void* data, msgpack_packer_write callback);
static void msgpack_packer_free(msgpack_packer* pk);

static int msgpack_pack_short(msgpack_packer* pk, short d);
static int msgpack_pack_int(msgpack_packer* pk, int d);
static int msgpack_pack_long(msgpack_packer* pk, long d);
static int msgpack_pack_long_long(msgpack_packer* pk, long long d);
static int msgpack_pack_unsigned_short(msgpack_packer* pk, unsigned short d);
static int msgpack_pack_unsigned_int(msgpack_packer* pk, unsigned int d);
static int msgpack_pack_unsigned_long(msgpack_packer* pk, unsigned long d);
static int msgpack_pack_unsigned_long_long(msgpack_packer* pk, unsigned long long d);

static int msgpack_pack_uint8(msgpack_packer* pk, uint8_t d);
static int msgpack_pack_uint16(msgpack_packer* pk, uint16_t d);
static int msgpack_pack_uint32(msgpack_packer* pk, uint32_t d);
static int msgpack_pack_uint64(msgpack_packer* pk, uint64_t d);
static int msgpack_pack_int8(msgpack_packer* pk, int8_t d);
static int msgpack_pack_int16(msgpack_packer* pk, int16_t d);
static int msgpack_pack_int32(msgpack_packer* pk, int32_t d);
static int msgpack_pack_int64(msgpack_packer* pk, int64_t d);

static int msgpack_pack_float(msgpack_packer* pk, float d);
static int msgpack_pack_double(msgpack_packer* pk, double d);

static int msgpack_pack_nil(msgpack_packer* pk);
static int msgpack_pack_true(msgpack_packer* pk);
static int msgpack_pack_false(msgpack_packer* pk);

static int msgpack_pack_array(msgpack_packer* pk, unsigned int n);

static int msgpack_pack_map(msgpack_packer* pk, unsigned int n);

static int msgpack_pack_raw(msgpack_packer* pk, size_t l);
static int msgpack_pack_raw_body(msgpack_packer* pk, const void* b, size_t l);

int msgpack_pack_object(msgpack_packer* pk, msgpack_object d);



#define msgpack_pack_inline_func(name) \
	static inline int msgpack_pack ## name

#define msgpack_pack_inline_func_cint(name) \
	static inline int msgpack_pack ## name

#define msgpack_pack_user msgpack_packer*

#define msgpack_pack_append_buffer(user, buf, len) \
	return (*(user)->callback)((user)->data, (const char*)buf, len)

#include "msgpack/pack_template.h"

static inline void msgpack_packer_init(msgpack_packer* pk, void* data, msgpack_packer_write callback)
{
	pk->data = data;
	pk->callback = callback;
}

static inline msgpack_packer* msgpack_packer_new(void* data, msgpack_packer_write callback)
{
	msgpack_packer* pk = (msgpack_packer*)calloc(1, sizeof(msgpack_packer));
	if(!pk) { return NULL; }
	msgpack_packer_init(pk, data, callback);
	return pk;
}

static inline void msgpack_packer_free(msgpack_packer* pk)
{
	free(pk);
}


#ifdef __cplusplus
}
#endif

#endif /* msgpack/pack.h */

