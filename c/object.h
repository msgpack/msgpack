/*
 * MessagePack for C dynamic typing routine
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
#ifndef MSGPACK_OBJECT_H__
#define MSGPACK_OBJECT_H__

#include "msgpack/zone.h"
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif


typedef enum {
	MSGPACK_OBJECT_NIL					= 0x01,
	MSGPACK_OBJECT_BOOLEAN				= 0x02,
	MSGPACK_OBJECT_POSITIVE_INTEGER		= 0x03,
	MSGPACK_OBJECT_NEGATIVE_INTEGER		= 0x04,
	MSGPACK_OBJECT_DOUBLE				= 0x05,
	MSGPACK_OBJECT_RAW					= 0x06,
	MSGPACK_OBJECT_ARRAY				= 0x07,
	MSGPACK_OBJECT_MAP					= 0x08,
} msgpack_object_type;

struct _msgpack_object;

struct _msgpack_object_kv;

typedef struct {
	uint32_t size;
	struct _msgpack_object* ptr;
} msgpack_object_array;

typedef struct {
	uint32_t size;
	struct _msgpack_object_kv* ptr;
} msgpack_object_map;

typedef struct {
	uint32_t size;
	const char* ptr;
} msgpack_object_raw;

typedef union {
	bool boolean;
	uint64_t u64;
	int64_t  i64;
	double   dec;
	msgpack_object_array array;
	msgpack_object_map map;
	msgpack_object_raw raw;
} msgpack_object_union;

typedef struct _msgpack_object {
	msgpack_object_type type;
	msgpack_object_union via;
} msgpack_object;

typedef struct _msgpack_object_kv {
	msgpack_object key;
	msgpack_object val;
} msgpack_object_kv;

typedef enum {
	MSGPACK_OBJECT_PARSE_SUCCESS		=  0,
	MSGPACK_OBJECT_EXTRA_BYTES			=  1,
	MSGPACK_OBJECT_INSUFFICIENT_BYTES	= -1,
	MSGPACK_OBJECT_PARSE_ERROR			= -2,
} msgpack_object_unpack_return;

msgpack_object_unpack_return
msgpack_object_unpack(const char* data, size_t len, size_t* off,
		msgpack_zone* z, msgpack_object* result);


#ifdef __cplusplus
}
#endif

#endif /* msgpack/object.h */

