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

#include "zone.h"
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif


/**
 * @defgroup msgpack_object Dynamically typed object
 * @ingroup msgpack
 * @{
 */

typedef enum {
	MSGPACK_OBJECT_NIL					= 0x00,
	MSGPACK_OBJECT_BOOLEAN				= 0x01,
	MSGPACK_OBJECT_POSITIVE_INTEGER		= 0x02,
	MSGPACK_OBJECT_NEGATIVE_INTEGER		= 0x03,
	MSGPACK_OBJECT_DOUBLE				= 0x04,
	MSGPACK_OBJECT_RAW					= 0x05,
	MSGPACK_OBJECT_ARRAY				= 0x06,
	MSGPACK_OBJECT_MAP					= 0x07,
} msgpack_object_type;


struct msgpack_object;
struct msgpack_object_kv;

typedef struct {
	uint32_t size;
	struct msgpack_object* ptr;
} msgpack_object_array;

typedef struct {
	uint32_t size;
	struct msgpack_object_kv* ptr;
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

typedef struct msgpack_object {
	msgpack_object_type type;
	msgpack_object_union via;
} msgpack_object;

typedef struct msgpack_object_kv {
	msgpack_object key;
	msgpack_object val;
} msgpack_object_kv;


void msgpack_object_print(FILE* out, msgpack_object o);

bool msgpack_object_equal(const msgpack_object x, const msgpack_object y);

/** @} */


#ifdef __cplusplus
}
#endif

#endif /* msgpack/object.h */

