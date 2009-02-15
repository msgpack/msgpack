/*
 * MessagePack for C unpacking routine
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
#ifndef MSGPACK_UNPACK_H__
#define MSGPACK_UNPACK_H__

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif


typedef struct {
	void* (*unpack_uint8)(void* data, uint8_t d);
	void* (*unpack_uint16)(void* data, uint16_t d);
	void* (*unpack_uint32)(void* data, uint32_t d);
	void* (*unpack_uint64)(void* data, uint64_t d);
	void* (*unpack_int8)(void* data, int8_t d);
	void* (*unpack_int16)(void* data, int16_t d);
	void* (*unpack_int32)(void* data, int32_t d);
	void* (*unpack_int64)(void* data, int64_t d);
	void* (*unpack_float)(void* data, float d);
	void* (*unpack_double)(void* data, double d);
	void* (*unpack_nil)(void* data);
	void* (*unpack_true)(void* data);
	void* (*unpack_false)(void* data);
	void* (*unpack_array)(void* data, unsigned int n);
	 void (*unpack_array_item)(void* data, void* c, void* o);
	void* (*unpack_map)(void* data, unsigned int n);
	void (*unpack_map_item)(void* data, void* c, void* k, void* v);
	void* (*unpack_raw)(void* data, const char* b, const char* p, unsigned int l);
} msgpack_unpack_callback;

typedef struct {
	void* data;
	msgpack_unpack_callback callback;
} msgpack_unpack_t;

msgpack_unpack_t* msgpack_unpack_new(void* data, msgpack_unpack_callback* callback);
void msgpack_unpack_free(msgpack_unpack_t* ctx);

int msgpack_unpack_execute(msgpack_unpack_t* ctx,
		const char* data, size_t len, size_t* off);
void* msgpack_unpack_data(msgpack_unpack_t* ctx);
void msgpack_unpack_reset(msgpack_unpack_t* ctx);


#ifdef __cplusplus
}
#endif

#endif /* msgpack/unpack.h */

