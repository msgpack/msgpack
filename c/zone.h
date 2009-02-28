/*
 * MessagePack for C memory pool implementation
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
#ifndef MSGPACK_ZONE_H__
#define MSGPACK_ZONE_H__

#include <stddef.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif


typedef struct msgpack_zone_chunk {
	size_t free;
	char* ptr;
	void* alloc;
} msgpack_zone_chunk;

typedef struct msgpack_zone_finalizer {
	void (*func)(void* data);
	void* data;
} msgpack_zone_finalizer;

typedef struct msgpack_zone_chunk_array {
	msgpack_zone_chunk* tail;
	msgpack_zone_chunk* end;
	msgpack_zone_chunk* array;
} msgpack_zone_chunk_array;

typedef struct msgpack_zone_finalizer_array {
	msgpack_zone_finalizer* tail;
	msgpack_zone_finalizer* end;
	msgpack_zone_finalizer* array;
} msgpack_zone_finalizer_array;

typedef struct msgpack_zone {
	msgpack_zone_chunk_array chunk_array;
	msgpack_zone_finalizer_array finalizer_array;
	size_t chunk_size;
} msgpack_zone;

#ifndef MSGPACK_ZONE_CHUNK_SIZE
#define MSGPACK_ZONE_CHUNK_SIZE 2048
#endif

bool msgpack_zone_init(msgpack_zone* zone, size_t chunk_size);
void msgpack_zone_destroy(msgpack_zone* zone);

msgpack_zone* msgpack_zone_new(size_t chunk_size);
void msgpack_zone_free(msgpack_zone* zone);

void* msgpack_zone_malloc(msgpack_zone* zone, size_t size);

bool msgpack_zone_push_finalizer(msgpack_zone* zone,
		void (*func)(void* data), void* data);

bool msgpack_zone_is_empty(msgpack_zone* zone);

void msgpack_zone_clear(msgpack_zone* zone);


#ifdef __cplusplus
}
#endif

#endif /* msgpack/zone.h */

