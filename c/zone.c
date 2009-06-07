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
#include "msgpack/zone.h"
#include <stdlib.h>
#include <string.h>

static inline bool init_chunk_array(msgpack_zone_chunk_array* ca, size_t chunk_size)
{
	// glibcは72バイト以下のmallocが高速
	const size_t nfirst = (sizeof(msgpack_zone_chunk) < 72/2) ?
			72 / sizeof(msgpack_zone_chunk) : 8;

	msgpack_zone_chunk* array = (msgpack_zone_chunk*)malloc(
			sizeof(msgpack_zone_chunk) * nfirst);
	if(array == NULL) {
		return false;
	}

	const size_t sz = chunk_size;

	char* ptr = (char*)malloc(sz);
	if(ptr == NULL) {
		free(array);
		return NULL;
	}

	ca->tail  = array;
	ca->end   = array + nfirst;
	ca->array = array;

	array[0].free  = sz;
	array[0].ptr   = ptr;
	array[0].alloc = ptr;

	return true;
}

static inline void destroy_chunk_array(msgpack_zone_chunk_array* ca)
{
	msgpack_zone_chunk* chunk = ca->array;
	for(; chunk != ca->tail+1; ++chunk) {
		free(chunk->alloc);
	}

	free(ca->array);
}

static inline void clear_chunk_array(msgpack_zone_chunk_array* ca)
{
	msgpack_zone_chunk* chunk = ca->array + 1;
	for(; chunk != ca->tail+1; ++chunk) {
		free(chunk->alloc);
	}

	ca->tail = ca->array;

	ca->array[0].free += ca->array[0].ptr - (char*)ca->array[0].alloc;
	ca->array[0].ptr   = (char*)ca->array[0].alloc;
}

void* msgpack_zone_malloc_expand(msgpack_zone* zone, size_t size)
{
	msgpack_zone_chunk_array* const ca = &zone->chunk_array;

	msgpack_zone_chunk* chunk = ++ca->tail;

	if(chunk == ca->end) {
		// ca->arrayに空きがない
		// ca->arrayを拡張する

		const size_t nused = ca->end - ca->array;
		const size_t nnext = (ca->end - ca->array) * 2;

		chunk = (msgpack_zone_chunk*)realloc(ca->array,
				sizeof(msgpack_zone_chunk) * nnext);
		if(chunk == NULL) {
			return NULL;
		}

		ca->array        = chunk;
		ca->end          = chunk + nnext;
		chunk = ca->tail = chunk + nused;
	}

	size_t sz = zone->chunk_size;

	while(sz < size) {
		sz *= 2;
	}

	char* ptr = (char*)malloc(sz);
	if(ptr == NULL) {
		return NULL;
	}

	chunk->free  = sz - size;
	chunk->ptr   = ptr + size;
	chunk->alloc = ptr;

	return ptr;
}


static inline void init_finalizer_array(msgpack_zone_finalizer_array* fa)
{
	fa->tail  = NULL;
	fa->end   = NULL;
	fa->array = NULL;
}

static inline void call_finalizer_array(msgpack_zone_finalizer_array* fa)
{
	// 逆順に呼び出し
	msgpack_zone_finalizer* fin = fa->tail;
	for(; fin != fa->array; --fin) {
		(*(fin-1)->func)((fin-1)->data);
	}
}

static inline void destroy_finalizer_array(msgpack_zone_finalizer_array* fa)
{
	call_finalizer_array(fa);
	free(fa->array);
}

static inline void clear_finalizer_array(msgpack_zone_finalizer_array* fa)
{
	call_finalizer_array(fa);
	fa->tail = fa->array;
}

bool msgpack_zone_push_finalizer_expand(msgpack_zone* zone,
		void (*func)(void* data), void* data)
{
	msgpack_zone_finalizer_array* const fa = &zone->finalizer_array;

	const size_t nused = fa->end - fa->array;

	size_t nnext;
	if(nused == 0) {
		// 初回の呼び出し：fa->tail == fa->end == fa->array == NULL

		// glibcは72バイト以下のmallocが高速
		nnext = (sizeof(msgpack_zone_finalizer) < 72/2) ?
				72 / sizeof(msgpack_zone_finalizer) : 8;

	} else {
		nnext = nused * 2;
	}

	msgpack_zone_finalizer* tmp =
		(msgpack_zone_finalizer*)realloc(fa->array,
				sizeof(msgpack_zone_finalizer) * nnext);
	if(tmp == NULL) {
		return false;
	}

	fa->array  = tmp;
	fa->end    = tmp + nnext;
	fa->tail   = tmp + nused;

	fa->tail->func = func;
	fa->tail->data = data;

	++fa->tail;

	return true;
}


bool msgpack_zone_is_empty(msgpack_zone* zone)
{
	msgpack_zone_chunk_array* const ca = &zone->chunk_array;
	msgpack_zone_finalizer_array* const fa = &zone->finalizer_array;
	return ca->array[0].ptr == ca->array[0].alloc &&
		ca->tail == ca->array &&
		fa->tail == fa->array;
}


bool msgpack_zone_init(msgpack_zone* zone, size_t chunk_size)
{
	zone->chunk_size = chunk_size;

	if(!init_chunk_array(&zone->chunk_array, chunk_size)) {
		return false;
	}

	init_finalizer_array(&zone->finalizer_array);

	return true;
}

void msgpack_zone_destroy(msgpack_zone* zone)
{
	destroy_finalizer_array(&zone->finalizer_array);
	destroy_chunk_array(&zone->chunk_array);
}

void msgpack_zone_clear(msgpack_zone* zone)
{
	clear_finalizer_array(&zone->finalizer_array);
	clear_chunk_array(&zone->chunk_array);
}

msgpack_zone* msgpack_zone_new(size_t chunk_size)
{
	msgpack_zone* zone = (msgpack_zone*)malloc(sizeof(msgpack_zone));
	if(zone == NULL) {
		return NULL;
	}

	if(!msgpack_zone_init(zone, chunk_size)) {
		free(zone);
		return NULL;
	}

	return zone;
}

void msgpack_zone_free(msgpack_zone* zone)
{
	msgpack_zone_destroy(zone);
	free(zone);
}

