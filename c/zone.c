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

typedef struct {
	size_t free;
	void* ptr;
	void* alloc;
} msgpack_zone_chunk;

struct _msgpack_zone {
	msgpack_zone_chunk* array;
	size_t ntail;
	size_t usable;
};

msgpack_zone* msgpack_zone_new()
{
	return calloc(1, sizeof(msgpack_zone));
}

void msgpack_zone_free(msgpack_zone* z)
{
	if(z->array) {
		size_t i;
		for(i=0; i <= z->ntail; ++i) {
			free(z->array[i].ptr);
		}
	}
	free(z);
}


void* msgpack_zone_malloc(msgpack_zone* z, size_t size)
{
	if(!z->array) {
		const size_t n = (sizeof(msgpack_zone_chunk) < 72/2) ?
				72 / sizeof(msgpack_zone_chunk) : 8;
		msgpack_zone_chunk* array =
			(msgpack_zone_chunk*)malloc(sizeof(msgpack_zone_chunk) * n);
		if(!array) { return NULL; }

		size_t sz = 2048;  /* FIXME chunk_size */
		while(sz < size) { sz *= 2; }
		char* p = (char*)malloc(sz);
		if(!p) {
			free(array);
			return NULL;
		}

		z->array = array;
		z->usable = n - 1;
		array[0].free  = sz - size;
		array[0].ptr   = p + size;
		array[0].alloc = p;
		return p;
	}

	if(z->array[z->ntail].free > size) {
		char* p = (char*)z->array[z->ntail].ptr;
		z->array[z->ntail].ptr   = p + size;
		z->array[z->ntail].free -= size;
		return p;
	}

	if(z->usable <= z->ntail) {
		const size_t n = (z->usable + 1) * 2;
		msgpack_zone_chunk* tmp =
			(msgpack_zone_chunk*)realloc(z->array, sizeof(msgpack_zone_chunk) * n);
		if(!tmp) { return NULL; }
		z->array  = tmp;
		z->usable = n - 1;
	}

	size_t sz = 2048;  /* FIXME chunk_size */
	while(sz < size) { sz *= 2; }
	char* p = (char*)malloc(sz);
	if(!p) { return NULL; }

	++z->ntail;
	z->array[z->ntail].free  = sz - size;
	z->array[z->ntail].ptr   = p + size;
	z->array[z->ntail].alloc = p;
	return p;
}

