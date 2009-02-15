/*
 * MessagePack for C simple buffer implementation
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
#ifndef MSGPACK_SBUFFER_H__
#define MSGPACK_SBUFFER_H__

#include <stdlib.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
	char* ptr;
	size_t size;
	size_t capacity;
} msgpack_sbuffer;

static inline void msgpack_sbuffer_init(msgpack_sbuffer* sbuf)
{
	memset(sbuf, 0, sizeof(msgpack_sbuffer));
}

static inline void msgpack_sbuffer_destroy(msgpack_sbuffer* sbuf)
{
	free(sbuf->ptr);
}

static inline int msgpack_sbuffer_write(void* data, const char* buf, unsigned int len)
{
	msgpack_sbuffer* sbuf = (msgpack_sbuffer*)data;
	if(sbuf->capacity - sbuf->size < len) {
		size_t nsize = (sbuf->capacity ? sbuf->capacity*2 : 2048);
		while(nsize < sbuf->size + len) { nsize *= 2; }

		void* tmp = realloc(sbuf->ptr, nsize);
		if(!tmp) { return -1; }

		sbuf->ptr = (char*)tmp;
		sbuf->capacity = nsize;
	}
	memcpy(sbuf->ptr + sbuf->size, buf, len);
	sbuf->size += len;
	return 0;
}


#ifdef __cplusplus
}
#endif

#endif /* msgpack/sbuffer.h */

