/*
 * MessagePack for C zero-copy buffer implementation
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
#include "msgpack/vrefbuffer.h"
#include <stdlib.h>
#include <string.h>

bool msgpack_vrefbuffer_init(msgpack_vrefbuffer* vbuf,
		size_t ref_size, size_t chunk_size)
{
	if(chunk_size < sizeof(msgpack_vrefbuffer_chunk)+72) {
		chunk_size = 72;
	} else {
		chunk_size -= sizeof(msgpack_vrefbuffer_chunk);
	}

	vbuf->chunk_size = chunk_size;
	vbuf->ref_size = ref_size;

	// glibcは72バイト以下のmallocが高速
	size_t nfirst = (sizeof(struct iovec) < 72/2) ?
			72 / sizeof(struct iovec) : 8;

	struct iovec* array = (struct iovec*)malloc(
			sizeof(struct iovec) * nfirst);
	if(array == NULL) {
		return false;
	}

	vbuf->tail  = array;
	vbuf->end   = array + nfirst;
	vbuf->array = array;

	vbuf->chunk = (msgpack_vrefbuffer_chunk*)malloc(
			chunk_size + sizeof(msgpack_vrefbuffer_chunk));
	if(vbuf->chunk == NULL) {
		free(array);
		return false;
	}

	vbuf->chunk->next = NULL;
	vbuf->chunk->free = chunk_size;

	return true;
}

void msgpack_vrefbuffer_destroy(msgpack_vrefbuffer* vbuf)
{
	msgpack_vrefbuffer_chunk* c = vbuf->chunk;
	while(true) {
		msgpack_vrefbuffer_chunk* n = c->next;
		free(c);
		if(n) {
			c = n;
		} else {
			break;
		}
	}
	free(vbuf->array);
}

int msgpack_vrefbuffer_append_ref(msgpack_vrefbuffer* vbuf,
		const char* buf, unsigned int len)
{
	if(vbuf->tail == vbuf->end) {
		const size_t nused = vbuf->tail - vbuf->array;
		const size_t nnext = nused * 2;

		struct iovec* nvec = (struct iovec*)realloc(
				vbuf->array, sizeof(struct iovec)*nnext);
		if(nvec == NULL) {
			return -1;
		}

		vbuf->array = nvec;
		vbuf->end   = nvec + nnext;
		vbuf->tail  = nvec + nused;
	}

	vbuf->tail->iov_base = (char*)buf;
	vbuf->tail->iov_len  = len;
	++vbuf->tail;

	return 0;
}

int msgpack_vrefbuffer_append_copy(msgpack_vrefbuffer* vbuf,
		const char* buf, unsigned int len)
{
	msgpack_vrefbuffer_chunk* chunk = vbuf->chunk;
	size_t cur_size = vbuf->chunk_size;

	if(chunk->free < len) {
		cur_size = (cur_size > len) ? cur_size : len;

		chunk = (msgpack_vrefbuffer_chunk*)malloc(
				cur_size + sizeof(msgpack_vrefbuffer_chunk));
		if(chunk == NULL) {
			return -1;
		}

		chunk->free = cur_size;
		chunk->next = vbuf->chunk;
		vbuf->chunk = chunk;
	}

	char* m = ((char*)chunk) + sizeof(msgpack_vrefbuffer_chunk)
		+ (cur_size - chunk->free);

	memcpy(m, buf, len);
	chunk->free -= len;

	if(vbuf->tail != vbuf->array && m ==
			(const char*)((vbuf->tail-1)->iov_base) + (vbuf->tail-1)->iov_len) {
		(vbuf->tail-1)->iov_len += len;
		return 0;
	} else {
		return msgpack_vrefbuffer_append_ref(vbuf, m, len);
	}
}

int msgpack_vrefbuffer_migrate(msgpack_vrefbuffer* vbuf, msgpack_vrefbuffer* to)
{
	const size_t tosize = to->tail - to->array;
	if(vbuf->tail + tosize < vbuf->end) {
		const size_t nused = vbuf->tail - vbuf->array;
		const size_t nsize = vbuf->end  - vbuf->array;
		const size_t reqsize = nused + tosize;
		size_t nnext = nsize * 2;
		while(nnext < reqsize) {
			nnext *= 2;
		}

		struct iovec* nvec = (struct iovec*)realloc(
				vbuf->array, sizeof(struct iovec)*nnext);
		if(nvec == NULL) {
			return -1;
		}

		vbuf->array = nvec;
		vbuf->end   = nvec + nnext;
		vbuf->tail  = nvec + nused;
	}

	memcpy(vbuf->tail, vbuf->array, sizeof(struct iovec)*tosize);
	return 0;
}

