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
#ifndef MSGPACK_UNPACKER_H__
#define MSGPACK_UNPACKER_H__

#include "msgpack/zone.h"
#include "msgpack/object.h"

#ifdef __cplusplus
extern "C" {
#endif


typedef struct msgpack_unpacker {
	char* buffer;
	size_t used;
	size_t free;
	size_t off;
	size_t parsed;
	msgpack_zone* z;
	size_t initial_buffer_size;
	void* ctx;
} msgpack_unpacker;


bool msgpack_unpacker_init(msgpack_unpacker* mpac, size_t initial_buffer_size);
void msgpack_unpacker_destroy(msgpack_unpacker* mpac);

msgpack_unpacker* msgpack_unpacker_new(size_t initial_buffer_size);
void msgpack_unpacker_free(msgpack_unpacker* mpac);

static inline bool   msgpack_unpacker_reserve_buffer(msgpack_unpacker* mpac, size_t size);
static inline char*  msgpack_unpacker_buffer(msgpack_unpacker* mpac);
static inline size_t msgpack_unpacker_buffer_capacity(const msgpack_unpacker* mpac);
static inline void   msgpack_unpacker_buffer_consumed(msgpack_unpacker* mpac, size_t size);


int msgpack_unpacker_execute(msgpack_unpacker* mpac);

msgpack_object msgpack_unpacker_data(msgpack_unpacker* mpac);

msgpack_zone* msgpack_unpacker_release_zone(msgpack_unpacker* mpac);

void msgpack_unpacker_reset_zone(msgpack_unpacker* mpac);

void msgpack_unpacker_reset(msgpack_unpacker* mpac);

static inline size_t msgpack_unpacker_message_size(const msgpack_unpacker* mpac);



typedef enum {
	MSGPACK_UNPACK_SUCCESS				=  2,
	MSGPACK_UNPACK_EXTRA_BYTES			=  1,
	MSGPACK_UNPACK_CONTINUE				=  0,
	MSGPACK_UNPACK_PARSE_ERROR			= -1,
} msgpack_unpack_return;

msgpack_unpack_return
msgpack_unpack(const char* data, size_t len, size_t* off,
		msgpack_zone* z, msgpack_object* result);


static inline size_t msgpack_unpacker_parsed_size(const msgpack_unpacker* mpac);

bool msgpack_unpacker_flush_zone(msgpack_unpacker* mpac);

bool msgpack_unpacker_expand_buffer(msgpack_unpacker* mpac, size_t size);

bool msgpack_unpacker_reserve_buffer(msgpack_unpacker* mpac, size_t size)
{
	if(mpac->free >= size) { return true; }
	return msgpack_unpacker_expand_buffer(mpac, size);
}

char* msgpack_unpacker_buffer(msgpack_unpacker* mpac)
{
	return mpac->buffer + mpac->used;
}

size_t msgpack_unpacker_buffer_capacity(const msgpack_unpacker* mpac)
{
	return mpac->free;
}

void msgpack_unpacker_buffer_consumed(msgpack_unpacker* mpac, size_t size)
{
	mpac->used += size;
	mpac->free -= size;
}

size_t msgpack_unpacker_message_size(const msgpack_unpacker* mpac)
{
	return mpac->parsed - mpac->off + mpac->used;
}

size_t msgpack_unpacker_parsed_size(const msgpack_unpacker* mpac)
{
	return mpac->parsed;
}


#ifdef __cplusplus
}
#endif

#endif /* msgpack/unpack.h */

