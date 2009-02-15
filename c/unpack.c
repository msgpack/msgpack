/*
 * MessagePack packing routine for C
 *
 * Copyright (C) 2008 FURUHASHI Sadayuki
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
#include "unpack.h"
#include "unpack_context.h"
#include <stdlib.h>

msgpack_unpack_t* msgpack_unpack_new(void* data, msgpack_unpack_callback* callback)
{
	msgpack_unpacker* ctx;
	ctx = (msgpack_unpacker*)calloc(1, sizeof(msgpack_unpacker));
	if(ctx == NULL) { return NULL; }
	msgpack_unpacker_init(ctx);
	((msgpack_unpack_t*)ctx)->data = data;
	((msgpack_unpack_t*)ctx)->callback = *callback;
	return (msgpack_unpack_t*)ctx;
}

void msgpack_unpack_free(msgpack_unpack_t* ctx)
{
	free((msgpack_unpacker*)ctx);
}

void* msgpack_unpack_data(msgpack_unpack_t* ctx)
{
	return msgpack_unpacker_data((msgpack_unpacker*)ctx);
}

void msgpack_unpack_reset(msgpack_unpack_t* ctx)
{
	msgpack_unpack_t x = ((msgpack_unpacker*)ctx)->user;
	msgpack_unpacker_init((msgpack_unpacker*)ctx);
	((msgpack_unpacker*)ctx)->user = x;
}

int msgpack_unpack_execute(msgpack_unpack_t* ctx, const char* data, size_t len, size_t* off)
{
	return msgpack_unpacker_execute(
			(msgpack_unpacker*)ctx,
			data, len, off);
}

