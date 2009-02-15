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
#include "pack_inline.h"
#include <stdlib.h>
#include <stdio.h>

msgpack_pack_t* msgpack_pack_new(void* data, msgpack_pack_callback_t callback)
{
	msgpack_pack_t* ctx = calloc(1, sizeof(msgpack_pack_t));
	if(!ctx) { return NULL; }
	ctx->data = data;
	ctx->callback = callback;
	return ctx;
}

void msgpack_pack_free(msgpack_pack_t* ctx)
{
	free(ctx);
}

static inline void msgpack_pack_append_buffer(msgpack_pack_t* ctx, const unsigned char* b, unsigned int l)
{
	ctx->callback(ctx->data, b, l);
}

