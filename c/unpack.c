/*
 * MessagePack unpacking routine for C
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
#include "msgpack/unpack.h"
#include "msgpack/unpack_define.h"
#include <stdlib.h>


#define msgpack_unpack_struct(name) \
	struct template_##name

#define msgpack_unpack_func(ret, name) \
	ret template_func_##name

#define msgpack_unpack_callback(name) \
	template_callback_##name

#define msgpack_unpack_object void*

#define msgpack_unpack_user msgpack_unpack_t


struct template_context;

static void template_func_init(struct template_context* ctx);

static void* template_func_data(struct template_context* ctx);

static int template_func_execute(struct template_context* ctx,
		const char* data, size_t len, size_t* off);


static inline void* template_callback_init(msgpack_unpack_t* x)
{ return NULL; }

static inline void* template_callback_uint8(msgpack_unpack_t* x, uint8_t d)
{ return x->callback.unpack_uint8(x->data, d); }

static inline void* template_callback_uint16(msgpack_unpack_t* x, uint16_t d)
{ return x->callback.unpack_uint16(x->data, d); }

static inline void* template_callback_uint32(msgpack_unpack_t* x, uint32_t d)
{ return x->callback.unpack_uint32(x->data, d); }

static inline void* template_callback_uint64(msgpack_unpack_t* x, uint64_t d)
{ return x->callback.unpack_uint64(x->data, d); }

static inline void* template_callback_int8(msgpack_unpack_t* x, int8_t d)
{ return x->callback.unpack_int8(x->data, d); }

static inline void* template_callback_int16(msgpack_unpack_t* x, int16_t d)
{ return x->callback.unpack_int16(x->data, d); }

static inline void* template_callback_int32(msgpack_unpack_t* x, int32_t d)
{ return x->callback.unpack_int32(x->data, d); }

static inline void* template_callback_int64(msgpack_unpack_t* x, int64_t d)
{ return x->callback.unpack_int64(x->data, d); }

static inline void* template_callback_float(msgpack_unpack_t* x, float d)
{ return x->callback.unpack_float(x->data, d); }

static inline void* template_callback_double(msgpack_unpack_t* x, double d)
{ return x->callback.unpack_double(x->data, d); }

static inline void* template_callback_nil(msgpack_unpack_t* x)
{ return x->callback.unpack_nil(x->data); }

static inline void* template_callback_true(msgpack_unpack_t* x)
{ return x->callback.unpack_true(x->data); }

static inline void* template_callback_false(msgpack_unpack_t* x)
{ return x->callback.unpack_false(x->data); }

static inline void* template_callback_array(msgpack_unpack_t* x, unsigned int n)
{ return x->callback.unpack_array(x->data, n); }

static inline void template_callback_array_item(msgpack_unpack_t* x, void* c, void* o)
{ x->callback.unpack_array_item(x->data, c, o); }

static inline void* template_callback_map(msgpack_unpack_t* x, unsigned int n)
{ return x->callback.unpack_map(x->data, n); }

static inline void template_callback_map_item(msgpack_unpack_t* x, void* c, void* k, void* v)
{ x->callback.unpack_map_item(x->data, c, k, v); }

static inline void* template_callback_raw(msgpack_unpack_t* x, const char* b, const char* p, unsigned int l)
{ return x->callback.unpack_raw(x->data, b, p, l); }


#include "msgpack/unpack_template.h"


msgpack_unpack_t* msgpack_unpack_new(void* data, msgpack_unpack_callback* callback)
{
	struct template_context* ctx;
	ctx = (struct template_context*)calloc(1, sizeof(struct template_context));
	if(ctx == NULL) { return NULL; }
	template_func_init(ctx);
	((msgpack_unpack_t*)ctx)->data = data;
	((msgpack_unpack_t*)ctx)->callback = *callback;
	return (msgpack_unpack_t*)ctx;
}

void msgpack_unpack_free(msgpack_unpack_t* ctx)
{
	free((struct template_context*)ctx);
}

void* msgpack_unpack_data(msgpack_unpack_t* ctx)
{
	return template_func_data((struct template_context*)ctx);
}

void msgpack_unpack_reset(msgpack_unpack_t* ctx)
{
	msgpack_unpack_t x = ((struct template_context*)ctx)->user;
	template_func_init((struct template_context*)ctx);
	((struct template_context*)ctx)->user = x;
}

int msgpack_unpack_execute(msgpack_unpack_t* ctx,
		const char* data, size_t len, size_t* off)
{
	return template_func_execute(
			(struct template_context*)ctx,
			data, len, off);
}


