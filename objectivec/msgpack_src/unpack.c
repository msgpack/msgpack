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
#include "msgpack/unpack.h"
#include "msgpack/unpack_define.h"
#include <stdlib.h>

#ifdef _msgpack_atomic_counter_header
#include _msgpack_atomic_counter_header
#endif


typedef struct {
	msgpack_zone* z;
	bool referenced;
} unpack_user;


#define msgpack_unpack_struct(name) \
	struct template ## name

#define msgpack_unpack_func(ret, name) \
	ret template ## name

#define msgpack_unpack_callback(name) \
	template_callback ## name

#define msgpack_unpack_object msgpack_object

#define msgpack_unpack_user unpack_user


struct template_context;
typedef struct template_context template_context;

static void template_init(template_context* ctx);

static msgpack_object template_data(template_context* ctx);

static int template_execute(template_context* ctx,
		const char* data, size_t len, size_t* off);


static inline msgpack_object template_callback_root(unpack_user* u)
{ msgpack_object o = {}; return o; }

static inline int template_callback_uint8(unpack_user* u, uint8_t d, msgpack_object* o)
{ o->type = MSGPACK_OBJECT_POSITIVE_INTEGER; o->via.u64 = d; return 0; }

static inline int template_callback_uint16(unpack_user* u, uint16_t d, msgpack_object* o)
{ o->type = MSGPACK_OBJECT_POSITIVE_INTEGER; o->via.u64 = d; return 0; }

static inline int template_callback_uint32(unpack_user* u, uint32_t d, msgpack_object* o)
{ o->type = MSGPACK_OBJECT_POSITIVE_INTEGER; o->via.u64 = d; return 0; }

static inline int template_callback_uint64(unpack_user* u, uint64_t d, msgpack_object* o)
{ o->type = MSGPACK_OBJECT_POSITIVE_INTEGER; o->via.u64 = d; return 0; }

static inline int template_callback_int8(unpack_user* u, int8_t d, msgpack_object* o)
{ if(d >= 0) { o->type = MSGPACK_OBJECT_POSITIVE_INTEGER; o->via.u64 = d; return 0; }
		else { o->type = MSGPACK_OBJECT_NEGATIVE_INTEGER; o->via.i64 = d; return 0; } }

static inline int template_callback_int16(unpack_user* u, int16_t d, msgpack_object* o)
{ if(d >= 0) { o->type = MSGPACK_OBJECT_POSITIVE_INTEGER; o->via.u64 = d; return 0; }
		else { o->type = MSGPACK_OBJECT_NEGATIVE_INTEGER; o->via.i64 = d; return 0; } }

static inline int template_callback_int32(unpack_user* u, int32_t d, msgpack_object* o)
{ if(d >= 0) { o->type = MSGPACK_OBJECT_POSITIVE_INTEGER; o->via.u64 = d; return 0; }
		else { o->type = MSGPACK_OBJECT_NEGATIVE_INTEGER; o->via.i64 = d; return 0; } }

static inline int template_callback_int64(unpack_user* u, int64_t d, msgpack_object* o)
{ if(d >= 0) { o->type = MSGPACK_OBJECT_POSITIVE_INTEGER; o->via.u64 = d; return 0; }
		else { o->type = MSGPACK_OBJECT_NEGATIVE_INTEGER; o->via.i64 = d; return 0; } }

static inline int template_callback_float(unpack_user* u, float d, msgpack_object* o)
{ o->type = MSGPACK_OBJECT_DOUBLE; o->via.dec = d; return 0; }

static inline int template_callback_double(unpack_user* u, double d, msgpack_object* o)
{ o->type = MSGPACK_OBJECT_DOUBLE; o->via.dec = d; return 0; }

static inline int template_callback_nil(unpack_user* u, msgpack_object* o)
{ o->type = MSGPACK_OBJECT_NIL; return 0; }

static inline int template_callback_true(unpack_user* u, msgpack_object* o)
{ o->type = MSGPACK_OBJECT_BOOLEAN; o->via.boolean = true; return 0; }

static inline int template_callback_false(unpack_user* u, msgpack_object* o)
{ o->type = MSGPACK_OBJECT_BOOLEAN; o->via.boolean = false; return 0; }

static inline int template_callback_array(unpack_user* u, unsigned int n, msgpack_object* o)
{
	o->type = MSGPACK_OBJECT_ARRAY;
	o->via.array.size = 0;
	o->via.array.ptr = (msgpack_object*)msgpack_zone_malloc(u->z, n*sizeof(msgpack_object));
	if(o->via.array.ptr == NULL) { return -1; }
	return 0;
}

static inline int template_callback_array_item(unpack_user* u, msgpack_object* c, msgpack_object o)
{ c->via.array.ptr[c->via.array.size++] = o; return 0; }

static inline int template_callback_map(unpack_user* u, unsigned int n, msgpack_object* o)
{
	o->type = MSGPACK_OBJECT_MAP;
	o->via.map.size = 0;
	o->via.map.ptr = (msgpack_object_kv*)msgpack_zone_malloc(u->z, n*sizeof(msgpack_object_kv));
	if(o->via.map.ptr == NULL) { return -1; }
	return 0;
}

static inline int template_callback_map_item(unpack_user* u, msgpack_object* c, msgpack_object k, msgpack_object v)
{
	c->via.map.ptr[c->via.map.size].key = k;
	c->via.map.ptr[c->via.map.size].val = v;
	++c->via.map.size;
	return 0;
}

static inline int template_callback_raw(unpack_user* u, const char* b, const char* p, unsigned int l, msgpack_object* o)
{
	o->type = MSGPACK_OBJECT_RAW;
	o->via.raw.ptr = p;
	o->via.raw.size = l;
	u->referenced = true;
	return 0;
}

#include "msgpack/unpack_template.h"


#define CTX_CAST(m) ((template_context*)(m))
#define CTX_REFERENCED(mpac) CTX_CAST((mpac)->ctx)->user.referenced

#define COUNTER_SIZE (sizeof(_msgpack_atomic_counter_t))


static inline void init_count(void* buffer)
{
	*(volatile _msgpack_atomic_counter_t*)buffer = 1;
}

static inline void decl_count(void* buffer)
{
	// atomic if(--*(_msgpack_atomic_counter_t*)buffer == 0) { free(buffer); }
	if(_msgpack_sync_decr_and_fetch((volatile _msgpack_atomic_counter_t*)buffer) == 0) {
		free(buffer);
	}
}

static inline void incr_count(void* buffer)
{
	// atomic ++*(_msgpack_atomic_counter_t*)buffer;
	_msgpack_sync_incr_and_fetch((volatile _msgpack_atomic_counter_t*)buffer);
}

static inline _msgpack_atomic_counter_t get_count(void* buffer)
{
	return *(volatile _msgpack_atomic_counter_t*)buffer;
}



bool msgpack_unpacker_init(msgpack_unpacker* mpac, size_t initial_buffer_size)
{
	if(initial_buffer_size < COUNTER_SIZE) {
		initial_buffer_size = COUNTER_SIZE;
	}

	char* buffer = (char*)malloc(initial_buffer_size);
	if(buffer == NULL) {
		return false;
	}

	void* ctx = malloc(sizeof(template_context));
	if(ctx == NULL) {
		free(buffer);
		return false;
	}

	msgpack_zone* z = msgpack_zone_new(MSGPACK_ZONE_CHUNK_SIZE);
	if(z == NULL) {
		free(ctx);
		free(buffer);
		return false;
	}

	mpac->buffer = buffer;
	mpac->used = COUNTER_SIZE;
	mpac->free = initial_buffer_size - mpac->used;
	mpac->off = COUNTER_SIZE;
	mpac->parsed = 0;
	mpac->initial_buffer_size = initial_buffer_size;
	mpac->z = z;
	mpac->ctx = ctx;

	init_count(mpac->buffer);

	template_init(CTX_CAST(mpac->ctx));
	CTX_CAST(mpac->ctx)->user.z = mpac->z;
	CTX_CAST(mpac->ctx)->user.referenced = false;

	return true;
}

void msgpack_unpacker_destroy(msgpack_unpacker* mpac)
{
	msgpack_zone_free(mpac->z);
	free(mpac->ctx);
	decl_count(mpac->buffer);
}


msgpack_unpacker* msgpack_unpacker_new(size_t initial_buffer_size)
{
	msgpack_unpacker* mpac = (msgpack_unpacker*)malloc(sizeof(msgpack_unpacker));
	if(mpac == NULL) {
		return NULL;
	}

	if(!msgpack_unpacker_init(mpac, initial_buffer_size)) {
		free(mpac);
		return NULL;
	}

	return mpac;
}

void msgpack_unpacker_free(msgpack_unpacker* mpac)
{
	msgpack_unpacker_destroy(mpac);
	free(mpac);
}

bool msgpack_unpacker_expand_buffer(msgpack_unpacker* mpac, size_t size)
{
	if(mpac->used == mpac->off && get_count(mpac->buffer) == 1
			&& !CTX_REFERENCED(mpac)) {
		// rewind buffer
		mpac->free += mpac->used - COUNTER_SIZE;
		mpac->used = COUNTER_SIZE;
		mpac->off = COUNTER_SIZE;

		if(mpac->free >= size) {
			return true;
		}
	}

	if(mpac->off == COUNTER_SIZE) {
		size_t next_size = (mpac->used + mpac->free) * 2;  // include COUNTER_SIZE
		while(next_size < size + mpac->used) {
			next_size *= 2;
		}

		char* tmp = (char*)realloc(mpac->buffer, next_size);
		if(tmp == NULL) {
			return false;
		}

		mpac->buffer = tmp;
		mpac->free = next_size - mpac->used;

	} else {
		size_t next_size = mpac->initial_buffer_size;  // include COUNTER_SIZE
		size_t not_parsed = mpac->used - mpac->off;
		while(next_size < size + not_parsed + COUNTER_SIZE) {
			next_size *= 2;
		}

		char* tmp = (char*)malloc(next_size);
		if(tmp == NULL) {
			return false;
		}

		init_count(tmp);

		memcpy(tmp+COUNTER_SIZE, mpac->buffer+mpac->off, not_parsed);

		if(CTX_REFERENCED(mpac)) {
			if(!msgpack_zone_push_finalizer(mpac->z, decl_count, mpac->buffer)) {
				free(tmp);
				return false;
			}
			CTX_REFERENCED(mpac) = false;
		} else {
			decl_count(mpac->buffer);
		}

		mpac->buffer = tmp;
		mpac->used = not_parsed + COUNTER_SIZE;
		mpac->free = next_size - mpac->used;
		mpac->off = COUNTER_SIZE;
	}

	return true;
}

int msgpack_unpacker_execute(msgpack_unpacker* mpac)
{
	size_t off = mpac->off;
	int ret = template_execute(CTX_CAST(mpac->ctx),
			mpac->buffer, mpac->used, &mpac->off);
	if(mpac->off > off) {
		mpac->parsed += mpac->off - off;
	}
	return ret;
}

msgpack_object msgpack_unpacker_data(msgpack_unpacker* mpac)
{
	return template_data(CTX_CAST(mpac->ctx));
}

msgpack_zone* msgpack_unpacker_release_zone(msgpack_unpacker* mpac)
{
	if(!msgpack_unpacker_flush_zone(mpac)) {
		return NULL;
	}

	msgpack_zone* r = msgpack_zone_new(MSGPACK_ZONE_CHUNK_SIZE);
	if(r == NULL) {
		return NULL;
	}

	msgpack_zone* old = mpac->z;
	mpac->z = r;
	CTX_CAST(mpac->ctx)->user.z = mpac->z;

	return old;
}

void msgpack_unpacker_reset_zone(msgpack_unpacker* mpac)
{
	msgpack_zone_clear(mpac->z);
}

bool msgpack_unpacker_flush_zone(msgpack_unpacker* mpac)
{
	if(CTX_REFERENCED(mpac)) {
		if(!msgpack_zone_push_finalizer(mpac->z, decl_count, mpac->buffer)) {
			return false;
		}
		CTX_REFERENCED(mpac) = false;

		incr_count(mpac->buffer);
	}

	return true;
}

void msgpack_unpacker_reset(msgpack_unpacker* mpac)
{
	template_init(CTX_CAST(mpac->ctx));
	// don't reset referenced flag
	mpac->parsed = 0;
}

bool msgpack_unpacker_next(msgpack_unpacker* mpac, msgpack_unpacked* result)
{
	if(result->zone != NULL) {
		msgpack_zone_free(result->zone);
	}

	int ret = msgpack_unpacker_execute(mpac);

	if(ret <= 0) {
		result->zone = NULL;
		memset(&result->data, 0, sizeof(msgpack_object));
		return false;
	}

	result->zone = msgpack_unpacker_release_zone(mpac);
	result->data = msgpack_unpacker_data(mpac);
	msgpack_unpacker_reset(mpac);

	return true;
}


msgpack_unpack_return
msgpack_unpack(const char* data, size_t len, size_t* off,
		msgpack_zone* result_zone, msgpack_object* result)
{
	size_t noff = 0;
	if(off != NULL) { noff = *off; }

	if(len <= noff) {
		// FIXME
		return MSGPACK_UNPACK_CONTINUE;
	}

	template_context ctx;
	template_init(&ctx);

	ctx.user.z = result_zone;
	ctx.user.referenced = false;

	int e = template_execute(&ctx, data, len, &noff);
	if(e < 0) {
		return MSGPACK_UNPACK_PARSE_ERROR;
	}

	if(off != NULL) { *off = noff; }

	if(e == 0) {
		return MSGPACK_UNPACK_CONTINUE;
	}

	*result = template_data(&ctx);

	if(noff < len) {
		return MSGPACK_UNPACK_EXTRA_BYTES;
	}

	return MSGPACK_UNPACK_SUCCESS;
}

bool msgpack_unpack_next(msgpack_unpacked* result,
		const char* data, size_t len, size_t* off)
{
	msgpack_unpacked_destroy(result);

	size_t noff = 0;
	if(off != NULL) { noff = *off; }

	if(len <= noff) {
		return false;
	}

	msgpack_zone* z = msgpack_zone_new(MSGPACK_ZONE_CHUNK_SIZE);

	template_context ctx;
	template_init(&ctx);

	ctx.user.z = z;
	ctx.user.referenced = false;

	int e = template_execute(&ctx, data, len, &noff);
	if(e <= 0) {
		msgpack_zone_free(z);
		return false;
	}

	if(off != NULL) { *off = noff; }

	result->zone = z;
	result->data = template_data(&ctx);

	return true;
}

