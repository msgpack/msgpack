/*
 * MessagePack for Python unpacking routine
 *
 * Copyright (C) 2009 Naoki INADA
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

#include "Python.h"


typedef struct {
    int reserved;
} unpack_user;


#define msgpack_unpack_struct(name) \
	struct template ## name

#define msgpack_unpack_func(ret, name) \
	ret template ## name

#define msgpack_unpack_callback(name) \
	template_callback ## name

#define msgpack_unpack_object PyObject*

#define msgpack_unpack_user unpack_user


struct template_context;
typedef struct template_context template_context;

static void template_init(template_context* ctx);

static msgpack_unpack_object template_data(template_context* ctx);

static int template_execute(template_context* ctx,
		const char* data, size_t len, size_t* off);


static inline msgpack_unpack_object template_callback_root(unpack_user* u)
{ PyObject *o = Py_None; Py_INCREF(o); return o; }

static inline int template_callback_uint8(unpack_user* u, uint8_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong((long)d); return 0; }

static inline int template_callback_uint16(unpack_user* u, uint16_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong((long)d); return 0; }

static inline int template_callback_uint32(unpack_user* u, uint32_t d, msgpack_unpack_object* o)
{
    if (d >= 0x80000000UL) {
        *o = PyLong_FromUnsignedLongLong((unsigned long long)d);
    } else {
        *o = PyInt_FromLong((long)d);
    }
    return 0;
}

static inline int template_callback_uint64(unpack_user* u, uint64_t d, msgpack_unpack_object* o)
{ *o = PyLong_FromUnsignedLongLong(d); return 0; }

static inline int template_callback_int8(unpack_user* u, int8_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong(d); return 0; }

static inline int template_callback_int16(unpack_user* u, int16_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong(d); return 0; }

static inline int template_callback_int32(unpack_user* u, int32_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong(d); return 0; }

static inline int template_callback_int64(unpack_user* u, int64_t d, msgpack_unpack_object* o)
{ *o = PyLong_FromLongLong(d); return 0; }

static inline int template_callback_float(unpack_user* u, float d, msgpack_unpack_object* o)
{ *o = PyFloat_FromDouble((double)d); return 0; }

static inline int template_callback_double(unpack_user* u, double d, msgpack_unpack_object* o)
{ *o = PyFloat_FromDouble(d); return 0; }

static inline int template_callback_nil(unpack_user* u, msgpack_unpack_object* o)
{ *o = Py_None; Py_INCREF(o); return 0; }

static inline int template_callback_true(unpack_user* u, msgpack_unpack_object* o)
{ *o = Py_True; Py_INCREF(o); return 0; }

static inline int template_callback_false(unpack_user* u, msgpack_unpack_object* o)
{ *o = Py_False; Py_INCREF(o); return 0; }

static inline int template_callback_array(unpack_user* u, unsigned int n, msgpack_unpack_object* o)
{
    /* TODO: use PyList_New(n). */
    *o = PyList_New(0);
    return 0;
}

static inline int template_callback_array_item(unpack_user* u, msgpack_unpack_object* c, msgpack_unpack_object o)
{
    PyList_Append(*c, o);
    return 0;
}

static inline int template_callback_map(unpack_user* u, unsigned int n, msgpack_unpack_object* o)
{
    *o = PyDict_New();
    return 0;
}

static inline int template_callback_map_item(unpack_user* u, msgpack_unpack_object* c, msgpack_unpack_object k, msgpack_unpack_object v)
{
    PyDict_SetItem(*c, k, v);
	return 0;
}

static inline int template_callback_raw(unpack_user* u, const char* b, const char* p, unsigned int l, msgpack_unpack_object* o)
{
    *o = PyString_FromStringAndSize(p, l);
	return 0;
}

#include "msgpack/unpack_template.h"


#if 0
#define CTX_CAST(m) ((template_context*)(m))
#define CTX_REFERENCED(mpac) CTX_CAST((mpac)->ctx)->user.referenced


static const size_t COUNTER_SIZE = sizeof(unsigned int);

static inline void init_count(void* buffer)
{
	*(volatile unsigned int*)buffer = 1;
}

static inline void decl_count(void* buffer)
{
	//if(--*(unsigned int*)buffer == 0) {
	if(__sync_sub_and_fetch((unsigned int*)buffer, 1) == 0) {
		free(buffer);
	}
}

static inline void incr_count(void* buffer)
{
	//++*(unsigned int*)buffer;
	__sync_add_and_fetch((unsigned int*)buffer, 1);
}

static inline unsigned int get_count(void* buffer)
{
	return *(volatile unsigned int*)buffer;
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

msgpack_unpack_object msgpack_unpacker_data(msgpack_unpacker* mpac)
{
	return template_data(CTX_CAST(mpac->ctx));
}

msgpack_zone* msgpack_unpacker_release_zone(msgpack_unpacker* mpac)
{
	if(!msgpack_unpacker_flush_zone(mpac)) {
		return false;
	}

	msgpack_zone* r = msgpack_zone_new(MSGPACK_ZONE_CHUNK_SIZE);
	if(r == NULL) {
		return NULL;
	}

	msgpack_zone* old = mpac->z;
	mpac->z = r;

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


msgpack_unpack_return
msgpack_unpack(const char* data, size_t len, size_t* off,
		msgpack_zone* z, msgpack_unpack_object* result)
{
	template_context ctx;
	template_init(&ctx);

	ctx.user.z = z;
	ctx.user.referenced = false;

	size_t noff = 0;
	if(off != NULL) { noff = *off; }

	int ret = template_execute(&ctx, data, len, &noff);
	if(ret < 0) {
		return MSGPACK_UNPACK_PARSE_ERROR;
	}

	if(off != NULL) { *off = noff; }

	if(ret == 0) {
		return MSGPACK_UNPACK_CONTINUE;
	}

	*result = template_data(&ctx);

	if(noff < len) {
		return MSGPACK_UNPACK_EXTRA_BYTES;
	}

	return MSGPACK_UNPACK_SUCCESS;
}
#endif
