/*
 * MessagePack for C dynamic typing routine
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
#include "msgpack/object.h"

typedef struct {
	msgpack_zone* z;
	bool referenced;
	bool failed;
} unpack_user;

#define msgpack_unpack_struct(name) \
	struct msgpack_unpacker ## name

#define msgpack_unpack_func(ret, name) \
	ret msgpack_unpacker ## name

#define msgpack_unpack_callback(name) \
	msgpack_unpack ## name

#define msgpack_unpack_object msgpack_object

#define msgpack_unpack_user unpack_user


struct msgpack_unpacker_context;

static void msgpack_unpacker_init(struct msgpack_unpacker_context* ctx);

static msgpack_object msgpack_unpacker_data(struct msgpack_unpacker_context* ctx);

static int msgpack_unpacker_execute(struct msgpack_unpacker_context* ctx,
		const char* data, size_t len, size_t* off);

static inline msgpack_object msgpack_unpack_init(unpack_user* u)
{ msgpack_object o; return o; }

static inline msgpack_object msgpack_unpack_uint8(unpack_user* u, uint8_t d)
{ msgpack_object o; o.type = MSGPACK_OBJECT_POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline msgpack_object msgpack_unpack_uint16(unpack_user* u, uint16_t d)
{ msgpack_object o; o.type = MSGPACK_OBJECT_POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline msgpack_object msgpack_unpack_uint32(unpack_user* u, uint32_t d)
{ msgpack_object o; o.type = MSGPACK_OBJECT_POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline msgpack_object msgpack_unpack_uint64(unpack_user* u, uint64_t d)
{ msgpack_object o; o.type = MSGPACK_OBJECT_POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline msgpack_object msgpack_unpack_int8(unpack_user* u, int8_t d)
{ if(d >= 0) { msgpack_object o; o.type = MSGPACK_OBJECT_POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { msgpack_object o; o.type = MSGPACK_OBJECT_NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline msgpack_object msgpack_unpack_int16(unpack_user* u, int16_t d)
{ if(d >= 0) { msgpack_object o; o.type = MSGPACK_OBJECT_POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { msgpack_object o; o.type = MSGPACK_OBJECT_NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline msgpack_object msgpack_unpack_int32(unpack_user* u, int32_t d)
{ if(d >= 0) { msgpack_object o; o.type = MSGPACK_OBJECT_POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { msgpack_object o; o.type = MSGPACK_OBJECT_NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline msgpack_object msgpack_unpack_int64(unpack_user* u, int64_t d)
{ if(d >= 0) { msgpack_object o; o.type = MSGPACK_OBJECT_POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { msgpack_object o; o.type = MSGPACK_OBJECT_NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline msgpack_object msgpack_unpack_float(unpack_user* u, float d)
{ msgpack_object o; o.type = MSGPACK_OBJECT_DOUBLE; o.via.dec = d; return o; }

static inline msgpack_object msgpack_unpack_double(unpack_user* u, double d)
{ msgpack_object o; o.type = MSGPACK_OBJECT_DOUBLE; o.via.dec = d; return o; }

static inline msgpack_object msgpack_unpack_nil(unpack_user* u)
{ msgpack_object o; o.type = MSGPACK_OBJECT_NIL; return o; }

static inline msgpack_object msgpack_unpack_true(unpack_user* u)
{ msgpack_object o; o.type = MSGPACK_OBJECT_BOOLEAN; o.via.boolean = true; return o; }

static inline msgpack_object msgpack_unpack_false(unpack_user* u)
{ msgpack_object o; o.type = MSGPACK_OBJECT_BOOLEAN; o.via.boolean = false; return o; }

static inline msgpack_object msgpack_unpack_array(unpack_user* u, unsigned int n)
{
	msgpack_object o;
	o.type = MSGPACK_OBJECT_ARRAY;
	o.via.array.size = 0;
	o.via.array.ptr = msgpack_zone_malloc(u->z, n*sizeof(msgpack_object));
	if(o.via.array.ptr == NULL) { u->failed = true; }
	return o;
}

static inline void msgpack_unpack_array_item(unpack_user* u, msgpack_object* c, msgpack_object o)
{
	if(u->failed) { return; }
	c->via.array.ptr[ c->via.array.size++ ] = o;
}

static inline msgpack_object msgpack_unpack_map(unpack_user* u, unsigned int n)
{
	msgpack_object o;
	o.type = MSGPACK_OBJECT_MAP;
	o.via.map.size = 0;
	o.via.map.ptr = msgpack_zone_malloc(u->z, n*sizeof(msgpack_object_kv));
	if(o.via.map.ptr == NULL) { u->failed = true; }
	return o;
}

static inline void msgpack_unpack_map_item(unpack_user* u, msgpack_object* c, msgpack_object k, msgpack_object v)
{
	if(u->failed) { return; }
	c->via.map.ptr[c->via.map.size].key = k;
	c->via.map.ptr[c->via.map.size].val = v;
	++c->via.map.size;
}

static inline msgpack_object msgpack_unpack_raw(unpack_user* u, const char* b, const char* p, unsigned int l)
{
	msgpack_object o;
	o.type = MSGPACK_OBJECT_RAW;
	o.via.raw.ptr = p;
	o.via.raw.size = l;
	u->referenced = true;
	return o;
}

#include "msgpack/unpack_template.h"

msgpack_object_unpack_return
msgpack_object_unpack(const char* data, size_t len, size_t* off,
		msgpack_zone* z, msgpack_object* result)
{
	struct msgpack_unpacker_context ctx;
	msgpack_unpacker_init(&ctx);
	unpack_user u = {z, false, false};
	ctx.user = u;

	size_t noff = (off ? *off : 0);
	int ret = msgpack_unpacker_execute(&ctx, data, len, &noff);
	if(ret < 0 || ctx.user.failed) {
		return MSGPACK_OBJECT_PARSE_ERROR;
	} else if(ret == 0) {
		return MSGPACK_OBJECT_INSUFFICIENT_BYTES;
	}
	*result = msgpack_unpacker_data(&ctx);
	if(off) { *off = noff; }
	if(ret == 0) {
		return MSGPACK_OBJECT_EXTRA_BYTES;
	}
	return MSGPACK_OBJECT_PARSE_SUCCESS;
}


