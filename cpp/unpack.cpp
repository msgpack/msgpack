//
// MessagePack for C++ deserializing routine
//
// Copyright (C) 2008 FURUHASHI Sadayuki
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
//
#include "msgpack/unpack.hpp"
#include "msgpack/unpack_define.h"
#include <stdlib.h>

namespace msgpack {


#define msgpack_unpack_struct(name) \
	struct msgpack_unpacker_##name

#define msgpack_unpack_func(ret, name) \
	ret msgpack_unpacker_##name

#define msgpack_unpack_callback(name) \
	msgpack_unpack_##name

#define msgpack_unpack_object object

#define msgpack_unpack_user zone*


struct msgpack_unpacker_context;

static void msgpack_unpacker_init(struct msgpack_unpacker_context* ctx);

static object msgpack_unpacker_data(struct msgpack_unpacker_context* ctx);

static int msgpack_unpacker_execute(struct msgpack_unpacker_context* ctx,
		const char* data, size_t len, size_t* off);


static inline object msgpack_unpack_init(zone** z)
{ return object(); }

static inline object msgpack_unpack_uint8(zone** z, uint8_t d)
{ object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline object msgpack_unpack_uint16(zone** z, uint16_t d)
{ object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline object msgpack_unpack_uint32(zone** z, uint32_t d)
{ object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline object msgpack_unpack_uint64(zone** z, uint64_t d)
{ object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline object msgpack_unpack_int8(zone** z, int8_t d)
{ if(d >= 0) { object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { object o; o.type = type::NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline object msgpack_unpack_int16(zone** z, int16_t d)
{ if(d >= 0) { object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { object o; o.type = type::NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline object msgpack_unpack_int32(zone** z, int32_t d)
{ if(d >= 0) { object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { object o; o.type = type::NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline object msgpack_unpack_int64(zone** z, int64_t d)
{ if(d >= 0) { object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { object o; o.type = type::NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline object msgpack_unpack_float(zone** z, float d)
{ object o; o.type = type::DOUBLE; o.via.dec = d; return o; }

static inline object msgpack_unpack_double(zone** z, double d)
{ object o; o.type = type::DOUBLE; o.via.dec = d; return o; }

static inline object msgpack_unpack_nil(zone** z)
{ object o; o.type = type::NIL; return o; }

static inline object msgpack_unpack_true(zone** z)
{ object o; o.type = type::BOOLEAN; o.via.boolean = true; return o; }

static inline object msgpack_unpack_false(zone** z)
{ object o; o.type = type::BOOLEAN; o.via.boolean = false; return o; }

static inline object msgpack_unpack_array(zone** z, unsigned int n)
{
	object o;
	o.type = type::ARRAY;
	o.via.container.size = 0;
	o.via.container.ptr = (*z)->malloc_container(n);
	return o;
}

static inline void msgpack_unpack_array_item(zone** z, object* c, object o)
{ c->via.container.ptr[ c->via.container.size++ ] = o; }

static inline object msgpack_unpack_map(zone** z, unsigned int n)
{
	object o;
	o.type = type::MAP;
	o.via.container.size = 0;
	o.via.container.ptr = (*z)->malloc_container(n*2);
	return o;
}

static inline void msgpack_unpack_map_item(zone** z, object* c, object k, object v)
{
	c->via.container.ptr[ c->via.container.size   ] = k;
	c->via.container.ptr[ c->via.container.size+1 ] = v;
	++c->via.container.size;
}

static inline object msgpack_unpack_raw(zone** z, const char* b, const char* p, unsigned int l)
{ object o; o.type = type::RAW; o.via.ref.ptr = p; o.via.ref.size = l; return o; }


#include "msgpack/unpack_template.h"


struct unpacker::context {
	context(zone* z)
	{
		msgpack_unpacker_init(&m_ctx);
		m_ctx.user = z;
	}

	~context() { }

	int execute(const char* data, size_t len, size_t* off)
	{
		return msgpack_unpacker_execute(&m_ctx, data, len, off);
	}

	object data()
	{
		return msgpack_unpacker_data(&m_ctx);
	}

	void reset()
	{
		zone* z = m_ctx.user;
		msgpack_unpacker_init(&m_ctx);
		m_ctx.user = z;
	}

	void reset(zone* z)
	{
		msgpack_unpacker_init(&m_ctx);
		m_ctx.user = z;
	}

	zone* user()
	{
		return m_ctx.user;
	}

	void user(zone* z)
	{
		m_ctx.user = z;
	}

private:
	msgpack_unpacker_context m_ctx;

private:
	context();
	context(const context&);
};


unpacker::unpacker(size_t initial_buffer_size) :
	m_buffer(NULL),
	m_used(0),
	m_free(0),
	m_off(0),
	m_zone(new zone()),
	m_ctx(new context(&*m_zone)),
	m_initial_buffer_size(initial_buffer_size)
{ }


unpacker::~unpacker()
{
	delete m_ctx;
}


void unpacker::expand_buffer(size_t len)
{
	if(m_off == 0) {
		size_t next_size;
		if(m_used != 0) { next_size = (m_used + m_free) * 2; }
		else { next_size = m_initial_buffer_size; }
		while(next_size < len + m_used) { next_size *= 2; }

		m_buffer = m_zone->realloc(m_buffer, next_size);
		m_free = next_size - m_used;

	} else {
		size_t next_size = m_initial_buffer_size;
		while(next_size < len + m_used - m_off) { next_size *= 2; }

		char* tmp = m_zone->malloc(next_size);
		memcpy(tmp, m_buffer+m_off, m_used-m_off);

		m_buffer = tmp;
		m_used = m_used - m_off;
		m_free = next_size - m_used;
		m_off = 0;
	}
}

bool unpacker::execute()
{
	int ret = m_ctx->execute(m_buffer, m_used, &m_off);
	if(ret < 0) {
		throw unpack_error("parse error");
	} else if(ret == 0) {
		return false;
	} else {
		return true;
	}
}

zone* unpacker::release_zone()
{
	zone* n = new zone();
	std::auto_ptr<zone> old(m_zone.release());
	m_zone.reset(n);

	//std::auto_ptr<zone> old(new zone());
	//m_zone.swap(old);

	// move all bytes in m_buffer to new buffer from the new zone
	if(m_used <= m_off) {
		m_buffer = NULL;
		m_used = 0;
		m_free = 0;
		m_off = 0;
	} else {
		try {
			expand_buffer(0);
		} catch (...) {
			// m_zone.swap(old);
			zone* tmp = old.release();
			old.reset(m_zone.release());
			m_zone.reset(tmp);
			throw;
		}
	}
	m_ctx->user(m_zone.get());
	return old.release();
}

object unpacker::data()
{
	return m_ctx->data();
}

void unpacker::reset()
{
	if(m_off != 0) { delete release_zone(); }
	m_ctx->reset();
}


object unpacker::unpack(const char* data, size_t len, zone& z, size_t* off)
{
	context ctx(&z);
	if(off) {
		int ret = ctx.execute(data, len, off);
		if(ret < 0) {
			throw unpack_error("parse error");
		} else if(ret == 0) {
			throw unpack_error("insufficient bytes");
		}
	} else {
		size_t noff = 0;
		int ret = ctx.execute(data, len, &noff);
		if(ret < 0) {
			throw unpack_error("parse error");
		} else if(ret == 0) {
			throw unpack_error("insufficient bytes");
		} else if(noff < len) {
			throw unpack_error("extra bytes");
		}
	}
	return ctx.data();
}


}  // namespace msgpack

