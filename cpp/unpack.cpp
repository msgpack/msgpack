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


//namespace {
struct allocator {
	zone* z;
	bool referenced;

	inline object* malloc_object(size_t n)
	{
		return (object*)z->malloc(sizeof(object)*n);
	}
};
//}  // noname namespace


#define msgpack_unpack_struct(name) \
	struct msgpack_unpacker_##name

#define msgpack_unpack_func(ret, name) \
	ret msgpack_unpacker_##name

#define msgpack_unpack_callback(name) \
	msgpack_unpack_##name

#define msgpack_unpack_object object

#define msgpack_unpack_user allocator


struct msgpack_unpacker_context;

static void msgpack_unpacker_init(struct msgpack_unpacker_context* ctx);

static object msgpack_unpacker_data(struct msgpack_unpacker_context* ctx);

static int msgpack_unpacker_execute(struct msgpack_unpacker_context* ctx,
		const char* data, size_t len, size_t* off);


static inline object msgpack_unpack_init(allocator* a)
{ return object(); }

static inline object msgpack_unpack_uint8(allocator* a, uint8_t d)
{ object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline object msgpack_unpack_uint16(allocator* a, uint16_t d)
{ object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline object msgpack_unpack_uint32(allocator* a, uint32_t d)
{ object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline object msgpack_unpack_uint64(allocator* a, uint64_t d)
{ object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }

static inline object msgpack_unpack_int8(allocator* a, int8_t d)
{ if(d >= 0) { object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { object o; o.type = type::NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline object msgpack_unpack_int16(allocator* a, int16_t d)
{ if(d >= 0) { object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { object o; o.type = type::NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline object msgpack_unpack_int32(allocator* a, int32_t d)
{ if(d >= 0) { object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { object o; o.type = type::NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline object msgpack_unpack_int64(allocator* a, int64_t d)
{ if(d >= 0) { object o; o.type = type::POSITIVE_INTEGER; o.via.u64 = d; return o; }
		else { object o; o.type = type::NEGATIVE_INTEGER; o.via.i64 = d; return o; } }

static inline object msgpack_unpack_float(allocator* a, float d)
{ object o; o.type = type::DOUBLE; o.via.dec = d; return o; }

static inline object msgpack_unpack_double(allocator* a, double d)
{ object o; o.type = type::DOUBLE; o.via.dec = d; return o; }

static inline object msgpack_unpack_nil(allocator* a)
{ object o; o.type = type::NIL; return o; }

static inline object msgpack_unpack_true(allocator* a)
{ object o; o.type = type::BOOLEAN; o.via.boolean = true; return o; }

static inline object msgpack_unpack_false(allocator* a)
{ object o; o.type = type::BOOLEAN; o.via.boolean = false; return o; }

static inline object msgpack_unpack_array(allocator* a, unsigned int n)
{
	object o;
	o.type = type::ARRAY;
	o.via.container.size = 0;
	o.via.container.ptr = a->malloc_object(n);
	return o;
}

static inline void msgpack_unpack_array_item(allocator* a, object* c, object o)
{ c->via.container.ptr[ c->via.container.size++ ] = o; }

static inline object msgpack_unpack_map(allocator* a, unsigned int n)
{
	object o;
	o.type = type::MAP;
	o.via.container.size = 0;
	o.via.container.ptr = a->malloc_object(n*2);
	return o;
}

static inline void msgpack_unpack_map_item(allocator* a, object* c, object k, object v)
{
	c->via.container.ptr[ c->via.container.size   ] = k;
	c->via.container.ptr[ c->via.container.size+1 ] = v;
	++c->via.container.size;
}

static inline object msgpack_unpack_raw(allocator* a, const char* b, const char* p, unsigned int l)
{
	object o;
	o.type = type::RAW;
	o.via.ref.ptr = p;
	o.via.ref.size = l;
	a->referenced = true;
	return o;
}

#include "msgpack/unpack_template.h"


namespace {
struct context {
	context()
	{
		msgpack_unpacker_init(&m_ctx);
		allocator a = {NULL, false};
		m_ctx.user = a;
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
		zone* z = m_ctx.user.z;
		msgpack_unpacker_init(&m_ctx);
		allocator a = {z, false};
		m_ctx.user = a;
	}

	void set_zone(zone* z)
	{
		m_ctx.user.z = z;
	}

	bool is_referenced() const
	{
		return m_ctx.user.referenced;
	}

private:
	msgpack_unpacker_context m_ctx;
	zone* m_zone;

private:
	context(const context&);
};

context* as_ctx(void* m)
{
	return reinterpret_cast<context*>(m);
}


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

}  // noname namespace


unpacker::unpacker(size_t initial_buffer_size) :
	m_buffer(NULL),
	m_used(0),
	m_free(0),
	m_off(0),
	m_zone(new zone()),
	m_ctx(new context()),
	m_initial_buffer_size(initial_buffer_size)
{
	if(m_initial_buffer_size < COUNTER_SIZE) {
		m_initial_buffer_size = COUNTER_SIZE;
	}

	as_ctx(m_ctx)->set_zone(m_zone.get());

	m_buffer = (char*)::malloc(m_initial_buffer_size);
	if(!m_buffer) { throw std::bad_alloc(); }
	init_count(m_buffer);

	m_used = COUNTER_SIZE;
	m_free = m_initial_buffer_size - m_used;
	m_off  = COUNTER_SIZE;
}


unpacker::~unpacker()
{
	delete as_ctx(m_ctx);
	decl_count(m_buffer);
}

void unpacker::expand_buffer(size_t len)
{
	if(m_used == m_off && get_count(m_buffer) == 1 &&
			!as_ctx(m_ctx)->is_referenced()) {
		// rewind buffer
		m_free += m_used - COUNTER_SIZE;
		m_used = COUNTER_SIZE;
		m_off = COUNTER_SIZE;
		if(m_free >= len) { return; }
	}

	if(m_off == COUNTER_SIZE) {
		size_t next_size = (m_used + m_free) * 2;
		while(next_size < len + m_used) { next_size *= 2; }

		char* tmp = (char*)::realloc(m_buffer, next_size);
		if(!tmp) { throw std::bad_alloc(); }

		m_buffer = tmp;
		m_free = next_size - m_used;

	} else {
		size_t next_size = m_initial_buffer_size;  // include COUNTER_SIZE
		size_t not_parsed = m_used - m_off;
		while(next_size < len + not_parsed + COUNTER_SIZE) { next_size *= 2; }

		char* tmp = (char*)::malloc(next_size);
		if(!tmp) { throw std::bad_alloc(); }
		init_count(tmp);

		try {
			m_zone->push_finalizer(decl_count, m_buffer);
		} catch (...) { free(tmp); throw; }

		memcpy(tmp+COUNTER_SIZE, m_buffer+m_off, not_parsed);

		m_buffer = tmp;
		m_used = not_parsed + COUNTER_SIZE;
		m_free = next_size - m_used;
		m_off = COUNTER_SIZE;
	}
}

bool unpacker::execute()
{
	int ret = as_ctx(m_ctx)->execute(m_buffer, m_used, &m_off);
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
	m_zone->push_finalizer(decl_count, m_buffer);
	incr_count(m_buffer);

	//std::auto_ptr<zone> old(new zone());
	//m_zone.swap(old);
	zone* n = new zone();
	std::auto_ptr<zone> old(m_zone.release());
	m_zone.reset(n);

	as_ctx(m_ctx)->set_zone(m_zone.get());

	return old.release();
}

object unpacker::data()
{
	return as_ctx(m_ctx)->data();
}

void unpacker::reset()
{
	if(!m_zone->empty()) { delete release_zone(); }
	as_ctx(m_ctx)->reset();
}


object unpacker::unpack(const char* data, size_t len, zone& z, size_t* off)
{
	context ctx;
	ctx.set_zone(&z);
	if(off) {
		size_t noff = *off;
		int ret = ctx.execute(data, len, &noff);
		if(ret < 0) {
			throw unpack_error("parse error");
		} else if(ret == 0) {
			throw unpack_error("insufficient bytes");
		}
		*off = noff;
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

