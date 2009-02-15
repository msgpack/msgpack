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
#include "unpack_context.hpp"
#include <stdlib.h>

namespace msgpack {


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

	object_class* data()
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
	msgpack_unpacker m_ctx;

private:
	context();
	context(const context&);
};


unpacker::unpacker() :
	m_zone(new zone()),
	m_ctx(new context(m_zone)),
	m_buffer(NULL),
	m_used(0),
	m_free(0),
	m_off(0)
{ }


unpacker::~unpacker()
{
	free(m_buffer);
	delete m_ctx;
	delete m_zone;
}


void unpacker::expand_buffer(size_t len)
{
	if(m_off == 0) {
		size_t next_size;
		if(m_free != 0) { next_size = m_free * 2; }
		else { next_size = UNPACKER_INITIAL_BUFFER_SIZE; }
		while(next_size < len + m_used) { next_size *= 2; }

		char* tmp = (char*)realloc(m_buffer, next_size);
		if(!tmp) { throw std::bad_alloc(); }
		m_buffer = tmp;
		//char* tmp = (char*)malloc(next_size);
		//if(!tmp) { throw std::bad_alloc(); }
		//memcpy(tmp, m_buffer, m_used);
		//free(m_buffer);

		m_buffer = tmp;
		m_free = next_size - m_used;

	} else {
		size_t next_size = UNPACKER_INITIAL_BUFFER_SIZE;
		while(next_size < len + m_used - m_off) { next_size *= 2; }

		char* tmp = (char*)malloc(next_size);
		if(!tmp) { throw std::bad_alloc(); }
		memcpy(tmp, m_buffer+m_off, m_used-m_off);

		try {
			m_zone->push_finalizer<void>(&zone::finalize_free, NULL, m_buffer);
		} catch (...) {
			free(tmp);
			throw;
		}

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
		expand_buffer(0);
		return true;
	}
}

zone* unpacker::release_zone()
{
	zone* nz = new zone();
	zone* z = m_zone;
	m_zone = nz;
	m_ctx->user(m_zone);
	return z;
}

object unpacker::data()
{
	return object(m_ctx->data());
}

void unpacker::reset()
{
	if(m_off != 0) { expand_buffer(0); }
	if(!m_zone->empty()) {
		delete m_zone;
		m_zone = NULL;
		m_zone = new zone();
	}
	m_ctx->reset();
}


object unpacker::unpack(const char* data, size_t len, zone& z)
{
	context ctx(&z);
	size_t off = 0;
	int ret = ctx.execute(data, len, &off);
	if(ret < 0) {
		throw unpack_error("parse error");
	} else if(ret == 0) {
		throw unpack_error("insufficient bytes");
	} else if(off < len) {
		throw unpack_error("extra bytes");
	}
	return ctx.data();
}


}  // namespace msgpack

