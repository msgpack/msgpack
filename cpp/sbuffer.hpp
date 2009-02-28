//
// MessagePack for C++ simple buffer implementation
//
// Copyright (C) 2008-2009 FURUHASHI Sadayuki
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
#ifndef MSGPACK_SBUFFER_HPP__
#define MSGPACK_SBUFFER_HPP__

#include "msgpack/sbuffer.h"
#include <stdexcept>

namespace msgpack {


class sbuffer : public msgpack_sbuffer {
public:
	sbuffer(size_t initsz = MSGPACK_SBUFFER_INIT_SIZE)
	{
		msgpack_sbuffer* sbuf = static_cast<msgpack_sbuffer*>(this);

		sbuf->data = (char*)::malloc(initsz);
		if(!sbuf->data) {
			throw std::bad_alloc();
		}

		sbuf->size = 0;
		sbuf->alloc = initsz;
	}

	~sbuffer()
	{
		msgpack_sbuffer* sbuf = static_cast<msgpack_sbuffer*>(this);
		::free(sbuf->data);
	}

public:
	void write(const char* buf, unsigned int len)
	{
		msgpack_sbuffer* sbuf = static_cast<msgpack_sbuffer*>(this);
		if(sbuf->alloc - sbuf->size < len) {
			expand_buffer(len);
		}
		memcpy(sbuf->data + sbuf->size, buf, len);
		sbuf->size += len;
	}

	char* data()
	{
		msgpack_sbuffer* sbuf = static_cast<msgpack_sbuffer*>(this);
		return sbuf->data;
	}

	const char* data() const
	{
		const msgpack_sbuffer* sbuf = static_cast<const msgpack_sbuffer*>(this);
		return sbuf->data;
	}

	size_t size() const
	{
		const msgpack_sbuffer* sbuf = static_cast<const msgpack_sbuffer*>(this);
		return sbuf->size;
	}

	char* release()
	{
		msgpack_sbuffer* sbuf = static_cast<msgpack_sbuffer*>(this);
		return msgpack_sbuffer_release(sbuf);
	}

private:
	void expand_buffer(size_t len)
	{
		msgpack_sbuffer* sbuf = static_cast<msgpack_sbuffer*>(this);

		size_t nsize = (sbuf->alloc) ?
				sbuf->alloc * 2 : MSGPACK_SBUFFER_INIT_SIZE;
	
		while(nsize < sbuf->size + len) { nsize *= 2; }
	
		void* tmp = realloc(sbuf->data, nsize);
		if(!tmp) {
			throw std::bad_alloc();
		}
	
		sbuf->data = (char*)tmp;
		sbuf->alloc = nsize;
	}

private:
	sbuffer(const sbuffer&);
};


}  // namespace msgpack

#endif /* msgpack/sbuffer.hpp */

