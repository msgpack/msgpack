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

#include <string.h>
#include <stdlib.h>
#include <stdexcept>

namespace msgpack {


class sbuffer {
public:
	sbuffer() : m_capacity(0), m_size(0), m_ptr(NULL) { }

	~sbuffer()
	{
		free(m_ptr);
	}

public:
	void write(const char* buf, size_t len)
	{
		if(m_capacity - m_size < len) {
			size_t nsize = (m_capacity ? m_capacity*2 : 2048);
			while(nsize < m_size + len) { nsize *= 2; }
	
			char* tmp = (char*)realloc(m_ptr, nsize);
			if(!tmp) { throw std::bad_alloc(); }
	
			m_ptr = tmp;
			m_capacity = nsize;
		}
		memcpy(m_ptr + m_size, buf, len);
		m_size += len;
	}

	char* data()
	{
		return m_ptr;
	}

	size_t size() const
	{
		return m_size;
	}

	char* release()
	{
		char* tmp = m_ptr;
		m_capacity = 0;
		m_size = 0;
		m_ptr = NULL;
		return tmp;
	}

private:
	size_t m_capacity;
	size_t m_size;
	char* m_ptr;

private:
	sbuffer(const sbuffer&);
};


}  // namespace msgpack

#endif /* msgpack/sbuffer.hpp */

