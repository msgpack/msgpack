//
// MessagePack for C++ memory pool
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
#include "msgpack/zone.hpp"
#include <algorithm>

namespace msgpack {


zone::zone(size_t chunk_size) :
	m_chunk_size(chunk_size)
{
	chunk dummy = {0, NULL, NULL};
	m_chunk_array.push_back(dummy);
}

zone::~zone()
{
	clear();
}

namespace {
	template <typename Private>
	struct zone_finalize {
		void operator() (Private& f) {
			(*f.func)(f.obj);
		}
	};

	template <typename Private>
	struct zone_free {
		void operator() (Private& c) {
			::free(c.alloc);
		}
	};
}

void zone::clear()
{
	std::for_each(m_finalizers.rbegin(), m_finalizers.rend(),
			zone_finalize<finalizer>());
	m_finalizers.clear();

	std::for_each(m_chunk_array.begin(), m_chunk_array.end(),
			zone_free<chunk>());
	m_chunk_array.resize(1);
	m_chunk_array[0].ptr  = NULL;
	m_chunk_array[0].free = 0;
}

bool zone::empty() const
{
	return m_chunk_array.back().alloc == NULL &&
		m_finalizers.empty();
}

void* zone::malloc(size_t size)
{
	if(m_chunk_array.back().free > size) {
		char* p = (char*)m_chunk_array.back().ptr;
		m_chunk_array.back().ptr   = p + size;
		m_chunk_array.back().free -= size;
		return p;
	}

	size_t sz = m_chunk_size;
	while(sz < size) { sz *= 2; }

	chunk dummy = {0, NULL, NULL};
	m_chunk_array.push_back(dummy);

	char* p = (char*)::malloc(sz);
	if(!p) {
		m_chunk_array.pop_back();
		throw std::bad_alloc();
	}

	m_chunk_array.back().free  = sz - size;
	m_chunk_array.back().ptr   = p + size;
	m_chunk_array.back().alloc = p;
	return p;
}


}  // namespace msgpack

