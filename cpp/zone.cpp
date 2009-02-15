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

namespace msgpack {


// FIXME custom allocator?

void zone::expand_chunk()
{
	cell_t* chunk = (cell_t*)malloc(sizeof(cell_t)*ZONE_CHUNK_SIZE);
	if(!chunk) { throw std::bad_alloc(); }
	try {
		m_pool.push_back(chunk);
	} catch (...) {
		free(chunk);
		throw;
	}
}

void zone::clear()
{
	if(!m_pool.empty()) {
		size_t base_size = m_used / ZONE_CHUNK_SIZE;
		size_t extend_size = m_used % ZONE_CHUNK_SIZE;
		for(size_t b=0; b < base_size; ++b) {
			cell_t* c(m_pool[b]);
			for(size_t e=0; e < ZONE_CHUNK_SIZE; ++e) {
				reinterpret_cast<object_class*>(c[e].data)->~object_class();
			}
		}
		cell_t* c(m_pool.back());
		for(size_t e=0; e < extend_size; ++e) {
			reinterpret_cast<object_class*>(c[e].data)->~object_class();
		}

		for(pool_t::iterator it(m_pool.begin()), it_end(m_pool.end());
				it != it_end;
				++it) {
			free(*it);
		}
		m_pool.clear();
	}
	m_used = 0;

	for(user_finalizer_t::reverse_iterator it(m_user_finalizer.rbegin()),
					it_end(m_user_finalizer.rend());
			it != it_end;
			++it) {
		it->call();
	}
	m_user_finalizer.clear();
}


}  // namespace msgpack

