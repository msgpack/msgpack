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


void zone::clear()
{
	for(std::vector<char*>::iterator it(m_ptrs.begin()), it_end(m_ptrs.end());
			it != it_end; ++it) {
		free(*it);
	}
	m_ptrs.clear();
}

char* zone::realloc_real(char* ptr, size_t count)
{
	for(std::vector<char*>::reverse_iterator it(m_ptrs.rbegin()), it_end(m_ptrs.rend());
			it != it_end; ++it) {
		if(*it == ptr) {
			char* tmp = (char*)::realloc(ptr, count);
			if(!tmp) { throw std::bad_alloc(); }
			*it = tmp;
			return tmp;
		}
	}
	throw std::bad_alloc();
}


}  // namespace msgpack

