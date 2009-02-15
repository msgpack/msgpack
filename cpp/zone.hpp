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
#ifndef MSGPACK_ZONE_HPP__
#define MSGPACK_ZONE_HPP__

#include "msgpack/object.hpp"
#include <cstdlib>
#include <vector>

namespace msgpack {


class zone {
public:
	zone();
	~zone();

public:
	char* malloc(size_t count);
	char* realloc(char* ptr, size_t count);
	object* malloc_container(size_t count);

	void clear();

private:
	std::vector<char*> m_ptrs;

private:
	char* realloc_real(char* ptr, size_t count);

private:
	zone(const zone&);
};


inline zone::zone() { }

inline zone::~zone() { clear(); }

inline char* zone::malloc(size_t count)
{
	char* ptr = (char*)::malloc(count);
	if(!ptr) { throw std::bad_alloc(); }
	try {
		m_ptrs.push_back(ptr);
	} catch (...) {
		free(ptr);
		throw;
	}
	return ptr;
}

inline char* zone::realloc(char* ptr, size_t count)
{
	if(ptr == NULL) {
		return zone::malloc(count);
	} else {
		return realloc_real(ptr, count);
	}
}

inline object* zone::malloc_container(size_t count)
{
	return (object*)zone::malloc(sizeof(object)*count);
}


}  // namespace msgpack

#endif /* msgpack/zone.hpp */

