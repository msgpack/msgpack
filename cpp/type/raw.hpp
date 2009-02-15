//
// MessagePack for C++ static resolution routine
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
#ifndef MSGPACK_TYPE_RAW_HPP__
#define MSGPACK_TYPE_RAW_HPP__

#include "msgpack/object.hpp"
#include <string.h>
#include <string>

namespace msgpack {
namespace type {


struct raw_ref {
	raw_ref() : ptr(NULL), size(0) {}
	raw_ref(const char* p, uint32_t s) : ptr(p), size(s) {}

	const char* ptr;
	uint32_t size;

	std::string str() { return std::string(ptr, size); }

	bool operator== (const raw_ref& x)
	{
		return size == x.size && memcmp(ptr, x.ptr, size) == 0;
	}

	bool operator!= (const raw_ref& x)
	{
		return !(*this != x);
	}

	bool operator< (const raw_ref& x)
	{
		if(size == x.size) { return memcmp(ptr, x.ptr, size) < 0; }
		else { return size < x.size; }
	}

	bool operator> (const raw_ref& x)
	{
		if(size == x.size) { return memcmp(ptr, x.ptr, size) > 0; }
		else { return size > x.size; }
	}
};

inline raw_ref& operator<< (raw_ref& v, object o)
{
	if(o.type != RAW) { throw type_error(); }
	v.ptr  = o.via.ref.ptr;
	v.size = o.via.ref.size;
	return v;
}


inline std::string& operator<< (std::string& v, object o)
{
	raw_ref r;
	r << o;
	v.assign(r.ptr, r.size);
	return v;
}


template <typename Stream>
inline const raw_ref& operator>> (const raw_ref& v, packer<Stream>& o)
{
	o.pack_raw(v.ptr, v.size);
	return v;
}


template <typename Stream>
inline const std::string& operator>> (const std::string& v, packer<Stream>& o)
{
	o.pack_raw(v.data(), v.size());
	return v;
}


}  // namespace type
}  // namespace msgpack

#endif /* msgpack/type/raw.hpp */

