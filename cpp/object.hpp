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
#ifndef MSGPACK_OBJECT_HPP__
#define MSGPACK_OBJECT_HPP__

#include "msgpack/pack.hpp"
#include <stdint.h>
#include <stdexcept>
#include <typeinfo>
#include <ostream>

namespace msgpack {


class type_error : public std::bad_cast { };


struct object {
	unsigned char type;
	union {
		bool boolean;
		uint64_t u64;
		int64_t  i64;
		double   dec;
		struct {
			object* ptr;
			uint32_t size;
		} container;
		struct {
			const char* ptr;
			uint32_t size;
		} ref;
	} via;
	// FIXME template <typename T> operator T() { T v; convert(*this, v); return v; };
};

std::ostream& operator<< (std::ostream& s, const object o);

bool operator==(const object x, const object y);
inline bool operator!=(const object x, const object y) { return !(x == y); }


template <typename Stream>
const object& operator>> (const object& v, packer<Stream>& o);


namespace type {
	static const unsigned char NIL					= 0x01;
	static const unsigned char BOOLEAN				= 0x02;
	static const unsigned char POSITIVE_INTEGER		= 0x03;
	static const unsigned char NEGATIVE_INTEGER		= 0x04;
	static const unsigned char DOUBLE				= 0x05;
	static const unsigned char RAW					= 0x06;
	static const unsigned char ARRAY				= 0x07;
	static const unsigned char MAP					= 0x08;


	template <typename T>
	inline T& operator<< (T& v, object o)
	{
		v = o;
		return v;
	}


	namespace detail {
		template <typename Stream, typename T>
		inline void pack_copy(T v, packer<Stream>& o)
			{ pack(v, o); }
	}

	template <typename Stream, typename T>
	inline const T& operator>> (const T& v, packer<Stream>& o)
	{
		detail::pack_copy(v.pack(), o);
		return v;
	}

}  // namespace type


template <typename T>
inline void convert(T& v, object o)
{
	using namespace type;
	v << o;
}


template <typename Stream, typename T>
inline void pack(T& v, packer<Stream>& o)
{
	using namespace type;
	v >> o;
}


template <typename Stream, typename T>
inline void pack(T& v, Stream& s)
{
	packer<Stream> pk(s);
	pack(v, pk);
}


}  // namespace msgpack

#include "msgpack/type.hpp"

#endif /* msgpack/object.hpp */

