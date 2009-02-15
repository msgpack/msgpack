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
#include <limits>
#include <ostream>

namespace msgpack {


class type_error : public std::bad_cast { };


namespace type {
	static const unsigned char NIL					= 0x01;
	static const unsigned char BOOLEAN				= 0x02;
	static const unsigned char POSITIVE_INTEGER		= 0x03;
	static const unsigned char NEGATIVE_INTEGER		= 0x04;
	static const unsigned char DOUBLE				= 0x05;
	static const unsigned char RAW					= 0x06;
	static const unsigned char ARRAY				= 0x07;
	static const unsigned char MAP					= 0x08;
}


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

	template <typename T>
	operator T() { T v; convert(v, *this); return v; };

	template <typename T>
	T as() { T v; convert(v, *this); return v; }

	bool is_nil() { return type == type::NIL; }
};

std::ostream& operator<< (std::ostream& s, const object o);

bool operator==(const object x, const object y);
inline bool operator!=(const object x, const object y) { return !(x == y); }


inline object& operator>> (object o, object& v)
	{ v = o; return v; }

template <typename Stream>
packer<Stream>& operator<< (packer<Stream>& o, const object& v);



template <typename T>
inline void convert(T& v, object o)
{
	o >> v;
}

template <typename Stream, typename T>
inline void pack(packer<Stream>& o, const T& v)
{
	o << v;
}

template <typename Stream, typename T>
inline void pack(Stream& s, const T& v)
{
	packer<Stream> pk(s);
	pack(pk, v);
}

template <typename Stream, typename T>
inline void pack_copy(packer<Stream>& o, T v)
{
	pack(o, v);
}

	

template <typename T>
inline T& operator>> (object o, T& v)
{
	v.msgpack_unpack(o);
	return v;
}

template <typename Stream, typename T>
inline packer<Stream>& operator<< (packer<Stream>& o, const T& v)
{
	o << v.msgpack_pack();
	return o;
}


template <typename Type>
class define : public Type {
public:
	typedef Type msgpack_type;
	typedef define<Type> define_type;

	define() {}
	define(msgpack_type v) : msgpack_type(v) {}

	msgpack_type msgpack_pack() const
	{
		return *this;
	}

	void msgpack_unpack(object o)
	{
		convert(static_cast<msgpack_type&>(*this), o);
	}
};



template <typename Stream>
packer<Stream>& operator<< (packer<Stream>& o, const object& v)
{
	switch(v.type) {
	case type::NIL:
		o.pack_nil();
		return o;

	case type::BOOLEAN:
		if(v.via.boolean) {
			o.pack_true();
		} else {
			o.pack_false();
		}
		return o;

	case type::POSITIVE_INTEGER:
		if(v.via.u64 <= (uint64_t)std::numeric_limits<uint16_t>::max()) {
			if(v.via.u64 <= (uint16_t)std::numeric_limits<uint8_t>::max()) {
				o.pack_uint8(v.via.u64);
			} else {
				o.pack_uint16(v.via.u64);
			}
		} else {
			if(v.via.u64 <= (uint64_t)std::numeric_limits<uint32_t>::max()) {
				o.pack_uint32(v.via.u64);
			} else {
				o.pack_uint64(v.via.u64);
			}
		}
		return o;

	case type::NEGATIVE_INTEGER:
		if(v.via.i64 >= (int64_t)std::numeric_limits<int16_t>::min()) {
			if(v.via.i64 >= (int64_t)std::numeric_limits<int8_t>::min()) {
				o.pack_int8(v.via.i64);
			} else {
				o.pack_int16(v.via.i64);
			}
		} else {
			if(v.via.i64 >= (int64_t)std::numeric_limits<int32_t>::min()) {
				o.pack_int64(v.via.i64);
			} else {
				o.pack_int64(v.via.i64);
			}
		}
		return o;

	case type::RAW:
		o.pack_raw(v.via.ref.size);
		o.pack_raw_body(v.via.ref.ptr, v.via.ref.size);
		return o;

	case type::ARRAY:
		o.pack_array(v.via.container.size);
		for(object* p(v.via.container.ptr),
				* const pend(v.via.container.ptr + v.via.container.size);
				p < pend; ++p) {
			*p >> o;
		}
		return o;
		// FIXME loop optimiziation

	case type::MAP:
		o.pack_map(v.via.container.size);
		for(object* p(v.via.container.ptr),
				* const pend(v.via.container.ptr + v.via.container.size*2);
				p < pend; ) {
			*p >> o; ++p;
			*p >> o; ++p;
		}
		return o;
		// FIXME loop optimiziation

	default:
		throw type_error();
	}
}


}  // namespace msgpack

#include "msgpack/type.hpp"

#endif /* msgpack/object.hpp */

