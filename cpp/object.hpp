//
// MessagePack for C++ static resolution routine
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
#ifndef MSGPACK_OBJECT_HPP__
#define MSGPACK_OBJECT_HPP__

#include "msgpack/object.h"
#include "msgpack/pack.hpp"
#include <stdint.h>
#include <string.h>
#include <stdexcept>
#include <typeinfo>
#include <limits>
#include <ostream>

namespace msgpack {


class type_error : public std::bad_cast { };


namespace type {
	enum object_type {
		NIL					= 0x01,
		BOOLEAN				= 0x02,
		POSITIVE_INTEGER	= 0x03,
		NEGATIVE_INTEGER	= 0x04,
		DOUBLE				= 0x05,
		RAW					= 0x06,
		ARRAY				= 0x07,
		MAP					= 0x08,
	};
}


struct object;
struct object_kv;

struct object_array {
	uint32_t size;
	object* ptr;
};

struct object_map {
	uint32_t size;
	object_kv* ptr;
};

struct object_raw {
	uint32_t size;
	const char* ptr;
};

struct object {
	union union_type {
		bool boolean;
		uint64_t u64;
		int64_t  i64;
		double   dec;
		object_array array;
		object_map map;
		object_raw raw;
		object_raw ref;  // obsolete
	};

	type::object_type type;
	union_type via;

	bool is_nil() { return type == type::NIL; }

	template <typename T>
	T as();

	template <typename T>
	void convert(T* v);

	object();
	object(msgpack_object obj);
	operator msgpack_object();

private:
	struct implicit_type;

public:
	implicit_type convert();
};

struct object_kv {
	object key;
	object val;
};

bool operator==(const object x, const object y);
bool operator!=(const object x, const object y);

std::ostream& operator<< (std::ostream& s, const object o);


template <typename Stream, typename T>
packer<Stream>& operator<< (packer<Stream>& o, const T& v);

template <typename T>
T& operator>> (object o, T& v);


struct object::implicit_type {
	implicit_type(object o) : obj(o) { }
	~implicit_type() { }

	template <typename T>
	operator T() { return obj.as<T>(); }

private:
	object obj;
};


template <typename Type>
class define : public Type {
public:
	typedef Type msgpack_type;
	typedef define<Type> define_type;

	define() {}
	define(const msgpack_type& v) : msgpack_type(v) {}

	template <typename Packer>
	void msgpack_pack(Packer& o) const
	{
		o << static_cast<const msgpack_type&>(*this);
	}

	void msgpack_unpack(object o)
	{
		o >> static_cast<msgpack_type&>(*this);
	}
};


template <typename Stream>
template <typename T>
inline packer<Stream>& packer<Stream>::pack(const T& v)
{
	*this << v;
	return *this;
}

inline object& operator>> (object o, object& v)
{
	v = o;
	return v;
}

template <typename T>
inline T& operator>> (object o, T& v)
{
	v.msgpack_unpack(o.convert());
	return v;
}

template <typename Stream, typename T>
inline packer<Stream>& operator<< (packer<Stream>& o, const T& v)
{
	v.msgpack_pack(o);
	return o;
}


inline bool operator!=(const object x, const object y)
{ return !(x == y); }


inline object::object() { }

inline object::object(msgpack_object obj)
{
	// FIXME beter way?
	::memcpy(this, &obj, sizeof(obj));
}

inline object::operator msgpack_object()
{
	// FIXME beter way?
	msgpack_object obj;
	::memcpy(&obj, this, sizeof(obj));
	return obj;
}


inline object::implicit_type object::convert()
{
	return implicit_type(*this);
}

template <typename T>
inline T object::as()
{
	T v;
	convert(&v);
	return v;
}

template <typename T>
inline void object::convert(T* v)
{
	*this >> *v;
}


// obsolete
template <typename T>
inline void convert(T& v, object o)
{
	o.convert(&v);
}

// obsolete
template <typename Stream, typename T>
inline void pack(packer<Stream>& o, const T& v)
{
	o.pack(v);
}

// obsolete
template <typename Stream, typename T>
inline void pack_copy(packer<Stream>& o, T v)
{
	pack(o, v);
}


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
		o.pack_raw(v.via.raw.size);
		o.pack_raw_body(v.via.raw.ptr, v.via.raw.size);
		return o;

	case type::ARRAY:
		o.pack_array(v.via.array.size);
		for(object* p(v.via.array.ptr),
				* const pend(v.via.array.ptr + v.via.array.size);
				p < pend; ++p) {
			o << *p;
		}
		return o;

	case type::MAP:
		o.pack_map(v.via.map.size);
		for(object_kv* p(v.via.map.ptr),
				* const pend(v.via.map.ptr + v.via.map.size);
				p < pend; ++p) {
			o << p->key;
			o << p->val;
		}
		return o;

	default:
		throw type_error();
	}
}


}  // namespace msgpack

#include "msgpack/type.hpp"

#endif /* msgpack/object.hpp */

