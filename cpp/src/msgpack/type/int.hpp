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
#ifndef MSGPACK_TYPE_INT_HPP__
#define MSGPACK_TYPE_INT_HPP__

#include "msgpack/object.hpp"
#include <limits>

namespace msgpack {


namespace type {
namespace detail {
	template <typename T, bool Signed>
	struct convert_integer_sign;

	template <typename T>
	struct convert_integer_sign<T, true> {
		static inline T convert(object o) {
			if(o.type == type::POSITIVE_INTEGER) {
				if(o.via.u64 > (uint64_t)std::numeric_limits<T>::max())
					{ throw type_error(); }
				return (T)o.via.u64;
			} else if(o.type == type::NEGATIVE_INTEGER) {
				if(o.via.i64 < (int64_t)std::numeric_limits<T>::min())
					{ throw type_error(); }
				return (T)o.via.i64;
			}
			throw type_error();
		}
	};
	
	template <typename T>
	struct convert_integer_sign<T, false> {
		static inline T convert(object o) {
			if(o.type == type::POSITIVE_INTEGER) {
				if(o.via.u64 > (uint64_t)std::numeric_limits<T>::max())
					{ throw type_error(); }
				return (T)o.via.u64;
			}
			throw type_error();
		}
	};

	template <typename T>
	static inline T convert_integer(object o)
	{
		return detail::convert_integer_sign<T, std::numeric_limits<T>::is_signed>::convert(o);
	}

}  // namespace detail
}  // namespace type


inline signed char& operator>> (object o, signed char& v)
	{ v = type::detail::convert_integer<signed char>(o); return v; }

inline signed short& operator>> (object o, signed short& v)
	{ v = type::detail::convert_integer<signed short>(o); return v; }

inline signed int& operator>> (object o, signed int& v)
	{ v = type::detail::convert_integer<signed int>(o); return v; }

inline signed long& operator>> (object o, signed long& v)
	{ v = type::detail::convert_integer<signed long>(o); return v; }

inline signed long long& operator>> (object o, signed long long& v)
	{ v = type::detail::convert_integer<signed long long>(o); return v; }


inline unsigned char& operator>> (object o, unsigned char& v)
	{ v = type::detail::convert_integer<unsigned char>(o); return v; }

inline unsigned short& operator>> (object o, unsigned short& v)
	{ v = type::detail::convert_integer<unsigned short>(o); return v; }

inline unsigned int& operator>> (object o, unsigned int& v)
	{ v = type::detail::convert_integer<unsigned int>(o); return v; }

inline unsigned long& operator>> (object o, unsigned long& v)
	{ v = type::detail::convert_integer<unsigned long>(o); return v; }

inline unsigned long long& operator>> (object o, unsigned long long& v)
	{ v = type::detail::convert_integer<unsigned long long>(o); return v; }


template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const signed char& v)
	{ o.pack_int8(v); return o; }

template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const signed short& v)
	{ o.pack_short(v); return o; }

template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const signed int& v)
	{ o.pack_int(v); return o; }

template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const signed long& v)
	{ o.pack_long(v); return o; }

template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const signed long long& v)
	{ o.pack_long_long(v); return o; }


template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const unsigned char& v)
	{ o.pack_uint8(v); return o; }

template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const unsigned short& v)
	{ o.pack_unsigned_short(v); return o; }

template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const unsigned int& v)
	{ o.pack_unsigned_int(v); return o; }

template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const unsigned long& v)
	{ o.pack_unsigned_long(v); return o; }

template <typename Stream>
inline packer<Stream>& operator<< (packer<Stream>& o, const unsigned long long& v)
	{ o.pack_unsigned_long_long(v); return o; }


inline void operator<< (object& o, signed char v)
	{ v < 0 ? o.type = type::NEGATIVE_INTEGER, o.via.i64 = v : o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }

inline void operator<< (object& o, signed short v)
	{ v < 0 ? o.type = type::NEGATIVE_INTEGER, o.via.i64 = v : o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }

inline void operator<< (object& o, signed int v)
	{ v < 0 ? o.type = type::NEGATIVE_INTEGER, o.via.i64 = v : o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }

inline void operator<< (object& o, signed long v)
	{ v < 0 ? o.type = type::NEGATIVE_INTEGER, o.via.i64 = v : o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }

inline void operator<< (object& o, signed long long v)
	{ v < 0 ? o.type = type::NEGATIVE_INTEGER, o.via.i64 = v : o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }


inline void operator<< (object& o, unsigned char v)
	{ o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }

inline void operator<< (object& o, unsigned short v)
	{ o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }

inline void operator<< (object& o, unsigned int v)
	{ o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }

inline void operator<< (object& o, unsigned long v)
	{ o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }

inline void operator<< (object& o, unsigned long long v)
	{ o.type = type::POSITIVE_INTEGER, o.via.u64 = v; }


inline void operator<< (object::with_zone& o, signed char v)
	{ static_cast<object&>(o) << v; }

inline void operator<< (object::with_zone& o, signed short v)
	{ static_cast<object&>(o) << v; }

inline void operator<< (object::with_zone& o, signed int v)
	{ static_cast<object&>(o) << v; }

inline void operator<< (object::with_zone& o, signed long v)
	{ static_cast<object&>(o) << v; }

inline void operator<< (object::with_zone& o, signed long long v)
	{ static_cast<object&>(o) << v; }


inline void operator<< (object::with_zone& o, unsigned char v)
	{ static_cast<object&>(o) << v; }

inline void operator<< (object::with_zone& o, unsigned short v)
	{ static_cast<object&>(o) << v; }

inline void operator<< (object::with_zone& o, unsigned int v)
	{ static_cast<object&>(o) << v; }

inline void operator<< (object::with_zone& o, unsigned long v)
	{ static_cast<object&>(o) << v; }

inline void operator<< (object::with_zone& o, unsigned long long v)
	{ static_cast<object&>(o) << v; }


}  // namespace msgpack

#endif /* msgpack/type/int.hpp */

