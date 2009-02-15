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
#ifndef MSGPACK_TYPE_INTEGER_HPP__
#define MSGPACK_TYPE_INTEGER_HPP__

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
			if(o.type == POSITIVE_INTEGER) {
				if(o.via.u64 > (uint64_t)std::numeric_limits<T>::max())
					{ throw type_error(); }
				return o.via.u64;
			} else if(o.type == NEGATIVE_INTEGER) {
				if(o.via.i64 < (int64_t)-std::numeric_limits<T>::max())
					{ throw type_error(); }
				return o.via.i64;
			}
			throw type_error();
		}
	};
	
	template <typename T>
	struct convert_integer_sign<T, false> {
		static inline T convert(object o) {
			if(o.type == POSITIVE_INTEGER) {
				if(o.via.u64 > (uint64_t)std::numeric_limits<T>::max())
					{ throw type_error(); }
				return o.via.u64;
			}
			throw type_error();
		}
	};
	
	template <typename T>
	static inline T convert_integer(object o)
	{
		return detail::convert_integer_sign<T, std::numeric_limits<T>::is_signed>::convert(o);
	}



	template <typename T, typename Stream, int Size, bool Signed>
	struct pack_integer_size_sign;

	template <typename T, typename Stream>
	struct pack_integer_size_sign<T, Stream, 1, true> {
		static inline void pack(T v, packer<Stream>& o)
			{ o.pack_int8(v); }
	};

	template <typename T, typename Stream>
	struct pack_integer_size_sign<T, Stream, 1, false> {
		static inline void pack(T v, packer<Stream>& o)
			{ o.pack_uint8(v); }
	};

	template <typename T, typename Stream>
	struct pack_integer_size_sign<T, Stream, 2, true> {
		static inline void pack(T v, packer<Stream>& o) {
			if( (int16_t)v <= (int16_t)std::numeric_limits<int8_t>::max() &&
				(int16_t)v >= (int16_t)std::numeric_limits<int8_t>::min())
				{ o.pack_int8(v); }
			else { o.pack_int16(v); }
		}
	};

	template <typename T, typename Stream>
	struct pack_integer_size_sign<T, Stream, 2, false> {
		static inline void pack(T v, packer<Stream>& o) {
			if( (uint16_t)v <= (uint16_t)std::numeric_limits<uint8_t>::max())
				{ o.pack_uint8(v); }
			else { o.pack_uint16(v); }
		}
	};

	template <typename T, typename Stream>
	struct pack_integer_size_sign<T, Stream, 4, true> {
		static inline void pack(T v, packer<Stream>& o) {
			if( (int32_t)v <= (int32_t)std::numeric_limits<int8_t>::max() &&
				(int32_t)v >= (int32_t)std::numeric_limits<int8_t>::min())
				{ o.pack_int8(v); }
			else if( (int32_t)v <= (int32_t)std::numeric_limits<int16_t>::max() &&
					 (int32_t)v >= (int32_t)std::numeric_limits<int16_t>::min())
				{ o.pack_int16(v); }
			else { o.pack_int32(v); }
		}
	};

	template <typename T, typename Stream>
	struct pack_integer_size_sign<T, Stream, 4, false> {
		static inline void pack(T v, packer<Stream>& o) {
			if( (uint32_t)v <= (uint32_t)std::numeric_limits<uint8_t>::max())
				{ o.pack_uint8(v); }
			else if( (uint32_t)v <= (uint32_t)std::numeric_limits<uint16_t>::max())
				{ o.pack_uint16(v); }
			else { o.pack_uint32(v); }
		}
	};

	template <typename T, typename Stream>
	struct pack_integer_size_sign<T, Stream, 8, true> {
		static inline void pack(T v, packer<Stream>& o) {
			if( (int64_t)v <= (int64_t)std::numeric_limits<int8_t>::max() &&
				(int64_t)v >= (int64_t)std::numeric_limits<int8_t>::min())
				{ o.pack_int8(v); }
			else if( (int64_t)v <= (int64_t)std::numeric_limits<int16_t>::max() &&
					 (int64_t)v >= (int64_t)std::numeric_limits<int16_t>::min())
				{ o.pack_int16(v); }
			else if( (int64_t)v <= (int64_t)std::numeric_limits<int32_t>::max() &&
					 (int64_t)v >= (int64_t)std::numeric_limits<int32_t>::min())
				{ o.pack_int32(v); }
			else { o.pack_int64(v); }
		}
	};

	template <typename T, typename Stream>
	struct pack_integer_size_sign<T, Stream, 8, false> {
		static inline void pack(T v, packer<Stream>& o) {
			if( (uint64_t)v <= (uint64_t)std::numeric_limits<uint8_t>::max())
				{ o.pack_uint8(v); }
			else if( (uint64_t)v <= (uint64_t)std::numeric_limits<uint16_t>::max())
				{ o.pack_uint16(v); }
			else if( (uint64_t)v <= (uint64_t)std::numeric_limits<uint32_t>::max())
				{ o.pack_uint32(v); }
			else { o.pack_uint64(v); }
		}
	};


	template <typename T, typename Stream>
	static inline void pack_integer(T v, packer<Stream>& o)
	{
		pack_integer_size_sign<T, Stream, sizeof(T), std::numeric_limits<T>::is_signed>::pack(v, o);
	}

}  // namespace detail


inline signed char& operator<< (signed char& v, object o)
	{ v = detail::convert_integer<signed char>(o); return v; }

inline signed short& operator<< (signed short& v, object o)
	{ v = detail::convert_integer<signed short>(o); return v; }

inline signed int& operator<< (signed int& v, object o)
	{ v = detail::convert_integer<signed int>(o); return v; }

inline signed long& operator<< (signed long& v, object o)
	{ v = detail::convert_integer<signed long>(o); return v; }

inline signed long long& operator<< (signed long long& v, object o)
	{ v = detail::convert_integer<signed long long>(o); return v; }


inline unsigned char& operator<< (unsigned char& v, object o)
	{ v = detail::convert_integer<unsigned char>(o); return v; }

inline unsigned short& operator<< (unsigned short& v, object o)
	{ v = detail::convert_integer<unsigned short>(o); return v; }

inline unsigned int& operator<< (unsigned int& v, object o)
	{ v = detail::convert_integer<unsigned int>(o); return v; }

inline unsigned long& operator<< (unsigned long& v, object o)
	{ v = detail::convert_integer<unsigned long>(o); return v; }

inline unsigned long long& operator<< (unsigned long long& v, object o)
	{ v = detail::convert_integer<unsigned long long>(o); return v; }


template <typename Stream>
inline const signed char& operator>> (const signed char& v, packer<Stream> o)
	{ detail::pack_integer<signed char>(v, o); return v; }

template <typename Stream>
inline const signed short& operator>> (const signed short& v, packer<Stream> o)
	{ detail::pack_integer<signed short>(v, o); return v; }

template <typename Stream>
inline const signed int& operator>> (const signed int& v, packer<Stream> o)
	{ detail::pack_integer<signed int>(v, o); return v; }

template <typename Stream>
inline const signed long& operator>> (const signed long& v, packer<Stream> o)
	{ detail::pack_integer<signed long>(v, o); return v; }

template <typename Stream>
inline const signed long long& operator>> (const signed long long& v, packer<Stream> o)
	{ detail::pack_integer<signed long long>(v, o); return v; }


template <typename Stream>
inline const unsigned char& operator>> (const unsigned char& v, packer<Stream> o)
	{ detail::pack_integer<unsigned char>(v, o); return v; }

template <typename Stream>
inline const unsigned short& operator>> (const unsigned short& v, packer<Stream> o)
	{ detail::pack_integer<unsigned short>(v, o); return v; }

template <typename Stream>
inline const unsigned int& operator>> (const unsigned int& v, packer<Stream> o)
	{ detail::pack_integer<unsigned int>(v, o); return v; }

template <typename Stream>
inline const unsigned long& operator>> (const unsigned long& v, packer<Stream> o)
	{ detail::pack_integer<unsigned long>(v, o); return v; }

template <typename Stream>
inline const unsigned long long& operator>> (const unsigned long long& v, packer<Stream> o)
	{ detail::pack_integer<unsigned long long>(v, o); return v; }


}  // namespace type
}  // namespace msgpack

#endif /* msgpack/type/integer.hpp */

