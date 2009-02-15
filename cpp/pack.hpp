//
// MessagePack for C++ serializing routine
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
#ifndef MSGPACK_PACK_HPP__
#define MSGPACK_PACK_HPP__

#include <arpa/inet.h>  // __BYTE_ORDER
#include <stdexcept>
#include <limits.h>
#include "msgpack/pack_define.h"

namespace msgpack {


template <typename Stream>
class packer {
public:
	packer(Stream& s);

public:
	void pack_uint8(uint8_t d)			{ pack_uint8_impl(m_stream, d); }
	void pack_uint16(uint16_t d)		{ pack_uint16_impl(m_stream, d); }
	void pack_uint32(uint32_t d)		{ pack_uint32_impl(m_stream, d); }
	void pack_uint64(uint64_t d)		{ pack_uint64_impl(m_stream, d); }
	void pack_int8(uint8_t d)			{ pack_int8_impl(m_stream, d); }
	void pack_int16(uint16_t d)			{ pack_int16_impl(m_stream, d); }
	void pack_int32(uint32_t d)			{ pack_int32_impl(m_stream, d); }
	void pack_int64(uint64_t d)			{ pack_int64_impl(m_stream, d); }

	void pack_short(int d)				{ pack_short_impl(m_stream, d); }
	void pack_int(int d)				{ pack_int_impl(m_stream, d); }
	void pack_long(long d)				{ pack_long_impl(m_stream, d); }
	void pack_long_long(long long d)	{ pack_long_long_impl(m_stream, d); }
	void pack_unsigned_short(unsigned short d)			{ pack_unsigned_short_impl(m_stream, d); }
	void pack_unsigned_int(unsigned int d)				{ pack_unsigned_int_impl(m_stream, d); }
	void pack_unsigned_long_long(unsigned long long d)	{ pack_unsigned_long_long_impl(m_stream, d); }

	void pack_float(float d)			{ pack_float_impl(m_stream, d); }
	void pack_double(double d)			{ pack_double_impl(m_stream, d); }

	void pack_nil()						{ pack_nil_impl(m_stream); }
	void pack_true()					{ pack_true_impl(m_stream); }
	void pack_false()					{ pack_false_impl(m_stream); }

	void pack_array(unsigned int n)		{ pack_array_impl(m_stream, n); }

	void pack_map(unsigned int n)		{ pack_map_impl(m_stream, n); }

	void pack_raw(size_t l)						{ pack_raw_impl(m_stream, l); }
	void pack_raw_body(const char* b, size_t l)	{ pack_raw_body_impl(m_stream, b, l); }

private:
	static void pack_uint8_impl(Stream& x, uint8_t d);
	static void pack_uint16_impl(Stream& x, uint16_t d);
	static void pack_uint32_impl(Stream& x, uint32_t d);
	static void pack_uint64_impl(Stream& x, uint64_t d);
	static void pack_int8_impl(Stream& x, int8_t d);
	static void pack_int16_impl(Stream& x, int16_t d);
	static void pack_int32_impl(Stream& x, int32_t d);
	static void pack_int64_impl(Stream& x, int64_t d);

	static void pack_short_impl(Stream& x, short d);
	static void pack_int_impl(Stream& x, int d);
	static void pack_long_impl(Stream& x, long d);
	static void pack_long_long_impl(Stream& x, long long d);
	static void pack_unsigned_short_impl(Stream& x, unsigned short d);
	static void pack_unsigned_int_impl(Stream& x, unsigned int d);
	static void pack_unsigned_long_impl(Stream& x, unsigned long d);
	static void pack_unsigned_long_long_impl(Stream& x, unsigned long long d);

	static void pack_float_impl(Stream& x, float d);
	static void pack_double_impl(Stream& x, double d);

	static void pack_nil_impl(Stream& x);
	static void pack_true_impl(Stream& x);
	static void pack_false_impl(Stream& x);

	static void pack_array_impl(Stream& x, unsigned int n);

	static void pack_map_impl(Stream& x, unsigned int n);

	static void pack_raw_impl(Stream& x, size_t l);
	static void pack_raw_body_impl(Stream& x, const void* b, size_t l);

	static void append_buffer(Stream& x, const unsigned char* buf, unsigned int len)
		{ x.write((const char*)buf, len); }

private:
	Stream& m_stream;

private:
	packer();
};

#define msgpack_pack_inline_func(name) \
	template <typename Stream> \
	inline void packer<Stream>::pack_ ## name ## _impl

#define msgpack_pack_inline_func_cint(name) \
	template <typename Stream> \
	inline void packer<Stream>::pack_ ## name ## _impl

#define msgpack_pack_user Stream&

#define msgpack_pack_append_buffer append_buffer

#include "msgpack/pack_template.h"


template <typename Stream>
packer<Stream>::packer(Stream& s) : m_stream(s) { }


}  // namespace msgpack

#endif /* msgpack/pack.hpp */

