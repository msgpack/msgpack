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

namespace msgpack {


template <typename Stream>
class packer {
public:
	packer(Stream& s);

public:
	void pack_int(int d)					{ pack_int_impl(m_stream, d); }
	void pack_unsigned_int(unsigned int d)	{ pack_unsigned_int_impl(m_stream, d); }
	void pack_uint8(uint8_t d)				{ pack_uint8_impl(m_stream, d); }
	void pack_uint16(uint16_t d)			{ pack_uint16_impl(m_stream, d); }
	void pack_uint32(uint32_t d)			{ pack_uint32_impl(m_stream, d); }
	void pack_uint64(uint64_t d)			{ pack_uint64_impl(m_stream, d); }
	void pack_int8(uint8_t d)				{ pack_int8_impl(m_stream, d); }
	void pack_int16(uint16_t d)				{ pack_int16_impl(m_stream, d); }
	void pack_int32(uint32_t d)				{ pack_int32_impl(m_stream, d); }
	void pack_int64(uint64_t d)				{ pack_int64_impl(m_stream, d); }
	void pack_float(float d)				{ pack_float_impl(m_stream, d); }
	void pack_double(double d)				{ pack_double_impl(m_stream, d); }
	void pack_nil()							{ pack_nil_impl(m_stream); }
	void pack_true()						{ pack_true_impl(m_stream); }
	void pack_false()						{ pack_false_impl(m_stream); }
	void pack_array(unsigned int n)			{ pack_array_impl(m_stream, n); }
	void pack_map(unsigned int n)			{ pack_map_impl(m_stream, n); }
	void pack_raw(const char* b, size_t l)	{ pack_raw_impl(m_stream, (const void*)b, l); }

private:
	static void pack_int_impl(Stream& x, int d);
	static void pack_unsigned_int_impl(Stream& x, unsigned int d);
	static void pack_uint8_impl(Stream& x, uint8_t d);
	static void pack_uint16_impl(Stream& x, uint16_t d);
	static void pack_uint32_impl(Stream& x, uint32_t d);
	static void pack_uint64_impl(Stream& x, uint64_t d);
	static void pack_int8_impl(Stream& x, int8_t d);
	static void pack_int16_impl(Stream& x, int16_t d);
	static void pack_int32_impl(Stream& x, int32_t d);
	static void pack_int64_impl(Stream& x, int64_t d);
	static void pack_float_impl(Stream& x, float d);
	static void pack_double_impl(Stream& x, double d);
	static void pack_nil_impl(Stream& x);
	static void pack_true_impl(Stream& x);
	static void pack_false_impl(Stream& x);
	static void pack_array_impl(Stream& x, unsigned int n);
	static void pack_map_impl(Stream& x, unsigned int n);
	static void pack_raw_impl(Stream& x, const void* b, size_t l);
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
#define msgpack_pack_user Stream&
#define msgpack_pack_append_buffer append_buffer
#include "msgpack/pack_template.h"


template <typename Stream>
packer<Stream>::packer(Stream& s) : m_stream(s) { }


/*
class dynamic_stream {
public:
	template <typename Stream>
	dynamic_stream(Stream& s);
public:
	void write(const char* buf, size_t len)
		{ (*m_function)(m_object, buf, len); }
private:
	void* m_object;
	void (*m_function)(void* object, const char* buf, size_t len);
private:
	struct write_trampoline;
};


class dynamic_packer {
public:
	template <typename Stream>
	dynamic_packer(Stream& s);

public:
	void pack_int(int d)					{ pack_int_impl(m_stream, d); }
	void pack_unsigned_int(unsigned int d)	{ pack_unsigned_int_impl(m_stream, d); }
	void pack_uint8(uint8_t d)				{ pack_uint8_impl(m_stream, d); }
	void pack_uint16(uint16_t d)			{ pack_uint16_impl(m_stream, d); }
	void pack_uint32(uint32_t d)			{ pack_uint32_impl(m_stream, d); }
	void pack_uint64(uint64_t d)			{ pack_uint64_impl(m_stream, d); }
	void pack_int8(uint8_t d)				{ pack_int8_impl(m_stream, d); }
	void pack_int16(uint16_t d)				{ pack_int16_impl(m_stream, d); }
	void pack_int32(uint32_t d)				{ pack_int32_impl(m_stream, d); }
	void pack_int64(uint64_t d)				{ pack_int64_impl(m_stream, d); }
	void pack_float(float d)				{ pack_float_impl(m_stream, d); }
	void pack_double(double d)				{ pack_double_impl(m_stream, d); }
	void pack_nil()							{ pack_nil_impl(m_stream); }
	void pack_true()						{ pack_true_impl(m_stream); }
	void pack_false()						{ pack_false_impl(m_stream); }
	void pack_array(unsigned int n)			{ pack_array_impl(m_stream, n); }
	void pack_map(unsigned int n)			{ pack_map_impl(m_stream, n); }
	void pack_string(const char* b)			{ pack_string_impl(m_stream, b); }
	void pack_raw(const char* b, size_t l)	{ pack_raw_impl(m_stream, (const void*)b, l); }

private:
	static void pack_int_impl(dynamic_stream& x, int d);
	static void pack_unsigned_int_impl(dynamic_stream& x, unsigned int d);
	static void pack_uint8_impl(dynamic_stream& x, uint8_t d);
	static void pack_uint16_impl(dynamic_stream& x, uint16_t d);
	static void pack_uint32_impl(dynamic_stream& x, uint32_t d);
	static void pack_uint64_impl(dynamic_stream& x, uint64_t d);
	static void pack_int8_impl(dynamic_stream& x, int8_t d);
	static void pack_int16_impl(dynamic_stream& x, int16_t d);
	static void pack_int32_impl(dynamic_stream& x, int32_t d);
	static void pack_int64_impl(dynamic_stream& x, int64_t d);
	static void pack_float_impl(dynamic_stream& x, float d);
	static void pack_double_impl(dynamic_stream& x, double d);
	static void pack_nil_impl(dynamic_stream& x);
	static void pack_true_impl(dynamic_stream& x);
	static void pack_false_impl(dynamic_stream& x);
	static void pack_array_impl(dynamic_stream& x, unsigned int n);
	static void pack_map_impl(dynamic_stream& x, unsigned int n);
	static void pack_string_impl(dynamic_stream& x, const char* b);
	static void pack_raw_impl(dynamic_stream& x, const void* b, size_t l);
	static void append_buffer(dynamic_stream& x, const unsigned char* buf, unsigned int len)
		{ x.write((const char*)buf, len); }

private:
	dynamic_stream m_stream;

private:
	dynamic_packer();
};

#define msgpack_pack_inline_func(name) \
	inline void dynamic_packer::pack_ ## name ## _impl
#define msgpack_pack_user dynamic_stream&
#define msgpack_pack_append_buffer append_buffer
#include "msgpack/pack_template.h"

template <typename Stream>
dynamic_packer::dynamic_packer(Stream& s) : m_stream(s) { }

struct dynamic_stream::write_trampoline {
private:
	template <typename R>
	struct ret_type {
		typedef R (*type)(void*, const char*, size_t);
	};

	template <typename Stream, typename R,
			typename Ptr, typename Sz, R (Stream::*MemFun)(Ptr*, Sz)>
	static R trampoline(void* obj, const char* buf, size_t len)
	{
		return (reinterpret_cast<Stream*>(obj)->*MemFun)(buf, len);
	}

public:
	template <typename Stream, typename R, typename Ptr, typename Sz>
	static typename ret_type<R>::type get(R (Stream::*func)(Ptr*, Sz))
	{
		R (*f)(void*, const char*, size_t) =
			&trampoline<Stream, R, Ptr, Sz, &Stream::write>;
		return f;
	}
};

template <typename Stream>
dynamic_stream::dynamic_stream(Stream& s)
{
	m_object = reinterpret_cast<void*>(&s);
	m_function = reinterpret_cast<void (*)(void*, const char*, size_t)>(
			write_trampoline::get(&Stream::write)
			);
}


template <typename Stream>
inline void pack(Stream& s, object o)
{
	dynamic_packer pk(s);
	o.pack(pk);
}
*/


}  // namespace msgpack

#endif /* msgpack/pack.hpp */

