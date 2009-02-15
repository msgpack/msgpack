/*
 * MessagePack packing routine
 *
 * Copyright (C) 2008 FURUHASHI Sadayuki
 *
 *    Licensed under the Apache License, Version 2.0 (the "License");
 *    you may not use this file except in compliance with the License.
 *    You may obtain a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 *    Unless required by applicable law or agreed to in writing, software
 *    distributed under the License is distributed on an "AS IS" BASIS,
 *    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *    See the License for the specific language governing permissions and
 *    limitations under the License.
 */
#ifndef MSGPACK_PACK_INLINE_IMPL_H__
#define MSGPACK_PACK_INLINE_IMPL_H__

#include <string.h>
#include <arpa/inet.h>

#ifdef __LITTLE_ENDIAN__

#define STORE_BE16(d) \
	((char*)&d)[1], ((char*)&d)[0]

#define STORE_BE32(d) \
	((char*)&d)[3], ((char*)&d)[2], ((char*)&d)[1], ((char*)&d)[0]

#define STORE_BE64(d) \
	((char*)&d)[7], ((char*)&d)[6], ((char*)&d)[5], ((char*)&d)[4], \
	((char*)&d)[3], ((char*)&d)[2], ((char*)&d)[1], ((char*)&d)[0]

#elif __BIG_ENDIAN__

#define STORE_BE16(d) \
	((char*)&d)[0], ((char*)&d)[1]

#define STORE_BE32(d) \
	((char*)&d)[0], ((char*)&d)[1], ((char*)&d)[2], ((char*)&d)[3]

#define STORE_BE64(d) \
	((char*)&d)[0], ((char*)&d)[1], ((char*)&d)[2], ((char*)&d)[3], \
	((char*)&d)[4], ((char*)&d)[5], ((char*)&d)[6], ((char*)&d)[7]

#endif


/*
 * Integer
 */

// wrapper
inline void msgpack_pack_int(msgpack_pack_context x, int d)
{
	if(d < -32) {
		if(d < -32768) { // signed 32
			const unsigned char buf[5] = {0xd2, STORE_BE32(d)};
			msgpack_pack_append_buffer(x, buf, 5);
		} else if(d < -128) { // signed 16
			const unsigned char buf[3] = {0xd1, STORE_BE16(d)};
			msgpack_pack_append_buffer(x, buf, 3);
		} else { // signed 8
			const unsigned char buf[2] = {0xd0, (uint8_t)d};
			msgpack_pack_append_buffer(x, buf, 2);
		}
	} else if(d < 128) { // fixnum
		msgpack_pack_append_buffer(x, (uint8_t*)&d, 1);
	} else {
		if(d < 256) {
			// unsigned 8
			const unsigned char buf[2] = {0xcc, (uint8_t)d};
			msgpack_pack_append_buffer(x, buf, 2);
		} else if(d < 65536) {
			// unsigned 16
			const unsigned char buf[3] = {0xcd, STORE_BE16(d)};
			msgpack_pack_append_buffer(x, buf, 3);
		} else {
			// unsigned 32
			const unsigned char buf[5] = {0xce, STORE_BE32(d)};
			msgpack_pack_append_buffer(x, buf, 5);
		}
	}
}

// wrapper
inline void msgpack_pack_unsigned_int(msgpack_pack_context x, unsigned int d)
{
	if(d < 128) {
		// fixnum
		msgpack_pack_append_buffer(x, (uint8_t*)&d, 1);
	} else if(d < 256) {
		// unsigned 8
		const unsigned char buf[2] = {0xcc, (uint8_t)d};
		msgpack_pack_append_buffer(x, buf, 2);
	} else if(d < 65536) {
		// unsigned 16
		const unsigned char buf[3] = {0xcd, STORE_BE16(d)};
		msgpack_pack_append_buffer(x, buf, 3);
	} else {
		// unsigned 32
		const unsigned char buf[5] = {0xce, STORE_BE32(d)};
		msgpack_pack_append_buffer(x, buf, 5);
	}
}

inline void msgpack_pack_unsigned_int_8(msgpack_pack_context x, uint8_t d)
{
	if(d < 128) {
		msgpack_pack_append_buffer(x, &d, 1);
	} else {
		const unsigned char buf[2] = {0xcc, d};
		msgpack_pack_append_buffer(x, buf, 2);
	}
}

inline void msgpack_pack_unsigned_int_16(msgpack_pack_context x, uint16_t d)
{
	const unsigned char buf[3] = {0xcd, STORE_BE16(d)};
	msgpack_pack_append_buffer(x, buf, 3);
}

inline void msgpack_pack_unsigned_int_32(msgpack_pack_context x, uint32_t d)
{
	const unsigned char buf[5] = {0xce, STORE_BE32(d)};
	msgpack_pack_append_buffer(x, buf, 5);
}

inline void msgpack_pack_unsigned_int_64(msgpack_pack_context x, uint64_t d)
{
	// FIXME optimization
	const unsigned char buf[9] = {0xcf, STORE_BE64(d)};
	msgpack_pack_append_buffer(x, buf, 9);
}

inline void msgpack_pack_signed_int_8(msgpack_pack_context x, int8_t d)
{
	if(d > 0) {
		msgpack_pack_append_buffer(x, (uint8_t*)&d, 1);
	} else if(d >= -32) {
		msgpack_pack_append_buffer(x, (uint8_t*)&d, 1);
	} else {
		const unsigned char buf[2] = {0xd0, d};
		msgpack_pack_append_buffer(x, buf, 2);
	}
}

inline void msgpack_pack_signed_int_16(msgpack_pack_context x, int16_t d)
{
	const unsigned char buf[3] = {0xd1, STORE_BE16(d)};
	msgpack_pack_append_buffer(x, buf, 3);
}

inline void msgpack_pack_signed_int_32(msgpack_pack_context x, int32_t d)
{
	const unsigned char buf[5] = {0xd2, STORE_BE32(d)};
	msgpack_pack_append_buffer(x, buf, 5);
}

inline void msgpack_pack_signed_int_64(msgpack_pack_context x, int64_t d)
{
	// FIXME optimization
	const unsigned char buf[9] = {0xd3, STORE_BE64(d)};
	msgpack_pack_append_buffer(x, buf, 9);
}


/*
 * Float
 */

inline void msgpack_pack_float(msgpack_pack_context x, float d)
{
	uint32_t n = *((uint32_t*)&d);  // FIXME
	const unsigned char buf[5] = {0xca, STORE_BE32(n)};
	msgpack_pack_append_buffer(x, buf, 5);
}

inline void msgpack_pack_double(msgpack_pack_context x, double d)
{
	uint64_t n = *((uint64_t*)&d);  // FIXME
	const unsigned char buf[9] = {0xcb, STORE_BE64(n)};
	msgpack_pack_append_buffer(x, buf, 9);
}


/*
 * Nil
 */

inline void msgpack_pack_nil(msgpack_pack_context x)
{
	static const unsigned char d = 0xc0;
	msgpack_pack_append_buffer(x, &d, 1);
}


/*
 * Boolean
 */

inline void msgpack_pack_true(msgpack_pack_context x)
{
	static const unsigned char d = 0xc3;
	msgpack_pack_append_buffer(x, &d, 1);
}

inline void msgpack_pack_false(msgpack_pack_context x)
{
	static const unsigned char d = 0xc2;
	msgpack_pack_append_buffer(x, &d, 1);
}


/*
 * Array
 */

inline void msgpack_pack_array(msgpack_pack_context x, unsigned int n)
{
	if(n < 16) {
		unsigned char d = 0x90 | n;
		msgpack_pack_append_buffer(x, &d, 1);
	} else if(n < 65536) {
		uint16_t d = (uint16_t)n;
		unsigned char buf[3] = {0xdc, STORE_BE16(d)};
		msgpack_pack_append_buffer(x, buf, 3);
	} else {
		uint32_t d = (uint32_t)n;
		unsigned char buf[5] = {0xdd, STORE_BE32(d)};
		msgpack_pack_append_buffer(x, buf, 5);
	}
}


/*
 * Map
 */

inline void msgpack_pack_map(msgpack_pack_context x, unsigned int n)
{
	if(n < 16) {
		unsigned char d = 0x80 | n;
		msgpack_pack_append_buffer(x, &d, 1);
	} else if(n < 65536) {
		uint16_t d = (uint16_t)n;
		unsigned char buf[3] = {0xde, STORE_BE16(d)};
		msgpack_pack_append_buffer(x, buf, 3);
	} else {
		uint32_t d = (uint32_t)n;
		unsigned char buf[5] = {0xdf, STORE_BE32(d)};
		msgpack_pack_append_buffer(x, buf, 5);
	}
}


/*
 * Raw
 */

inline void msgpack_pack_string(msgpack_pack_context x, const char* b)
{
	uint32_t l = strlen(b);
	msgpack_pack_append_buffer(x, (const unsigned char*)b, l+1);
}

inline void msgpack_pack_raw(msgpack_pack_context x, const void* b, size_t l)
{
	if(l < 32) {
		unsigned char d = 0xa0 | l;
		msgpack_pack_append_buffer(x, &d, 1);
	} else if(l < 65536) {
		uint16_t d = (uint16_t)l;
		unsigned char buf[3] = {0xda, STORE_BE16(d)};
		msgpack_pack_append_buffer(x, buf, 3);
	} else {
		uint32_t d = (uint32_t)l;
		unsigned char buf[5] = {0xdb, STORE_BE32(d)};
		msgpack_pack_append_buffer(x, buf, 5);
	}
	msgpack_pack_append_buffer(x, b, l);
}


#undef STORE_BE16(d)
#undef STORE_BE32(d)
#undef STORE_BE64(d)


#endif /* msgpack/pack/inline_impl.h */

