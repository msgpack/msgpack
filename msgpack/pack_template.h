/*
 * MessagePack packing routine template
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

#if !defined(__LITTLE_ENDIAN__) && !defined(__BIG_ENDIAN__)
#if __BYTE_ORDER == __LITTLE_ENDIAN
#define __LITTLE_ENDIAN__
#elif __BYTE_ORDER == __BIG_ENDIAN
#define __BIG_ENDIAN__
#endif
#endif

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


#ifndef msgpack_pack_inline_func
#error msgpack_pack_inline_func template is not defined
#endif

#ifndef msgpack_pack_user
#error msgpack_pack_user type is not defined
#endif

#ifndef msgpack_pack_append_buffer
#error msgpack_pack_append_buffer callback is not defined
#endif


/*
 * Integer
 */

// wrapper
msgpack_pack_inline_func(int)(msgpack_pack_user x, int d)
{
	if(d < -32) {
		if(d < -32768) {
			// signed 32
			const unsigned char buf[5] = {0xd2, STORE_BE32(d)};
			msgpack_pack_append_buffer(x, buf, 5);
		} else if(d < -128) {
			// signed 16
			const unsigned char buf[3] = {0xd1, STORE_BE16(d)};
			msgpack_pack_append_buffer(x, buf, 3);
		} else {
			// signed 8
			const unsigned char buf[2] = {0xd0, (uint8_t)d};
			msgpack_pack_append_buffer(x, buf, 2);
		}
	} else if(d < 128) {
		// fixnum
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
msgpack_pack_inline_func(unsigned_int)(msgpack_pack_user x, unsigned int d)
{
	if(d < 256) {
		if(d < 128) {
			// fixnum
			msgpack_pack_append_buffer(x, (unsigned char*)&d, 1);
		} else {
			// unsigned 8
			const unsigned char buf[2] = {0xcc, (uint8_t)d};
			msgpack_pack_append_buffer(x, buf, 2);
		}
	} else {
		if(d < 65536) {
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

msgpack_pack_inline_func(uint8)(msgpack_pack_user x, uint8_t d)
{
	if(d < 128) {
		msgpack_pack_append_buffer(x, &d, 1);
	} else {
		const unsigned char buf[2] = {0xcc, d};
		msgpack_pack_append_buffer(x, buf, 2);
	}
}

msgpack_pack_inline_func(uint16)(msgpack_pack_user x, uint16_t d)
{
	const unsigned char buf[3] = {0xcd, STORE_BE16(d)};
	msgpack_pack_append_buffer(x, buf, 3);
}

msgpack_pack_inline_func(uint32)(msgpack_pack_user x, uint32_t d)
{
	const unsigned char buf[5] = {0xce, STORE_BE32(d)};
	msgpack_pack_append_buffer(x, buf, 5);
}

msgpack_pack_inline_func(uint64)(msgpack_pack_user x, uint64_t d)
{
	const unsigned char buf[9] = {0xcf, STORE_BE64(d)};
	msgpack_pack_append_buffer(x, buf, 9);
}

msgpack_pack_inline_func(int8)(msgpack_pack_user x, int8_t d)
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

msgpack_pack_inline_func(int16)(msgpack_pack_user x, int16_t d)
{
	const unsigned char buf[3] = {0xd1, STORE_BE16(d)};
	msgpack_pack_append_buffer(x, buf, 3);
}

msgpack_pack_inline_func(int32)(msgpack_pack_user x, int32_t d)
{
	const unsigned char buf[5] = {0xd2, STORE_BE32(d)};
	msgpack_pack_append_buffer(x, buf, 5);
}

msgpack_pack_inline_func(int64)(msgpack_pack_user x, int64_t d)
{
	const unsigned char buf[9] = {0xd3, STORE_BE64(d)};
	msgpack_pack_append_buffer(x, buf, 9);
}


/*
 * Float
 */

msgpack_pack_inline_func(float)(msgpack_pack_user x, float d)
{
	uint32_t n = *((uint32_t*)&d);  // FIXME
	const unsigned char buf[5] = {0xca, STORE_BE32(n)};
	msgpack_pack_append_buffer(x, buf, 5);
}

msgpack_pack_inline_func(double)(msgpack_pack_user x, double d)
{
	uint64_t n = *((uint64_t*)&d);  // FIXME
	const unsigned char buf[9] = {0xcb, STORE_BE64(n)};
	msgpack_pack_append_buffer(x, buf, 9);
}


/*
 * Nil
 */

msgpack_pack_inline_func(nil)(msgpack_pack_user x)
{
	static const unsigned char d = 0xc0;
	msgpack_pack_append_buffer(x, &d, 1);
}


/*
 * Boolean
 */

msgpack_pack_inline_func(true)(msgpack_pack_user x)
{
	static const unsigned char d = 0xc3;
	msgpack_pack_append_buffer(x, &d, 1);
}

msgpack_pack_inline_func(false)(msgpack_pack_user x)
{
	static const unsigned char d = 0xc2;
	msgpack_pack_append_buffer(x, &d, 1);
}


/*
 * Array
 */

msgpack_pack_inline_func(array)(msgpack_pack_user x, unsigned int n)
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

msgpack_pack_inline_func(map)(msgpack_pack_user x, unsigned int n)
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

msgpack_pack_inline_func(raw)(msgpack_pack_user x, size_t l)
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
}

msgpack_pack_inline_func(raw_body)(msgpack_pack_user x, const void* b, size_t l)
{
	msgpack_pack_append_buffer(x, (const unsigned char*)b, l);
}

#undef msgpack_pack_inline_func
#undef msgpack_pack_user
#undef msgpack_pack_append_buffer

#undef STORE_BE16
#undef STORE_BE32
#undef STORE_BE64

