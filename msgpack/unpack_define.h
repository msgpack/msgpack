/*
 * MessagePack unpacking routine template
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
#ifndef MSGPACK_UNPACK_DEFINE_H__
#define MSGPACK_UNPACK_DEFINE_H__

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>
#ifndef __WIN32__
#include <arpa/inet.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif


#ifndef MSGPACK_MAX_STACK_SIZE
#define MSGPACK_MAX_STACK_SIZE 16
#endif


#if !defined(__LITTLE_ENDIAN__) && !defined(__BIG_ENDIAN__)
#if __BYTE_ORDER == __LITTLE_ENDIAN
#define __LITTLE_ENDIAN__
#elif __BYTE_ORDER == __BIG_ENDIAN
#define __BIG_ENDIAN__
#endif
#endif

#define msgpack_betoh16(x) ntohs(x)
#define msgpack_betoh32(x) ntohl(x)

#ifdef __LITTLE_ENDIAN__
#if defined(__bswap_64)
#  define msgpack_betoh64(x) __bswap_64(x)
#elif defined(__DARWIN_OSSwapInt64)
#  define msgpack_betoh64(x) __DARWIN_OSSwapInt64(x)
#else
static inline uint64_t msgpack_betoh64(uint64_t x) {
	return	((x << 56) & 0xff00000000000000ULL ) |
			((x << 40) & 0x00ff000000000000ULL ) |
			((x << 24) & 0x0000ff0000000000ULL ) |
			((x <<  8) & 0x000000ff00000000ULL ) |
			((x >>  8) & 0x00000000ff000000ULL ) |
			((x >> 24) & 0x0000000000ff0000ULL ) |
			((x >> 40) & 0x000000000000ff00ULL ) |
			((x >> 56) & 0x00000000000000ffULL ) ;
}
#endif
#else
#define msgpack_betoh64(x) (x)
#endif


typedef enum {
	CS_HEADER            = 0x00,  // nil

	//CS_                = 0x01,
	//CS_                = 0x02,  // false
	//CS_                = 0x03,  // true

	//CS_                = 0x04,
	//CS_                = 0x05,
	//CS_                = 0x06,
	//CS_                = 0x07,

	//CS_                = 0x08,
	//CS_                = 0x09,
	CS_FLOAT             = 0x0a,
	CS_DOUBLE            = 0x0b,
	CS_UINT_8            = 0x0c,
	CS_UINT_16           = 0x0d,
	CS_UINT_32           = 0x0e,
	CS_UINT_64           = 0x0f,
	CS_INT_8             = 0x10,
	CS_INT_16            = 0x11,
	CS_INT_32            = 0x12,
	CS_INT_64            = 0x13,

	//CS_                = 0x14,
	//CS_                = 0x15,
	//CS_BIG_INT_16        = 0x16,
	//CS_BIG_INT_32        = 0x17,
	//CS_BIG_FLOAT_16      = 0x18,
	//CS_BIG_FLOAT_32      = 0x19,
	CS_RAW_16            = 0x1a,
	CS_RAW_32            = 0x1b,
	CS_ARRAY_16          = 0x1c,
	CS_ARRAY_32          = 0x1d,
	CS_MAP_16            = 0x1e,
	CS_MAP_32            = 0x1f,

	//ACS_BIG_INT_VALUE,
	//ACS_BIG_FLOAT_VALUE,
	ACS_RAW_VALUE,
} msgpack_unpack_state;


typedef enum {
	CT_ARRAY_ITEM,
	CT_MAP_KEY,
	CT_MAP_VALUE,
} msgpack_container_type;


#ifdef __cplusplus
}
#endif

#endif /* msgpack/unpack_define.h */

