/*
 * MessagePack unpacking routine
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
#ifndef MSGPACK_UNPACK_INLINE_IMPL_H__
#define MSGPACK_UNPACK_INLINE_IMPL_H__

#include <string.h>
#include <assert.h>
#include <arpa/inet.h>
/*#include <stdio.h>*/

#ifdef __cplusplus
extern "C" {
#endif

// Positive FixNum  0xxxxxxx  0x00 - 0x7f
// Negative FixNum  111xxxxx  0xe0 - 0xff
// Variable         110xxxxx  0xc0 - 0xdf
//    nil              00000  0xc0
//    string           00001  0xc1
//    false            00010  0xc2
//    true             00011  0xc3
//    (?)              00100  0xc4
//    (?)              00101  0xc5
//    (?)              00110  0xc6
//    (?)              00111  0xc7
//    (?)              01000  0xc8
//    (?)              01001  0xc9
//    float            01010  0xca
//    double           01011  0xcb
//    uint  8          01100  0xcc
//    uint 16          01101  0xcd
//    uint 32          01110  0xce
//    uint 64          01111  0xcf
//    int  8           10000  0xd0
//    int 16           10001  0xd1
//    int 32           10010  0xd2
//    int 64           10011  0xd3
//    (?)              10100  0xd4
//    (?)              10101  0xd5
//    (big float 16)   10110  0xd6
//    (big float 32)   10111  0xd7
//    (big integer 16) 11000  0xd8
//    (big integer 32) 11001  0xd9
//    raw 16           11010  0xda
//    raw 32           11011  0xdb
//    array 16         11100  0xdc
//    array 32         11101  0xdd
//    map 16           11110  0xde
//    map 32           11111  0xdf
// FixRaw           101xxxxx  0xa0 - 0xbf
// FixArray         1001xxxx  0x90 - 0x9f
// FixMap           1000xxxx  0x80 - 0x8f


#if !defined(__LITTLE_ENDIAN__) && !defined(__BIG_ENDIAN__)
#if __BYTE_ORDER == __LITTLE_ENDIAN
#define __LITTLE_ENDIAN__
#elif __BYTE_ORDER == __BIG_ENDIAN
#define __BIG_ENDIAN__
#endif
#endif

#define betoh16(x) ntohs(x)
#define betoh32(x) ntohl(x)

#ifdef __LITTLE_ENDIAN__
#if defined(__bswap_64)
#  define betoh64(x) __bswap_64(x)
#elif defined(__DARWIN_OSSwapInt64)
#  define betoh64(x) __DARWIN_OSSwapInt64(x)
#else
static inline uint64_t betoh64(uint64_t x) {
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
#define betoh64(x) (x)
#endif


typedef enum {
	CS_HEADER            = 0x00,  // nil

	//CS_STRING          = 0x01,
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
	CS_UNSIGNED_INT_8    = 0x0c,
	CS_UNSIGNED_INT_16   = 0x0d,
	CS_UNSIGNED_INT_32   = 0x0e,
	CS_UNSIGNED_INT_64   = 0x0f,
	CS_SIGNED_INT_8      = 0x10,
	CS_SIGNED_INT_16     = 0x11,
	CS_SIGNED_INT_32     = 0x12,
	CS_SIGNED_INT_64     = 0x13,

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
} current_state_t;


typedef enum {
	CT_ARRAY_ITEM,
	CT_MAP_KEY,
	CT_MAP_VALUE,
} container_type_t;


void msgpack_unpacker_init(msgpack_unpacker* ctx)
{
	memset(ctx, 0, sizeof(msgpack_unpacker));  // FIXME init ctx->user?
	ctx->cs = CS_HEADER;
	ctx->trail = 0;
	ctx->top = 0;
	ctx->stack[0].obj = msgpack_unpack_init(&ctx->user);
}

int msgpack_unpacker_execute(msgpack_unpacker* ctx, const char* data, size_t len, size_t* off)
{
	assert(len >= *off);

	const unsigned char* p = (unsigned char*)data + *off;
	const unsigned char* const pe = (unsigned char*)data + len;
	const void* n = NULL;

	unsigned int trail = ctx->trail;
	unsigned int cs = ctx->cs;
	unsigned int top = ctx->top;
	msgpack_unpacker_stack* stack = ctx->stack;
	msgpack_unpack_context* user = &ctx->user;

	msgpack_object obj;
	msgpack_unpacker_stack* c = NULL;

	int ret;

#define push_simple_value(func) \
	obj = func(user); \
	/*printf("obj %d\n",obj);*/ \
	goto _push
#define push_fixed_value(func, arg) \
	obj = func(user, arg); \
	/*printf("obj %d\n",obj);*/ \
	goto _push
#define push_variable_value(func, base, pos, len) \
	obj = func(user, (const char*)base, (const char*)pos, len); \
	/*printf("obj %d\n",obj);*/ \
	goto _push

/*
#define again_terminal_trail(_cs, from) \
	cs = _cs; \
	stack[top].tmp.terminal_trail_start = from; \
	goto _terminal_trail_again
*/
#define again_fixed_trail(_cs, trail_len) \
	trail = trail_len; \
	cs = _cs; \
	goto _fixed_trail_again
#define again_fixed_trail_if_zero(_cs, trail_len, ifzero) \
	trail = trail_len; \
	if(trail == 0) { goto ifzero; } \
	cs = _cs; \
	goto _fixed_trail_again

#define start_container(func, count_, ct_) \
	stack[top].obj = func(user, count_); \
	if((count_) == 0) { obj = stack[top].obj; goto _push; } \
	if(top >= MSG_STACK_SIZE) { goto _failed; } \
	stack[top].ct = ct_; \
	stack[top].count = count_; \
	/*printf("container %d count %d stack %d\n",stack[top].obj,count_,top);*/ \
	/*printf("stack push %d\n", top);*/ \
	++top; \
	goto _header_again

#define NEXT_CS(p) \
	((unsigned int)*p & 0x1f)

#define PTR_CAST_8(ptr)   (*(uint8_t*)ptr)
#define PTR_CAST_16(ptr)  betoh16(*(uint16_t*)ptr)
#define PTR_CAST_32(ptr)  betoh32(*(uint32_t*)ptr)
#define PTR_CAST_64(ptr)  betoh64(*(uint64_t*)ptr)

	if(p == pe) { goto _out; }
	do {
		switch(cs) {
		case CS_HEADER:
			switch(*p) {
			case 0x00 ... 0x7f:  // Positive Fixnum
				push_fixed_value(msgpack_unpack_unsigned_int_8, *(uint8_t*)p);
			case 0xe0 ... 0xff:  // Negative Fixnum
				push_fixed_value(msgpack_unpack_signed_int_8, *(int8_t*)p);
			case 0xc0 ... 0xdf:  // Variable
				switch(*p) {
				case 0xc0:  // nil
					push_simple_value(msgpack_unpack_nil);
				//case 0xc1:  // string
				//	again_terminal_trail(NEXT_CS(p), p+1);
				case 0xc2:  // false
					push_simple_value(msgpack_unpack_false);
				case 0xc3:  // true
					push_simple_value(msgpack_unpack_true);
				//case 0xc4:
				//case 0xc5:
				//case 0xc6:
				//case 0xc7:
				//case 0xc8:
				//case 0xc9:
				case 0xca:  // float
				case 0xcb:  // double
				case 0xcc:  // unsigned int  8
				case 0xcd:  // unsigned int 16
				case 0xce:  // unsigned int 32
				case 0xcf:  // unsigned int 64
				case 0xd0:  // signed int  8
				case 0xd1:  // signed int 16
				case 0xd2:  // signed int 32
				case 0xd3:  // signed int 64
					again_fixed_trail(NEXT_CS(p), 1 << (((unsigned int)*p) & 0x03));
				//case 0xd4:
				//case 0xd5:
				//case 0xd6:  // big integer 16
				//case 0xd7:  // big integer 32
				//case 0xd8:  // big float 16
				//case 0xd9:  // big float 32
				case 0xda:  // raw 16
				case 0xdb:  // raw 32
				case 0xdc:  // array 16
				case 0xdd:  // array 32
				case 0xde:  // map 16
				case 0xdf:  // map 32
					again_fixed_trail(NEXT_CS(p), 2 << (((unsigned int)*p) & 0x01));
				default:
					goto _failed;
				}
			case 0xa0 ... 0xbf:  // FixRaw
				again_fixed_trail_if_zero(ACS_RAW_VALUE, ((unsigned int)*p & 0x1f), _raw_zero);
			case 0x90 ... 0x9f:  // FixArray
				start_container(msgpack_unpack_array_start, ((unsigned int)*p) & 0x0f, CT_ARRAY_ITEM);
			case 0x80 ... 0x8f:  // FixMap
				start_container(msgpack_unpack_map_start, ((unsigned int)*p) & 0x0f, CT_MAP_KEY);

			default:
				goto _failed;
			}
			// end CS_HEADER


		//_terminal_trail_again:
		//	++p;

		//case CS_STRING:
		//	if(*p == 0) {
		//		const unsigned char* start = stack[top].tmp.terminal_trail_start;
		//		obj = msgpack_unpack_string(user, start, p-start);
		//		goto _push;
		//	}
		//	goto _terminal_trail_again;


		_fixed_trail_again:
			++p;

		default:
			if((size_t)(pe - p) < trail) { goto _out; }
			n = p;  p += trail - 1;
			switch(cs) {
			//case CS_
			//case CS_
			case CS_FLOAT: {
					uint32_t x = PTR_CAST_32(n);  // FIXME
					push_fixed_value(msgpack_unpack_float, *((float*)&x)); }
			case CS_DOUBLE: {
					uint64_t x = PTR_CAST_64(n);  // FIXME
					push_fixed_value(msgpack_unpack_double, *((double*)&x)); }
			case CS_UNSIGNED_INT_8:
				push_fixed_value(msgpack_unpack_unsigned_int_8, (uint8_t)PTR_CAST_8(n));
			case CS_UNSIGNED_INT_16:
				push_fixed_value(msgpack_unpack_unsigned_int_16, (uint16_t)PTR_CAST_16(n));
			case CS_UNSIGNED_INT_32:
				push_fixed_value(msgpack_unpack_unsigned_int_32, (uint32_t)PTR_CAST_32(n));
			case CS_UNSIGNED_INT_64:
				push_fixed_value(msgpack_unpack_unsigned_int_64, (uint64_t)PTR_CAST_64(n));

			case CS_SIGNED_INT_8:
				push_fixed_value(msgpack_unpack_signed_int_8, (int8_t)PTR_CAST_8(n));
			case CS_SIGNED_INT_16:
				push_fixed_value(msgpack_unpack_signed_int_16, (int16_t)PTR_CAST_16(n));
			case CS_SIGNED_INT_32:
				push_fixed_value(msgpack_unpack_signed_int_32, (int32_t)PTR_CAST_32(n));
			case CS_SIGNED_INT_64:
				push_fixed_value(msgpack_unpack_signed_int_64, (int64_t)PTR_CAST_64(n));

			//case CS_
			//case CS_
			//case CS_BIG_INT_16:
			//	again_fixed_trail_if_zero(ACS_BIG_INT_VALUE, (uint16_t)PTR_CAST_16(n), _big_int_zero);
			//case CS_BIG_INT_32:
			//	again_fixed_trail_if_zero(ACS_BIG_INT_VALUE, (uint32_t)PTR_CAST_32(n), _big_int_zero);
			//case ACS_BIG_INT_VALUE:
			//_big_int_zero:
			//	// FIXME
			//	push_variable_value(msgpack_unpack_big_int, data, n, trail);

			//case CS_BIG_FLOAT_16:
			//	again_fixed_trail_if_zero(ACS_BIG_FLOAT_VALUE, (uint16_t)PTR_CAST_16(n), _big_float_zero);
			//case CS_BIG_FLOAT_32:
			//	again_fixed_trail_if_zero(ACS_BIG_FLOAT_VALUE, (uint32_t)PTR_CAST_32(n), _big_float_zero);
			//case ACS_BIG_FLOAT_VALUE:
			//_big_float_zero:
			//	// FIXME
			//	push_variable_value(msgpack_unpack_big_float, data, n, trail);

			case CS_RAW_16:
				again_fixed_trail_if_zero(ACS_RAW_VALUE, (uint16_t)PTR_CAST_16(n), _raw_zero);
			case CS_RAW_32:
				again_fixed_trail_if_zero(ACS_RAW_VALUE, (uint32_t)PTR_CAST_32(n), _raw_zero);
			case ACS_RAW_VALUE:
			_raw_zero:
				push_variable_value(msgpack_unpack_raw, data, n, trail);

			case CS_ARRAY_16:
				start_container(msgpack_unpack_array_start, (uint16_t)PTR_CAST_16(n), CT_ARRAY_ITEM);
			case CS_ARRAY_32:
				start_container(msgpack_unpack_array_start, (uint32_t)PTR_CAST_32(n), CT_ARRAY_ITEM);

			case CS_MAP_16:
				start_container(msgpack_unpack_map_start, (uint16_t)PTR_CAST_16(n), CT_MAP_KEY);
			case CS_MAP_32:
				start_container(msgpack_unpack_map_start, (uint32_t)PTR_CAST_32(n), CT_MAP_KEY);

			default:
				goto _failed;
			}
		}

_push:
	if(top == 0) { goto _finish; }
	c = &stack[top-1];
	switch(c->ct) {
	case CT_ARRAY_ITEM:
		msgpack_unpack_array_item(user, c->obj, obj);
		if(--c->count == 0) {
			obj = c->obj;
			--top;
			/*printf("stack pop %d\n", top);*/
			goto _push;
		}
		goto _header_again;
	case CT_MAP_KEY:
		c->tmp.map_key = obj;
		c->ct = CT_MAP_VALUE;
		goto _header_again;
	case CT_MAP_VALUE:
		msgpack_unpack_map_item(user, c->obj, c->tmp.map_key, obj);
		if(--c->count == 0) {
			obj = c->obj;
			--top;
			/*printf("stack pop %d\n", top);*/
			goto _push;
		}
		c->ct = CT_MAP_KEY;
		goto _header_again;

	default:
		goto _failed;
	}

_header_again:
		cs = CS_HEADER;
		++p;
	} while(p != pe);
	goto _out;


_finish:
	stack[0].obj = obj;
	++p;
	ret = 1;
	/*printf("-- finish --\n"); */
	goto _end;

_failed:
	/*printf("** FAILED **\n"); */
	ret = -1;
	goto _end;

_out:
	ret = 0;
	goto _end;

_end:
	ctx->cs = cs;
	ctx->trail = trail;
	ctx->top = top;
	*off = p - (const unsigned char*)data;

	return ret;
}


#ifdef betoh16
#undef betoh16
#endif

#ifdef betoh32
#undef betoh32
#endif

#ifdef betoh64
#undef betoh64
#endif

#ifdef __cplusplus
}
#endif

#endif /* msgpack/unpack/inline_impl.h */

