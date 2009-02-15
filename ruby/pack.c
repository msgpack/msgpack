/*
 * MessagePack packing routine for Ruby
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
#include "ruby.h"
#include <stddef.h>
#include <stdint.h>

#define msgpack_pack_inline_func(name) \
	static inline void msgpack_pack_##name

#define msgpack_pack_user VALUE

#define msgpack_pack_append_buffer(user, buf, len) \
	rb_str_buf_cat(user, (const void*)buf, len)

/*
static void msgpack_pack_int(VALUE x, int d);
static void msgpack_pack_unsigned_int(VALUE x, unsigned int d);
static void msgpack_pack_long(VALUE x, long d);
static void msgpack_pack_unsigned_long(VALUE x, unsigned long d);
static void msgpack_pack_uint8(VALUE x, uint8_t d);
static void msgpack_pack_uint16(VALUE x, uint16_t d);
static void msgpack_pack_uint32(VALUE x, uint32_t d);
static void msgpack_pack_uint64(VALUE x, uint64_t d);
static void msgpack_pack_int8(VALUE x, int8_t d);
static void msgpack_pack_int16(VALUE x, int16_t d);
static void msgpack_pack_int32(VALUE x, int32_t d);
static void msgpack_pack_int64(VALUE x, int64_t d);
static void msgpack_pack_float(VALUE x, float d);
static void msgpack_pack_double(VALUE x, double d);
static void msgpack_pack_nil(VALUE x);
static void msgpack_pack_true(VALUE x);
static void msgpack_pack_false(VALUE x);
static void msgpack_pack_array(VALUE x, unsigned int n);
static void msgpack_pack_map(VALUE x, unsigned int n);
static void msgpack_pack_raw(VALUE x, size_t l);
static void msgpack_pack_raw_body(VALUE x, const void* b, size_t l);
*/

#include "msgpack/pack_template.h"


#ifndef RUBY_VM
#include "st.h"  // ruby hash
#endif

static ID s_to_msgpack;

#define ARG_BUFFER(name, argc, argv) \
	VALUE name; \
	if(argc == 1) { \
		name = argv[0]; \
	} else if(argc == 0) { \
		name = rb_str_buf_new(0); \
	} else { \
		rb_raise(rb_eArgError, "wrong number of arguments (%d for 0)", argc); \
	}

static VALUE MessagePack_NilClass_to_msgpack(int argc, VALUE *argv, VALUE self)
{
	ARG_BUFFER(out, argc, argv);
	msgpack_pack_nil(out);
	return out;
}

static VALUE MessagePack_TrueClass_to_msgpack(int argc, VALUE *argv, VALUE self)
{
	ARG_BUFFER(out, argc, argv);
	msgpack_pack_true(out);
	return out;
}

static VALUE MessagePack_FalseClass_to_msgpack(int argc, VALUE *argv, VALUE self)
{
	ARG_BUFFER(out, argc, argv);
	msgpack_pack_false(out);
	return out;
}


static VALUE MessagePack_Fixnum_to_msgpack(int argc, VALUE *argv, VALUE self)
{
	ARG_BUFFER(out, argc, argv);
	msgpack_pack_long(out, FIX2LONG(self));
	return out;
}


#ifndef RBIGNUM_SIGN  // Ruby 1.8
#define RBIGNUM_SIGN(b) (RBIGNUM(b)->sign)
#endif

static VALUE MessagePack_Bignum_to_msgpack(int argc, VALUE *argv, VALUE self)
{
	ARG_BUFFER(out, argc, argv);
	// FIXME bignum
	if(RBIGNUM_SIGN(self)) {  // positive
		msgpack_pack_uint64(out, rb_big2ull(self));
	} else {  // negative
		msgpack_pack_int64(out, rb_big2ll(self));
	}
	return out;
}

static VALUE MessagePack_Float_to_msgpack(int argc, VALUE *argv, VALUE self)
{
	ARG_BUFFER(out, argc, argv);
	msgpack_pack_double(out, rb_num2dbl(self));
	return out;
}

static VALUE MessagePack_String_to_msgpack(int argc, VALUE *argv, VALUE self)
{
	ARG_BUFFER(out, argc, argv);
	msgpack_pack_raw(out, RSTRING_LEN(self));
	msgpack_pack_raw_body(out, RSTRING_PTR(self), RSTRING_LEN(self));
	return out;
}

static VALUE MessagePack_Array_to_msgpack(int argc, VALUE *argv, VALUE self)
{
	ARG_BUFFER(out, argc, argv);
	msgpack_pack_array(out, RARRAY_LEN(self));
	VALUE* p = RARRAY_PTR(self);
	VALUE* const pend = p + RARRAY_LEN(self);
	for(;p != pend; ++p) {
		rb_funcall(*p, s_to_msgpack, 1, out);
	}
	return out;
}

#ifndef RHASH_SIZE  // Ruby 1.8
#define RHASH_SIZE(h) (RHASH(h)->tbl ? RHASH(h)->tbl->num_entries : 0)
#endif

static int MessagePack_Hash_to_msgpack_foreach(VALUE key, VALUE value, VALUE out)
{
	if (key == Qundef) { return ST_CONTINUE; }
	rb_funcall(key, s_to_msgpack, 1, out);
	rb_funcall(value, s_to_msgpack, 1, out);
	return ST_CONTINUE;
}

static VALUE MessagePack_Hash_to_msgpack(int argc, VALUE *argv, VALUE self)
{
	ARG_BUFFER(out, argc, argv);
	msgpack_pack_map(out, RHASH_SIZE(self));
	rb_hash_foreach(self, MessagePack_Hash_to_msgpack_foreach, out);
	return out;
}


static VALUE MessagePack_pack(VALUE self, VALUE data)
{
	return rb_funcall(data, s_to_msgpack, 0);
}


void Init_msgpack_pack(VALUE mMessagePack)
{
	s_to_msgpack = rb_intern("to_msgpack");
	rb_define_method_id(rb_cNilClass,   s_to_msgpack, MessagePack_NilClass_to_msgpack, -1);
	rb_define_method_id(rb_cTrueClass,  s_to_msgpack, MessagePack_TrueClass_to_msgpack, -1);
	rb_define_method_id(rb_cFalseClass, s_to_msgpack, MessagePack_FalseClass_to_msgpack, -1);
	rb_define_method_id(rb_cFixnum, s_to_msgpack, MessagePack_Fixnum_to_msgpack, -1);
	rb_define_method_id(rb_cBignum, s_to_msgpack, MessagePack_Bignum_to_msgpack, -1);
	rb_define_method_id(rb_cFloat,  s_to_msgpack, MessagePack_Float_to_msgpack, -1);
	rb_define_method_id(rb_cString, s_to_msgpack, MessagePack_String_to_msgpack, -1);
	rb_define_method_id(rb_cArray,  s_to_msgpack, MessagePack_Array_to_msgpack, -1);
	rb_define_method_id(rb_cHash,   s_to_msgpack, MessagePack_Hash_to_msgpack, -1);
	rb_define_module_function(mMessagePack, "pack", MessagePack_pack, 1);
}

