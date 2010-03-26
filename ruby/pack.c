/*
 * MessagePack for Ruby packing routine
 *
 * Copyright (C) 2008-2009 FURUHASHI Sadayuki
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
#include "msgpack/pack_define.h"

static ID s_to_msgpack;
static ID s_append;

#define msgpack_pack_inline_func(name) \
	static inline void msgpack_pack ## name

#define msgpack_pack_inline_func_cint(name) \
	static inline void msgpack_pack ## name

#define msgpack_pack_user VALUE

#define msgpack_pack_append_buffer(user, buf, len) \
	((TYPE(user) == T_STRING) ? \
		rb_str_buf_cat(user, (const void*)buf, len) : \
		rb_funcall(user, s_append, 1, rb_str_new((const void*)buf,len)))

#include "msgpack/pack_template.h"


#ifndef RUBY_VM
#include "st.h"  // ruby hash
#endif

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


static VALUE MessagePack_pack(int argc, VALUE* argv, VALUE self)
{
	VALUE out;
	if(argc == 1) {
		out = rb_str_buf_new(0);
	} else if(argc == 2) {
		out = argv[1];
	} else {
		rb_raise(rb_eArgError, "wrong number of arguments (%d for 1)", argc);
	}
	return rb_funcall(argv[0], s_to_msgpack, 1, out);
}


void Init_msgpack_pack(VALUE mMessagePack)
{
	s_to_msgpack = rb_intern("to_msgpack");
	s_append = rb_intern("<<");
	rb_define_method_id(rb_cNilClass,   s_to_msgpack, MessagePack_NilClass_to_msgpack, -1);
	rb_define_method_id(rb_cTrueClass,  s_to_msgpack, MessagePack_TrueClass_to_msgpack, -1);
	rb_define_method_id(rb_cFalseClass, s_to_msgpack, MessagePack_FalseClass_to_msgpack, -1);
	rb_define_method_id(rb_cFixnum, s_to_msgpack, MessagePack_Fixnum_to_msgpack, -1);
	rb_define_method_id(rb_cBignum, s_to_msgpack, MessagePack_Bignum_to_msgpack, -1);
	rb_define_method_id(rb_cFloat,  s_to_msgpack, MessagePack_Float_to_msgpack, -1);
	rb_define_method_id(rb_cString, s_to_msgpack, MessagePack_String_to_msgpack, -1);
	rb_define_method_id(rb_cArray,  s_to_msgpack, MessagePack_Array_to_msgpack, -1);
	rb_define_method_id(rb_cHash,   s_to_msgpack, MessagePack_Hash_to_msgpack, -1);
	rb_define_module_function(mMessagePack, "pack", MessagePack_pack, -1);
}

