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
#include "pack_inline.h"

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
	msgpack_pack_int(out, FIX2INT(self));
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
	msgpack_pack_raw(out, RSTRING_PTR(self), RSTRING_LEN(self));
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
	rb_define_method_id(rb_cFloat,  s_to_msgpack, MessagePack_Float_to_msgpack, -1);
	rb_define_method_id(rb_cString, s_to_msgpack, MessagePack_String_to_msgpack, -1);
	rb_define_method_id(rb_cArray,  s_to_msgpack, MessagePack_Array_to_msgpack, -1);
	rb_define_method_id(rb_cHash,   s_to_msgpack, MessagePack_Hash_to_msgpack, -1);
	rb_define_module_function(mMessagePack, "pack", MessagePack_pack, 1);
}

