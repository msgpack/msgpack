/*
 * MessagePack for Ruby unpacking routine
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
#include "msgpack/unpack_define.h"


typedef struct {
	int finished;
	VALUE origstr;
} msgpack_unpack_context;


#define msgpack_unpack_struct(name) \
	struct msgpack_unpacker ## name

#define msgpack_unpack_func(ret, name) \
	ret msgpack_unpacker ## name

#define msgpack_unpack_callback(name) \
	template_callback ## name

#define msgpack_unpack_object VALUE

#define msgpack_unpack_user msgpack_unpack_context


struct msgpack_unpacker_context;
typedef struct msgpack_unpacker_context msgpack_unpacker;

static void msgpack_unpacker_init(msgpack_unpacker* ctx);

static VALUE msgpack_unpacker_data(msgpack_unpacker* ctx);

static int msgpack_unpacker_execute(msgpack_unpacker* ctx,
		const char* data, size_t len, size_t* off);


static inline VALUE template_callback_init(msgpack_unpack_context* x)
{ return Qnil; }

static inline VALUE template_callback_uint8(msgpack_unpack_context* x, uint8_t d)
{ return INT2FIX(d); }

static inline VALUE template_callback_uint16(msgpack_unpack_context* x, uint16_t d)
{ return INT2FIX(d); }

static inline VALUE template_callback_uint32(msgpack_unpack_context* x, uint32_t d)
{ return UINT2NUM(d); }

static inline VALUE template_callback_uint64(msgpack_unpack_context* x, uint64_t d)
{ return rb_ull2inum(d); }

static inline VALUE template_callback_int8(msgpack_unpack_context* x, int8_t d)
{ return INT2FIX((long)d); }

static inline VALUE template_callback_int16(msgpack_unpack_context* x, int16_t d)
{ return INT2FIX((long)d); }

static inline VALUE template_callback_int32(msgpack_unpack_context* x, int32_t d)
{ return INT2NUM((long)d); }

static inline VALUE template_callback_int64(msgpack_unpack_context* x, int64_t d)
{ return rb_ll2inum(d); }

static inline VALUE template_callback_float(msgpack_unpack_context* x, float d)
{ return rb_float_new(d); }

static inline VALUE template_callback_double(msgpack_unpack_context* x, double d)
{ return rb_float_new(d); }

static inline VALUE template_callback_nil(msgpack_unpack_context* x)
{ return Qnil; }

static inline VALUE template_callback_true(msgpack_unpack_context* x)
{ return Qtrue; }

static inline VALUE template_callback_false(msgpack_unpack_context* x)
{ return Qfalse; }

static inline VALUE template_callback_array(msgpack_unpack_context* x, unsigned int n)
{ return rb_ary_new2(n); }

static inline void template_callback_array_item(msgpack_unpack_context* x, VALUE* c, VALUE o)
{ rb_ary_push(*c, o); }  // FIXME set value directry RARRAY_PTR(obj)[RARRAY_LEN(obj)++]

static inline VALUE template_callback_map(msgpack_unpack_context* x, unsigned int n)
{ return rb_hash_new(); }

static inline void template_callback_map_item(msgpack_unpack_context* x, VALUE* c, VALUE k, VALUE v)
{ rb_hash_aset(*c, k, v); }

static inline VALUE template_callback_raw(msgpack_unpack_context* x, const char* b, const char* p, unsigned int l)
{ return l == 0 ? rb_str_new(0,0) : rb_str_substr(x->origstr, p - b, l); }


#include "msgpack/unpack_template.h"


#define UNPACKER(from, name) \
	msgpack_unpacker *name = NULL; \
	Data_Get_Struct(from, msgpack_unpacker, name); \
	if(name == NULL) { \
		rb_raise(rb_eArgError, "NULL found for " # name " when shouldn't be."); \
	}

#define CHECK_STRING_TYPE(value) \
	value = rb_check_string_type(value); \
	if( NIL_P(value) ) { \
		rb_raise(rb_eTypeError, "instance of String needed"); \
	}

static VALUE cUnpacker;
static VALUE eUnpackError;

static void MessagePack_Unpacker_free(void* data)
{
	if(data) { free(data); }
}

static void MessagePack_Unpacker_mark(msgpack_unpacker *mp)
{
	unsigned int i;
	for(i=0; i < mp->top; ++i) {
		rb_gc_mark(mp->stack[i].obj);
		rb_gc_mark(mp->stack[i].map_key);
	}
}

static VALUE MessagePack_Unpacker_alloc(VALUE klass)
{
	VALUE obj;
	msgpack_unpacker* mp = ALLOC_N(msgpack_unpacker, 1);
	obj = Data_Wrap_Struct(klass, MessagePack_Unpacker_mark,
			MessagePack_Unpacker_free, mp);
	return obj;
}

static VALUE MessagePack_Unpacker_reset(VALUE self)
{
	UNPACKER(self, mp);
	msgpack_unpacker_init(mp);
	msgpack_unpack_context ctx = {0, Qnil};
	mp->user = ctx;
	return self;
}

static VALUE MessagePack_Unpacker_initialize(VALUE self)
{
	return MessagePack_Unpacker_reset(self);
}


static VALUE MessagePack_Unpacker_execute_impl(VALUE args)
{
	VALUE self = ((VALUE*)args)[0];
	VALUE data = ((VALUE*)args)[1];

	UNPACKER(self, mp);
	size_t from = NUM2UINT(((VALUE*)args)[2]);
	char* dptr = RSTRING_PTR(data);
	long dlen = FIX2LONG(((VALUE*)args)[3]);
	int ret;

	if(from >= dlen) {
		rb_raise(eUnpackError, "offset is bigger than data buffer size.");
	}

	mp->user.origstr = data;
	ret = msgpack_unpacker_execute(mp, dptr, (size_t)dlen, &from);
	mp->user.origstr = Qnil;

	if(ret < 0) {
		rb_raise(eUnpackError, "parse error.");
	} else if(ret > 0) {
		mp->user.finished = 1;
		return ULONG2NUM(from);
	} else {
		mp->user.finished = 0;
		return ULONG2NUM(from);
	}
}

static VALUE MessagePack_Unpacker_execute_rescue(VALUE nouse)
{
	rb_gc_enable();
#ifdef RUBY_VM
	rb_exc_raise(rb_errinfo());
#else
	rb_exc_raise(ruby_errinfo);
#endif
}

static VALUE MessagePack_Unpacker_execute_limit(VALUE self, VALUE data,
		VALUE off, VALUE limit)
{
	// FIXME execute実行中はmp->topが更新されないのでGC markが機能しない
	rb_gc_disable();
	VALUE args[4] = {self, data, off, limit};
	VALUE ret = rb_rescue(MessagePack_Unpacker_execute_impl, (VALUE)args,
			MessagePack_Unpacker_execute_rescue, Qnil);
	rb_gc_enable();
	return ret;
}

static VALUE MessagePack_Unpacker_execute(VALUE self, VALUE data, VALUE off)
{
	return MessagePack_Unpacker_execute_limit(self, data, off,
			LONG2FIX(RSTRING_LEN(data)));
}

static VALUE MessagePack_Unpacker_finished_p(VALUE self)
{
	UNPACKER(self, mp);
	if(mp->user.finished) {
		return Qtrue;
	}
	return Qfalse;
}

static VALUE MessagePack_Unpacker_data(VALUE self)
{
	UNPACKER(self, mp);
	return msgpack_unpacker_data(mp);
}


static VALUE MessagePack_unpack_impl(VALUE args)
{
	msgpack_unpacker* mp = (msgpack_unpacker*)((VALUE*)args)[0];
	VALUE data = ((VALUE*)args)[1];

	size_t from = 0;
	char* dptr = RSTRING_PTR(data);
	long dlen = FIX2LONG(((VALUE*)args)[2]);
	int ret;

	mp->user.origstr = data;
	ret = msgpack_unpacker_execute(mp, dptr, (size_t)dlen, &from);
	mp->user.origstr = Qnil;

	if(ret < 0) {
		rb_raise(eUnpackError, "parse error.");
	} else if(ret == 0) {
		rb_raise(eUnpackError, "insufficient bytes.");
	} else {
		if(from < dlen) {
			rb_raise(eUnpackError, "extra bytes.");
		}
		return msgpack_unpacker_data(mp);
	}
}

static VALUE MessagePack_unpack_rescue(VALUE args)
{
	rb_gc_enable();
#ifdef RUBY_VM
	rb_exc_raise(rb_errinfo());
#else
	rb_exc_raise(ruby_errinfo);
#endif
}

static VALUE MessagePack_unpack_limit(VALUE self, VALUE data, VALUE limit)
{
	CHECK_STRING_TYPE(data);
	msgpack_unpacker mp;
	msgpack_unpacker_init(&mp);
	msgpack_unpack_context ctx = {0, Qnil};
	mp.user = ctx;

	rb_gc_disable();
	VALUE args[3] = {(VALUE)&mp, data, limit};
	VALUE ret = rb_rescue(MessagePack_unpack_impl, (VALUE)args,
			MessagePack_unpack_rescue, Qnil);
	rb_gc_enable();
	return ret;
}

static VALUE MessagePack_unpack(VALUE self, VALUE data)
{
	return MessagePack_unpack_limit(self, data,
			LONG2FIX(RSTRING_LEN(data)));
}


void Init_msgpack_unpack(VALUE mMessagePack)
{
	eUnpackError = rb_define_class_under(mMessagePack, "UnpackError", rb_eStandardError);
	cUnpacker = rb_define_class_under(mMessagePack, "Unpacker", rb_cObject);
	rb_define_alloc_func(cUnpacker, MessagePack_Unpacker_alloc);
	rb_define_method(cUnpacker, "initialize", MessagePack_Unpacker_initialize, 0);
	rb_define_method(cUnpacker, "execute", MessagePack_Unpacker_execute, 2);
	rb_define_method(cUnpacker, "execute_limit", MessagePack_Unpacker_execute_limit, 3);
	rb_define_method(cUnpacker, "finished?", MessagePack_Unpacker_finished_p, 0);
	rb_define_method(cUnpacker, "data", MessagePack_Unpacker_data, 0);
	rb_define_method(cUnpacker, "reset", MessagePack_Unpacker_reset, 0);
	rb_define_module_function(mMessagePack, "unpack", MessagePack_unpack, 1);
	rb_define_module_function(mMessagePack, "unpack_limit", MessagePack_unpack_limit, 2);
}


