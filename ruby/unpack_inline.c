/*
 * MessagePack unpacking routine for Ruby
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
#include "unpack_context.h"

static inline VALUE msgpack_unpack_init(msgpack_unpack_context* x)
{ return Qnil; }

static inline VALUE msgpack_unpack_unsigned_int_8(msgpack_unpack_context* x, uint8_t d)
{ return INT2FIX(d); }

static inline VALUE msgpack_unpack_unsigned_int_16(msgpack_unpack_context* x, uint16_t d)
{ return INT2FIX(d); }

static inline VALUE msgpack_unpack_unsigned_int_32(msgpack_unpack_context* x, uint32_t d)
{ return UINT2NUM(d); }

static inline VALUE msgpack_unpack_unsigned_int_64(msgpack_unpack_context* x, uint64_t d)
{ return rb_ull2inum(d); }

static inline VALUE msgpack_unpack_signed_int_8(msgpack_unpack_context* x, int8_t d)
{ return INT2FIX((long)d); }

static inline VALUE msgpack_unpack_signed_int_16(msgpack_unpack_context* x, int16_t d)
{ return INT2FIX((long)d); }

static inline VALUE msgpack_unpack_signed_int_32(msgpack_unpack_context* x, int32_t d)
{ return INT2NUM((long)d); }

static inline VALUE msgpack_unpack_signed_int_64(msgpack_unpack_context* x, int64_t d)
{ return rb_ll2inum(d); }

static inline VALUE msgpack_unpack_float(msgpack_unpack_context* x, float d)
{ return rb_float_new(d); }

static inline VALUE msgpack_unpack_double(msgpack_unpack_context* x, double d)
{ return rb_float_new(d); }

static inline VALUE msgpack_unpack_nil(msgpack_unpack_context* x)
{ return Qnil; }

static inline VALUE msgpack_unpack_true(msgpack_unpack_context* x)
{ return Qtrue; }

static inline VALUE msgpack_unpack_false(msgpack_unpack_context* x)
{ return Qfalse; }

static inline VALUE msgpack_unpack_array_start(msgpack_unpack_context* x, unsigned int n)
{ return rb_ary_new2(n); }

static inline void msgpack_unpack_array_item(msgpack_unpack_context* x, VALUE c, VALUE o)
{ rb_ary_push(c, o); }  // FIXME set value directry RARRAY_PTR(obj)[RARRAY_LEN(obj)++]

static inline VALUE msgpack_unpack_map_start(msgpack_unpack_context* x, unsigned int n)
{ return rb_hash_new(); }

static inline void msgpack_unpack_map_item(msgpack_unpack_context* x, VALUE c, VALUE k, VALUE v)
{ rb_hash_aset(c, k, v); }

static inline VALUE msgpack_unpack_raw(msgpack_unpack_context* x, const void* b, const void* p, size_t l)
{ return rb_str_new(p, l); }

#include "msgpack/unpack/inline_impl.h"

