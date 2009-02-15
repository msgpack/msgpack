/*
 * MessagePack unpacking routine for C
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

static inline void* msgpack_unpack_init(msgpack_unpack_t* x)
{ return NULL; }

static inline void* msgpack_unpack_unsigned_int_8(msgpack_unpack_t* x, uint8_t d)
{ return x->callback.unpack_unsigned_int_8(x->data, d); }

static inline void* msgpack_unpack_unsigned_int_16(msgpack_unpack_t* x, uint16_t d)
{ return x->callback.unpack_unsigned_int_16(x->data, d); }

static inline void* msgpack_unpack_unsigned_int_32(msgpack_unpack_t* x, uint32_t d)
{ return x->callback.unpack_unsigned_int_32(x->data, d); }

static inline void* msgpack_unpack_unsigned_int_64(msgpack_unpack_t* x, uint64_t d)
{ return x->callback.unpack_unsigned_int_64(x->data, d); }

static inline void* msgpack_unpack_signed_int_8(msgpack_unpack_t* x, int8_t d)
{ return x->callback.unpack_signed_int_8(x->data, d); }

static inline void* msgpack_unpack_signed_int_16(msgpack_unpack_t* x, int16_t d)
{ return x->callback.unpack_signed_int_16(x->data, d); }

static inline void* msgpack_unpack_signed_int_32(msgpack_unpack_t* x, int32_t d)
{ return x->callback.unpack_signed_int_32(x->data, d); }

static inline void* msgpack_unpack_signed_int_64(msgpack_unpack_t* x, int64_t d)
{ return x->callback.unpack_signed_int_64(x->data, d); }

static inline void* msgpack_unpack_float(msgpack_unpack_t* x, float d)
{ return x->callback.unpack_float(x->data, d); }

static inline void* msgpack_unpack_double(msgpack_unpack_t* x, double d)
{ return x->callback.unpack_double(x->data, d); }

static inline void* msgpack_unpack_nil(msgpack_unpack_t* x)
{ return x->callback.unpack_nil(x->data); }

static inline void* msgpack_unpack_true(msgpack_unpack_t* x)
{ return x->callback.unpack_true(x->data); }

static inline void* msgpack_unpack_false(msgpack_unpack_t* x)
{ return x->callback.unpack_false(x->data); }

static inline void* msgpack_unpack_array_start(msgpack_unpack_t* x, unsigned int n)
{ return x->callback.unpack_array_start(x->data, n); }

static inline void msgpack_unpack_array_item(msgpack_unpack_t* x, void* c, void* o)
{ x->callback.unpack_array_item(x->data, c, o); }

static inline void* msgpack_unpack_map_start(msgpack_unpack_t* x, unsigned int n)
{ return x->callback.unpack_map_start(x->data, n); }

static inline void msgpack_unpack_map_item(msgpack_unpack_t* x, void* c, void* k, void* v)
{ x->callback.unpack_map_item(x->data, c, k, v); }

static inline void* msgpack_unpack_string(msgpack_unpack_t* x, const void* b, size_t l)
{ return x->callback.unpack_string(x->data, b, l); }

static inline void* msgpack_unpack_raw(msgpack_unpack_t* x, const void* b, size_t l)
{ return x->callback.unpack_raw(x->data, b, l); }


#include "msgpack/unpack/inline_impl.h"

