#include "unpack_context.hpp"


extern "C" {
using namespace msgpack;


static inline object_class* msgpack_unpack_init(zone** z)
{ return NULL; }

static inline object_class* msgpack_unpack_unsigned_int_8(zone** z, uint8_t d)
{ return (*z)->nu8(d); }

static inline object_class* msgpack_unpack_unsigned_int_16(zone** z, uint16_t d)
{ return (*z)->nu16(d); }

static inline object_class* msgpack_unpack_unsigned_int_32(zone** z, uint32_t d)
{ return (*z)->nu32(d); }

static inline object_class* msgpack_unpack_unsigned_int_64(zone** z, uint64_t d)
{ return (*z)->nu64(d); }

static inline object_class* msgpack_unpack_signed_int_8(zone** z, int8_t d)
{ return (*z)->ni8(d); }

static inline object_class* msgpack_unpack_signed_int_16(zone** z, int16_t d)
{ return (*z)->ni16(d); }

static inline object_class* msgpack_unpack_signed_int_32(zone** z, int32_t d)
{ return (*z)->ni32(d); }

static inline object_class* msgpack_unpack_signed_int_64(zone** z, int64_t d)
{ return (*z)->ni64(d); }

static inline object_class* msgpack_unpack_float(zone** z, float d)
{ return (*z)->nfloat(d); }

static inline object_class* msgpack_unpack_double(zone** z, double d)
{ return (*z)->ndouble(d); }

static inline object_class* msgpack_unpack_nil(zone** z)
{ return (*z)->nnil(); }

static inline object_class* msgpack_unpack_true(zone** z)
{ return (*z)->ntrue(); }

static inline object_class* msgpack_unpack_false(zone** z)
{ return (*z)->nfalse(); }

static inline object_class* msgpack_unpack_array_start(zone** z, unsigned int n)
{ return (*z)->narray(n); }

static inline void msgpack_unpack_array_item(zone** z, object_class* c, object_class* o)
{ reinterpret_cast<object_array*>(c)->push_back(o); }

static inline object_class* msgpack_unpack_map_start(zone** z, unsigned int n)
{ return (*z)->narray(); }

static inline void msgpack_unpack_map_item(zone** z, object_class* c, object_class* k, object_class* v)
{ reinterpret_cast<object_map*>(c)->store(k, v); }

static inline object_class* msgpack_unpack_string(zone** z, const void* b, size_t l)
{ return (*z)->nraw(b, l); }

static inline object_class* msgpack_unpack_raw(zone** z, const void* b, size_t l)
{ return (*z)->nraw(b, l); }


}  // extern "C"

#include "msgpack/unpack/inline_impl.h"

