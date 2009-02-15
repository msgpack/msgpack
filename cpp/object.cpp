#include "msgpack/object.hpp"
#include "msgpack/pack.hpp"

namespace msgpack {

namespace {

template <typename T, typename X, bool TSigned, bool XSigned>
struct numeric_overflow_signed_impl;

template <typename T, typename X>
struct numeric_overflow_signed_impl<T, X, true, true> {
	static int test(X x) {
		if(		( std::numeric_limits<T>::is_integer &&  std::numeric_limits<X>::is_integer) ||
				(!std::numeric_limits<T>::is_integer && !std::numeric_limits<X>::is_integer) ) {
			if( sizeof(T) < sizeof(X) ) {
				if( static_cast<X>( std::numeric_limits<T>::max()) < x ) { return 1; }
				if( static_cast<X>(-std::numeric_limits<T>::max()) > x ) { return -1; }
			}
		} else if(std::numeric_limits<T>::is_integer) {
			if( static_cast<X>( std::numeric_limits<T>::max()) < x) { return 1; }
			if( static_cast<X>(-std::numeric_limits<T>::max()) > x) { return -1; }
		}
		return 0;
	}
};

template <typename T, typename X>
struct numeric_overflow_signed_impl<T, X, true, false> {
	static int test(X x) {
		if(		( std::numeric_limits<T>::is_integer &&  std::numeric_limits<X>::is_integer) ||
				(!std::numeric_limits<T>::is_integer && !std::numeric_limits<X>::is_integer) ) {
			if( sizeof(T) <= sizeof(X) ) {
				if( static_cast<X>(std::numeric_limits<T>::max()) < x ) { return 1; }
			}
		} else if(std::numeric_limits<T>::is_integer) {
			if( static_cast<X>( std::numeric_limits<T>::max()) < x) { return 1; }
		}
		return 0;
	}
};

template <typename T, typename X>
struct numeric_overflow_signed_impl<T, X, false, true> {
	static int test(X x) {
		if( static_cast<X>(0) > x ) { return -1; }
		if(		( std::numeric_limits<T>::is_integer &&  std::numeric_limits<X>::is_integer) ||
				(!std::numeric_limits<T>::is_integer && !std::numeric_limits<X>::is_integer) ) {
			if( sizeof(T) < sizeof(X) ) {
				if( static_cast<X>(std::numeric_limits<T>::max()) < x ) { return 1; }
			}
		} else if(std::numeric_limits<T>::is_integer) {
			if( static_cast<X>( std::numeric_limits<T>::max()) < x) { return 1; }
		}
		return 0;
	}
};

template <typename T, typename X>
struct numeric_overflow_signed_impl<T, X, false, false> {
	static int test(X x) {
		if(		( std::numeric_limits<T>::is_integer &&  std::numeric_limits<X>::is_integer) ||
				(!std::numeric_limits<T>::is_integer && !std::numeric_limits<X>::is_integer) ) {
			if( sizeof(T) < sizeof(X) ) {
				if( static_cast<X>(std::numeric_limits<T>::max()) < x ) { return 1; }
			}
		} else if(std::numeric_limits<T>::is_integer) {
			if( static_cast<X>(std::numeric_limits<T>::max()) < x ) { return 1; }
		}
		return 0;
	}
};

template <typename T, typename X>
struct numeric_overflow {
	static int test(X x) {
		return numeric_overflow_signed_impl<T, X, std::numeric_limits<T>::is_signed, std::numeric_limits<X>::is_signed>::test(x);
	}
	static void check(X x) {
		int r = test(x);
		if(r ==  1) { throw positive_overflow_error(); }
		if(r == -1) { throw negative_overflow_error(); }
	}
};

template <typename T, typename X>
struct numeric_underflow {
	static bool test(X x) {
		return static_cast<X>(static_cast<T>(x)) != x;
	}
	static void check(X x) {
		if(test(x)) { throw underflow_error(); }
	}
};

template <typename T, typename X>
inline T integer_cast(X x) {
	numeric_overflow<T,X>::check(x);
	return static_cast<T>(x); }

template <typename T, typename X>
inline T float_cast(X x) {
	numeric_overflow<T,X>::check(x);
	numeric_underflow<T,X>::check(x);
	return static_cast<T>(x); }

template <typename V>
inline bool numequal(V v, const object_class* x)
	try { return v == static_cast<V>(*x); }
	catch (type_error&) { return false; }

template <typename V>
inline bool numless(V v, const object_class* x)
	try { return v < static_cast<V>(*x); }
	catch (positive_overflow_error&) { return true; }
	catch (overflow_error&) { return false; }

template <typename V>
inline bool numgreater(V v, const object_class* x)
	try { return v > static_cast<V>(*x); }
	catch (negative_overflow_error&) { return true; }
	catch (overflow_error&) { return false; }

template <typename V>
inline void numeric_inspect(V v, std::ostream& s)
	{ s << v; }

template <>
inline void numeric_inspect<uint8_t>(uint8_t v, std::ostream& s)
	{ s << (uint16_t)v; }

template <>
inline void numeric_inspect<int8_t>(int8_t v, std::ostream& s)
	{ s << (int16_t)v; }

template <typename V>
inline void numeric_pack(dynamic_packer& p, V v);

template <>
inline void numeric_pack<uint8_t>(dynamic_packer& p, uint8_t v)
	{ p.pack_unsigned_int_8(v); }

template <>
inline void numeric_pack<uint16_t>(dynamic_packer& p, uint16_t v)
	{ p.pack_unsigned_int_16(v); }

template <>
inline void numeric_pack<uint32_t>(dynamic_packer& p, uint32_t v)
	{ p.pack_unsigned_int_32(v); }

template <>
inline void numeric_pack<uint64_t>(dynamic_packer& p, uint64_t v)
	{ p.pack_unsigned_int_64(v); }

template <>
inline void numeric_pack<int8_t>(dynamic_packer& p, int8_t v)
	{ p.pack_unsigned_int_8(v); }

template <>
inline void numeric_pack<int16_t>(dynamic_packer& p, int16_t v)
	{ p.pack_unsigned_int_16(v); }

template <>
inline void numeric_pack<int32_t>(dynamic_packer& p, int32_t v)
	{ p.pack_unsigned_int_32(v); }

template <>
inline void numeric_pack<int64_t>(dynamic_packer& p, int64_t v)
	{ p.pack_unsigned_int_64(v); }

template <>
inline void numeric_pack<float>(dynamic_packer& p, float v)
	{ p.pack_float(v); }

template <>
inline void numeric_pack<double>(dynamic_packer& p, double v)
	{ p.pack_double(v); }

}  // noname namespace


bool object_nil::isnil() const { return true; }
bool object_nil::operator== (const object_class* x) const
	{ return typeid(*this) == typeid(*x); }
void object_nil::pack(dynamic_packer& p) const
	{ p.pack_nil(); }
const object_class* object_nil::inspect(std::ostream& s) const
	{ s << "nil"; return this; }

bool object_true::xbool() const { return true; }
bool object_true::operator== (const object_class* x) const
	{ return typeid(*this) == typeid(*x); }
void object_true::pack(dynamic_packer& p) const
	{ p.pack_true(); }
const object_class* object_true::inspect(std::ostream& s) const
	{ s << "true"; return this; }

bool object_false::xbool() const { return false; }
bool object_false::operator== (const object_class* x) const
	{ return typeid(*this) == typeid(*x); }
void object_false::pack(dynamic_packer& p) const
	{ p.pack_false(); }
const object_class* object_false::inspect(std::ostream& s) const
	{ s << "false"; return this; }


#define INTEGER_OBJECT(NAME) \
uint8_t  object_##NAME::xu8    () const { return val; }							\
uint16_t object_##NAME::xu16   () const { return integer_cast<uint16_t>(val); }	\
uint32_t object_##NAME::xu32   () const { return integer_cast<uint32_t>(val); }	\
uint64_t object_##NAME::xu64   () const { return integer_cast<uint64_t>(val); }	\
int8_t   object_##NAME::xi8    () const { return integer_cast<int8_t>(val);   }	\
int16_t  object_##NAME::xi16   () const { return integer_cast<int16_t>(val);  }	\
int32_t  object_##NAME::xi32   () const { return integer_cast<int32_t>(val);  }	\
int64_t  object_##NAME::xi64   () const { return integer_cast<int64_t>(val);  }	\
float    object_##NAME::xfloat () const { return integer_cast<float>(val);    }	\
double   object_##NAME::xdouble() const { return integer_cast<double>(val);   }	\
bool object_##NAME::operator== (const object_class* x) const					\
	try { return val == x->x##NAME(); }											\
	catch (type_error&) { return false; }										\
bool object_##NAME::operator<  (const object_class* x) const					\
	try { return val < x->x##NAME(); }											\
	catch (positive_overflow_error&) { return true; }							\
	catch (overflow_error&) { return false; }									\
bool object_##NAME::operator>  (const object_class* x) const					\
	try { return val > x->x##NAME(); }											\
	catch (negative_overflow_error&) { return true; }							\
	catch (overflow_error&) { return false; }									\
void object_##NAME::pack(dynamic_packer& p) const								\
	{ numeric_pack(p, val); }													\
const object_class* object_##NAME::inspect(std::ostream& s) const				\
	{ numeric_inspect(val, s); return this; }									\


INTEGER_OBJECT(u8)
INTEGER_OBJECT(u16)
INTEGER_OBJECT(u32)
INTEGER_OBJECT(u64)
INTEGER_OBJECT(i8)
INTEGER_OBJECT(i16)
INTEGER_OBJECT(i32)
INTEGER_OBJECT(i64)

#undef INTEGER_OBJECT(NAME)


#define FLOAT_OBJECT(NAME) \
uint8_t  object_##NAME::xu8    () const { return val; }							\
uint16_t object_##NAME::xu16   () const { return integer_cast<uint16_t>(val); }	\
uint32_t object_##NAME::xu32   () const { return integer_cast<uint32_t>(val); }	\
uint64_t object_##NAME::xu64   () const { return integer_cast<uint64_t>(val); }	\
int8_t   object_##NAME::xi8    () const { return integer_cast<int8_t>(val);   }	\
int16_t  object_##NAME::xi16   () const { return integer_cast<int16_t>(val);  }	\
int32_t  object_##NAME::xi32   () const { return integer_cast<int32_t>(val);  }	\
int64_t  object_##NAME::xi64   () const { return integer_cast<int64_t>(val);  }	\
float    object_##NAME::xfloat () const { return float_cast<float>(val);    }	\
double   object_##NAME::xdouble() const { return float_cast<double>(val);   }	\
bool object_##NAME::operator== (const object_class* x) const					\
	try { return val == x->x##NAME(); }											\
	catch (type_error&) { return false; }										\
bool object_##NAME::operator<  (const object_class* x) const {					\
	try { return val < x->xdouble(); }											\
	catch (positive_overflow_error&) { return true; }							\
	catch (overflow_error&) { return false; }									\
	catch (underflow_error&) {													\
		if(val < 0.0) {															\
			if(numeric_overflow<int64_t, double>::test(val) == -1) { return true; } \
			try { return static_cast<int64_t>(val) < x->xi64(); }				\
			catch (type_error&) { return true; }								\
		} else {																\
			if(numeric_overflow<uint64_t, double>::test(val) == 1) { return false; } \
			try { return static_cast<uint64_t>(val) < x->xu64(); }				\
			catch (type_error&) { return false; }								\
		}																		\
	} }																			\
bool object_##NAME::operator>  (const object_class* x) const {					\
	try { return val > x->xdouble(); }											\
	catch (negative_overflow_error&) { return true; }							\
	catch (overflow_error&) { return false; }									\
	catch (underflow_error&) {													\
		if(val < 0.0) {															\
			if(numeric_overflow<int64_t, double>::test(val) == -1) { return false; } \
			try { return static_cast<int64_t>(val) > x->xi64(); }				\
			catch (type_error&) { return false; }								\
		} else {																\
			if(numeric_overflow<uint64_t, double>::test(val) == 1) { return true; } \
			try { return static_cast<uint64_t>(val) > x->xu64(); }				\
			catch (type_error&) { return true; }								\
		}																		\
	} }																			\
void object_##NAME::pack(dynamic_packer& p) const								\
	{ numeric_pack(p, val); }													\
const object_class* object_##NAME::inspect(std::ostream& s) const				\
	{ s << val; return this; }													\

FLOAT_OBJECT(float)
FLOAT_OBJECT(double)

#undef FLOAT_OBJECT(NAME)


#define RAW_OBJECT(NAME, EXTRA) \
EXTRA																			\
bool object_##NAME::operator== (const object_class* x) const					\
	try {																		\
		const_raw xr(x->xraw());												\
		return len == xr.len && (ptr == xr.ptr || memcmp(ptr, xr.ptr, len) == 0); \
	} catch (type_error&) { return false; }										\
bool object_##NAME::operator<  (const object_class* x) const {					\
	const_raw xr(x->xraw());													\
	if(len == xr.len) { return ptr != xr.ptr && memcmp(ptr, xr.ptr, len) < 0; }	\
	else { return len < xr.len; } }												\
bool object_##NAME::operator>  (const object_class* x) const {					\
	const_raw xr(x->xraw());													\
	if(len == xr.len) { return ptr != xr.ptr && memcmp(ptr, xr.ptr, len) > 0; }	\
	else { return len > xr.len; } }												\
void object_##NAME::pack(dynamic_packer& p) const								\
	{ p.pack_raw(ptr, len); }													\
const object_class* object_##NAME::inspect(std::ostream& s) const				\
	{ (s << '"').write((const char*)ptr, len) << '"'; return this; }  // FIXME escape


RAW_OBJECT(raw_ref,
	raw object_raw_ref::xraw() { return raw(ptr, len); }
	const_raw object_raw_ref::xraw() const { return const_raw(ptr, len); } )

RAW_OBJECT(const_raw_ref,
	const_raw object_const_raw_ref::xraw() const { return const_raw(ptr, len); } )

#undef RAW_OBJECT(NAME, EXTRA)


      array& object_array::xarray()       { return val; }
const array& object_array::xarray() const { return val; }
bool object_array::operator== (const object_class* x) const
	try {
		const std::vector<object>& xa(x->xarray());
		if(val.size() != xa.size()) { return false; }
		for(std::vector<object>::const_iterator iv(val.begin()), iv_end(val.end()), ix(xa.begin());
				iv != iv_end;
				++iv, ++ix) {
			if(*iv != *ix) { return false; }
		}
		return true;
	} catch (type_error&) { return false; }
const object_class* object_array::inspect(std::ostream& s) const
{
	s << '[';
	if(!val.empty()) {
		std::vector<object>::const_iterator it(val.begin());
		s << *it;
		++it;
		for(std::vector<object>::const_iterator it_end(val.end());
				it != it_end;
				++it) {
			s << ", " << *it;
		}
	}
	s << ']';
	return this;
}
void object_array::pack(dynamic_packer& p) const
{
	p.pack_array(val.size());
	for(std::vector<object>::const_iterator it(val.begin()), it_end(val.end());
			it != it_end;
			++it) {
		it->pack(p);
	}
}


      map& object_map::xmap()       { return val; }
const map& object_map::xmap() const { return val; }
bool object_map::operator== (const object_class* x) const
	try {
		const std::map<object, object>& xm(x->xmap());
		if(val.size() != xm.size()) { return false; }
		for(std::map<object, object>::const_iterator iv(val.begin()), iv_end(val.end()), ix(xm.begin());
				iv != iv_end;
				++iv, ++ix) {
			if(iv->first != ix->first || iv->second != ix->first) { return false; }
		}
		return true;
	} catch (type_error&) { return false; }
const object_class* object_map::inspect(std::ostream& s) const
{
	s << '{';
	if(!val.empty()) {
		std::map<object, object>::const_iterator it(val.begin());
		s << it->first << "=>" << it->second;
		++it;
		for(std::map<object, object>::const_iterator it_end(val.end());
				it != it_end;
				++it) {
			s << ", " << it->first << "=>" << it->second;
		}
	}
	s << '}';
	return this;
}
void object_map::pack(dynamic_packer& p) const
{
	p.pack_map(val.size());
	for(std::map<object, object>::const_iterator it(val.begin()), it_end(val.end());
			it != it_end;
			++it) {
		it->first.pack(p);
		it->second.pack(p);
	}
}


}  // namespace msgpack

