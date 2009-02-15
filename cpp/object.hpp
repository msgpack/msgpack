#ifndef MSGPACK_OBJECT_HPP__
#define MSGPACK_OBJECT_HPP__
#include <iostream>

#include <cstddef>
#include <stdexcept>
#include <typeinfo>
#include <ostream>
#include <vector>
#include <map>
#include <string>

namespace msgpack {


class type_error      : public std::bad_cast { };
class cast_error      : public type_error { };
class overflow_error  : public type_error { };
class underflow_error : public type_error { };
class positive_overflow_error : public overflow_error { };
class negative_overflow_error : public overflow_error { };


struct raw {
	explicit raw() : ptr(NULL), len(0) {}
	explicit raw(void* p, size_t l) : ptr(p), len(l) {}
public:
	void* ptr;
	size_t len;
public:
	std::string str() { return std::string((const char*)ptr, len); }
};

struct const_raw {
	const_raw() : ptr(NULL), len(0) {}
	const_raw(const void* p, size_t l) : ptr(p), len(l) {}
public:
	const void* ptr;
	size_t len;
public:
	std::string str() { return std::string((const char*)ptr, len); }
};


struct object;

typedef std::map<object, object> map;
typedef std::vector<object> array;


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


struct object_class {
	virtual ~object_class() {}
	virtual     bool   isnil() const { return false; }
	virtual     bool   xbool() const { throw cast_error(); }
	virtual  uint8_t     xu8() const { throw cast_error(); }
	virtual uint16_t    xu16() const { throw cast_error(); }
	virtual uint32_t    xu32() const { throw cast_error(); }
	virtual uint64_t    xu64() const { throw cast_error(); }
	virtual   int8_t     xi8() const { throw cast_error(); }
	virtual  int16_t    xi16() const { throw cast_error(); }
	virtual  int32_t    xi32() const { throw cast_error(); }
	virtual  int64_t    xi64() const { throw cast_error(); }
	virtual    float  xfloat() const { throw cast_error(); }
	virtual   double xdouble() const { throw cast_error(); }
	virtual      raw    xraw() { throw cast_error(); }
	virtual   array&  xarray() { throw cast_error(); }
	virtual     map&    xmap() { throw cast_error(); }
	virtual    const_raw   xraw() const { throw cast_error(); }
	virtual const array& xarray() const { throw cast_error(); }
	virtual const   map&   xmap() const { throw cast_error(); }
	virtual bool operator== (const object_class* x) const { return false; }
	bool operator!= (const object_class* x) const { return !(this->operator==(x)); }
	virtual bool operator<  (const object_class* x) const { throw cast_error(); }
	virtual bool operator>  (const object_class* x) const { throw cast_error(); }
	operator     bool() const { return   xbool(); } // FIXME !isnil();
	operator  uint8_t() const { return     xu8(); }
	operator uint16_t() const { return    xu16(); }
	operator uint32_t() const { return    xu32(); }
	operator uint64_t() const { return    xu64(); }
	operator   int8_t() const { return     xi8(); }
	operator  int16_t() const { return    xi16(); }
	operator  int32_t() const { return    xi32(); }
	operator  int64_t() const { return    xi64(); }
	operator    float() const { return  xfloat(); }
	operator   double() const { return xdouble(); }
	operator    raw() { return   xraw(); }
	operator array&() { return xarray(); }
	operator   map&() { return   xmap(); }
	operator    const_raw() const { return   xraw(); }
	operator const array&() const { return xarray(); }
	operator const   map&() const { return   xmap(); }
	virtual const object_class* inspect(std::ostream& s) const
		{ s << '<' << typeid(*this).name() << '>'; return this; }
protected:
	template <typename T, typename X>
	static void check_overflow(X x) { numeric_overflow<T, X>::check(x); }
	template <typename T, typename X>
	static void check_underflow(X x) { numeric_underflow<T, X>::check(x); }
};

inline std::ostream& operator<< (std::ostream& s, const object_class* o)
	{ o->inspect(s); return s; }


struct object_container_mixin {};
struct object_constructor_mixin {};


struct object {
	explicit object() : val(NULL) {}
	object(object_class* v) : val(v) {}
	//object(object_class& v) : val(&v) {}
	~object() {}
	    bool   isnil() const { return val->isnil();   }
	    bool   xbool() const { return val->xbool();   }
	 uint8_t     xu8() const { return val->xu8();     }
	uint16_t    xu16() const { return val->xu16();    }
	uint32_t    xu32() const { return val->xu32();    }
	uint64_t    xu64() const { return val->xu64();    }
	  int8_t     xi8() const { return val->xi8();     }
	 int16_t    xi16() const { return val->xi16();    }
	 int32_t    xi32() const { return val->xi32();    }
	 int64_t    xi64() const { return val->xi64();    }
	   float  xfloat() const { return val->xfloat();  }
	  double xdouble() const { return val->xdouble(); }
	     raw    xraw() { return val->xraw();   }
	  array&  xarray() { return val->xarray(); }
	    map&    xmap() { return val->xmap();   }
	   const_raw   xraw() const { return const_cast<const object_class*>(val)->xraw();   }
	const array& xarray() const { return const_cast<const object_class*>(val)->xarray(); }
	const   map&   xmap() const { return const_cast<const object_class*>(val)->xmap();   }
	bool operator== (object x) const { return val->operator== (x.val); }
	bool operator!= (object x) const { return val->operator!= (x.val); }
	bool operator<  (object x) const { return val->operator<  (x.val); }
	bool operator>  (object x) const { return val->operator>  (x.val); }
	operator     bool() const { return val->operator bool();     }
	operator  uint8_t() const { return val->operator uint8_t();  }
	operator uint16_t() const { return val->operator uint16_t(); }
	operator uint32_t() const { return val->operator uint32_t(); }
	operator uint64_t() const { return val->operator uint64_t(); }
	operator   int8_t() const { return val->operator int8_t();   }
	operator  int16_t() const { return val->operator int16_t();  }
	operator  int32_t() const { return val->operator int32_t();  }
	operator  int64_t() const { return val->operator int64_t();  }
	operator    float() const { return val->operator float();    }
	operator   double() const { return val->operator double();   }
	operator    raw() { return val->operator raw();    }
	operator array&() { return val->operator array&(); }
	operator   map&() { return val->operator map&();   }
	operator    raw() const { return val->operator raw();    }
	operator array&() const { return val->operator array&(); }
	operator   map&() const { return val->operator map&();   }
	const object& inspect(std::ostream& s) const
		{ val->inspect(s); return *this; }
private:
	friend class object_container_mixin;
	friend class object_constructor_mixin;
	object_class* val;
};

inline std::ostream& operator<< (std::ostream& s, const object& o)
	{ o.inspect(s); return s; }


struct object_nil : object_class {
	bool isnil() const { return true; }
	bool operator== (const object_class* x) const { return typeid(*this) == typeid(*x); }
	const object_class* inspect(std::ostream& s) const
		{ s << "nil"; return this; }
};

struct object_true : object_class {
	bool xbool() const { return true; }
	bool operator== (const object_class* x) const { return typeid(*this) == typeid(*x); }
	const object_class* inspect(std::ostream& s) const
		{ s << "true"; return this; }
};

struct object_false : object_class {
	bool xbool() const { return false; }
	bool operator== (const object_class* x) const { return typeid(*this) == typeid(*x); }
	const object_class* inspect(std::ostream& s) const
		{ s << "false"; return this; }
};

struct object_u8 : object_class {
	explicit object_u8(uint8_t v) : val(v) {}
	 uint8_t  xu8() const { return val; }
	uint16_t xu16() const { return static_cast<uint16_t>(val); }
	uint32_t xu32() const { return static_cast<uint32_t>(val); }
	uint64_t xu64() const { return static_cast<uint64_t>(val); }
	  int8_t  xi8() const { check_overflow<int8_t>(val);
							return static_cast<int8_t>(val);  }
	 int16_t xi16() const { return static_cast<int16_t>(val); }
	 int32_t xi32() const { return static_cast<int32_t>(val); }
	 int64_t xi64() const { return static_cast<int64_t>(val); }
	 float  xfloat() const { return static_cast<float>(val); }
	double xdouble() const { return static_cast<double>(val); }
	bool operator== (const object_class* x) const { try { return val == x->xu8(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return val < x->xu8(); }
										catch (positive_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	bool operator>  (const object_class* x) const { try { return val > x->xu8(); }
										catch (negative_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	const object_class* inspect(std::ostream& s) const
		{ s << (uint16_t)val; return this; }
private:
	uint8_t val;
};

struct object_u16 : object_class {
	explicit object_u16(uint16_t v) : val(v) {}
	 uint8_t  xu8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	uint16_t xu16() const { return val; }
	uint32_t xu32() const { return static_cast<uint32_t>(val); }
	uint64_t xu64() const { return static_cast<uint64_t>(val); }
	  int8_t  xi8() const { check_overflow<int8_t>(val);
							return static_cast<int8_t>(val);  }
	 int16_t xi16() const { check_overflow<int16_t>(val);
							return static_cast<int16_t>(val); }
	 int32_t xi32() const { return static_cast<int32_t>(val); }
	 int64_t xi64() const { return static_cast<int64_t>(val); }
	 float  xfloat() const { return static_cast<float>(val); }
	double xdouble() const { return static_cast<double>(val); }
	bool operator== (const object_class* x) const { try { return val == x->xu16(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return val < x->xu16(); }
										catch (positive_overflow_error&) { return true; }
										catch (type_error&) { return false; } }
	bool operator>  (const object_class* x) const { try { return val > x->xu16(); }
										catch (negative_overflow_error&) { return true; }
										catch (type_error&) { return false; } }
	const object_class* inspect(std::ostream& s) const
		{ s << val; return this; }
private:
	uint16_t val;
};

struct object_u32 : object_class {
	explicit object_u32(uint32_t v) : val(v) {}
	 uint8_t  xu8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val);  }
	uint16_t xu16() const { check_overflow<uint16_t>(val);
							return static_cast<uint16_t>(val); }
	uint32_t xu32() const { return val; }
	uint64_t xu64() const { return static_cast<uint64_t>(val); }
	  int8_t  xi8() const { check_overflow<int8_t>(val);
							return static_cast<int8_t>(val);  }
	 int16_t xi16() const { check_overflow<int16_t>(val);
							return static_cast<int16_t>(val); }
	 int32_t xi32() const { check_overflow<int32_t>(val);
							return static_cast<int32_t>(val); }
	 int64_t xi64() const { return static_cast<int64_t>(val); }
	 float  xfloat() const { check_underflow<float>(val);
							return static_cast<float>(val); }
	double xdouble() const { return static_cast<double>(val); }
	bool operator== (const object_class* x) const { try { return val == x->xu32(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return val < x->xu32(); }
										catch (positive_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	bool operator>  (const object_class* x) const { try { return val > x->xu32(); }
										catch (negative_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	const object_class* inspect(std::ostream& s) const
		{ s << val; return this; }
private:
	uint32_t val;
};

struct object_u64 : object_class {
	explicit object_u64(uint64_t v) : val(v) {}
	 uint8_t  xu8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val);  }
	uint16_t xu16() const { check_overflow<uint16_t>(val);
							return static_cast<uint16_t>(val); }
	uint32_t xu32() const { check_overflow<uint32_t>(val);
							return static_cast<uint32_t>(val); }
	uint64_t xu64() const { return val; }
	  int8_t  xi8() const { check_overflow<int8_t>(val);
							return static_cast<int8_t>(val);  }
	 int16_t xi16() const { check_overflow<int16_t>(val);
							return static_cast<int16_t>(val); }
	 int32_t xi32() const { check_overflow<int32_t>(val);
							return static_cast<int32_t>(val); }
	 int64_t xi64() const { check_overflow<int64_t>(val);
							return static_cast<int64_t>(val); }
	 float  xfloat() const { check_underflow<float>(val);
							return static_cast<float>(val); }
	double xdouble() const { check_underflow<double>(val);
							 return static_cast<double>(val); }
	bool operator== (const object_class* x) const { try { return val == x->xu64(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return val < x->xu64(); }
										catch (positive_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	bool operator>  (const object_class* x) const { try { return val > x->xu64(); }
										catch (negative_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	const object_class* inspect(std::ostream& s) const
		{ s << val; return this; }
private:
	uint64_t val;
};

struct object_i8 : object_class {
	explicit object_i8(int8_t v) : val(v) {}
	 uint8_t  xu8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val);  }
	uint16_t xu16() const { check_overflow<uint16_t>(val);
							return static_cast<uint16_t>(val); }
	uint32_t xu32() const { check_overflow<uint32_t>(val);
							return static_cast<uint32_t>(val); }
	uint64_t xu64() const { check_overflow<uint64_t>(val);
							return static_cast<uint64_t>(val); }
	  int8_t  xi8() const { return val; }
	 int16_t xi16() const { return static_cast<int16_t>(val); }
	 int32_t xi32() const { return static_cast<int32_t>(val); }
	 int64_t xi64() const { return static_cast<int64_t>(val); }
	 float  xfloat() const { return static_cast<float>(val); }
	double xdouble() const { return static_cast<double>(val); }
	bool operator== (const object_class* x) const { try { return val == x->xi8(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return val < x->xi8(); }
										catch (positive_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	bool operator>  (const object_class* x) const { try { return val > x->xi8(); }
										catch (negative_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	const object_class* inspect(std::ostream& s) const
		{ s << (int16_t)val; return this; }
private:
	int8_t val;
};

struct object_i16 : object_class {
	explicit object_i16(int16_t v) : val(v) {}
	 uint8_t  xu8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val);  }
	uint16_t xu16() const { check_overflow<uint16_t>(val);
							return static_cast<uint16_t>(val); }
	uint32_t xu32() const { check_overflow<uint32_t>(val);
							return static_cast<uint32_t>(val); }
	uint64_t xu64() const { check_overflow<uint64_t>(val);
							return static_cast<uint64_t>(val); }
	  int8_t  xi8() const { check_overflow<int8_t>(val);
							return static_cast<int8_t>(val);  }
	 int16_t xi16() const { return val; }
	 int32_t xi32() const { return static_cast<int32_t>(val); }
	 int64_t xi64() const { return static_cast<int64_t>(val); }
	 float  xfloat() const { return static_cast<float>(val); }
	double xdouble() const { return static_cast<double>(val); }
	bool operator== (const object_class* x) const { try { return val == x->xi16(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return val < x->xi16(); }
										catch (positive_overflow_error&) { return true; }
										catch (type_error&) { return false; } }
	bool operator>  (const object_class* x) const { try { return val > x->xi16(); }
										catch (negative_overflow_error&) { return true; }
										catch (type_error&) { return false; } }
	const object_class* inspect(std::ostream& s) const
		{ s << val; return this; }
private:
	int16_t val;
};

struct object_i32 : object_class {
	explicit object_i32(int32_t v) : val(v) {}
	 uint8_t  xu8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val);  }
	uint16_t xu16() const { check_overflow<uint16_t>(val);
							return static_cast<uint16_t>(val); }
	uint32_t xu32() const { check_overflow<uint32_t>(val);
							return static_cast<uint32_t>(val); }
	uint64_t xu64() const { check_overflow<uint64_t>(val);
							return static_cast<uint64_t>(val); }
	  int8_t  xi8() const { check_overflow<int8_t>(val);
							return static_cast<int8_t>(val);  }
	 int16_t xi16() const { check_overflow<int16_t>(val);
							return static_cast<int16_t>(val); }
	 int32_t xi32() const { return val; }
	 int64_t xi64() const { return static_cast<int64_t>(val); }
	 float  xfloat() const { check_underflow<float>(val);
							return static_cast<float>(val); }
	double xdouble() const { return static_cast<double>(val); }
	bool operator== (const object_class* x) const { try { return val == x->xi32(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return val < x->xi32(); }
										catch (positive_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	bool operator>  (const object_class* x) const { try { return val > x->xi32(); }
										catch (negative_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	const object_class* inspect(std::ostream& s) const
		{ s << val; return this; }
private:
	int32_t val;
};

struct object_i64 : object_class {
	explicit object_i64(int64_t v) : val(v) {}
	 uint8_t  xu8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val);  }
	uint16_t xu16() const { check_overflow<uint16_t>(val);
							return static_cast<uint16_t>(val); }
	uint32_t xu32() const { check_overflow<uint32_t>(val);
							return static_cast<uint32_t>(val); }
	uint64_t xu64() const { check_overflow<uint64_t>(val);
							return static_cast<uint64_t>(val); }
	  int8_t  xi8() const { check_overflow<int8_t>(val);
							return static_cast<int8_t>(val);  }
	 int16_t xi16() const { check_overflow<int16_t>(val);
							return static_cast<int16_t>(val); }
	 int32_t xi32() const { check_overflow<int32_t>(val);
							return static_cast<int32_t>(val); }
	 int64_t xi64() const { return val; }
	 float  xfloat() const { check_underflow<float>(val);
							return static_cast<float>(val); }
	double xdouble() const { check_underflow<double>(val);
							 return static_cast<double>(val); }
	bool operator== (const object_class* x) const { try { return val == x->xi64(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return val < x->xi64(); }
										catch (positive_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	bool operator>  (const object_class* x) const { try { return val > x->xi64(); }
										catch (negative_overflow_error&) { return true; }
										catch (overflow_error&) { return false; } }
	const object_class* inspect(std::ostream& s) const
		{ s << val; return this; }
private:
	int64_t val;
};


struct object_float : object_class {
	object_float(float v) : val(v) {}
	 uint8_t  xu8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	uint16_t xu16() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	uint32_t xu32() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	uint64_t xu64() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	  int8_t  xi8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	 int16_t xi16() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	 int32_t xi32() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	 int64_t xi64() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	 float  xfloat() const { return val; }
	double xdouble() const { return static_cast<double>(val); }
	bool operator== (const object_class* x) const { try { return val == x->xfloat(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return static_cast<double>(val) < x->xdouble(); }
										catch (positive_overflow_error&) { return true; }
										catch (overflow_error&) { return false; }
										catch (underflow_error&) {
											if(val < 0.0) {
												if(numeric_overflow<int64_t, float>::test(val) == -1) { return true; }
												try { return static_cast<int64_t>(val) < x->xi64(); }
												catch (type_error&) { return true; }
											} else {
												if(numeric_overflow<uint64_t, float>::test(val) == 1) { return false; }
												try { return static_cast<uint64_t>(val) < x->xu64(); }
												catch (type_error&) { return false; }
											}
										} }
	bool operator>  (const object_class* x) const { try { return static_cast<double>(val) > x->xdouble(); }
										catch (negative_overflow_error&) { return true; }
										catch (overflow_error&) { return false; }
										catch (underflow_error&) {
											if(val < 0.0) {
												if(numeric_overflow<int64_t, float>::test(val) == -1) { return false; }
												try { return static_cast<int64_t>(val) > x->xi64(); }
												catch (type_error&) { return false; }
											} else {
												if(numeric_overflow<uint64_t, float>::test(val) == 1) { return true; }
												try { return static_cast<uint64_t>(val) > x->xu64(); }
												catch (type_error&) { return true; }
											}
										} }
	const object_class* inspect(std::ostream& s) const
		{ s << val; return this; }
private:
	float val;
};


struct object_double : object_class {
	object_double(double v) : val(v) {}
	 uint8_t  xu8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	uint16_t xu16() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	uint32_t xu32() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	uint64_t xu64() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	  int8_t  xi8() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	 int16_t xi16() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	 int32_t xi32() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	 int64_t xi64() const { check_overflow<uint8_t>(val);
							return static_cast<uint8_t>(val); }
	 float  xfloat() const { check_overflow<float>(val);
							check_underflow<float>(val);
							return static_cast<float>(val); }
	double xdouble() const { return val; }
	bool operator== (const object_class* x) const { try { return val == x->xdouble(); }
										catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { try { return val < x->xdouble(); }
										catch (positive_overflow_error&) { return true; }
										catch (overflow_error&) { return false; }
										catch (underflow_error&) {
											if(val < 0.0) {
												if(numeric_overflow<int64_t, double>::test(val) == -1) { return true; }
												try { return static_cast<int64_t>(val) < x->xi64(); }
												catch (type_error&) { return true; }
											} else {
												if(numeric_overflow<uint64_t, double>::test(val) == 1) { return false; }
												try { return static_cast<uint64_t>(val) < x->xu64(); }
												catch (type_error&) { return false; }
											}
										} }
	bool operator>  (const object_class* x) const { try { return val > x->xdouble(); }
										catch (negative_overflow_error&) { return true; }
										catch (overflow_error&) { return false; }
										catch (underflow_error&) {
											if(val < 0.0) {
												if(numeric_overflow<int64_t, double>::test(val) == -1) { return false; }
												try { return static_cast<int64_t>(val) > x->xi64(); }
												catch (type_error&) { return false; }
											} else {
												if(numeric_overflow<uint64_t, double>::test(val) == 1) { return true; }
												try { return static_cast<uint64_t>(val) > x->xu64(); }
												catch (type_error&) { return true; }
											}
										} }
	const object_class* inspect(std::ostream& s) const
		{ s << val; return this; }
private:
	double val;
};


struct object_raw : object_class {
	explicit object_raw(void* p, uint32_t l) : ptr(p), len(l) {}
	raw xraw() { return raw(ptr, len); }
	const_raw xraw() const { return const_raw(ptr, len); }
	bool operator== (const object_class* x) const { try { const_raw xr(x->xraw());
		return len == xr.len && (ptr == xr.ptr || memcmp(ptr, xr.ptr, len) == 0); }
		catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { const_raw xr(x->xraw());
		if(len == xr.len) { return ptr != xr.ptr && memcmp(ptr, xr.ptr, len) < 0; }
		else { return len < xr.len; } }
	bool operator>  (const object_class* x) const { const_raw xr(x->xraw());
		if(len == xr.len) { return ptr != xr.ptr && memcmp(ptr, xr.ptr, len) > 0; }
		else { return len > xr.len; } }
	const object_class* inspect(std::ostream& s) const
		{ (s << '"').write((const char*)ptr, len) << '"'; return this; }  // FIXME escape
private:
	void* ptr;
	uint32_t len;
};

struct object_const_raw : object_class {
	explicit object_const_raw(const void* p, uint32_t l) : ptr(p), len(l) {}
	const_raw xraw() const { return const_raw(ptr, len); }
	bool operator== (const object_class* x) const { try { const_raw xr(x->xraw());
		return len == xr.len && (ptr == xr.ptr || memcmp(ptr, xr.ptr, len) == 0); }
		catch (type_error&) { return false; } }
	bool operator<  (const object_class* x) const { const_raw xr(x->xraw());
		if(len == xr.len) { return ptr != xr.ptr && memcmp(ptr, xr.ptr, len) < 0; }
		else { return len < xr.len; } }
	bool operator>  (const object_class* x) const { const_raw xr(x->xraw());
		if(len == xr.len) { return ptr != xr.ptr && memcmp(ptr, xr.ptr, len) > 0; }
		else { return len > xr.len; } }
	const object_class* inspect(std::ostream& s) const
		{ (s << '"').write((const char*)ptr, len) << '"'; return this; }  // FIXME escape
private:
	const void* ptr;
	uint32_t len;
};

struct object_array : object_class, object_container_mixin {
	explicit object_array() {}
	explicit object_array(uint32_t n) { val.reserve(n); }
	array& xarray() { return val; }
	const array& xarray() const { return val; }
	bool operator== (const object_class* x) const { try {
		const std::vector<object>& xa(x->xarray());
		if(val.size() != xa.size()) { return false; }
		for(std::vector<object>::const_iterator iv(val.begin()), iv_end(val.end()), ix(xa.begin());
				iv != iv_end;
				++iv, ++ix) {
			if(*iv != *ix) { return false; }
		}
		return true;
		} catch (type_error&) { return false; } }
	// FIXME operator< operator>
	const object_class* inspect(std::ostream& s) const {
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
		return this; }
public:
	void push_back(object o) { val.push_back(o); }
private:
	std::vector<object> val;
};

// FIXME hash, operator==: nil, true, false, containerを入れられない
struct object_map : object_class, object_container_mixin {
	explicit object_map() {}
	map& xmap() { return val; }
	const map& xmap() const { return val; }
	bool operator== (const object_class* x) const { try {
		const std::map<object, object>& xm(x->xmap());
		if(val.size() != xm.size()) { return false; }
		for(std::map<object, object>::const_iterator iv(val.begin()), iv_end(val.end()), ix(xm.begin());
				iv != iv_end;
				++iv, ++ix) {
			if(iv->first != ix->first || iv->second != ix->first) { return false; }
		}
		return true;
		} catch (type_error&) { return false; } }
	// FIXME operator< operator>
	const object_class* inspect(std::ostream& s) const {
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
		return this; }
public:
	void store(object k, object v) { val[k] = v; }
private:
	std::map<object, object> val;
};


}  // namespace msgpack

#endif /* msgpack/object.hpp */

