#ifndef MSGPACK_OBJECT_HPP__
#define MSGPACK_OBJECT_HPP__

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
	explicit const_raw() : ptr(NULL), len(0) {}
	explicit const_raw(const void* p, size_t l) : ptr(p), len(l) {}
	const_raw(const raw& m) : ptr(m.ptr), len(m.len) {}
public:
	const void* ptr;
	size_t len;
public:
	std::string str() { return std::string((const char*)ptr, len); }
};


struct object;

typedef std::map<object, object> map;
typedef std::vector<object> array;

class dynamic_packer;


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
	virtual void pack(dynamic_packer& p) const = 0;
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
	void pack(dynamic_packer& p) const { val->pack(p); }
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
	bool isnil() const;
	bool operator== (const object_class* x) const;
	void pack(dynamic_packer& p) const;
	const object_class* inspect(std::ostream& s) const;
};

struct object_true : object_class {
	bool xbool() const;
	bool operator== (const object_class* x) const;
	void pack(dynamic_packer& p) const;
	const object_class* inspect(std::ostream& s) const;
};

struct object_false : object_class {
	bool xbool() const;
	bool operator== (const object_class* x) const;
	void pack(dynamic_packer& p) const;
	const object_class* inspect(std::ostream& s) const;
};

#define INTEGER_CLASS(TYPE, NAME) \
struct object_##NAME : object_class {						\
	explicit object_##NAME(TYPE v) : val(v) {}				\
	uint8_t  xu8    () const;								\
	uint16_t xu16   () const;								\
	uint32_t xu32   () const;								\
	uint64_t xu64   () const;								\
	int8_t   xi8    () const;								\
	int16_t  xi16   () const;								\
	int32_t  xi32   () const;								\
	int64_t  xi64   () const;								\
	float    xfloat () const;								\
	double   xdouble() const;								\
	bool operator== (const object_class* x) const;			\
	bool operator<  (const object_class* x) const;			\
	bool operator>  (const object_class* x) const;			\
	void pack(dynamic_packer& p) const;						\
	const object_class* inspect(std::ostream& s) const;		\
private:													\
	TYPE val;												\
};

INTEGER_CLASS(uint8_t,  u8)
INTEGER_CLASS(uint16_t, u16)
INTEGER_CLASS(uint32_t, u32)
INTEGER_CLASS(uint64_t, u64)
INTEGER_CLASS(int8_t,  i8)
INTEGER_CLASS(int16_t, i16)
INTEGER_CLASS(int32_t, i32)
INTEGER_CLASS(int64_t, i64)

#undef INTEGER_CLASS(TYPE, NAME)


#define FLOAT_CLASS(TYPE, NAME) \
struct object_##NAME : object_class {						\
	object_##NAME(TYPE v) : val(v) {}						\
	uint8_t  xu8    () const;								\
	uint16_t xu16   () const;								\
	uint32_t xu32   () const;								\
	uint64_t xu64   () const;								\
	int8_t   xi8    () const;								\
	int16_t  xi16   () const;								\
	int32_t  xi32   () const;								\
	int64_t  xi64   () const;								\
	float    xfloat () const;								\
	double   xdouble() const;								\
	bool operator== (const object_class* x) const;			\
	bool operator<  (const object_class* x) const;			\
	bool operator>  (const object_class* x) const;			\
	void pack(dynamic_packer& p) const;						\
	const object_class* inspect(std::ostream& s) const;		\
private:													\
	TYPE val;												\
};

FLOAT_CLASS(float, float)
FLOAT_CLASS(double, double)

#undef FLOAT_CLASS(TYPE, NAME)


#define RAW_CLASS(NAME, TYPE, EXTRA) \
struct object_##NAME : object_class {									\
	explicit object_##NAME(TYPE p, uint32_t l) : ptr(p), len(l) {}		\
	EXTRA																\
	bool operator== (const object_class* x) const;						\
	bool operator<  (const object_class* x) const;						\
	bool operator>  (const object_class* x) const;						\
	void pack(dynamic_packer& p) const;									\
	const object_class* inspect(std::ostream& s) const;					\
private:																\
	TYPE ptr;															\
	uint32_t len;														\
};

RAW_CLASS(raw_ref, void*, raw xraw(); const_raw xraw() const; )
RAW_CLASS(const_raw_ref, const void*, const_raw xraw() const; )

#undef RAW_CLASS(NAME, TYPE, EXTRA)


struct object_array : object_class, object_container_mixin {
	explicit object_array() {}
	explicit object_array(uint32_t n) { val.reserve(n); }
	array& xarray();
	const array& xarray() const;
	bool operator== (const object_class* x) const;
	// FIXME operator<, operator>
	void pack(dynamic_packer& p) const;
	const object_class* inspect(std::ostream& s) const;
public:
	void push_back(object o) { val.push_back(o); }
private:
	std::vector<object> val;
};


// FIXME hash, operator==: nil, true, false, array, mapを入れられない
struct object_map : object_class, object_container_mixin {
	explicit object_map() {}
	map& xmap();
	const map& xmap() const;
	bool operator== (const object_class* x) const;
	// FIXME operator<, operator>
	void pack(dynamic_packer& p) const;
	const object_class* inspect(std::ostream& s) const;
public:
	void store(object k, object v) { val[k] = v; }
private:
	std::map<object, object> val;
};


}  // namespace msgpack

#endif /* msgpack/object.hpp */

