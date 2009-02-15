#ifndef MSGPACK_UNPACK_H__
#define MSGPACK_UNPACK_H__

#include <stdint.h>
#include <stddef.h>

namespace MessagePack {

class Unpacker {
	class object {
		template <typename T>
		object(const T& x) : m_obj(new holder<T>(x)) {}
	};

	class type_error      : public std::exception { };
	class cast_error      : public type_error { };
	class overflow_error  : public type_error { };
	class underflow_error : public type_error { };

	struct object {
		virtual ~object() {}
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
		virtual      std::map<object, object>&    xmap() const { throw cast_error(); }
		virtual                   std::string& xstring() const { throw cast_error(); }
		virtual std::pair<const char*, size_t>    xraw() const { throw cast_error(); }
	public:
		template <typename T, typename X>
		inline void check_overflow(X x) {
			if(std::numeric_limits<T>::max() < x) { throw overflow_error(); }
		}
		template <typename T, typename X>
		inline void check_underflow(X x) {
			if(std::numeric_limits<T>::min() > x) { throw overflow_error(); }
		}
	};

private:
	struct object_nil : object {
		bool isnil() const { return true; }
	};

	struct object_true : object {
		bool xbool() const { return true; }
	};

	struct object_false : object {
		bool xbool() const { return false; }
	};

	struct object_u8 : object {
		object_u8(uint8_t val) : m_val(val) {}
		 uint8_t  xu8() const { return m_val; }
		uint16_t xu16() const { return static_cast<uint16_t>(m_val); }
		uint32_t xu32() const { return static_cast<uint32_t>(m_val); }
		uint64_t xu64() const { return static_cast<uint64_t>(m_val); }
		  int8_t  xi8() const { check_overflow<int8_t>(m_val); return m_val; }
		 int16_t xi16() const { return static_cast<int16_t>(m_val); }
		 int32_t xi32() const { return static_cast<int32_t>(m_val); }
		 int64_t xi64() const { return static_cast<int64_t>(m_val); }
	private:
		uint8_t m_val;
	};

	struct object_u16 : object {
		object_u16(uint16_t val) : m_val(val) {}
		 uint8_t  xu8() const { check_overflow<uint8_t>(m_val); return m_val; }
		uint16_t xu16() const { return m_val; }
		uint32_t xu32() const { return static_cast<uint32_t>(m_val); }
		uint64_t xu64() const { return static_cast<uint64_t>(m_val); }
		  int8_t  xi8() const { check_overflow< int8_t>(m_val); return m_val; }
		 int16_t xi16() const { check_overflow<int16_t>(m_val); return m_val; }
		 int32_t xi32() const { return static_cast<int32_t>(m_val); }
		 int64_t xi64() const { return static_cast<int64_t>(m_val); }
	private:
		uint16_t m_val;
	};

	...
};

}  // namespace MessagePack

typedef struct {
	void* (*unpack_unsigned_int_8)(void* data, uint8_t d);
	void* (*unpack_unsigned_int_16)(void* data, uint16_t d);
	void* (*unpack_unsigned_int_32)(void* data, uint32_t d);
	void* (*unpack_unsigned_int_64)(void* data, uint64_t d);
	void* (*unpack_signed_int_8)(void* data, int8_t d);
	void* (*unpack_signed_int_16)(void* data, int16_t d);
	void* (*unpack_signed_int_32)(void* data, int32_t d);
	void* (*unpack_signed_int_64)(void* data, int64_t d);
	void* (*unpack_float)(void* data, float d);
	void* (*unpack_double)(void* data, double d);
	void* (*unpack_big_int)(void* data, const void* b, unsigned int l);
	void* (*unpack_big_float)(void* data, const void* b, unsigned int l);
	void* (*unpack_nil)(void* data);
	void* (*unpack_true)(void* data);
	void* (*unpack_false)(void* data);
	void* (*unpack_array_start)(void* data, unsigned int n);
	 void (*unpack_array_item)(void* data, void* c, void* o);
	void* (*unpack_map_start)(void* data, unsigned int n);
	 void (*unpack_map_item)(void* data, void* c, void* k, void* v);
	void* (*unpack_string)(void* data, const void* b, size_t l);
	void* (*unpack_raw)(void* data, const void* b, size_t l);
	void* data;
} msgpack_unpack_t;

msgpack_unpack_t* msgpack_unpack_new(void);
void msgpack_unpack_free(msgpack_unpack_t* ctx);
int msgpack_unpack_execute(msgpack_unpack_t* ctx, const char* data, size_t len, size_t* off);
void* msgpack_unpack_data(msgpack_unpack_t* ctx);

#endif /* msgpack/unpack.h */


