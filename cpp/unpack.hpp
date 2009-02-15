#ifndef MSGPACK_UNPACK_HPP__
#define MSGPACK_UNPACK_HPP__

#include "msgpack/object.hpp"
#include "msgpack/zone.hpp"
#include <stdexcept>

#ifndef MSGPACK_UNPACKER_INITIAL_BUFFER_SIZE
#define MSGPACK_UNPACKER_INITIAL_BUFFER_SIZE 8*1024
#endif

namespace msgpack {


struct unpack_error : public std::runtime_error {
	unpack_error(const std::string& msg) :
		std::runtime_error(msg) { }
};


class unpacker {
public:
	unpacker();
	~unpacker();

public:
	void reserve_buffer(size_t len);
	void* buffer();
	size_t buffer_capacity() const;
	void buffer_consumed(size_t len);
	bool execute();
	zone* release_zone();  // never throw
	object data();
	void reset();

private:
	zone* m_zone;

	struct context;
	context* m_ctx;

	void* m_buffer;
	size_t m_used;
	size_t m_free;
	size_t m_off;
	void expand_buffer(size_t len);

private:
	unpacker(const unpacker&);

public:
	static object unpack(const void* data, size_t len, zone& z);
};


inline void unpacker::reserve_buffer(size_t len)
{
	if(m_free >= len) { return; }
	expand_buffer(len);
}

inline void* unpacker::buffer()
	{ return (void*)(((char*)m_buffer)+m_used); }

inline size_t unpacker::buffer_capacity() const
	{ return m_free; }

inline void unpacker::buffer_consumed(size_t len)
{
	m_used += len;
	m_free -= len;
}


inline object unpack(const void* data, size_t len, zone& z)
{
	return unpacker::unpack(data, len, z);
}


}  // namespace msgpack

#endif /* msgpack/unpack.hpp */

