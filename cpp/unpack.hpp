#ifndef MSGPACK_UNPACK_HPP__
#define MSGPACK_UNPACK_HPP__

#include "msgpack/object.hpp"
#include "msgpack/zone.hpp"
#include <stdexcept>

namespace msgpack {


struct unpack_error : public std::runtime_error {
	unpack_error(const std::string& msg) :
		std::runtime_error(msg) { }
};


class unpacker {
public:
	unpacker(zone& z);
	~unpacker();
public:
	size_t execute(const void* data, size_t len, size_t off);
	bool is_finished() { return m_finished; }
	object data();
	void reset();
private:
	struct context;
	context* m_ctx;
	zone& m_zone;
	bool m_finished;
private:
	unpacker();
	unpacker(const unpacker&);
public:
	static object unpack(const void* data, size_t len, zone& z);
};


inline object unpack(const void* data, size_t len, zone& z)
{
	return unpacker::unpack(data, len, z);
}


}  // namespace msgpack

#endif /* msgpack/unpack.hpp */

