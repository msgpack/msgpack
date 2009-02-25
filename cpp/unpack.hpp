//
// MessagePack for C++ deserializing routine
//
// Copyright (C) 2008-2009 FURUHASHI Sadayuki
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
//
#ifndef MSGPACK_UNPACK_HPP__
#define MSGPACK_UNPACK_HPP__

#include "msgpack/unpack.h"
#include "msgpack/object.hpp"
#include "msgpack/zone.hpp"
#include <memory>
#include <stdexcept>

#ifndef MSGPACK_UNPACKER_DEFAULT_INITIAL_BUFFER_SIZE
#define MSGPACK_UNPACKER_DEFAULT_INITIAL_BUFFER_SIZE (32*1024)
#endif

namespace msgpack {


struct unpack_error : public std::runtime_error {
	unpack_error(const std::string& msg) :
		std::runtime_error(msg) { }
};


class unpacker : public msgpack_unpacker {
public:
	unpacker(size_t initial_buffer_size = MSGPACK_UNPACKER_DEFAULT_INITIAL_BUFFER_SIZE);
	~unpacker();

public:
	/*! 1. reserve buffer. at least `size' bytes of capacity will be ready */
	void reserve_buffer(size_t size);

	/*! 2. read data to the buffer() up to buffer_capacity() bytes */
	char* buffer();
	size_t buffer_capacity() const;

	/*! 3. specify the number of bytes actually copied */
	void buffer_consumed(size_t size);

	/*! 4. repeat execute() until it retunrs false */
	bool execute();

	/*! 5.1. if execute() returns true, take out the parsed object */
	object data();

	/*! 5.2. the object is valid until the zone is deleted */
	// Note that once release_zone() from unpacker, you must delete it
	// otherwise the memrory will leak.
	zone* release_zone();

	/*! 5.3. after release_zone(), re-initialize unpacker */
	void reset();


	// Basic usage of the unpacker is as following:
	//
	// msgpack::unpacker pac;
	//
	// while( /* readable */ ) {
	//
	//     // 1.
	//     pac.reserve(1024);
	//
	//     // 2.
	//     ssize_t bytes =
	//         read(the_source, pac.buffer(), pac.buffer_capacity());
	//
	//     // error handling ...
	//
	//     // 3.
	//     pac.buffer_consumed(bytes);
	//
	//     // 4.
	//     while(pac.execute()) {
	//         // 5.1
	//         object o = pac.data();
	//
	//         // 5.2
	//         std::auto_ptr<msgpack::zone> olife( pac.release_zone() );
	//
	//         // boost::shared_ptr is also usable:
	//         // boost::shared_ptr<msgpack::zone> olife( pac.release_zone() );
	//
	//         // 5.3
	//         pac.reset();
	//
	//         // do some with the object with the old zone.
	//         do_something(o, olife);
	//     }
	// }
	//

public:
	// These functions are usable when non-MessagePack message follows after
	// MessagePack message.

	/*! get address of the buffer that is not parsed */
	char* nonparsed_buffer();
	size_t nonparsed_size() const;

	/*! skip specified size of non-parsed buffer, leaving the buffer */
	// Note that the `size' argument must be smaller than nonparsed_size()
	void skip_nonparsed_buffer(size_t size);

	/*! remove unparsed buffer from unpacker */
	// Note that reset() leaves non-parsed buffer.
	void remove_nonparsed_buffer();

private:
	unpacker(const unpacker&);
};


typedef enum {
	UNPACK_SUCCESS				=  2,
	UNPACK_EXTRA_BYTES			=  1,
	UNPACK_CONTINUE				=  0,
	UNPACK_PARSE_ERROR			= -1,
} unpack_return;

static unpack_return unpack(const char* data, size_t len, size_t* off,
		zone* z, object* result);


// obsolete
static object unpack(const char* data, size_t len, zone& z, size_t* off = NULL);


inline unpacker::unpacker(size_t initial_buffer_size)
{
	if(!msgpack_unpacker_init(this, initial_buffer_size)) {
		throw std::bad_alloc();
	}
}

inline unpacker::~unpacker()
{
	msgpack_unpacker_destroy(this);
}

inline void unpacker::reserve_buffer(size_t size)
{
	if(!msgpack_unpacker_reserve_buffer(this, size)) {
		throw std::bad_alloc();
	}
}

inline char* unpacker::buffer()
{
	return msgpack_unpacker_buffer(this);
}

inline size_t unpacker::buffer_capacity() const
{
	return msgpack_unpacker_buffer_capacity(this);
}

inline void unpacker::buffer_consumed(size_t size)
{
	return msgpack_unpacker_buffer_consumed(this, size);
}


inline bool unpacker::execute()
{
	int ret = msgpack_unpacker_execute(this);
	if(ret < 0) {
		throw unpack_error("parse error");
	} else if(ret == 0) {
		return false;
	} else {
		return true;
	}
}

inline object unpacker::data()
{
	return msgpack_unpacker_data(this);
}

inline zone* unpacker::release_zone()
{
	if(!msgpack_unpacker_flush_zone(this)) {
		throw std::bad_alloc();
	}

	zone* r = new zone();

	msgpack_zone old = *this->z;
	*this->z = *z;
	*z = old;

	return r;
}

inline void unpacker::reset()
{
	msgpack_unpacker_reset(this);
}


inline char* unpacker::nonparsed_buffer()
{
	return buf + off;
}

inline size_t unpacker::nonparsed_size() const
{
	return used - off;
}

inline void unpacker::skip_nonparsed_buffer(size_t size)
{
	off += size;
}

inline void unpacker::remove_nonparsed_buffer()
{
	used = off;
}


inline unpack_return unpack(const char* data, size_t len, size_t* off,
		zone* z, object* result)
{
	return (unpack_return)msgpack_unpack(data, len, off,
			z, reinterpret_cast<msgpack_object*>(result));
}

// obsolete
inline object unpack(const char* data, size_t len, zone& z, size_t* off)
{
	object result;

	switch( msgpack::unpack(data, len, off, &z, &result) ) {
	case UNPACK_SUCCESS:
		return result;

	case UNPACK_EXTRA_BYTES:
		if(off) {
			return result;
		} else {
			throw unpack_error("extra bytes");
		}

	case UNPACK_CONTINUE:
		throw unpack_error("insufficient bytes");

	case UNPACK_PARSE_ERROR:
	default:
		throw unpack_error("parse error");
	}
}


}  // namespace msgpack

#endif /* msgpack/unpack.hpp */

