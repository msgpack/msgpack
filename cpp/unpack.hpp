//
// MessagePack for C++ deserializing routine
//
// Copyright (C) 2008 FURUHASHI Sadayuki
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

#include "msgpack/object.hpp"
#include "msgpack/zone.hpp"
#include <memory>
#include <stdexcept>

#ifndef MSGPACK_UNPACKER_INITIAL_BUFFER_SIZE
#define MSGPACK_UNPACKER_INITIAL_BUFFER_SIZE 8*1024
#endif

namespace msgpack {


static const size_t UNPACKER_INITIAL_BUFFER_SIZE = MSGPACK_UNPACKER_INITIAL_BUFFER_SIZE;


struct unpack_error : public std::runtime_error {
	unpack_error(const std::string& msg) :
		std::runtime_error(msg) { }
};


class unpacker {
public:
	unpacker();
	~unpacker();

public:
	/*! 1. reserve buffer. at least `len' bytes of capacity will be ready */
	void reserve_buffer(size_t len);

	/*! 2. read data to the buffer() up to buffer_capacity() bytes */
	char* buffer();
	size_t buffer_capacity() const;

	/*! 3. specify the number of bytes actually copied */
	void buffer_consumed(size_t len);

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
	//         read(the_source, pac.buffer, pac.buffer_capacity());
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
	// Note that there are no parsed buffer when execute() returned true.

	/*! get address of buffer that is not parsed */
	char* nonparsed_buffer();
	size_t nonparsed_size() const;

	/*! get the number of bytes that is already parsed */
	size_t parsed_size() const;

	/*! remove unparsed buffer from unpacker */
	// Note that reset() leaves non-parsed buffer.
	void remove_nonparsed_buffer();

private:
	char* m_buffer;
	size_t m_used;
	size_t m_free;
	size_t m_off;

	std::auto_ptr<zone> m_zone;

	struct context;
	context* m_ctx;

private:
	void expand_buffer(size_t len);

private:
	unpacker(const unpacker&);

public:
	static object unpack(const char* data, size_t len, zone& z, size_t* off = NULL);
};


inline void unpacker::reserve_buffer(size_t len)
{
	if(m_free >= len) { return; }
	expand_buffer(len);
}

inline char* unpacker::buffer()
	{ return m_buffer + m_used; }

inline size_t unpacker::buffer_capacity() const
	{ return m_free; }

inline void unpacker::buffer_consumed(size_t len)
{
	m_used += len;
	m_free -= len;
}


inline char* unpacker::nonparsed_buffer()
	{ return m_buffer + m_off; }

inline size_t unpacker::nonparsed_size() const
	{ return m_used - m_off; }

inline size_t unpacker::parsed_size() const
	{ return m_off; }

inline void unpacker::remove_nonparsed_buffer()
	{ m_used = m_off; }


inline object unpack(const char* data, size_t len, zone& z, size_t* off = NULL)
{
	return unpacker::unpack(data, len, z, off);
}


}  // namespace msgpack

#endif /* msgpack/unpack.hpp */

