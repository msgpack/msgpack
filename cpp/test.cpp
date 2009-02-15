#include <iostream>
#include <string>
#include <msgpack.hpp>
#include <sstream>
#include <memory>

using namespace msgpack;

class checker {
public:
	template <typename T>
	void check(const char* d, size_t len, T should) {
		try {
			std::cout << "----" << std::endl;

			object o;
			try {
				o = unpack(d, len, m_zone);
			} catch (std::runtime_error& e) {
				std::cout << o << std::endl;
				std::cout << "**" << e.what() << "**" << std::endl;
				return;
			}

			std::cout << o << std::endl;

			try {
				std::stringstream s;
				pack(should, s);
				std::string str(s.str());
				object ro = unpack(str.data(), str.size(), m_zone);
				std::cout << ro << std::endl;
				if(ro != o) { throw std::runtime_error("NOT MATCH"); }
			} catch (std::runtime_error& e) {
				std::cout << "** REUNPACK FAILED **" << std::endl;
				std::cout << e.what() << std::endl;
			} catch (...) {
				std::cout << "** REUNPACK FAILED **" << std::endl;
				std::cout << "unknown error" << std::endl;
			}

		} catch (...) { m_zone.clear(); throw; }
		m_zone.clear();
	}
private:
	zone m_zone;
};

int main(void)
{
	checker c;

	{  // SimpleValue
		const char d[] = {
			0x93, 0xc0, 0xc2, 0xc3,
		};
		c.check(d, sizeof(d),
			type::make_tuple(
				type::nil(), false, true
			)
		);
	}

	{  // Fixnum
		const char d[] = {
			0x92,
				0x93, 0x00, 0x40, 0x7f,
				0x93, 0xe0, 0xf0, 0xff,
		};
		c.check(d, sizeof(d),
			type::make_tuple(
				type::make_tuple(
					0, 64, 127
				),
				type::make_tuple(
					-32, -16, -1
				)
			)
		);
	}

	{  // FixArray
		const char d[] = {
			0x92,
				0x90,
				0x91,
					0x91, 0xc0,
		};
		std::vector<int> empty;
		c.check(d, sizeof(d),
			type::make_tuple(
				empty,
				type::make_tuple(
					type::make_tuple(
						type::nil()
					)
				)
			)
		);
	}

	{  // FixRaw
		const char d[] = {
			0x94,
				0xa0,
				0xa1, 'a',
				0xa2, 'b', 'c',
				0xa3, 'd', 'e', 'f',
		};
		c.check(d, sizeof(d),
			type::make_tuple(
				std::string(""),
				std::string("a"),
				std::string("bc"),
				type::raw_ref("def", 3)
			)
		);
	}


	static const unsigned TASK_ARRAY = 100;
	static const unsigned TASK_REPEAT = 10;
	std::vector<std::string> task;

	// create task
	{
		static char traw[64];
		memset(traw, 'a', sizeof(traw));
	
		task.resize(TASK_ARRAY);
		for(unsigned i=0; i < TASK_ARRAY; ++i) {
			task[i] = std::string(traw, sizeof(traw));
		}
	}


	std::stringstream stream;

	// send message
	{
		for(unsigned i=0; i < TASK_REPEAT; ++i) {
			pack(task, stream);
		}
		std::cout << "send " << stream.str().size() << " bytes" << std::endl;
	}

	ssize_t total_bytes = stream.str().size();
	stream.seekg(0);

	// reserive message
	{
		unsigned num_msg = 0;
		static const size_t RESERVE_SIZE = 32;//*1024;

		unpacker pac;

		while(stream.good() && total_bytes > 0) {

			// 1. reserve buffer
			pac.reserve_buffer(RESERVE_SIZE);

			// 2. read data to buffer() up to buffer_capacity() bytes
			size_t sz = stream.readsome(
					pac.buffer(),
					pac.buffer_capacity());

			total_bytes -= sz;
			std::cout << "read " << sz << " bytes to capacity "
					<< pac.buffer_capacity() << " bytes"
					<< std::endl;

			// 3. specify the number of  bytes actually copied
			pac.buffer_consumed(sz);

			// 4. repeat execute() until it returns false
			while( pac.execute() ) {
				// 5.1. take out the parsed object
				object o = pac.data();

				// 5.2 release the zone
				std::auto_ptr<zone> olife( pac.release_zone() );

				// 5.3 re-initialize the unpacker */
				pac.reset();

				// do some with the o and olife
				std::cout << "message parsed: " << o << std::endl;
				++num_msg;
			}

		}

		std::cout << "stream finished" << std::endl;
		std::cout << num_msg << " messages reached" << std::endl;
	}

	return 0;
}

