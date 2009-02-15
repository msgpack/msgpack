#include <iostream>
#include <string>
#include <msgpack/unpack.hpp>
#include <msgpack/pack.hpp>
#include <sstream>
#include <boost/scoped_ptr.hpp>

class checker {
public:
	void check(const char* d, size_t len, msgpack::object should) {
		using msgpack::object;
		try {
			std::cout << "----" << std::endl;

			object o;
			try {
				o = msgpack::unpack(d, len, m_zone);
			} catch (std::runtime_error& e) {
				std::cout << should << std::endl;
				std::cout << "**" << e.what() << "**" << std::endl;
				return;
			}

			std::cout << o << std::endl;
			if(o != should) {
				std::cout << "** TEST FAILED **" << std::endl;
			}

			try {
				std::string s;
				msgpack::pack(s, o);
				object ro = msgpack::unpack(s.data(), s.size(), m_zone);
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
	msgpack::zone m_zone;
};

int main(void)
{
	checker c;

	{  // SimpleValue
		msgpack::zone z;
		const char d[] = {
			0x93, 0xc0, 0xc2, 0xc3,
		};
		c.check(d, sizeof(d),
			z.narray(
				z.nnil(), z.nfalse(), z.ntrue()
			)
		);
	}

	{  // Fixnum
		msgpack::zone z;
		const char d[] = {
			0x92,
				0x93, 0x00, 0x40, 0x7f,
				0x93, 0xe0, 0xf0, 0xff,
		};
		c.check(d, sizeof(d),
			z.narray(
				z.narray(
					z.nu8(0),
					z.nu8(64),
					z.nu8(127)
				),
				z.narray(
					z.ni8(-32),
					z.ni8(-16),
					z.ni8(-1)
				)
			)
		);
	}

	{  // FixArray
		msgpack::zone z;
		const char d[] = {
			0x92,
				0x90,
				0x91,
					0x91, 0xc0,
		};
		c.check(d, sizeof(d),
			z.narray(
				z.narray(),
				z.narray(
					z.narray(
						z.nnil()
					)
				)
			)
		);
	}

	{  // FixRaw
		msgpack::zone z;
		const char d[] = {
			0x94,
				0xa0,
				0xa1, 'a',
				0xa2, 'b', 'c',
				0xa3, 'd', 'e', 'f',
		};
		c.check(d, sizeof(d),
			z.narray(
				z.nraw_ref("", 0),
				z.nraw_ref("a", 1),
				z.nraw_ref("bc", 2),
				z.nraw_ref("def", 3)
			)
		);
	}

	static const uint16_t TASK_ARRAY = 100;
	static char tarray[3];
	static char traw[64];

	{
		memset(traw, 'a', sizeof(traw));
		traw[0] = 0xda;
		uint16_t n = htons(sizeof(traw)-3);
		traw[1] = ((char*)&n)[0];
		traw[2] = ((char*)&n)[1];

		msgpack::zone z;
		std::cout << msgpack::unpack(traw, sizeof(traw), z) << std::endl;;
	}

	{
		tarray[0] = 0xdc;
		uint16_t n = htons(TASK_ARRAY);
		tarray[1] = ((char*)&n)[0];
		tarray[2] = ((char*)&n)[1];
	}

	{
		// write message
		ssize_t total_bytes = 0;
		std::stringstream stream;
		for(unsigned q=0; q < 10; ++q) {
			stream.write(tarray, sizeof(tarray));
			total_bytes += sizeof(tarray);
			for(uint16_t i=0; i < TASK_ARRAY; ++i) {
				stream.write(traw, sizeof(traw));
				total_bytes += sizeof(traw);
			}
		}

		stream.seekg(0);

		// reserive message
		unsigned num_msg = 0;

		static const size_t RESERVE_SIZE = 32;//*1024;

		msgpack::unpacker upk;
		while(stream.good() && total_bytes > 0) {

			// 1. reserve buffer
			upk.reserve_buffer(RESERVE_SIZE);

			// 2. read data to buffer() up to buffer_capacity() bytes
			size_t sz = stream.readsome(
					(char*)upk.buffer(),
					upk.buffer_capacity());

			total_bytes -= sz;
			std::cout << "read " << sz << " bytes to capacity "
					<< upk.buffer_capacity() << " bytes"
					<< std::endl;

			// 3. specify the number of  bytes actually copied
			upk.buffer_consumed(sz);

			// 4. repeat execute() until it returns false
			while( upk.execute() ) {
				std::cout << "message parsed" << std::endl;

				// 5.1. take out the parsed object
				msgpack::object o = upk.data();

				// 5.2. the parsed object is valid until the zone is deleted
				boost::scoped_ptr<msgpack::zone> pz(upk.release_zone());

				std::cout << o << std::endl;
				++num_msg;

				// 5.3 re-initialize unpacker
				upk.reset();
			}

		}

		std::cout << "stream finished" << std::endl;
		std::cout << num_msg << " messages reached" << std::endl;
	}

	return 0;
}

