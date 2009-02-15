#include <iostream>
#include <string>
#include <msgpack/unpack.hpp>
#include <msgpack/pack.hpp>

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
				z.nraw("", 0),
				z.nraw("a", 1),
				z.nraw("bc", 2),
				z.nraw("def", 3)
			)
		);
	}

	return 0;
}

