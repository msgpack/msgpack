#include <msgpack.hpp>
#include <string>
#include <iostream>
#include <sstream>

int main(void)
{
	// this is target object
	msgpack::type::tuple<int, bool, std::string> src(1, true, "example");

	// any classes that implements write(const char*,size_t) can be a buffer
	std::stringstream buffer;
	msgpack::pack(buffer, src);

	// send the buffer ...
	buffer.seekg(0);

	// deserialize the buffer into msgpack::object type
	msgpack::zone mempool;
	std::string str(buffer.str());
	msgpack::object deserialized =
		msgpack::unpack(str.data(), str.size(), mempool);

	// msgpack::object supports ostream
	std::cout << deserialized << std::endl;

	// convert msgpack::object type into the original type
	msgpack::type::tuple<int, bool, std::string> dst;
	msgpack::convert(dst, deserialized);
}

