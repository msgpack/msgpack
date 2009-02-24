#include <msgpack.hpp>
#include <string>
#include <iostream>
#include <sstream>

int main(void)
{
	msgpack::type::tuple<int, bool, std::string> src(1, true, "example");

	// serialize the object into the buffer.
	// any classes that implements write(const char*,size_t) can be a buffer.
	std::stringstream buffer;
	msgpack::pack(buffer, src);

	// send the buffer ...
	buffer.seekg(0);

	// deserialize the buffer into msgpack::object instance.
	std::string str(buffer.str());

	// deserialized object is valid during the msgpack::zone instance alive.
	msgpack::zone mempool;

	msgpack::object deserialized;
	msgpack::unpack(str.data(), str.size(), NULL, &mempool, &deserialized);

	// msgpack::object supports ostream.
	std::cout << deserialized << std::endl;

	// convert msgpack::object instance into the original type.
	// if the type is mismatched, it throws msgpack::type_error exception.
	msgpack::type::tuple<int, bool, std::string> dst;
	deserialized.convert(&dst);

	return 0;
}

