#include <msgpack.hpp>
#include <string>
#include <iostream>
#include <sstream>

namespace myprotocol {
	using namespace msgpack::type;
	using msgpack::define;

	struct Get : define< tuple<uint32_t, std::string> > {
		Get() { }
		Get(uint32_t f, const std::string& k) :
			define_type(msgpack_type(f, k)) { }
		uint32_t&    flags() { return get<0>(); }
		std::string& key()   { return get<1>(); }
	};

	struct Put : define< tuple<uint32_t, std::string, raw_ref> > {
		Put() { }
		Put(uint32_t f, const std::string& k, const char* valref, size_t vallen) :
			define_type(msgpack_type( f, k, raw_ref(valref,vallen) )) { }
		uint32_t&    flags() { return get<0>(); }
		std::string& key()   { return get<1>(); }
		raw_ref&     value() { return get<2>(); }
	};

	struct MultiGet : define< std::vector<Get> > {
	};
}


int main(void)
{
	// send Get request
	std::stringstream stream;
	{
		myprotocol::Get req;
		req.flags() = 0;
		req.key()   = "key0";
		msgpack::pack(stream, req);
	}

	stream.seekg(0);

	// receive Get request
	{
		std::string buffer(stream.str());

		msgpack::zone mempool;
		msgpack::object o =
			msgpack::unpack(buffer.data(), buffer.size(), mempool);

		myprotocol::Get req;
		msgpack::convert(req, o);
		std::cout << "received: " << o << std::endl;
	}


	stream.str("");


	// send MultiGet request
	{
		myprotocol::MultiGet req;
		req.push_back( myprotocol::Get(1, "key1") );
		req.push_back( myprotocol::Get(2, "key2") );
		req.push_back( myprotocol::Get(3, "key3") );
		msgpack::pack(stream, req);
	}

	stream.seekg(0);

	// receive MultiGet request
	{
		std::string buffer(stream.str());

		msgpack::zone mempool;
		msgpack::object o =
			msgpack::unpack(buffer.data(), buffer.size(), mempool);

		myprotocol::MultiGet req;
		msgpack::convert(req, o);
		std::cout << "received: " << o << std::endl;
	}
}

