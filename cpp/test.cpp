#include "msgpack.hpp"

#include <gtest/gtest.h>

TEST(MSGPACKC, simple_buffer)
{
	msgpack::sbuffer sbuf;

	int v = 0;

	msgpack::pack(sbuf, v);

	msgpack::zone z;
	msgpack::object obj;

	msgpack::unpack_return ret =
		msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);

	EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);

	obj.convert(&v);

	EXPECT_EQ(0, v);
}
