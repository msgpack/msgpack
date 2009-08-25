#include "msgpack.h"

#include <gtest/gtest.h>

TEST(MSGPACKC, simple_buffer)
{
	msgpack_sbuffer sbuf;
	msgpack_sbuffer_init(&sbuf);

	msgpack_packer pk;
	msgpack_packer_init(&pk, &sbuf, msgpack_sbuffer_write);

	msgpack_pack_int(pk, 1);

	msgpack_zone z;
	msgpack_zone_init(&z, 2048);

	msgpack_object obj;

	msgpack_unpack_return ret =
		msgpack_unpack(sbuf.data, sbuf.size, NULL, &z, &obj);

	EXPECT_EQ(ret, MSGPACK_UNPACK_SUCCESS);

	EXPECT_EQ(MSGPACK_OBJECT_POSITIVE_INTEGER, obj.type);
	EXPECT_EQ(1, obj.via.u64);
}

