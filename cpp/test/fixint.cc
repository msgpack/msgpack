#include <msgpack.hpp>
#include <gtest/gtest.h>

template <typename T>
void check_size(size_t size) {
	T v(0);
	msgpack::sbuffer sbuf;
	msgpack::pack(sbuf, v);
	EXPECT_EQ(size, sbuf.size());
}

TEST(fixint, size)
{
	check_size<msgpack::type::fix_int8>(2);
	check_size<msgpack::type::fix_int16>(3);
	check_size<msgpack::type::fix_int32>(5);
	check_size<msgpack::type::fix_int64>(9);

	check_size<msgpack::type::fix_uint8>(2);
	check_size<msgpack::type::fix_uint16>(3);
	check_size<msgpack::type::fix_uint32>(5);
	check_size<msgpack::type::fix_uint64>(9);
}

