#include <msgpack.h>
#include <gtest/gtest.h>
#include <stdio.h>

TEST(streaming, basic)
{
	msgpack_sbuffer* buffer = msgpack_sbuffer_new();

	msgpack_packer* pk = msgpack_packer_new(buffer, msgpack_sbuffer_write);
	EXPECT_EQ(0, msgpack_pack_int(pk, 1));
	EXPECT_EQ(0, msgpack_pack_int(pk, 2));
	EXPECT_EQ(0, msgpack_pack_int(pk, 3));
	msgpack_packer_free(pk);

	const char* input = buffer->data;
	const char* const eof = input + buffer->size;

	msgpack_unpacker pac;
	msgpack_unpacker_init(&pac, MSGPACK_UNPACKER_INIT_BUFFER_SIZE);

	msgpack_unpacked result;
	msgpack_unpacked_init(&result);

	int count = 0;
	while(count < 3) {
		msgpack_unpacker_reserve_buffer(&pac, 32*1024);

		/* read buffer into msgpack_unapcker_buffer(&pac) upto
		 * msgpack_unpacker_buffer_capacity(&pac) bytes. */
		size_t len = 1;
		memcpy(msgpack_unpacker_buffer(&pac), input, len);
		input += len;

		msgpack_unpacker_buffer_consumed(&pac, len);

		while(msgpack_unpacker_next(&pac, &result)) {
			msgpack_object obj = result.data;
			switch(count++) {
			case 0:
				EXPECT_EQ(MSGPACK_OBJECT_POSITIVE_INTEGER, result.data.type);
				EXPECT_EQ(1, result.data.via.u64);
				break;
			case 1:
				EXPECT_EQ(MSGPACK_OBJECT_POSITIVE_INTEGER, result.data.type);
				EXPECT_EQ(2, result.data.via.u64);
				break;
			case 2:
				EXPECT_EQ(MSGPACK_OBJECT_POSITIVE_INTEGER, result.data.type);
				EXPECT_EQ(3, result.data.via.u64);
				return;
			}
		}

		EXPECT_TRUE(input < eof);
	}
}

