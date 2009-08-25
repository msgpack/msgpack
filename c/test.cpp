#include "msgpack.h"

#include <vector>
#include <limits>

#include <gtest/gtest.h>

using namespace std;

const unsigned int kLoop = 10000;

#define GEN_TEST_SIGNED(test_type, func_type)                   \
  do {                                                          \
    vector<test_type> v;                                        \
    v.push_back(0);                                             \
    v.push_back(1);                                             \
    v.push_back(-1);                                            \
    v.push_back(numeric_limits<test_type>::min());              \
    v.push_back(numeric_limits<test_type>::max());              \
    for (unsigned int i = 0; i < kLoop; i++)                    \
      v.push_back(rand());                                      \
    for (unsigned int i = 0; i < v.size() ; i++) {              \
      test_type val = v[i];                                     \
      msgpack_sbuffer sbuf;                                     \
      msgpack_sbuffer_init(&sbuf);                              \
      msgpack_packer pk;                                        \
      msgpack_packer_init(&pk, &sbuf, msgpack_sbuffer_write);   \
      msgpack_pack_##func_type(&pk, val);                       \
      msgpack_zone z;                                           \
      msgpack_zone_init(&z, 2048);                              \
      msgpack_object obj;                                       \
      msgpack_unpack_return ret =                               \
        msgpack_unpack(sbuf.data, sbuf.size, NULL, &z, &obj);   \
      EXPECT_EQ(MSGPACK_UNPACK_SUCCESS, ret);                   \
      if (val < 0) {                                            \
        EXPECT_EQ(MSGPACK_OBJECT_NEGATIVE_INTEGER, obj.type);   \
        EXPECT_EQ(val, obj.via.i64);                            \
      } else {                                                  \
        EXPECT_EQ(MSGPACK_OBJECT_POSITIVE_INTEGER, obj.type);   \
        EXPECT_EQ(val, obj.via.u64);                            \
      }                                                         \
      EXPECT_EQ(val, obj.via.u64);                              \
    }                                                           \
  } while(0)

#define GEN_TEST_UNSIGNED(test_type, func_type)                 \
  do {                                                          \
    vector<test_type> v;                                        \
    v.push_back(0);                                             \
    v.push_back(1);                                             \
    v.push_back(-1);                                            \
    v.push_back(numeric_limits<test_type>::min());              \
    v.push_back(numeric_limits<test_type>::max());              \
    for (unsigned int i = 0; i < kLoop; i++)                    \
      v.push_back(rand());                                      \
    for (unsigned int i = 0; i < v.size() ; i++) {              \
      test_type val = v[i];                                     \
      msgpack_sbuffer sbuf;                                     \
      msgpack_sbuffer_init(&sbuf);                              \
      msgpack_packer pk;                                        \
      msgpack_packer_init(&pk, &sbuf, msgpack_sbuffer_write);   \
      msgpack_pack_##func_type(&pk, val);                       \
      msgpack_zone z;                                           \
      msgpack_zone_init(&z, 2048);                              \
      msgpack_object obj;                                       \
      msgpack_unpack_return ret =                               \
        msgpack_unpack(sbuf.data, sbuf.size, NULL, &z, &obj);   \
      EXPECT_EQ(MSGPACK_UNPACK_SUCCESS, ret);                   \
      EXPECT_EQ(MSGPACK_OBJECT_POSITIVE_INTEGER, obj.type);     \
      EXPECT_EQ(val, obj.via.u64);                              \
    }                                                           \
  } while(0)

TEST(MSGPACKC, simple_buffer_short)
{
  GEN_TEST_SIGNED(short, short);
}

TEST(MSGPACKC, simple_buffer_int)
{
  GEN_TEST_SIGNED(int, int);
}

TEST(MSGPACKC, simple_buffer_long)
{
  GEN_TEST_SIGNED(long, long);
}

TEST(MSGPACKC, simple_buffer_long_long)
{
  GEN_TEST_SIGNED(long long, long_long);
}

TEST(MSGPACKC, simple_buffer_unsigned_short)
{
  GEN_TEST_UNSIGNED(unsigned short, unsigned_short);
}

TEST(MSGPACKC, simple_buffer_unsigned_int)
{
  GEN_TEST_UNSIGNED(unsigned int, unsigned_int);
}

TEST(MSGPACKC, simple_buffer_unsigned_long)
{
  GEN_TEST_UNSIGNED(unsigned long, unsigned_long);
}

TEST(MSGPACKC, simple_buffer_unsigned_long_long)
{
  GEN_TEST_UNSIGNED(unsigned long long, unsigned_long_long);
}

TEST(MSGPACKC, simple_buffer_uint8)
{
  GEN_TEST_UNSIGNED(uint8_t, uint8);
}

TEST(MSGPACKC, simple_buffer_uint16)
{
  GEN_TEST_UNSIGNED(uint16_t, uint16);
}

TEST(MSGPACKC, simple_buffer_uint32)
{
  GEN_TEST_UNSIGNED(uint32_t, uint32);
}

TEST(MSGPACKC, simple_buffer_uint64)
{
  GEN_TEST_UNSIGNED(uint64_t, uint64);
}

TEST(MSGPACKC, simple_buffer_int8)
{
  GEN_TEST_SIGNED(int8_t, int8);
}

TEST(MSGPACKC, simple_buffer_int16)
{
  GEN_TEST_SIGNED(int16_t, int16);
}

TEST(MSGPACKC, simple_buffer_int32)
{
  GEN_TEST_SIGNED(int32_t, int32);
}

TEST(MSGPACKC, simple_buffer_int64)
{
  GEN_TEST_SIGNED(int64_t, int64);
}
