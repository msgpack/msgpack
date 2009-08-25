#include "msgpack.h"

#include <vector>
#include <limits>

#include <gtest/gtest.h>

using namespace std;

#define LOOP 10000

TEST(MSGPACKC, simple_buffer_short)
{
  vector<short> v;
  v.push_back(0);
  v.push_back(1);
  v.push_back(-1);
  v.push_back(numeric_limits<short>::min());
  v.push_back(numeric_limits<short>::max());
  for (unsigned int i = 0; i < LOOP; i++)
    v.push_back(rand());

  for (unsigned int i = 0; i < v.size(); i++) {
    short val = v[i];
    msgpack_sbuffer sbuf;
    msgpack_sbuffer_init(&sbuf);

    msgpack_packer pk;
    msgpack_packer_init(&pk, &sbuf, msgpack_sbuffer_write);
    msgpack_pack_short(&pk, val);

    msgpack_zone z;
    msgpack_zone_init(&z, 2048);

    msgpack_object obj;
    msgpack_unpack_return ret =
      msgpack_unpack(sbuf.data, sbuf.size, NULL, &z, &obj);

    EXPECT_EQ(MSGPACK_UNPACK_SUCCESS, ret);
    if (val < 0) {
      EXPECT_EQ(MSGPACK_OBJECT_NEGATIVE_INTEGER, obj.type);
      EXPECT_EQ(val, obj.via.i64);
    } else {
      EXPECT_EQ(MSGPACK_OBJECT_POSITIVE_INTEGER, obj.type);
      EXPECT_EQ(val, obj.via.u64);
    }
  }
}

TEST(MSGPACKC, simple_buffer_int)
{
  vector<int> v;
  v.push_back(0);
  v.push_back(1);
  v.push_back(-1);
  v.push_back(numeric_limits<int>::min());
  v.push_back(numeric_limits<int>::max());
  for (unsigned int i = 0; i < LOOP; i++)
    v.push_back(rand());

  for (unsigned int i = 0; i < v.size(); i++) {
    int val = v[i];
    msgpack_sbuffer sbuf;
    msgpack_sbuffer_init(&sbuf);

    msgpack_packer pk;
    msgpack_packer_init(&pk, &sbuf, msgpack_sbuffer_write);
    msgpack_pack_int(&pk, val);

    msgpack_zone z;
    msgpack_zone_init(&z, 2048);

    msgpack_object obj;
    msgpack_unpack_return ret =
      msgpack_unpack(sbuf.data, sbuf.size, NULL, &z, &obj);

    EXPECT_EQ(MSGPACK_UNPACK_SUCCESS, ret);
    if (val < 0) {
      EXPECT_EQ(MSGPACK_OBJECT_NEGATIVE_INTEGER, obj.type);
      EXPECT_EQ(val, obj.via.i64);
    } else {
      EXPECT_EQ(MSGPACK_OBJECT_POSITIVE_INTEGER, obj.type);
      EXPECT_EQ(val, obj.via.u64);
    }
  }
}

TEST(MSGPACKC, simple_buffer_long)
{
  vector<long> v;
  v.push_back(0);
  v.push_back(1);
  v.push_back(-1);
  v.push_back(numeric_limits<long>::min());
  v.push_back(numeric_limits<long>::max());
  for (unsigned int i = 0; i < LOOP; i++)
    v.push_back(rand());

  for (unsigned int i = 0; i < v.size() ; i++) {
    long val = v[i];

    msgpack_sbuffer sbuf;
    msgpack_sbuffer_init(&sbuf);

    msgpack_packer pk;
    msgpack_packer_init(&pk, &sbuf, msgpack_sbuffer_write);
    msgpack_pack_int(&pk, val);

    msgpack_zone z;
    msgpack_zone_init(&z, 2048);

    msgpack_object obj;
    msgpack_unpack_return ret =
      msgpack_unpack(sbuf.data, sbuf.size, NULL, &z, &obj);

    EXPECT_EQ(MSGPACK_UNPACK_SUCCESS, ret);
    if (val < 0) {
      EXPECT_EQ(MSGPACK_OBJECT_NEGATIVE_INTEGER, obj.type);
      EXPECT_EQ(val, obj.via.i64);
    } else {
      EXPECT_EQ(MSGPACK_OBJECT_POSITIVE_INTEGER, obj.type);
      EXPECT_EQ(val, obj.via.u64);
    }
  }
}
