#include "msgpack.hpp"

#include <math.h>
#include <string>
#include <vector>
#include <map>
#include <deque>
#include <set>
#include <list>

#include <gtest/gtest.h>

using namespace std;

const unsigned int kLoop = 10000;
const unsigned int kElements = 100;
const double kEPS = 1e-10;

#define GEN_TEST(test_type)                                           \
  do {                                                                \
    vector<test_type> v;                                              \
    v.push_back(0);                                                   \
    v.push_back(1);                                                   \
    v.push_back(2);                                                   \
    v.push_back(numeric_limits<test_type>::min());                    \
    v.push_back(numeric_limits<test_type>::max());                    \
    for (unsigned int i = 0; i < kLoop; i++)                          \
      v.push_back(rand());                                            \
    for (unsigned int i = 0; i < v.size() ; i++) {                    \
      msgpack::sbuffer sbuf;                                          \
      test_type val1 = v[i];                                          \
      msgpack::pack(sbuf, val1);                                      \
      msgpack::zone z;                                                \
      msgpack::object obj;                                            \
      msgpack::unpack_return ret =                                    \
        msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);    \
      EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);                        \
      test_type val2;                                                 \
      obj.convert(&val2);                                             \
      EXPECT_EQ(val1, val2);                                          \
    }                                                                 \
} while(0)

TEST(MSGPACK, simple_buffer_short)
{
  GEN_TEST(short);
}

TEST(MSGPACK, simple_buffer_int)
{
  GEN_TEST(int);
}

TEST(MSGPACK, simple_buffer_long)
{
  GEN_TEST(long);
}

TEST(MSGPACK, simple_buffer_long_long)
{
  GEN_TEST(long long);
}

TEST(MSGPACK, simple_buffer_unsigned_short)
{
  GEN_TEST(unsigned short);
}

TEST(MSGPACK, simple_buffer_unsigned_int)
{
  GEN_TEST(unsigned int);
}

TEST(MSGPACK, simple_buffer_unsigned_long)
{
  GEN_TEST(unsigned long);
}

TEST(MSGPACK, simple_buffer_unsigned_long_long)
{
  GEN_TEST(unsigned long long);
}

TEST(MSGPACK, simple_buffer_uint8)
{
  GEN_TEST(uint8_t);
}

TEST(MSGPACK, simple_buffer_uint16)
{
  GEN_TEST(uint16_t);
}

TEST(MSGPACK, simple_buffer_uint32)
{
  GEN_TEST(uint32_t);
}

TEST(MSGPACK, simple_buffer_uint64)
{
  GEN_TEST(uint64_t);
}

TEST(MSGPACK, simple_buffer_int8)
{
  GEN_TEST(int8_t);
}

TEST(MSGPACK, simple_buffer_int16)
{
  GEN_TEST(int16_t);
}

TEST(MSGPACK, simple_buffer_int32)
{
  GEN_TEST(int32_t);
}

TEST(MSGPACK, simple_buffer_int64)
{
  GEN_TEST(int64_t);
}

TEST(MSGPACK, simple_buffer_float)
{
  vector<float> v;
  v.push_back(0.0);
  v.push_back(-0.0);
  v.push_back(1.0);
  v.push_back(-1.0);
  v.push_back(numeric_limits<float>::min());
  v.push_back(numeric_limits<float>::max());
  v.push_back(nanf("tag"));
  v.push_back(1.0/0.0); // inf
  v.push_back(-(1.0/0.0)); // -inf
  for (unsigned int i = 0; i < kLoop; i++) {
    v.push_back(drand48());
    v.push_back(-drand48());
  }
  for (unsigned int i = 0; i < v.size() ; i++) {
    msgpack::sbuffer sbuf;
    float val1 = v[i];
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    float val2;
    obj.convert(&val2);

    if (isnan(val1))
      EXPECT_TRUE(isnan(val2));
    else if (isinf(val1))
      EXPECT_TRUE(isinf(val2));
    else
      EXPECT_TRUE(fabs(val2 - val1) <= kEPS);
  }
}

TEST(MSGPACK, simple_buffer_double)
{
  vector<double> v;
  v.push_back(0.0);
  v.push_back(-0.0);
  v.push_back(1.0);
  v.push_back(-1.0);
  v.push_back(numeric_limits<double>::min());
  v.push_back(numeric_limits<double>::max());
  v.push_back(nanf("tag"));
  v.push_back(1.0/0.0); // inf
  v.push_back(-(1.0/0.0)); // -inf
  for (unsigned int i = 0; i < kLoop; i++) {
    v.push_back(drand48());
    v.push_back(-drand48());
  }
  for (unsigned int i = 0; i < v.size() ; i++) {
    msgpack::sbuffer sbuf;
    double val1 = v[i];
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    double val2;
    obj.convert(&val2);

    if (isnan(val1))
      EXPECT_TRUE(isnan(val2));
    else if (isinf(val1))
      EXPECT_TRUE(isinf(val2));
    else
      EXPECT_TRUE(fabs(val2 - val1) <= kEPS);
  }
}

TEST(MSGPACK, simple_buffer_true)
{
  msgpack::sbuffer sbuf;
  bool val1 = true;
  msgpack::pack(sbuf, val1);
  msgpack::zone z;
  msgpack::object obj;
  msgpack::unpack_return ret =
    msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
  EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
  bool val2;
  obj.convert(&val2);
  EXPECT_EQ(val1, val2);
}

TEST(MSGPACK, simple_buffer_false)
{
  msgpack::sbuffer sbuf;
  bool val1 = false;
  msgpack::pack(sbuf, val1);
  msgpack::zone z;
  msgpack::object obj;
  msgpack::unpack_return ret =
    msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
  EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
  bool val2;
  obj.convert(&val2);
  EXPECT_EQ(val1, val2);
}

//-----------------------------------------------------------------------------

TEST(MSGPACK_STL, simple_buffer_string)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    string val1;
    for (unsigned int i = 0; i < kElements; i++)
      val1 += 'a' + rand() % 26;
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    string val2;
    obj.convert(&val2);
    EXPECT_EQ(val1.size(), val2.size());
    EXPECT_EQ(val1, val2);
  }
}

TEST(MSGPACK_STL, simple_buffer_vector)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    vector<int> val1;
    for (unsigned int i = 0; i < kElements; i++)
      val1.push_back(rand());
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    vector<int> val2;
    obj.convert(&val2);
    EXPECT_EQ(val1.size(), val2.size());
    EXPECT_TRUE(equal(val1.begin(), val1.end(), val2.begin()));
  }
}

TEST(MSGPACK_STL, simple_buffer_map)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    map<int, int> val1;
    for (unsigned int i = 0; i < kElements; i++)
      val1[rand()] = rand();
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    map<int, int> val2;
    obj.convert(&val2);
    EXPECT_EQ(val1.size(), val2.size());
    EXPECT_TRUE(equal(val1.begin(), val1.end(), val2.begin()));
  }
}

TEST(MSGPACK_STL, simple_buffer_deque)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    deque<int> val1;
    for (unsigned int i = 0; i < kElements; i++)
      val1.push_back(rand());
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    deque<int> val2;
    obj.convert(&val2);
    EXPECT_EQ(val1.size(), val2.size());
    EXPECT_TRUE(equal(val1.begin(), val1.end(), val2.begin()));
  }
}

TEST(MSGPACK_STL, simple_buffer_list)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    list<int> val1;
    for (unsigned int i = 0; i < kElements; i++)
      val1.push_back(rand());
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    list<int> val2;
    obj.convert(&val2);
    EXPECT_EQ(val1.size(), val2.size());
    EXPECT_TRUE(equal(val1.begin(), val1.end(), val2.begin()));
  }
}

TEST(MSGPACK_STL, simple_buffer_set)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    set<int> val1;
    for (unsigned int i = 0; i < kElements; i++)
      val1.insert(rand());
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    set<int> val2;
    obj.convert(&val2);
    EXPECT_EQ(val1.size(), val2.size());
    EXPECT_TRUE(equal(val1.begin(), val1.end(), val2.begin()));
  }
}

TEST(MSGPACK_STL, simple_buffer_pair)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    pair<int, int> val1 = make_pair(rand(), rand());
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    pair<int, int> val2;
    obj.convert(&val2);
    EXPECT_EQ(val1.first, val2.first);
    EXPECT_EQ(val1.second, val2.second);
  }
}

class TestClass
{
public:
  TestClass() : i(0), s("kzk") {}
  int i;
  string s;
  MSGPACK_DEFINE(i, s);
};

TEST(MSGPACK_USER_DEFINED, simple_buffer_class)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    TestClass val1;
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    TestClass val2;
    val2.i = -1;
    val2.s = "";
    obj.convert(&val2);
    EXPECT_EQ(val1.i, val2.i);
    EXPECT_EQ(val1.s, val2.s);
  }
}

class TestClass2
{
public:
  TestClass2() : i(0), s("kzk") {
    for (unsigned int i = 0; i < kElements; i++)
      v.push_back(rand());
  }
  int i;
  string s;
  vector<int> v;
  MSGPACK_DEFINE(i, s, v);
};

TEST(MSGPACK_USER_DEFINED, simple_buffer_class_old_to_new)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    TestClass val1;
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    TestClass2 val2;
    val2.i = -1;
    val2.s = "";
    val2.v = vector<int>();
    obj.convert(&val2);
    EXPECT_EQ(val1.i, val2.i);
    EXPECT_EQ(val1.s, val2.s);
    EXPECT_FALSE(val2.s.empty());
  }
}

TEST(MSGPACK_USER_DEFINED, simple_buffer_class_new_to_old)
{
  for (unsigned int k = 0; k < kLoop; k++) {
    TestClass2 val1;
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    TestClass val2;
    val2.i = -1;
    val2.s = "";
    obj.convert(&val2);
    EXPECT_EQ(val1.i, val2.i);
    EXPECT_EQ(val1.s, val2.s);
    EXPECT_FALSE(val2.s.empty());
  }
}

class TestEnumMemberClass
{
public:
  TestEnumMemberClass()
    : t1(STATE_A), t2(STATE_B), t3(STATE_C) {}

  enum TestEnumType {
    STATE_INVALID = 0,
    STATE_A = 1,
    STATE_B = 2,
    STATE_C = 3
  };
  TestEnumType t1;
  TestEnumType t2;
  TestEnumType t3;

  MSGPACK_DEFINE((int&)t1, (int&)t2, (int&)t3);
};

TEST(MSGPACK_USER_DEFINED, simple_buffer_enum_member)
{
  TestEnumMemberClass val1;
  msgpack::sbuffer sbuf;
  msgpack::pack(sbuf, val1);
  msgpack::zone z;
  msgpack::object obj;
  msgpack::unpack_return ret =
    msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
  EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
  TestEnumMemberClass val2;
  val2.t1 = TestEnumMemberClass::STATE_INVALID;
  val2.t2 = TestEnumMemberClass::STATE_INVALID;
  val2.t3 = TestEnumMemberClass::STATE_INVALID;
  obj.convert(&val2);
  EXPECT_EQ(val1.t1, val2.t1);
  EXPECT_EQ(val1.t2, val2.t2);
  EXPECT_EQ(val1.t3, val2.t3);
}

class TestUnionMemberClass
{
public:
  TestUnionMemberClass() {}
  TestUnionMemberClass(double f) {
    is_double = true;
    value.f = f;
  }
  TestUnionMemberClass(int i) {
    is_double = false;
    value.i = i;
  }

  union {
    double f;
    int i;
  } value;
  bool is_double;

  template <typename Packer>
  void msgpack_pack(Packer& pk) const
  {
    if (is_double)
      pk.pack(msgpack::type::tuple<bool, double>(true, value.f));
    else
      pk.pack(msgpack::type::tuple<bool, int>(false, value.i));
  }

  void msgpack_unpack(msgpack::object o)
  {
    msgpack::type::tuple<bool, msgpack::object> tuple;
    o.convert(&tuple);

    is_double = tuple.get<0>();
    if (is_double)
      tuple.get<1>().convert(&value.f);
    else
      tuple.get<1>().convert(&value.i);
  }
};

TEST(MSGPACK_USER_DEFINED, simple_buffer_union_member)
{
  {
    // double
    TestUnionMemberClass val1(1.0);
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    TestUnionMemberClass val2;
    obj.convert(&val2);
    EXPECT_EQ(val1.is_double, val2.is_double);
    EXPECT_TRUE(fabs(val1.value.f - val2.value.f) < kEPS);
  }
  {
    // int
    TestUnionMemberClass val1(1);
    msgpack::sbuffer sbuf;
    msgpack::pack(sbuf, val1);
    msgpack::zone z;
    msgpack::object obj;
    msgpack::unpack_return ret =
      msgpack::unpack(sbuf.data(), sbuf.size(), NULL, &z, &obj);
    EXPECT_EQ(ret, msgpack::UNPACK_SUCCESS);
    TestUnionMemberClass val2;
    obj.convert(&val2);
    EXPECT_EQ(val1.is_double, val2.is_double);
    EXPECT_EQ(val1.value.i, 1);
    EXPECT_EQ(val1.value.i, val2.value.i);
  }
}
