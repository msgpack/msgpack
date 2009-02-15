
msgpack_object msgpack_unpack_init(msgpack_unpack_context* x);
msgpack_object msgpack_unpack_unsigned_int_8(msgpack_unpack_context* x, uint8_t d);
msgpack_object msgpack_unpack_unsigned_int_16(msgpack_unpack_context* x, uint16_t d);
msgpack_object msgpack_unpack_unsigned_int_32(msgpack_unpack_context* x, uint32_t d);
msgpack_object msgpack_unpack_unsigned_int_64(msgpack_unpack_context* x, uint64_t d);
msgpack_object msgpack_unpack_signed_int_8(msgpack_unpack_context* x, int8_t d);
msgpack_object msgpack_unpack_signed_int_16(msgpack_unpack_context* x, int16_t d);
msgpack_object msgpack_unpack_signed_int_32(msgpack_unpack_context* x, int32_t d);
msgpack_object msgpack_unpack_signed_int_64(msgpack_unpack_context* x, int64_t d);
msgpack_object msgpack_unpack_float(msgpack_unpack_context* x, float d);
msgpack_object msgpack_unpack_double(msgpack_unpack_context* x, double d);
msgpack_object msgpack_unpack_big_int(msgpack_unpack_context* x, const void* b, unsigned int l);
msgpack_object msgpack_unpack_big_float(msgpack_unpack_context* x, const void* b, unsigned int l);
msgpack_object msgpack_unpack_nil(msgpack_unpack_context* x);
msgpack_object msgpack_unpack_true(msgpack_unpack_context* x);
msgpack_object msgpack_unpack_false(msgpack_unpack_context* x);
msgpack_object msgpack_unpack_array_start(msgpack_unpack_context* x, unsigned int n);
          void msgpack_unpack_array_item(msgpack_unpack_context* x, msgpack_object c, msgpack_object o);
msgpack_object msgpack_unpack_map_start(msgpack_unpack_context* x, unsigned int n);
          void msgpack_unpack_map_item(msgpack_unpack_context* x, msgpack_object c, msgpack_object k, msgpack_object v);
msgpack_object msgpack_unpack_string(msgpack_unpack_context* x, const void* b, size_t l);
msgpack_object msgpack_unpack_raw(msgpack_unpack_context* x, const void* b, const void* p, size_t l);

