
#ifndef MSGPACK_PACK_H
#define MSGPACK_PACK_H

#include "ext/standard/php_var.h"

#if PHP_API_VERSION < 20100412
#define msgpack_serialize_data_t HashTable
#else
typedef HashTable* msgpack_serialize_data_t;
#endif

enum msgpack_serialize_type
{
    MSGPACK_SERIALIZE_TYPE_NONE =  0,
    MSGPACK_SERIALIZE_TYPE_REFERENCE =  1,
    MSGPACK_SERIALIZE_TYPE_RECURSIVE,
    MSGPACK_SERIALIZE_TYPE_CUSTOM_OBJECT,
    MSGPACK_SERIALIZE_TYPE_OBJECT,
    MSGPACK_SERIALIZE_TYPE_OBJECT_REFERENCE,
};

void msgpack_serialize_zval(
    smart_str *buf, zval *val, HashTable *var_hash TSRMLS_DC);

#endif
