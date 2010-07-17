
#ifndef MSGPACL_PACK_H
#define MSGPACL_PACK_H

#include "ext/standard/php_smart_str.h"

enum msgpack_serialize_type
{
    MSGPACK_SERIALIZE_TYPE_REFERENCE =  1,
    MSGPACK_SERIALIZE_TYPE_OBJECT,
    MSGPACK_SERIALIZE_TYPE_CUSTOM_OBJECT,
};

void msgpack_serialize_zval(
    smart_str *buf, zval *val, HashTable *var_hash TSRMLS_DC);

#endif
