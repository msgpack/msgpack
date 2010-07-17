
#ifndef MSGPACL_UNPACK_H
#define MSGPACL_UNPACK_H

#include "ext/standard/php_var.h"

typedef enum
{
    MSGPACK_UNPACK_SUCCESS     =  2,
    MSGPACK_UNPACK_EXTRA_BYTES =  1,
    MSGPACK_UNPACK_CONTINUE    =  0,
    MSGPACK_UNPACK_PARSE_ERROR = -1,
} msgpack_unpack_return;

typedef struct
{
    unsigned char *data;
    size_t length;
    size_t offset;
} msgpack_unserialize_data;

int msgpack_unserialize_zval(
    zval **return_value, msgpack_unserialize_data *mpsd,
    php_unserialize_data_t *var_hash TSRMLS_DC);

#endif
