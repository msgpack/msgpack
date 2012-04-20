
#ifndef MSGPACK_UNPACK_H
#define MSGPACK_UNPACK_H

#include "ext/standard/php_var.h"

#define MSGPACK_EMBED_STACK_SIZE 1024

#include "msgpack/unpack_define.h"

typedef enum
{
    MSGPACK_UNPACK_SUCCESS     =  2,
    MSGPACK_UNPACK_EXTRA_BYTES =  1,
    MSGPACK_UNPACK_CONTINUE    =  0,
    MSGPACK_UNPACK_PARSE_ERROR = -1,
} msgpack_unpack_return;

typedef struct php_unserialize_data msgpack_unserialize_data_t;

typedef struct {
    zval *retval;
    long deps;
    msgpack_unserialize_data_t *var_hash;
    long stack[MSGPACK_EMBED_STACK_SIZE];
    int type;
} msgpack_unserialize_data;

void msgpack_unserialize_var_init(msgpack_unserialize_data_t *var_hashx);
void msgpack_unserialize_var_destroy(
    msgpack_unserialize_data_t *var_hashx, zend_bool err);

void msgpack_unserialize_init(msgpack_unserialize_data *unpack);

int msgpack_unserialize_uint8(
    msgpack_unserialize_data *unpack, uint8_t data, zval **obj);
int msgpack_unserialize_uint16(
    msgpack_unserialize_data *unpack, uint16_t data, zval **obj);
int msgpack_unserialize_uint32(
    msgpack_unserialize_data *unpack, uint32_t data, zval **obj);
int msgpack_unserialize_uint64(
    msgpack_unserialize_data *unpack, uint64_t data, zval **obj);
int msgpack_unserialize_int8(
    msgpack_unserialize_data *unpack, int8_t data, zval **obj);
int msgpack_unserialize_int16(
    msgpack_unserialize_data *unpack, int16_t data, zval **obj);
int msgpack_unserialize_int32(
    msgpack_unserialize_data *unpack, int32_t data, zval **obj);
int msgpack_unserialize_int64(
    msgpack_unserialize_data *unpack, int64_t data, zval **obj);
int msgpack_unserialize_float(
    msgpack_unserialize_data *unpack, float data, zval **obj);
int msgpack_unserialize_double(
    msgpack_unserialize_data *unpack, double data, zval **obj);
int msgpack_unserialize_nil(msgpack_unserialize_data *unpack, zval **obj);
int msgpack_unserialize_true(msgpack_unserialize_data *unpack, zval **obj);
int msgpack_unserialize_false(msgpack_unserialize_data *unpack, zval **obj);
int msgpack_unserialize_raw(
    msgpack_unserialize_data *unpack, const char* base, const char* data,
    unsigned int len, zval **obj);
int msgpack_unserialize_array(
    msgpack_unserialize_data *unpack, unsigned int count, zval **obj);
int msgpack_unserialize_array_item(
    msgpack_unserialize_data *unpack, zval **container, zval *obj);
int msgpack_unserialize_map(
    msgpack_unserialize_data *unpack, unsigned int count, zval **obj);
int msgpack_unserialize_map_item(
    msgpack_unserialize_data *unpack, zval **container, zval *key, zval *val);

/* template functions */
#define msgpack_unpack_struct(name)    struct template ## name
#define msgpack_unpack_func(ret, name) ret template ## name
#define msgpack_unpack_callback(name)  template_callback ## name

#define msgpack_unpack_object zval*
#define unpack_user           msgpack_unserialize_data
#define msgpack_unpack_user   msgpack_unserialize_data

struct template_context;
typedef struct template_context msgpack_unpack_t;

static void template_init(msgpack_unpack_t* unpack);
static msgpack_unpack_object template_data(msgpack_unpack_t* unpack);
static int template_execute(
    msgpack_unpack_t* unpack, const char* data, size_t len, size_t* off);

static inline msgpack_unpack_object template_callback_root(unpack_user* user)
{
    msgpack_unserialize_init(user);
    return NULL;
}

#define template_callback_uint8(user, data, obj) \
    msgpack_unserialize_uint8(user, data, obj)
#define template_callback_uint16(user, data, obj) \
    msgpack_unserialize_uint16(user, data, obj)
#define template_callback_uint32(user, data, obj) \
    msgpack_unserialize_uint32(user, data, obj)
#define template_callback_uint64(user, data, obj) \
    msgpack_unserialize_uint64(user, data, obj)
#define template_callback_int8(user, data, obj) \
    msgpack_unserialize_int8(user, data, obj)
#define template_callback_int16(user, data, obj) \
    msgpack_unserialize_int16(user, data, obj)
#define template_callback_int32(user, data, obj) \
    msgpack_unserialize_int32(user, data, obj)
#define template_callback_int64(user, data, obj) \
    msgpack_unserialize_int64(user, data, obj)
#define template_callback_float(user, data, obj) \
    msgpack_unserialize_float(user, data, obj)
#define template_callback_double(user, data, obj) \
    msgpack_unserialize_double(user, data, obj)
#define template_callback_nil(user, obj) \
    msgpack_unserialize_nil(user, obj)
#define template_callback_true(user, obj) \
    msgpack_unserialize_true(user, obj)
#define template_callback_false(user, obj) \
    msgpack_unserialize_false(user, obj)
#define template_callback_raw(user, base, data, len, obj) \
    msgpack_unserialize_raw(user, base, data, len, obj)
#define template_callback_array(user, count, obj) \
    msgpack_unserialize_array(user, count, obj)
#define template_callback_array_item(user, container, obj) \
    msgpack_unserialize_array_item(user, container, obj)
#define template_callback_map(user, count, obj) \
    msgpack_unserialize_map(user, count, obj)
#define template_callback_map_item(user, container, key, val) \
    msgpack_unserialize_map_item(user, container, key, val)

#include "msgpack/unpack_template.h"

#endif
