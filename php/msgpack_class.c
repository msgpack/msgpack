
#include "php.h"

#include "php_msgpack.h"
#include "msgpack_pack.h"
#include "msgpack_unpack.h"
#include "msgpack_class.h"

typedef struct {
    zend_object object;
    smart_str buffer;
    zval *retval;
    long offset;
} php_msgpack_unpacker_t;

#if ZEND_MODULE_API_NO >= 20060613
#define MAGPACK_METHOD_BASE(classname, name) zim_##classname##_##name
#else
#define MSGPACK_METHOD_BASE(classname, name) zif_##classname##_##name
#endif

#define MSGPACK_METHOD(classname, name, retval, thisptr) \
    MAGPACK_METHOD_BASE(classname, name)(0, retval, NULL, thisptr, 0 TSRMLS_CC)

#define MSGPACK_UNPACKER_OBJECT       \
    php_msgpack_unpacker_t *unpacker; \
    unpacker =(php_msgpack_unpacker_t *)zend_object_store_get_object(getThis() TSRMLS_CC);

/* MessagePack */
static zend_class_entry *msgpack_ce = NULL;

static ZEND_METHOD(msgpack, pack);
static ZEND_METHOD(msgpack, unpack);
static ZEND_METHOD(msgpack, unpacker);

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_base_pack, 0, 0, 1)
    ZEND_ARG_INFO(0, value)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_base_unpack, 0, 0, 1)
    ZEND_ARG_INFO(0, str)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_base_unpacker, 0, 0, 0)
ZEND_END_ARG_INFO()

static const zend_function_entry msgpack_base_methods[] = {
    ZEND_ME(msgpack, pack, arginfo_msgpack_base_pack, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, unpack, arginfo_msgpack_base_unpack, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, unpacker, arginfo_msgpack_base_unpacker, ZEND_ACC_PUBLIC)
    {NULL, NULL, NULL}
};

/* MessagePackUnpacker */
static zend_class_entry *msgpack_unpacker_ce = NULL;

static ZEND_METHOD(msgpack, __construct);
static ZEND_METHOD(msgpack, __destruct);
static ZEND_METHOD(msgpack, feed);
static ZEND_METHOD(msgpack, execute);
static ZEND_METHOD(msgpack, data);
static ZEND_METHOD(msgpack, reset);

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker___construct, 0, 0, 0)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker___destruct, 0, 0, 0)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker_feed, 0, 0, 1)
    ZEND_ARG_INFO(0, str)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker_execute, 1, 0, 0)
    ZEND_ARG_INFO(0, str)
    ZEND_ARG_INFO(1, offset)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker_data, 0, 0, 0)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker_reset, 0, 0, 0)
ZEND_END_ARG_INFO()

static const zend_function_entry msgpack_unpacker_methods[] = {
    ZEND_ME(msgpack, __construct,
            arginfo_msgpack_unpacker___construct, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, __destruct,
            arginfo_msgpack_unpacker___destruct, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, feed, arginfo_msgpack_unpacker_feed, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, execute, arginfo_msgpack_unpacker_execute, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, data, arginfo_msgpack_unpacker_data, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, reset, arginfo_msgpack_unpacker_reset, ZEND_ACC_PUBLIC)
    {NULL, NULL, NULL}
};

static void php_msgpack_unpacker_free(
    php_msgpack_unpacker_t *unpacker TSRMLS_DC)
{
    zend_object_std_dtor(&unpacker->object TSRMLS_CC);
    efree(unpacker);
}

static zend_object_value php_msgpack_unpacker_new(
    zend_class_entry *ce TSRMLS_DC)
{
    zend_object_value retval;
    zval *tmp;
    php_msgpack_unpacker_t *unpacker;

    unpacker = emalloc(sizeof(php_msgpack_unpacker_t));

    zend_object_std_init(&unpacker->object, ce TSRMLS_CC);

    zend_hash_copy(
        unpacker->object.properties, &ce->default_properties,
        (copy_ctor_func_t)zval_add_ref, (void *)&tmp, sizeof(zval *));

    retval.handle = zend_objects_store_put(
        unpacker, (zend_objects_store_dtor_t)zend_objects_destroy_object,
        (zend_objects_free_object_storage_t)php_msgpack_unpacker_free,
        NULL TSRMLS_CC);
    retval.handlers = zend_get_std_object_handlers();

    return retval;
}

/* MessagePack */
static ZEND_METHOD(msgpack, pack)
{
    zval *parameter;
    smart_str buf = {0};

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "z", &parameter) == FAILURE)
    {
        return;
    }

    php_msgpack_serialize(&buf, parameter TSRMLS_CC);

    ZVAL_STRINGL(return_value, buf.c, buf.len, 1);

    smart_str_free(&buf);
}

static ZEND_METHOD(msgpack, unpack)
{
    char *str;
    int str_len;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "s", &str, &str_len) == FAILURE)
    {
        return;
    }

    if (!str_len)
    {
        RETURN_NULL();
    }

    php_msgpack_unserialize(return_value, str, str_len TSRMLS_CC);
}

static ZEND_METHOD(msgpack, unpacker)
{
    zval temp;

    object_init_ex(return_value, msgpack_unpacker_ce);

    MSGPACK_METHOD(msgpack, __construct, &temp, return_value);
}

/* MessagePackUnpacker */
static ZEND_METHOD(msgpack, __construct)
{
    MSGPACK_UNPACKER_OBJECT;

    unpacker->buffer.c = NULL;
    unpacker->buffer.len = 0;
    unpacker->buffer.a = 0;
    unpacker->retval = NULL;
    unpacker->offset = 0;
}

static ZEND_METHOD(msgpack, __destruct)
{
    MSGPACK_UNPACKER_OBJECT;

    smart_str_free(&unpacker->buffer);

    if (unpacker->retval != NULL)
    {
        zval_ptr_dtor(&unpacker->retval);
    }
}

static ZEND_METHOD(msgpack, feed)
{
    char *str;
    int str_len;
    MSGPACK_UNPACKER_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "s", &str, &str_len) == FAILURE)
    {
        return;
    }

    if (!str_len)
    {
        RETURN_FALSE;
    }

    smart_str_appendl(&unpacker->buffer, str, str_len);

    RETURN_TRUE;
}

static ZEND_METHOD(msgpack, execute)
{
    char *str = NULL;
    long str_len = 0;
    zval *offset;
    int ret;
    php_unserialize_data_t var_hash;
    msgpack_unserialize_data mpsd;
    MSGPACK_UNPACKER_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "|sz/",
            &str, &str_len, &offset) == FAILURE)
    {
        return;
    }

    if (str != NULL)
    {
        mpsd.data = (unsigned char *)str;
        mpsd.length = str_len;
        mpsd.offset = Z_LVAL_P(offset);
    }
    else
    {
        mpsd.data = (unsigned char *)unpacker->buffer.c;
        mpsd.length = unpacker->buffer.len;
        mpsd.offset = unpacker->offset;
    }

    if (mpsd.length <= 0 || mpsd.length == mpsd.offset)
    {
        RETURN_FALSE;
    }

    PHP_VAR_UNSERIALIZE_INIT(var_hash);

    if (unpacker->retval == NULL)
    {
        ALLOC_INIT_ZVAL(unpacker->retval);
    }

    MSGPACK_G(error_display) = 0;

    ret = msgpack_unserialize_zval(
        &unpacker->retval, &mpsd, &var_hash TSRMLS_CC);

    MSGPACK_G(error_display) = 1;

    PHP_VAR_UNSERIALIZE_DESTROY(var_hash);

    if (str != NULL)
    {
        ZVAL_LONG(offset, mpsd.offset);
    }
    else
    {
        unpacker->offset = mpsd.offset;
    }

    switch (ret)
    {
        case MSGPACK_UNPACK_EXTRA_BYTES:
        case MSGPACK_UNPACK_SUCCESS:
            RETURN_TRUE;
        default:
            RETURN_FALSE;
    }
}

static ZEND_METHOD(msgpack, data)
{
    MSGPACK_UNPACKER_OBJECT;

    RETURN_ZVAL(unpacker->retval, 1, 1);
}

static ZEND_METHOD(msgpack, reset)
{
    smart_str buffer = {0};
    MSGPACK_UNPACKER_OBJECT;

    if (unpacker->buffer.len > unpacker->offset)
    {
        smart_str_appendl(&buffer, unpacker->buffer.c + unpacker->offset,
                          unpacker->buffer.len - unpacker->offset);
    }

    smart_str_free(&unpacker->buffer);

    unpacker->buffer.c = NULL;
    unpacker->buffer.len = 0;
    unpacker->buffer.a = 0;
    unpacker->offset = 0;

    if (buffer.len > 0)
    {
        smart_str_appendl(&unpacker->buffer, buffer.c, buffer.len);
    }

    smart_str_free(&buffer);

    if (unpacker->retval != NULL)
    {
        zval_ptr_dtor(&unpacker->retval);
        unpacker->retval = NULL;
    }
}

void msgpack_init_class(TSRMLS_DC)
{
    zend_class_entry ce;

    INIT_CLASS_ENTRY(ce, "MessagePack", msgpack_base_methods);
    msgpack_ce = zend_register_internal_class(&ce TSRMLS_CC);

    INIT_CLASS_ENTRY(ce, "MessagePackUnpacker", msgpack_unpacker_methods);
    msgpack_unpacker_ce = zend_register_internal_class(&ce TSRMLS_CC);
    msgpack_unpacker_ce->create_object = php_msgpack_unpacker_new;
}
