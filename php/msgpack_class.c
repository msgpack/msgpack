
#include "php.h"

#include "php_msgpack.h"
#include "msgpack_pack.h"
#include "msgpack_unpack.h"
#include "msgpack_class.h"
#include "msgpack_convert.h"
#include "msgpack_errors.h"

typedef struct {
    zend_object object;
    long php_only;
} php_msgpack_base_t;

typedef struct {
    zend_object object;
    smart_str buffer;
    zval *retval;
    long offset;
    msgpack_unpack_t mp;
    msgpack_unserialize_data_t var_hash;
    long php_only;
    zend_bool finished;
    int error;
} php_msgpack_unpacker_t;

#if ZEND_MODULE_API_NO >= 20060613
#   define MSGPACK_METHOD_BASE(classname, name) zim_##classname##_##name
#else
#   define MSGPACK_METHOD_BASE(classname, name) zif_##classname##_##name
#endif

#if ZEND_MODULE_API_NO >= 20090115
#   define PUSH_PARAM(arg) zend_vm_stack_push(arg TSRMLS_CC)
#   define POP_PARAM() (void)zend_vm_stack_pop(TSRMLS_C)
#   define PUSH_EO_PARAM()
#   define POP_EO_PARAM()
#else
#   define PUSH_PARAM(arg) zend_ptr_stack_push(&EG(argument_stack), arg)
#   define POP_PARAM() (void)zend_ptr_stack_pop(&EG(argument_stack))
#   define PUSH_EO_PARAM() zend_ptr_stack_push(&EG(argument_stack), NULL)
#   define POP_EO_PARAM() (void)zend_ptr_stack_pop(&EG(argument_stack))
#endif

#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION > 0)
#define MSGPACK_METHOD_HELPER(classname, name, retval, thisptr, num, param) \
    PUSH_PARAM(param); PUSH_PARAM((void*)num);                              \
    PUSH_EO_PARAM();                                                        \
    MSGPACK_METHOD_BASE(classname, name)(num, retval, NULL, thisptr, 0 TSRMLS_CC); \
    POP_EO_PARAM();                                                         \
    POP_PARAM(); POP_PARAM();
#define MSGPACK_METHOD(classname, name, retval, thisptr) \
    MSGPACK_METHOD_BASE(classname, name)(0, retval, NULL, thisptr, 0 TSRMLS_CC)
#else
#define MSGPACK_METHOD_HELPER(classname, name, retval, thisptr, num, param) \
    PUSH_PARAM(param); PUSH_PARAM((void*)num);                              \
    PUSH_EO_PARAM();                                                        \
    MSGPACK_METHOD_BASE(classname, name)(num, retval, thisptr, 0 TSRMLS_CC); \
    POP_EO_PARAM();                                                         \
    POP_PARAM(); POP_PARAM();
#define MSGPACK_METHOD(classname, name, retval, thisptr) \
    MSGPACK_METHOD_BASE(classname, name)(0, retval, thisptr, 0 TSRMLS_CC)
#endif

#define MSGPACK_METHOD1(classname, name, retval, thisptr, param1) \
    MSGPACK_METHOD_HELPER(classname, name, retval, thisptr, 1, param1);

#define MSGPACK_BASE_OBJECT   \
    php_msgpack_base_t *base; \
    base = (php_msgpack_base_t *)zend_object_store_get_object(getThis() TSRMLS_CC);

#define MSGPACK_UNPACKER_OBJECT       \
    php_msgpack_unpacker_t *unpacker; \
    unpacker = (php_msgpack_unpacker_t *)zend_object_store_get_object(getThis() TSRMLS_CC);

/* MessagePack */
static zend_class_entry *msgpack_ce = NULL;

static ZEND_METHOD(msgpack, __construct);
static ZEND_METHOD(msgpack, setOption);
static ZEND_METHOD(msgpack, pack);
static ZEND_METHOD(msgpack, unpack);
static ZEND_METHOD(msgpack, unpacker);

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_base___construct, 0, 0, 0)
    ZEND_ARG_INFO(0, opt)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_base_setOption, 0, 0, 2)
    ZEND_ARG_INFO(0, option)
    ZEND_ARG_INFO(0, value)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_base_pack, 0, 0, 1)
    ZEND_ARG_INFO(0, value)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_base_unpack, 0, 0, 1)
    ZEND_ARG_INFO(0, str)
    ZEND_ARG_INFO(0, object)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_base_unpacker, 0, 0, 0)
ZEND_END_ARG_INFO()

static const zend_function_entry msgpack_base_methods[] = {
    ZEND_ME(msgpack, __construct,
            arginfo_msgpack_base___construct, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, setOption, arginfo_msgpack_base_setOption, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, pack, arginfo_msgpack_base_pack, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, unpack, arginfo_msgpack_base_unpack, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack, unpacker, arginfo_msgpack_base_unpacker, ZEND_ACC_PUBLIC)
    {NULL, NULL, NULL}
};

/* MessagePackUnpacker */
static zend_class_entry *msgpack_unpacker_ce = NULL;

static ZEND_METHOD(msgpack_unpacker, __construct);
static ZEND_METHOD(msgpack_unpacker, __destruct);
static ZEND_METHOD(msgpack_unpacker, setOption);
static ZEND_METHOD(msgpack_unpacker, feed);
static ZEND_METHOD(msgpack_unpacker, execute);
static ZEND_METHOD(msgpack_unpacker, data);
static ZEND_METHOD(msgpack_unpacker, reset);

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker___construct, 0, 0, 0)
    ZEND_ARG_INFO(0, opt)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker___destruct, 0, 0, 0)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker_setOption, 0, 0, 2)
    ZEND_ARG_INFO(0, option)
    ZEND_ARG_INFO(0, value)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker_feed, 0, 0, 1)
    ZEND_ARG_INFO(0, str)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker_execute, 1, 0, 0)
    ZEND_ARG_INFO(0, str)
    ZEND_ARG_INFO(1, offset)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker_data, 0, 0, 0)
    ZEND_ARG_INFO(0, object)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unpacker_reset, 0, 0, 0)
ZEND_END_ARG_INFO()

static const zend_function_entry msgpack_unpacker_methods[] = {
    ZEND_ME(msgpack_unpacker, __construct,
            arginfo_msgpack_unpacker___construct, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack_unpacker, __destruct,
            arginfo_msgpack_unpacker___destruct, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack_unpacker, setOption,
            arginfo_msgpack_unpacker_setOption, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack_unpacker, feed,
            arginfo_msgpack_unpacker_feed, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack_unpacker, execute,
            arginfo_msgpack_unpacker_execute, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack_unpacker, data,
            arginfo_msgpack_unpacker_data, ZEND_ACC_PUBLIC)
    ZEND_ME(msgpack_unpacker, reset,
            arginfo_msgpack_unpacker_reset, ZEND_ACC_PUBLIC)
    {NULL, NULL, NULL}
};

static void php_msgpack_base_free(php_msgpack_base_t *base TSRMLS_DC)
{
#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION > 0)
    zend_object_std_dtor(&base->object TSRMLS_CC);
#else
    if (base->object.properties)
    {
        zend_hash_destroy(base->object.properties);
        FREE_HASHTABLE(base->object.properties);
    }
#endif
    efree(base);
}

static zend_object_value php_msgpack_base_new(zend_class_entry *ce TSRMLS_DC)
{
    zend_object_value retval;
    php_msgpack_base_t *base;
#if PHP_API_VERSION < 20100412
    zval *tmp;
#endif

    base = emalloc(sizeof(php_msgpack_base_t));

#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION > 0)
    zend_object_std_init(&base->object, ce TSRMLS_CC);
#else
    ALLOC_HASHTABLE(base->object.properties);
    zend_hash_init(base->object.properties, 0, NULL, ZVAL_PTR_DTOR, 0);
    base->object.ce = ce;
#endif

#if PHP_API_VERSION < 20100412
    zend_hash_copy(
        base->object.properties, &ce->default_properties,
        (copy_ctor_func_t)zval_add_ref, (void *)&tmp, sizeof(zval *));
#else
    object_properties_init(&base->object, ce);
#endif

    retval.handle = zend_objects_store_put(
        base, (zend_objects_store_dtor_t)zend_objects_destroy_object,
        (zend_objects_free_object_storage_t)php_msgpack_base_free,
        NULL TSRMLS_CC);
    retval.handlers = zend_get_std_object_handlers();

    return retval;
}

static void php_msgpack_unpacker_free(
    php_msgpack_unpacker_t *unpacker TSRMLS_DC)
{
#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION > 0)
    zend_object_std_dtor(&unpacker->object TSRMLS_CC);
#else
    if (unpacker->object.properties)
    {
        zend_hash_destroy(unpacker->object.properties);
        FREE_HASHTABLE(unpacker->object.properties);
    }
#endif
    efree(unpacker);
}

static zend_object_value php_msgpack_unpacker_new(
    zend_class_entry *ce TSRMLS_DC)
{
    zend_object_value retval;
    php_msgpack_unpacker_t *unpacker;
#if PHP_API_VERSION < 20100412
    zval *tmp;
#endif

    unpacker = emalloc(sizeof(php_msgpack_unpacker_t));

#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION > 0)
    zend_object_std_init(&unpacker->object, ce TSRMLS_CC);
#else
    ALLOC_HASHTABLE(unpacker->object.properties);
    zend_hash_init(unpacker->object.properties, 0, NULL, ZVAL_PTR_DTOR, 0);
    unpacker->object.ce = ce;
#endif

#if PHP_API_VERSION < 20100412
    zend_hash_copy(
        unpacker->object.properties, &ce->default_properties,
        (copy_ctor_func_t)zval_add_ref, (void *)&tmp, sizeof(zval *));
#else
    object_properties_init(&unpacker->object, ce);
#endif

    retval.handle = zend_objects_store_put(
        unpacker, (zend_objects_store_dtor_t)zend_objects_destroy_object,
        (zend_objects_free_object_storage_t)php_msgpack_unpacker_free,
        NULL TSRMLS_CC);
    retval.handlers = zend_get_std_object_handlers();

    return retval;
}

/* MessagePack */
static ZEND_METHOD(msgpack, __construct)
{
    zend_bool php_only = MSGPACK_G(php_only);
    MSGPACK_BASE_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "|b", &php_only) == FAILURE)
    {
        return;
    }

    base->php_only = php_only;
}

static ZEND_METHOD(msgpack, setOption)
{
    long option;
    zval *value;
    MSGPACK_BASE_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "lz", &option, &value) == FAILURE)
    {
        return;
    }

    switch (option)
    {
        case MSGPACK_CLASS_OPT_PHPONLY:
            convert_to_boolean(value);
            base->php_only = Z_BVAL_P(value);
            break;
        default:
            MSGPACK_WARNING("[msgpack] (MessagePack::setOption) "
                            "error setting msgpack option");
            RETURN_FALSE;
            break;
    }

    RETURN_TRUE;
}

static ZEND_METHOD(msgpack, pack)
{
    zval *parameter;
    smart_str buf = {0};
    int php_only = MSGPACK_G(php_only);
    MSGPACK_BASE_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "z", &parameter) == FAILURE)
    {
        return;
    }

    MSGPACK_G(php_only) = base->php_only;

    php_msgpack_serialize(&buf, parameter TSRMLS_CC);

    MSGPACK_G(php_only) = php_only;

    ZVAL_STRINGL(return_value, buf.c, buf.len, 1);

    smart_str_free(&buf);
}

static ZEND_METHOD(msgpack, unpack)
{
    char *str;
    int str_len;
    zval *object = NULL;
    int php_only = MSGPACK_G(php_only);
    MSGPACK_BASE_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "s|z",
            &str, &str_len, &object) == FAILURE)
    {
        return;
    }

    if (!str_len)
    {
        RETURN_NULL();
    }

    MSGPACK_G(php_only) = base->php_only;

    if (object == NULL)
    {
        php_msgpack_unserialize(return_value, str, str_len TSRMLS_CC);
    }
    else
    {
        zval *zv;

        ALLOC_INIT_ZVAL(zv);
        php_msgpack_unserialize(zv, str, str_len TSRMLS_CC);

        if (msgpack_convert_template(return_value, object, &zv) != SUCCESS)
        {
            RETURN_NULL();
        }
    }

    MSGPACK_G(php_only) = php_only;
}

static ZEND_METHOD(msgpack, unpacker)
{
    zval temp, *opt;
    MSGPACK_BASE_OBJECT;

    ALLOC_INIT_ZVAL(opt);
    ZVAL_BOOL(opt, base->php_only);

    object_init_ex(return_value, msgpack_unpacker_ce);

    MSGPACK_METHOD1(msgpack_unpacker, __construct, &temp, return_value, opt);

    zval_ptr_dtor(&opt);
}

/* MessagePackUnpacker */
static ZEND_METHOD(msgpack_unpacker, __construct)
{
    zend_bool php_only = MSGPACK_G(php_only);
    MSGPACK_UNPACKER_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "|b", &php_only) == FAILURE)
    {
        return;
    }

    unpacker->php_only = php_only;

    unpacker->buffer.c = NULL;
    unpacker->buffer.len = 0;
    unpacker->buffer.a = 0;
    unpacker->retval = NULL;
    unpacker->offset = 0;
    unpacker->finished = 0;
    unpacker->error = 0;

    template_init(&unpacker->mp);

    msgpack_unserialize_var_init(&unpacker->var_hash);

    (&unpacker->mp)->user.var_hash =
        (msgpack_unserialize_data_t *)&unpacker->var_hash;
}

static ZEND_METHOD(msgpack_unpacker, __destruct)
{
    MSGPACK_UNPACKER_OBJECT;

    smart_str_free(&unpacker->buffer);

    if (unpacker->retval != NULL)
    {
        zval_ptr_dtor(&unpacker->retval);
    }

    msgpack_unserialize_var_destroy(&unpacker->var_hash, unpacker->error);
}

static ZEND_METHOD(msgpack_unpacker, setOption)
{
    long option;
    zval *value;
    MSGPACK_UNPACKER_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "lz", &option, &value) == FAILURE)
    {
        return;
    }

    switch (option)
    {
        case MSGPACK_CLASS_OPT_PHPONLY:
            convert_to_boolean(value);
            unpacker->php_only = Z_BVAL_P(value);
            break;
        default:
            MSGPACK_WARNING("[msgpack] (MessagePackUnpacker::setOption) "
                            "error setting msgpack option");
            RETURN_FALSE;
            break;
    }

    RETURN_TRUE;
}

static ZEND_METHOD(msgpack_unpacker, feed)
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

static ZEND_METHOD(msgpack_unpacker, execute)
{
    char *str = NULL, *data;
    long str_len = 0;
    zval *offset = NULL;
    int ret;
    size_t len, off;
    int error_display = MSGPACK_G(error_display);
    int php_only = MSGPACK_G(php_only);
    MSGPACK_UNPACKER_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "|sz/",
            &str, &str_len, &offset) == FAILURE)
    {
        return;
    }

    if (str != NULL)
    {
        data = (char *)str;
        len = (size_t)str_len;
        if (offset != NULL)
        {
            off = Z_LVAL_P(offset);
        }
        else
        {
            off = 0;
        }
    }
    else
    {
        data = (char *)unpacker->buffer.c;
        len = unpacker->buffer.len;
        off = unpacker->offset;
    }

    if (unpacker->retval == NULL)
    {
        ALLOC_INIT_ZVAL(unpacker->retval);
    }
    else if (unpacker->finished)
    {
        zval_ptr_dtor(&unpacker->retval);

        msgpack_unserialize_var_destroy(&unpacker->var_hash, unpacker->error);
        unpacker->error = 0;

        ALLOC_INIT_ZVAL(unpacker->retval);

        template_init(&unpacker->mp);

        msgpack_unserialize_var_init(&unpacker->var_hash);

        (&unpacker->mp)->user.var_hash =
            (msgpack_unserialize_data_t *)&unpacker->var_hash;
    }
    (&unpacker->mp)->user.retval = (zval *)unpacker->retval;

    MSGPACK_G(error_display) = 0;
    MSGPACK_G(php_only) = unpacker->php_only;

    ret = template_execute(&unpacker->mp, data, len, &off);

    MSGPACK_G(error_display) = error_display;
    MSGPACK_G(php_only) = php_only;

    if (str != NULL)
    {
        if (offset != NULL)
        {
            ZVAL_LONG(offset, off);
        }
    }
    else
    {
        unpacker->offset = off;
    }

    switch (ret)
    {
        case MSGPACK_UNPACK_EXTRA_BYTES:
        case MSGPACK_UNPACK_SUCCESS:
            unpacker->finished = 1;
            unpacker->error = 0;
            RETURN_TRUE;
        default:
            unpacker->error = 1;
            RETURN_FALSE;
    }
}

static ZEND_METHOD(msgpack_unpacker, data)
{
    zval *object = NULL;
    MSGPACK_UNPACKER_OBJECT;

    if (zend_parse_parameters(
            ZEND_NUM_ARGS() TSRMLS_CC, "|z", &object) == FAILURE)
    {
        return;
    }

    if (unpacker->retval != NULL)
    {
        if (object == NULL)
        {
            ZVAL_ZVAL(return_value, unpacker->retval, 1, 0);
        }
        else
        {
            zval *zv;

            ALLOC_INIT_ZVAL(zv);
            ZVAL_ZVAL(zv, unpacker->retval, 1, 0);

            if (msgpack_convert_object(return_value, object, &zv) != SUCCESS)
            {
                RETURN_NULL();
            }
        }

        MSGPACK_METHOD(msgpack_unpacker, reset, NULL, getThis());

        return;
    }

    RETURN_FALSE;
}

static ZEND_METHOD(msgpack_unpacker, reset)
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
    unpacker->finished = 0;

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

    msgpack_unserialize_var_destroy(&unpacker->var_hash, unpacker->error);
    unpacker->error = 0;


    template_init(&unpacker->mp);

    msgpack_unserialize_var_init(&unpacker->var_hash);

    (&unpacker->mp)->user.var_hash =
        (msgpack_unserialize_data_t *)&unpacker->var_hash;
}

void msgpack_init_class()
{
    zend_class_entry ce;
    TSRMLS_FETCH();

    /* base */
    INIT_CLASS_ENTRY(ce, "MessagePack", msgpack_base_methods);
    msgpack_ce = zend_register_internal_class(&ce TSRMLS_CC);
    msgpack_ce->create_object = php_msgpack_base_new;

#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION > 0)
    zend_declare_class_constant_long(
        msgpack_ce, ZEND_STRS("OPT_PHPONLY") - 1,
        MSGPACK_CLASS_OPT_PHPONLY TSRMLS_CC);
#endif

    /* unpacker */
    INIT_CLASS_ENTRY(ce, "MessagePackUnpacker", msgpack_unpacker_methods);
    msgpack_unpacker_ce = zend_register_internal_class(&ce TSRMLS_CC);
    msgpack_unpacker_ce->create_object = php_msgpack_unpacker_new;
}
