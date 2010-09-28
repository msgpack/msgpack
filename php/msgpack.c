
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "php.h"
#include "php_ini.h"
#include "ext/standard/info.h"
#include "ext/standard/php_smart_str.h"
#include "ext/standard/php_incomplete_class.h"
#include "ext/standard/php_var.h"
#include "ext/session/php_session.h"

#include "php_msgpack.h"
#include "msgpack_pack.h"
#include "msgpack_unpack.h"
#include "msgpack_class.h"
#include "msgpack/version.h"

static ZEND_FUNCTION(msgpack_serialize);
static ZEND_FUNCTION(msgpack_unserialize);

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_serialize, 0, 0, 1)
    ZEND_ARG_INFO(0, value)
ZEND_END_ARG_INFO()

ZEND_BEGIN_ARG_INFO_EX(arginfo_msgpack_unserialize, 0, 0, 1)
    ZEND_ARG_INFO(0, str)
ZEND_END_ARG_INFO()

PHP_INI_BEGIN()
STD_PHP_INI_BOOLEAN(
    "msgpack.error_display", "1", PHP_INI_ALL, OnUpdateBool,
    error_display, zend_msgpack_globals, msgpack_globals)
STD_PHP_INI_BOOLEAN(
    "msgpack.php_only", "1", PHP_INI_ALL, OnUpdateBool,
    php_only, zend_msgpack_globals, msgpack_globals)
PHP_INI_END()

PS_SERIALIZER_FUNCS(msgpack);

static const zend_function_entry msgpack_functions[] = {
    ZEND_FE(msgpack_serialize, arginfo_msgpack_serialize)
    ZEND_FE(msgpack_unserialize, arginfo_msgpack_unserialize)
    ZEND_FALIAS(msgpack_pack, msgpack_serialize, arginfo_msgpack_serialize)
    ZEND_FALIAS(msgpack_unpack, msgpack_unserialize, arginfo_msgpack_unserialize)
    {NULL, NULL, NULL}
};

static void msgpack_init_globals(zend_msgpack_globals *msgpack_globals)
{
    TSRMLS_FETCH();

    if (PG(display_errors))
    {
        msgpack_globals->error_display = 1;
    }
    else
    {
        msgpack_globals->error_display = 0;
    }

    msgpack_globals->php_only = 1;
}

static ZEND_MINIT_FUNCTION(msgpack)
{
    ZEND_INIT_MODULE_GLOBALS(msgpack, msgpack_init_globals, NULL);

    REGISTER_INI_ENTRIES();

#if HAVE_PHP_SESSION
    php_session_register_serializer("msgpack",
                                    PS_SERIALIZER_ENCODE_NAME(msgpack),
                                    PS_SERIALIZER_DECODE_NAME(msgpack));
#endif

    msgpack_init_class();

    return SUCCESS;
}

static ZEND_MSHUTDOWN_FUNCTION(msgpack)
{
    UNREGISTER_INI_ENTRIES();

    return SUCCESS;
}

static ZEND_MINFO_FUNCTION(msgpack)
{
    php_info_print_table_start();
    php_info_print_table_row(2, "MessagePack Support", "enabled");
#if HAVE_PHP_SESSION
    php_info_print_table_row(2, "Session Support", "enabled" );
#endif
    php_info_print_table_row(2, "extension Version", MSGPACK_EXTENSION_VERSION);
    php_info_print_table_row(2, "header Version", MSGPACK_VERSION);
    php_info_print_table_end();

    DISPLAY_INI_ENTRIES();
}

zend_module_entry msgpack_module_entry = {
#if ZEND_MODULE_API_NO >= 20010901
    STANDARD_MODULE_HEADER,
#endif
    "msgpack",
    msgpack_functions,
    ZEND_MINIT(msgpack),
    ZEND_MSHUTDOWN(msgpack),
    NULL,
    NULL,
    ZEND_MINFO(msgpack),
#if ZEND_MODULE_API_NO >= 20010901
    MSGPACK_VERSION,
#endif
    STANDARD_MODULE_PROPERTIES
};

#ifdef COMPILE_DL_MSGPACK
ZEND_GET_MODULE(msgpack)
#endif

PS_SERIALIZER_ENCODE_FUNC(msgpack)
{
    smart_str buf = {0};
    php_serialize_data_t var_hash;

    PHP_VAR_SERIALIZE_INIT(var_hash);

    msgpack_serialize_zval(&buf, PS(http_session_vars), &var_hash TSRMLS_CC);

    if (newlen)
    {
        *newlen = buf.len;
    }

    smart_str_0(&buf);
    *newstr = buf.c;

    PHP_VAR_SERIALIZE_DESTROY(var_hash);

    return SUCCESS;
}

PS_SERIALIZER_DECODE_FUNC(msgpack)
{
    int ret;
    HashTable *tmp_hash;
    HashPosition tmp_hash_pos;
    char *key_str;
    ulong key_long;
    uint key_len;
    zval *tmp;
    zval **value;
    size_t off = 0;
    msgpack_unpack_t mp;
    php_unserialize_data_t var_hash;

    ALLOC_INIT_ZVAL(tmp);

    template_init(&mp);

    msgpack_unserialize_var_init(&var_hash);

    (&mp)->user.retval = (zval *)tmp;
    (&mp)->user.var_hash = (php_unserialize_data_t *)&var_hash;

    ret = template_execute(&mp, (char *)val, (size_t)vallen, &off);

    msgpack_unserialize_var_destroy(&var_hash);

    tmp_hash = HASH_OF(tmp);

    zend_hash_internal_pointer_reset_ex(tmp_hash, &tmp_hash_pos);
    while (zend_hash_get_current_data_ex(
               tmp_hash, (void *)&value, &tmp_hash_pos) == SUCCESS)
    {
        ret = zend_hash_get_current_key_ex(
            tmp_hash, &key_str, &key_len, &key_long, 0, &tmp_hash_pos);
        switch (ret)
        {
            case HASH_KEY_IS_LONG:
                /* ??? */
                break;
            case HASH_KEY_IS_STRING:
                php_set_session_var(
                    key_str, key_len - 1, *value, NULL TSRMLS_CC);
                php_add_session_var(key_str, key_len - 1 TSRMLS_CC);
                break;
        }
        zend_hash_move_forward_ex(tmp_hash, &tmp_hash_pos);
    }

    zval_ptr_dtor(&tmp);

    return SUCCESS;
}

PHP_MSGPACK_API void php_msgpack_serialize(smart_str *buf, zval *val TSRMLS_DC)
{
    php_serialize_data_t var_hash;

    PHP_VAR_SERIALIZE_INIT(var_hash);

    msgpack_serialize_zval(buf, val, &var_hash TSRMLS_CC);

    PHP_VAR_SERIALIZE_DESTROY(var_hash);
}

PHP_MSGPACK_API void php_msgpack_unserialize(
    zval *return_value, char *str, size_t str_len TSRMLS_DC)
{
    int ret;
    size_t off = 0;
    msgpack_unpack_t mp;
    php_unserialize_data_t var_hash;

    if (str_len <= 0)
    {
        RETURN_NULL();
    }

    template_init(&mp);

    msgpack_unserialize_var_init(&var_hash);

    (&mp)->user.retval = (zval *)return_value;
    (&mp)->user.var_hash = (php_unserialize_data_t *)&var_hash;

    ret = template_execute(&mp, str, (size_t)str_len, &off);

    msgpack_unserialize_var_destroy(&var_hash);

    switch (ret)
    {
        case MSGPACK_UNPACK_PARSE_ERROR:
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (php_msgpack_unserialize) Parse error");
            }
            break;
        case MSGPACK_UNPACK_CONTINUE:
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (php_msgpack_unserialize) "
                           "Insufficient data for unserializing");
            }
            break;
        case MSGPACK_UNPACK_EXTRA_BYTES:
        case MSGPACK_UNPACK_SUCCESS:
            if (off < (size_t)str_len && MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (php_msgpack_unserialize) Extra bytes");
            }
            break;
        default:
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (php_msgpack_unserialize) Unknown result");
            }
            break;
    }
}

static ZEND_FUNCTION(msgpack_serialize)
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

static ZEND_FUNCTION(msgpack_unserialize)
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
