
#include "php.h"
#include "php_ini.h"
#include "ext/standard/php_smart_str.h"
#include "ext/standard/php_incomplete_class.h"
#include "ext/standard/php_var.h"

#include "php_msgpack.h"
#include "msgpack_pack.h"
#include "msgpack_errors.h"

#include "msgpack/pack_define.h"
#define msgpack_pack_user smart_str*
#define msgpack_pack_inline_func(name) \
    static inline void msgpack_pack ## name
#define msgpack_pack_inline_func_cint(name) \
    static inline void msgpack_pack ## name
#define msgpack_pack_append_buffer(user, buf, len) \
    smart_str_appendl(user, (const void*)buf, len)
#include "msgpack/pack_template.h"

#if ZEND_MODULE_API_NO < 20090626
#   define Z_ISREF_P(pz) PZVAL_IS_REF(pz)
#endif

inline static int msgpack_var_add(
    HashTable *var_hash, zval *var, void *var_old TSRMLS_DC)
{
    ulong var_no;
    char id[32], *p;
    int len;

    if ((Z_TYPE_P(var) == IS_OBJECT) && Z_OBJ_HT_P(var)->get_class_entry)
    {
        p = smart_str_print_long(
            id + sizeof(id) - 1,
            (((size_t)Z_OBJCE_P(var) << 5)
             | ((size_t)Z_OBJCE_P(var) >> (sizeof(long) * 8 - 5)))
            + (long)Z_OBJ_HANDLE_P(var));
        len = id + sizeof(id) - 1 - p;
    }
    else if (Z_TYPE_P(var) == IS_ARRAY)
    {
        p = smart_str_print_long(id + sizeof(id) - 1, (long)var);
        len = id + sizeof(id) - 1 - p;
    }
    else
    {
        return FAILURE;
    }

    if (var_old && zend_hash_find(var_hash, p, len, var_old) == SUCCESS)
    {
        if (!Z_ISREF_P(var))
        {
            var_no = -1;
            zend_hash_next_index_insert(
                var_hash, &var_no, sizeof(var_no), NULL);
        }
        return FAILURE;
    }

    var_no = zend_hash_num_elements(var_hash) + 1;

    zend_hash_add(var_hash, p, len, &var_no, sizeof(var_no), NULL);

    return SUCCESS;
}

inline static void msgpack_serialize_string(
    smart_str *buf, char *str, size_t len)
{
    msgpack_pack_raw(buf, len);
    msgpack_pack_raw_body(buf, str, len);
}

inline static void msgpack_serialize_class(
    smart_str *buf, zval *val, zval *retval_ptr, HashTable *var_hash,
    char *class_name, zend_uint name_len, zend_bool incomplete_class TSRMLS_DC)
{
    int count;
    HashTable *ht = HASH_OF(retval_ptr);

    count = zend_hash_num_elements(ht);
    if (incomplete_class)
    {
        --count;
    }

    if (count > 0)
    {
        char *key;
        zval **data, **name;
        ulong key_index;
        HashPosition pos;
        int n;
        zval nval, *nvalp;

        msgpack_pack_map(buf, count + 1);

        msgpack_pack_nil(buf);
        msgpack_serialize_string(buf, class_name, name_len);

        ZVAL_NULL(&nval);
        nvalp = &nval;

        zend_hash_internal_pointer_reset_ex(ht, &pos);

        for (;; zend_hash_move_forward_ex(ht, &pos))
        {
            n = zend_hash_get_current_key_ex(
                ht, &key, NULL, &key_index, 0, &pos);

            if (n == HASH_KEY_NON_EXISTANT)
            {
                break;
            }
            if (incomplete_class && strcmp(key, MAGIC_MEMBER) == 0)
            {
                continue;
            }

            zend_hash_get_current_data_ex(ht, (void **)&name, &pos);

            if (Z_TYPE_PP(name) != IS_STRING)
            {
                MSGPACK_NOTICE(
                    "[msgpack] (%s) __sleep should return an array only "
                    "containing the names of instance-variables to serialize",
                    __FUNCTION__);
                continue;
            }

            if (zend_hash_find(
                    Z_OBJPROP_P(val), Z_STRVAL_PP(name),
                    Z_STRLEN_PP(name) + 1, (void *)&data) == SUCCESS)
            {
                msgpack_serialize_string(
                    buf, Z_STRVAL_PP(name), Z_STRLEN_PP(name));
                msgpack_serialize_zval(buf, *data, var_hash TSRMLS_CC);
            }
            else
            {
                zend_class_entry *ce;
                ce = zend_get_class_entry(val TSRMLS_CC);
                if (ce)
                {
                    char *prot_name, *priv_name;
                    int prop_name_length;

                    do
                    {
                        zend_mangle_property_name(
                            &priv_name, &prop_name_length, ce->name,
                            ce->name_length, Z_STRVAL_PP(name),
                            Z_STRLEN_PP(name),
                            ce->type & ZEND_INTERNAL_CLASS);
                        if (zend_hash_find(
                                Z_OBJPROP_P(val), priv_name,
                                prop_name_length + 1,
                                (void *)&data) == SUCCESS)
                        {
                            msgpack_serialize_string(
                                buf, priv_name, prop_name_length);

                            pefree(priv_name,
                                   ce->type & ZEND_INTERNAL_CLASS);

                            msgpack_serialize_zval(
                                buf, *data, var_hash TSRMLS_CC);
                            break;
                        }

                        pefree(priv_name,
                               ce->type & ZEND_INTERNAL_CLASS);

                        zend_mangle_property_name(
                            &prot_name, &prop_name_length, "*", 1,
                            Z_STRVAL_PP(name), Z_STRLEN_PP(name),
                            ce->type & ZEND_INTERNAL_CLASS);

                        if (zend_hash_find(
                                Z_OBJPROP_P(val), prot_name,
                                prop_name_length + 1,
                                (void *)&data) == SUCCESS)
                        {
                            msgpack_serialize_string(
                                buf, prot_name, prop_name_length);

                            pefree(prot_name,
                                   ce->type & ZEND_INTERNAL_CLASS);

                            msgpack_serialize_zval(
                                buf, *data, var_hash TSRMLS_CC);
                            break;
                        }

                        pefree(prot_name, ce->type & ZEND_INTERNAL_CLASS);

                        MSGPACK_NOTICE(
                            "[msgpack] (%s) \"%s\" returned as member "
                            "variable from __sleep() but does not exist",
                            __FUNCTION__, Z_STRVAL_PP(name));

                        msgpack_serialize_string(
                            buf, Z_STRVAL_PP(name), Z_STRLEN_PP(name));

                        msgpack_serialize_zval(
                            buf, nvalp, var_hash TSRMLS_CC);
                    }
                    while (0);
                }
                else
                {
                    msgpack_serialize_string(
                        buf, Z_STRVAL_PP(name), Z_STRLEN_PP(name));

                    msgpack_serialize_zval(buf, nvalp, var_hash TSRMLS_CC);
                }
            }
        }
    }
}

inline static void msgpack_serialize_array(
    smart_str *buf, zval *val, HashTable *var_hash, zend_bool object,
    char* class_name, zend_uint name_len, zend_bool incomplete_class TSRMLS_DC)
{
    HashTable *ht;
    size_t n;
    zend_bool hash = 1;

    if (object)
    {
        ht = Z_OBJPROP_P(val);
    }
    else
    {
        ht = HASH_OF(val);
    }

    if (ht)
    {
        n = zend_hash_num_elements(ht);
    }
    else
    {
        n = 0;
    }

    if (n > 0 && incomplete_class)
    {
        --n;
    }

    if (object)
    {
        if (n == 0)
        {
            msgpack_pack_map(buf, n);
        }
        else
        {
            if (MSGPACK_G(php_only))
            {
                if (Z_ISREF_P(val))
                {
                    msgpack_pack_map(buf, n + 2);
                    msgpack_pack_nil(buf);
                    msgpack_pack_long(buf, MSGPACK_SERIALIZE_TYPE_REFERENCE);
                }
                else
                {
                    msgpack_pack_map(buf, n + 1);
                }

                msgpack_pack_nil(buf);

                msgpack_serialize_string(buf, class_name, name_len);
            }
            else
            {
                msgpack_pack_array(buf, n);
                hash = 0;
            }
        }
    }
    else if (n == 0)
    {
        hash = 0;
        msgpack_pack_array(buf, n);
    }
    else if (Z_ISREF_P(val) && MSGPACK_G(php_only))
    {
        msgpack_pack_map(buf, n + 1);
        msgpack_pack_nil(buf);
        msgpack_pack_long(buf, MSGPACK_SERIALIZE_TYPE_REFERENCE);
    }
    else if (ht->nNumOfElements == ht->nNextFreeElement)
    {
        hash = 0;
        msgpack_pack_array(buf, n);
    }
    else
    {
        msgpack_pack_map(buf, n);
    }

    if (n > 0)
    {
        if (object || hash)
        {
            char *key;
            uint key_len;
            int key_type;
            ulong key_index;
            zval **data;
            HashPosition pos;

            zend_hash_internal_pointer_reset_ex(ht, &pos);
            for (;; zend_hash_move_forward_ex(ht, &pos))
            {
                key_type = zend_hash_get_current_key_ex(
                    ht, &key, &key_len, &key_index, 0, &pos);

                if (key_type == HASH_KEY_NON_EXISTANT)
                {
                    break;
                }
                if (incomplete_class && strcmp(key, MAGIC_MEMBER) == 0)
                {
                    continue;
                }

                if (hash)
                {
                    switch (key_type)
                    {
                        case HASH_KEY_IS_LONG:
                            msgpack_pack_long(buf, key_index);
                            break;
                        case HASH_KEY_IS_STRING:
                            msgpack_serialize_string(buf, key, key_len - 1);
                            break;
                        default:
                            msgpack_serialize_string(buf, "", sizeof(""));
                            MSGPACK_WARNING(
                                "[msgpack] (%s) key is not string nor array",
                                __FUNCTION__);
                            break;
                    }
                }

                if (zend_hash_get_current_data_ex(
                        ht, (void *)&data, &pos) != SUCCESS ||
                    !data || data == &val ||
                    (Z_TYPE_PP(data) == IS_ARRAY &&
                     Z_ARRVAL_PP(data)->nApplyCount > 1))
                {
                    msgpack_pack_nil(buf);
                }
                else
                {
                    if (Z_TYPE_PP(data) == IS_ARRAY)
                    {
                        Z_ARRVAL_PP(data)->nApplyCount++;
                    }

                    msgpack_serialize_zval(buf, *data, var_hash TSRMLS_CC);

                    if (Z_TYPE_PP(data) == IS_ARRAY)
                    {
                        Z_ARRVAL_PP(data)->nApplyCount--;
                    }
                }
            }
        }
        else
        {
            zval **data;
            uint i;

            for (i = 0; i < n; i++)
            {
                if (zend_hash_index_find(ht, i, (void *)&data) != SUCCESS ||
                    !data || data == &val ||
                    (Z_TYPE_PP(data) == IS_ARRAY &&
                     Z_ARRVAL_PP(data)->nApplyCount > 1))
                {
                    msgpack_pack_nil(buf);
                }
                else
                {
                    if (Z_TYPE_PP(data) == IS_ARRAY)
                    {
                        Z_ARRVAL_PP(data)->nApplyCount++;
                    }

                    msgpack_serialize_zval(buf, *data, var_hash TSRMLS_CC);

                    if (Z_TYPE_PP(data) == IS_ARRAY)
                    {
                        Z_ARRVAL_PP(data)->nApplyCount--;
                    }
                }
            }
        }
    }
}

inline static void msgpack_serialize_object(
    smart_str *buf, zval *val, HashTable *var_hash,
    char* class_name, zend_uint name_len, zend_bool incomplete_class TSRMLS_DC)
{
    zval *retval_ptr = NULL;
    zval fname;
    int res;
    zend_class_entry *ce = NULL;

    if (Z_OBJ_HT_P(val)->get_class_entry)
    {
        ce = Z_OBJCE_P(val);
    }

#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION > 0)
    if (ce && ce->serialize != NULL)
    {
        unsigned char *serialized_data = NULL;
        zend_uint serialized_length;

        if (ce->serialize(
                val, &serialized_data, &serialized_length,
                (zend_serialize_data *)var_hash TSRMLS_CC) == SUCCESS &&
            !EG(exception))
        {
            /* has custom handler */
            msgpack_pack_map(buf, 2);

            msgpack_pack_nil(buf);
            msgpack_pack_long(buf, MSGPACK_SERIALIZE_TYPE_CUSTOM_OBJECT);

            msgpack_serialize_string(buf, (char *)ce->name, ce->name_length);
            msgpack_pack_raw(buf, serialized_length);
            msgpack_pack_raw_body(buf, serialized_data, serialized_length);
        }
        else
        {
            msgpack_pack_nil(buf);
        }

        if (serialized_data)
        {
            efree(serialized_data);
        }

        return;
    }
#endif

    if (ce && ce != PHP_IC_ENTRY &&
        zend_hash_exists(&ce->function_table, "__sleep", sizeof("__sleep")))
    {
        INIT_PZVAL(&fname);
        ZVAL_STRINGL(&fname, "__sleep", sizeof("__sleep") - 1, 0);
        res = call_user_function_ex(CG(function_table), &val, &fname,
                                    &retval_ptr, 0, 0, 1, NULL TSRMLS_CC);
        if (res == SUCCESS && !EG(exception))
        {
            if (retval_ptr)
            {
                if (HASH_OF(retval_ptr))
                {
                    msgpack_serialize_class(
                        buf, val, retval_ptr, var_hash,
                        class_name, name_len, incomplete_class TSRMLS_CC);
                }
                else
                {
                    MSGPACK_NOTICE(
                        "[msgpack] (%s) __sleep should return an array only "
                        "containing the names of instance-variables "
                        "to serialize", __FUNCTION__);
                    msgpack_pack_nil(buf);
                }
                zval_ptr_dtor(&retval_ptr);
            }
            return;
        }
    }

    if (retval_ptr)
    {
        zval_ptr_dtor(&retval_ptr);
    }

    msgpack_serialize_array(
        buf, val, var_hash, 1,
        class_name, name_len, incomplete_class TSRMLS_CC);
}

void msgpack_serialize_zval(
    smart_str *buf, zval *val, HashTable *var_hash TSRMLS_DC)
{
    ulong *var_already;

    if (MSGPACK_G(php_only) &&
        var_hash &&
        msgpack_var_add(
            var_hash, val, (void *)&var_already TSRMLS_CC) == FAILURE)
    {
        if (Z_ISREF_P(val))
        {
            if (Z_TYPE_P(val) == IS_ARRAY)
            {
                msgpack_pack_map(buf, 2);

                msgpack_pack_nil(buf);
                msgpack_pack_long(buf, MSGPACK_SERIALIZE_TYPE_RECURSIVE);

                msgpack_pack_long(buf, 0);
                msgpack_pack_long(buf, *var_already);

                return;
            }
            else if (Z_TYPE_P(val) == IS_OBJECT)
            {
                msgpack_pack_map(buf, 2);

                msgpack_pack_nil(buf);
                msgpack_pack_long(buf, MSGPACK_SERIALIZE_TYPE_OBJECT_REFERENCE);

                msgpack_pack_long(buf, 0);
                msgpack_pack_long(buf, *var_already);

                return;
            }
        }
        else if (Z_TYPE_P(val) == IS_OBJECT)
        {
            msgpack_pack_map(buf, 2);

            msgpack_pack_nil(buf);
            msgpack_pack_long(buf, MSGPACK_SERIALIZE_TYPE_OBJECT);

            msgpack_pack_long(buf, 0);
            msgpack_pack_long(buf, *var_already);

            return;
        }
    }

    switch (Z_TYPE_P(val))
    {
        case IS_NULL:
            msgpack_pack_nil(buf);
            break;
        case IS_BOOL:
            if (Z_BVAL_P(val))
            {
                msgpack_pack_true(buf);
            }
            else
            {
                msgpack_pack_false(buf);
            }
            break;
        case IS_LONG:
            msgpack_pack_long(buf, Z_LVAL_P(val));
            break;
        case IS_DOUBLE:
            {
                double dbl = Z_DVAL_P(val);
                msgpack_pack_double(buf, dbl);
            }
            break;
        case IS_STRING:
            msgpack_serialize_string(
                buf, Z_STRVAL_P(val), Z_STRLEN_P(val));
            break;
        case IS_ARRAY:
            msgpack_serialize_array(
                buf, val, var_hash, 0, NULL, 0, 0 TSRMLS_CC);
            break;
        case IS_OBJECT:
            {
                PHP_CLASS_ATTRIBUTES;
                PHP_SET_CLASS_ATTRIBUTES(val);

                msgpack_serialize_object(
                    buf, val, var_hash, class_name, name_len,
                    incomplete_class TSRMLS_CC);

                PHP_CLEANUP_CLASS_ATTRIBUTES();
            }
            break;
        default:
            MSGPACK_WARNING(
                "[msgpack] (%s) type is unsupported, encoded as null",
                __FUNCTION__);
            msgpack_pack_nil(buf);
            break;
    }
    return;
}
