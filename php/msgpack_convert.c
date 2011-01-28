
#include "php.h"

#include "php_msgpack.h"
#include "msgpack_convert.h"
#include "msgpack_errors.h"

#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION < 3)
#   define Z_REFCOUNT_P(pz)    ((pz)->refcount)
#   define Z_SET_ISREF_P(pz)   (pz)->is_ref = 1
#   define Z_UNSET_ISREF_P(pz) (pz)->is_ref = 0
#endif

#define MSGPACK_CONVERT_COPY_ZVAL(_pz, _ppz)   \
    ALLOC_INIT_ZVAL(_pz);                      \
    *(_pz) = **(_ppz);                         \
    if (PZVAL_IS_REF(*(_ppz))) {               \
        if (Z_REFCOUNT_P(*(_ppz)) > 0) {       \
            zval_copy_ctor(_pz);               \
        } else {                               \
            FREE_ZVAL(*(_ppz));                \
        }                                      \
        INIT_PZVAL(_pz);                       \
        Z_SET_ISREF_P(_pz);                    \
    } else {                                   \
        zval_copy_ctor(_pz);                   \
        INIT_PZVAL(_pz);                       \
    }

#define MSGPACK_CONVERT_UPDATE_PROPERTY(_ht, _key, _key_len, _val, _var)  \
    if (zend_symtable_update(                                             \
            _ht, _key, _key_len, &_val, sizeof(_val), NULL) == SUCCESS) { \
        zend_hash_add(_var, _key, _key_len, &_val, sizeof(_val), NULL);   \
        return SUCCESS;                                                   \
    }

inline int msgpack_convert_long_to_properties(
    HashTable *ht, HashTable **properties, HashPosition *prop_pos,
    uint key_index, zval *val, HashTable *var)
{
    if (*properties != NULL)
    {
        char *prop_key;
        uint prop_key_len;
        ulong prop_key_index;

        for (;; zend_hash_move_forward_ex(*properties, prop_pos))
        {
            if (zend_hash_get_current_key_ex(
                    *properties, &prop_key, &prop_key_len,
                    &prop_key_index, 0, prop_pos) == HASH_KEY_IS_STRING)
            {
                if (var == NULL ||
                    !zend_hash_exists(var, prop_key, prop_key_len))
                {
                    zend_hash_move_forward_ex(*properties, prop_pos);
                    return zend_symtable_update(
                        ht, prop_key, prop_key_len,
                        &val, sizeof(val), NULL);
                }
            }
            else
            {
                break;
            }
        }

        *properties = NULL;
    }

    return zend_hash_index_update(ht, key_index, &val, sizeof(val), NULL);
}

inline int msgpack_convert_string_to_properties(
    zval *object, char *key, uint key_len, zval *val, HashTable *var)
{
    zval **data = NULL;
    HashTable *ht;
    zend_class_entry *ce;
    char *prot_name, *priv_name;
    int prop_name_len;
    TSRMLS_FETCH();

    ht = HASH_OF(object);
    ce = zend_get_class_entry(object TSRMLS_CC);

    /* private */
    zend_mangle_property_name(
        &priv_name, &prop_name_len, ce->name, ce->name_length, key, key_len, 1);
    if (zend_hash_find(
            ht, priv_name, prop_name_len, (void **)&data) == SUCCESS)
    {
        MSGPACK_CONVERT_UPDATE_PROPERTY(ht, priv_name, prop_name_len, val, var);
    }

    /* protected */
    zend_mangle_property_name(
        &prot_name, &prop_name_len, "*", 1, key, key_len, 1);
    if (zend_hash_find(
            ht, prot_name, prop_name_len, (void **)&data) == SUCCESS)
    {
        MSGPACK_CONVERT_UPDATE_PROPERTY(ht, prot_name, prop_name_len, val, var);
    }

    /* public */
    MSGPACK_CONVERT_UPDATE_PROPERTY(ht, key, key_len, val, var);

    return FAILURE;
}

int msgpack_convert_object(zval *return_value, zval *object, zval **value)
{
    zend_class_entry *ce, **pce;
    HashTable *properties = NULL;
    HashPosition prop_pos;
    TSRMLS_FETCH();

    switch (Z_TYPE_P(object))
    {
        case IS_STRING:
            if (zend_lookup_class(
                    Z_STRVAL_P(object), Z_STRLEN_P(object),
                    &pce TSRMLS_CC) != SUCCESS)
            {
                MSGPACK_ERROR("[msgpack] (%s) Class '%s' not found",
                              __FUNCTION__, Z_STRVAL_P(object));
                return FAILURE;
            }
            ce = *pce;
            break;
        case IS_OBJECT:
            ce = zend_get_class_entry(object TSRMLS_CC);
            break;
        default:
            MSGPACK_ERROR("[msgpack] (%s) Object type is unsupported",
                          __FUNCTION__);
            return FAILURE;
    }

    if (Z_TYPE_PP(value) == IS_OBJECT)
    {
        zend_class_entry *vce;

        vce = zend_get_class_entry(*value TSRMLS_CC);
        if (strcmp(ce->name, vce->name) == 0)
        {
            *return_value = **value;
            zval_copy_ctor(return_value);
            zval_ptr_dtor(value);
            return SUCCESS;
        }
    }

    object_init_ex(return_value, ce);
    properties = Z_OBJ_HT_P(return_value)->get_properties(
        return_value TSRMLS_CC);
    if (HASH_OF(object))
    {
        properties = HASH_OF(object);
    }
    zend_hash_internal_pointer_reset_ex(properties, &prop_pos);

    switch (Z_TYPE_PP(value))
    {
        case IS_ARRAY:
        {
            char *key;
            uint key_len;
            int key_type;
            ulong key_index;
            zval **data;
            HashPosition pos;
            HashTable *ht, *ret;
            HashTable *var = NULL;
            int num;

            ht = HASH_OF(*value);
            ret = HASH_OF(return_value);

            num = zend_hash_num_elements(ht);
            if (num <= 0)
            {
                zval_ptr_dtor(value);
                break;
            }

            ALLOC_HASHTABLE(var);
            zend_hash_init(var, num, NULL, NULL, 0);

            /* string */
            if (ht->nNumOfElements != ht->nNextFreeElement)
            {
                zend_hash_internal_pointer_reset_ex(ht, &pos);
                for (;; zend_hash_move_forward_ex(ht, &pos))
                {
                    key_type = zend_hash_get_current_key_ex(
                        ht, &key, &key_len, &key_index, 0, &pos);

                    if (key_type == HASH_KEY_NON_EXISTANT)
                    {
                        break;
                    }

                    if (zend_hash_get_current_data_ex(
                            ht, (void *)&data, &pos) != SUCCESS)
                    {
                        continue;
                    }

                    if (key_type == HASH_KEY_IS_STRING)
                    {
                        zval *val;
                        MSGPACK_CONVERT_COPY_ZVAL(val, data);
                        if (msgpack_convert_string_to_properties(
                                return_value, key, key_len, val, var) != SUCCESS)
                        {
                            zval_ptr_dtor(&val);
                            MSGPACK_WARNING(
                                "[msgpack] (%s) "
                                "illegal offset type, skip this decoding",
                                __FUNCTION__);
                        }
                    }
                }
            }

            /* index */
            zend_hash_internal_pointer_reset_ex(ht, &pos);
            for (;; zend_hash_move_forward_ex(ht, &pos))
            {
                key_type = zend_hash_get_current_key_ex(
                    ht, &key, &key_len, &key_index, 0, &pos);

                if (key_type == HASH_KEY_NON_EXISTANT)
                {
                    break;
                }

                if (zend_hash_get_current_data_ex(
                        ht, (void *)&data, &pos) != SUCCESS)
                {
                    continue;
                }

                switch (key_type)
                {
                    case HASH_KEY_IS_LONG:
                    {
                        zval *val;
                        MSGPACK_CONVERT_COPY_ZVAL(val, data);
                        if (msgpack_convert_long_to_properties(
                                ret, &properties, &prop_pos,
                                key_index, val, var) != SUCCESS)
                        {
                            zval_ptr_dtor(&val);
                            MSGPACK_WARNING(
                                "[msgpack] (%s) "
                                "illegal offset type, skip this decoding",
                                __FUNCTION__);
                        }
                        break;
                    }
                    case HASH_KEY_IS_STRING:
                        break;
                    default:
                        MSGPACK_WARNING(
                            "[msgpack] (%s) key is not string nor array",
                            __FUNCTION__);
                        break;
                }
            }

            zend_hash_destroy(var);
            FREE_HASHTABLE(var);

            zval_ptr_dtor(value);
            break;
        }
        default:
            if (msgpack_convert_long_to_properties(
                    HASH_OF(return_value), &properties, &prop_pos,
                    0, *value, NULL) != SUCCESS)
            {
                MSGPACK_WARNING(
                    "[msgpack] (%s) illegal offset type, skip this decoding",
                    __FUNCTION__);
            }
            break;
    }

    return SUCCESS;
}
