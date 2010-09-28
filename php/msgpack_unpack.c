
#include "php.h"
#include "php_ini.h"
#include "ext/standard/php_incomplete_class.h"

#include "php_msgpack.h"
#include "msgpack_pack.h"
#include "msgpack_unpack.h"

#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION < 3)
#   define Z_ADDREF_PP(ppz)      ZVAL_ADDREF(*(ppz))
#   define Z_SET_ISREF_PP(ppz)   (*(ppz))->is_ref = 1
#   define Z_UNSET_ISREF_PP(ppz) (*(ppz))->is_ref = 0
#endif

#define VAR_ENTRIES_MAX 1024

typedef struct
{
    zval *data[VAR_ENTRIES_MAX];
    long used_slots;
    long value_slots;
    long access_slots[VAR_ENTRIES_MAX];
    bool alloc_slots[VAR_ENTRIES_MAX];
    void *next;
} var_entries;

#define MSGPACK_UNSERIALIZE_ALLOC(_unpack)                     \
    if (_unpack->deps <= 0) {                                  \
        *obj = _unpack->retval;                                \
        msgpack_var_push(_unpack->var_hash, obj, true, false); \
    } else {                                                   \
        ALLOC_INIT_ZVAL(*obj);                                 \
        msgpack_var_push(_unpack->var_hash, obj, false, true); \
    }

#define MSGPACK_UNSERIALIZE_ALLOC_VALUE(_unpack)               \
    if (_unpack->deps <= 0) {                                  \
        *obj = _unpack->retval;                                \
        msgpack_var_push(_unpack->var_hash, obj, true, false); \
    } else {                                                   \
        ALLOC_INIT_ZVAL(*obj);                                 \
        msgpack_var_push(_unpack->var_hash, obj, true, true);  \
    }

#define MSGPACK_UNSERIALIZE_PUSH_ITEM(_unpack, _count, _val)         \
    msgpack_var_alloc(_unpack->var_hash, _count);                    \
    if (Z_TYPE_P(_val) != IS_ARRAY && Z_TYPE_P(_val) != IS_OBJECT) { \
        msgpack_var_push(_unpack->var_hash, &_val, true, false);     \
    }

#define MSGPACK_UNSERIALIZE_FINISH_ITEM(_unpack) \
    long deps = _unpack->deps - 1;               \
    _unpack->stack[deps]--;                      \
    if (_unpack->stack[deps] == 0) {             \
        _unpack->deps--;                         \
    }

#define MSGPACK_UNSERIALIZE_FINISH_MAP_ITEM(_unpack, _key, _val) \
    zval_ptr_dtor(&_key);                                        \
    zval_ptr_dtor(&_val);                                        \
    msgpack_var_alloc(_unpack->var_hash, 2);                     \
    MSGPACK_UNSERIALIZE_FINISH_ITEM(_unpack);


inline static void msgpack_var_push(
    php_unserialize_data_t *var_hashx, zval **rval, bool value, bool alloc)
{
    var_entries *var_hash, *prev = NULL;

    if (!var_hashx)
    {
        return;
    }

    var_hash = var_hashx->first;

    while (var_hash && var_hash->used_slots == VAR_ENTRIES_MAX)
    {
        prev = var_hash;
        var_hash = var_hash->next;
    }

    if (!var_hash)
    {
        var_hash = emalloc(sizeof(var_entries));
        var_hash->used_slots = 0;
        var_hash->value_slots = 0;
        var_hash->next = 0;

        if (!var_hashx->first)
        {
            var_hashx->first = var_hash;
        }
        else
        {
            prev->next = var_hash;
        }
    }

    var_hash->alloc_slots[var_hash->used_slots] = alloc;

    if (value)
    {
        var_hash->access_slots[var_hash->value_slots++] = var_hash->used_slots;
    }

    var_hash->data[var_hash->used_slots++] = *rval;
}

inline static void msgpack_var_alloc(
    php_unserialize_data_t *var_hashx, long count)
{
    long i;
    var_entries *var_hash = var_hashx->first;

    while (var_hash && var_hash->used_slots == VAR_ENTRIES_MAX)
    {
        var_hash = var_hash->next;
    }

    if (!var_hash || count <= 0)
    {
        return;
    }

    for (i = var_hash->used_slots - 1; i >= 0; i--)
    {
        if (var_hash->alloc_slots[i])
        {
            var_hash->alloc_slots[i] = false;
            if (--count <= 0)
            {
                break;
            }
        }
    }
}

inline static int msgpack_var_access(
    php_unserialize_data_t *var_hashx, long id, zval ***store)
{
    var_entries *var_hash = var_hashx->first;

    while (id >= VAR_ENTRIES_MAX &&
           var_hash && var_hash->used_slots == VAR_ENTRIES_MAX)
    {
        var_hash = var_hash->next;
        id -= VAR_ENTRIES_MAX;
    }

    if (!var_hash)
    {
        return !SUCCESS;
    }

    if (id < 0 || id >= var_hash->value_slots)
    {
        return !SUCCESS;
    }

    id = var_hash->access_slots[id];

    if (id < 0 || id >= var_hash->used_slots)
    {
        return !SUCCESS;
    }

    *store = &var_hash->data[id];

    return SUCCESS;
}

inline static zend_class_entry* msgpack_unserialize_class(
    zval **container, char *class_name, size_t name_len)
{
    zend_class_entry *ce, **pce;
    bool incomplete_class = false;
    zval *user_func, *retval_ptr, **args[1], *arg_func_name;
    TSRMLS_FETCH();

    do
    {
        /* Try to find class directly */
        if (zend_lookup_class(class_name, name_len, &pce TSRMLS_CC) == SUCCESS)
        {
            ce = *pce;
            break;
        }

        /* Check for unserialize callback */
        if ((PG(unserialize_callback_func) == NULL) ||
            (PG(unserialize_callback_func)[0] == '\0'))
        {
            incomplete_class = 1;
            ce = PHP_IC_ENTRY;
            break;
        }

        /* Call unserialize callback */
        ALLOC_INIT_ZVAL(user_func);
        ZVAL_STRING(user_func, PG(unserialize_callback_func), 1);
        args[0] = &arg_func_name;
        ALLOC_INIT_ZVAL(arg_func_name);
        ZVAL_STRING(arg_func_name, class_name, 1);
        if (call_user_function_ex(
                CG(function_table), NULL, user_func, &retval_ptr,
                1, args, 0, NULL TSRMLS_CC) != SUCCESS)
        {
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (msgpack_unserialize_class) "
                           "defined (%s) but not found", class_name);
            }

            incomplete_class = 1;
            ce = PHP_IC_ENTRY;
            zval_ptr_dtor(&user_func);
            zval_ptr_dtor(&arg_func_name);
            break;
        }
        if (retval_ptr)
        {
            zval_ptr_dtor(&retval_ptr);
        }

        /* The callback function may have defined the class */
        if (zend_lookup_class(class_name, name_len, &pce TSRMLS_CC) == SUCCESS)
        {
            ce = *pce;
        }
        else
        {
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (msgpack_unserialize_class) "
                           "Function %s() hasn't defined the class "
                           "it was called for", class_name);
            }

            incomplete_class = true;
            ce = PHP_IC_ENTRY;
        }

        zval_ptr_dtor(&user_func);
        zval_ptr_dtor(&arg_func_name);
    }
    while(0);

    if (EG(exception))
    {
        if (MSGPACK_G(error_display))
        {
            zend_error(E_WARNING,
                       "[msgpack] (msgpack_unserialize_class) "
                       "Exception error");
        }

        return NULL;
    }

    object_init_ex(*container, ce);

    /* store incomplete class name */
    if (incomplete_class)
    {
        php_store_class_name(*container, class_name, name_len);
    }

    return ce;
}

void msgpack_unserialize_var_init(php_unserialize_data_t *var_hashx)
{
    var_hashx->first = 0;
    var_hashx->first_dtor = 0;
}

void msgpack_unserialize_var_destroy(php_unserialize_data_t *var_hashx)
{
    void *next;
    long i;
    var_entries *var_hash = var_hashx->first;

    while (var_hash)
    {
        for (i = 0; i < var_hash->used_slots; i++)
        {
            if (var_hash->alloc_slots[i] && var_hash->data[i])
            {
                zval_ptr_dtor(&var_hash->data[i]);
            }
        }

        next = var_hash->next;
        efree(var_hash);
        var_hash = next;
    }

    /*
    var_hash = var_hashx->first_dtor;

    while (var_hash)
    {
        for (i = 0; i < var_hash->used_slots; i++)
        {
            zval_ptr_dtor(&var_hash->data[i]);
        }
        next = var_hash->next;
        efree(var_hash);
        var_hash = next;
    }
    */
}

void msgpack_unserialize_init(msgpack_unserialize_data *unpack)
{
    unpack->deps = 0;
    unpack->type = MSGPACK_SERIALIZE_TYPE_NONE;
}

int msgpack_unserialize_uint8(
    msgpack_unserialize_data *unpack, uint8_t data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_LONG(*obj, data);

    return 0;
}

int msgpack_unserialize_uint16(
    msgpack_unserialize_data *unpack, uint16_t data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_LONG(*obj, data);

    return 0;
}

int msgpack_unserialize_uint32(
    msgpack_unserialize_data *unpack, uint32_t data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_LONG(*obj, data);

    return 0;
}

int msgpack_unserialize_uint64(
    msgpack_unserialize_data *unpack, uint64_t data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_LONG(*obj, data);

    return 0;
}

int msgpack_unserialize_int8(
    msgpack_unserialize_data *unpack, int8_t data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_LONG(*obj, data);

    return 0;
}

int msgpack_unserialize_int16(
    msgpack_unserialize_data *unpack, int16_t data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_LONG(*obj, data);

    return 0;
}

int msgpack_unserialize_int32(
    msgpack_unserialize_data *unpack, int32_t data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_LONG(*obj, data);

    return 0;
}

int msgpack_unserialize_int64(
    msgpack_unserialize_data *unpack, int64_t data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_LONG(*obj, data);

    return 0;
}

int msgpack_unserialize_float(
    msgpack_unserialize_data *unpack, float data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_DOUBLE(*obj, data);

    return 0;
}

int msgpack_unserialize_double(
    msgpack_unserialize_data *unpack, double data, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_DOUBLE(*obj, data);

    return 0;
}

int msgpack_unserialize_nil(msgpack_unserialize_data *unpack, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_NULL(*obj);

    return 0;
}

int msgpack_unserialize_true(msgpack_unserialize_data *unpack, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_BOOL(*obj, 1);

    return 0;
}

int msgpack_unserialize_false(msgpack_unserialize_data *unpack, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    ZVAL_BOOL(*obj, 0);

    return 0;
}

int msgpack_unserialize_raw(
    msgpack_unserialize_data *unpack, const char* base,
    const char* data, unsigned int len, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC(unpack);

    if (len == 0)
    {
        ZVAL_STRINGL(*obj, "", 0, 1);
    }
    else
    {
        ZVAL_STRINGL(*obj, data, len, 1);
    }

    return 0;
}

int msgpack_unserialize_array(
    msgpack_unserialize_data *unpack, unsigned int count, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC_VALUE(unpack);

    array_init(*obj);

    unpack->stack[unpack->deps++] = count;

    return 0;
}

int msgpack_unserialize_array_item(
    msgpack_unserialize_data *unpack, zval **container, zval *obj)
{
    MSGPACK_UNSERIALIZE_PUSH_ITEM(unpack, 1, obj);

    add_next_index_zval(*container, obj);

    MSGPACK_UNSERIALIZE_FINISH_ITEM(unpack);

    return 0;
}

int msgpack_unserialize_map(
    msgpack_unserialize_data *unpack, unsigned int count, zval **obj)
{
    MSGPACK_UNSERIALIZE_ALLOC_VALUE(unpack);

    unpack->stack[unpack->deps++] = count;

    unpack->type = MSGPACK_SERIALIZE_TYPE_NONE;

    return 0;
}

int msgpack_unserialize_map_item(
    msgpack_unserialize_data *unpack, zval **container, zval *key, zval *val)
{
    TSRMLS_FETCH();

    if (MSGPACK_G(php_only))
    {
        if (Z_TYPE_P(key) == IS_NULL)
        {
            unpack->type = MSGPACK_SERIALIZE_TYPE_NONE;

            if (Z_TYPE_P(val) == IS_LONG)
            {
                switch (Z_LVAL_P(val))
                {
                    case MSGPACK_SERIALIZE_TYPE_REFERENCE:
                        Z_SET_ISREF_PP(container);
                        break;
                    case MSGPACK_SERIALIZE_TYPE_RECURSIVE:
                        unpack->type = MSGPACK_SERIALIZE_TYPE_RECURSIVE;
                        break;
                    case MSGPACK_SERIALIZE_TYPE_CUSTOM_OBJECT:
                        unpack->type = MSGPACK_SERIALIZE_TYPE_CUSTOM_OBJECT;
                        break;
                    default:
                        break;
                }
            }
            else if (Z_TYPE_P(val) == IS_STRING)
            {
                zend_class_entry *ce = msgpack_unserialize_class(
                    container, Z_STRVAL_P(val), Z_STRLEN_P(val));

                if (ce == NULL)
                {
                    MSGPACK_UNSERIALIZE_FINISH_MAP_ITEM(unpack, key, val);

                    return 0;
                }
            }

            MSGPACK_UNSERIALIZE_FINISH_MAP_ITEM(unpack, key, val);

            return 0;
        }
        else if (unpack->type == MSGPACK_SERIALIZE_TYPE_CUSTOM_OBJECT)
        {
            unpack->type = MSGPACK_SERIALIZE_TYPE_NONE;

            zend_class_entry *ce = msgpack_unserialize_class(
                container, Z_STRVAL_P(key), Z_STRLEN_P(key));

            if (ce == NULL)
            {
                MSGPACK_UNSERIALIZE_FINISH_MAP_ITEM(unpack, key, val);

                return 0;
            }

            /* implementing Serializable */
            if (ce->unserialize == NULL)
            {
                if (MSGPACK_G(error_display))
                {
                    zend_error(E_WARNING,
                               "[msgpack] (msgpack_unserialize_map_item) "
                               "Class %s has no unserializer", ce->name);
                }

                MSGPACK_UNSERIALIZE_FINISH_MAP_ITEM(unpack, key, val);

                return 0;
            }

            ce->unserialize(
                container, ce,
                (const unsigned char *)Z_STRVAL_P(val), Z_STRLEN_P(val) + 1,
                NULL TSRMLS_CC);

            MSGPACK_UNSERIALIZE_FINISH_MAP_ITEM(unpack, key, val);

            return 0;
        }
        else if (unpack->type == MSGPACK_SERIALIZE_TYPE_RECURSIVE)
        {
            zval **rval;

            unpack->type = MSGPACK_SERIALIZE_TYPE_NONE;

            if (msgpack_var_access(
                    unpack->var_hash, Z_LVAL_P(val) - 1, &rval) != SUCCESS)
            {
                if (MSGPACK_G(error_display))
                {
                    zend_error(E_WARNING,
                               "[msgpack] (msgpack_unserialize_map_item) "
                               "Invalid references value: %ld",
                               Z_LVAL_P(val) - 1);
                }

                MSGPACK_UNSERIALIZE_FINISH_MAP_ITEM(unpack, key, val);

                return 0;
            }

            if (container != NULL)
            {
                zval_ptr_dtor(container);
            }

            *container = *rval;

            Z_ADDREF_PP(container);

            MSGPACK_UNSERIALIZE_FINISH_MAP_ITEM(unpack, key, val);

            return 0;
        }
    }

    MSGPACK_UNSERIALIZE_PUSH_ITEM(unpack, 2, val);

    if (Z_TYPE_PP(container) != IS_ARRAY && Z_TYPE_PP(container) != IS_OBJECT)
    {
        array_init(*container);
    }

    switch (Z_TYPE_P(key))
    {
        case IS_LONG:
            if (zend_hash_index_update(
                    HASH_OF(*container), Z_LVAL_P(key), &val,
                    sizeof(val), NULL) == FAILURE)
            {
                zval_ptr_dtor(&val);
                if (MSGPACK_G(error_display))
                {
                    zend_error(E_WARNING,
                               "[msgpack] (msgpack_unserialize_map_item) "
                               "illegal offset type, skip this decoding");
                }
            }
            break;
        case IS_STRING:
            if (zend_symtable_update(
                    HASH_OF(*container), Z_STRVAL_P(key), Z_STRLEN_P(key) + 1,
                    &val, sizeof(val), NULL) == FAILURE)
            {
                zval_ptr_dtor(&val);
                if (MSGPACK_G(error_display))
                {
                    zend_error(E_WARNING,
                               "[msgpack] (msgpack_unserialize_map_item) "
                               "illegal offset type, skip this decoding");
                }
            }
            break;
        default:
            zval_ptr_dtor(&val);
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (msgpack_unserialize_map_item) "
                           "illegal offset type, skip this decoding");
            }
            break;
    }

    zval_ptr_dtor(&key);

    long deps = unpack->deps - 1;
    unpack->stack[deps]--;
    if (unpack->stack[deps] == 0)
    {
        unpack->deps--;

        /* wakeup */
        if (MSGPACK_G(php_only) &&
            Z_TYPE_PP(container) == IS_OBJECT &&
            Z_OBJCE_PP(container) != PHP_IC_ENTRY &&
            zend_hash_exists(
                &Z_OBJCE_PP(container)->function_table,
                "__wakeup", sizeof("__wakeup")))
        {
            zval f, *h = NULL;

            INIT_PZVAL(&f);
            ZVAL_STRINGL(&f, "__wakeup", sizeof("__wakeup") - 1, 0);
            call_user_function_ex(
                CG(function_table), container, &f, &h, 0, 0, 1, NULL TSRMLS_CC);
            if (h)
            {
                zval_ptr_dtor(&h);
            }
        }
    }

    return 0;
}
