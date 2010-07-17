
#include "php.h"
#include "php_ini.h"
#include "ext/standard/php_incomplete_class.h"
#include "ext/standard/php_var.h"

#include "php_msgpack.h"
#include "msgpack_pack.h"
#include "msgpack_unpack.h"

#include "msgpack/unpack_define.h"

#define VAR_ENTRIES_MAX 1024

#if (PHP_MAJOR_VERSION == 5 && PHP_MINOR_VERSION < 3)
#   define Z_ADDREF_PP(ppz)      ZVAL_ADDREF(*(ppz))
#   define Z_SET_ISREF_PP(ppz)   (*(ppz))->is_ref = 1
#   define Z_UNSET_ISREF_PP(ppz) (*(ppz))->is_ref = 0
#endif

typedef struct
{
    zval *data[VAR_ENTRIES_MAX];
    long used_slots;
    void *next;
} var_entries;

inline static void msgpack_var_push(
    php_unserialize_data_t *var_hashx, zval **rval)
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

    var_hash->data[var_hash->used_slots++] = *rval;
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

    if (id < 0 || id >= var_hash->used_slots)
    {
        return !SUCCESS;
    }

    *store = &var_hash->data[id];

    return SUCCESS;
}

inline static int msgpack_unserialize_array(
    zval **return_value, msgpack_unserialize_data *mpsd,
    ulong ct, php_unserialize_data_t *var_hash TSRMLS_DC)
{
    ulong i;
    HashTable *ht;

    msgpack_var_push(var_hash, return_value);

    if (Z_TYPE_PP(return_value) != IS_ARRAY)
    {
        array_init(*return_value);
    }

    ht = HASH_OF(*return_value);

    for (i = 0; i < ct; i++)
    {
        zval *val;

        /* value */
        ALLOC_INIT_ZVAL(val);

        if (msgpack_unserialize_zval(&val, mpsd, var_hash TSRMLS_CC) <= 0)
        {
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (msgpack_unserialize_array) "
                           "Invalid value");
            }
            zval_ptr_dtor(&val);

            return MSGPACK_UNPACK_PARSE_ERROR;
        }

        /* update */
        zend_hash_index_update(ht, i, &val, sizeof(zval *), NULL);
    }

    return MSGPACK_UNPACK_SUCCESS;
}

inline static int msgpack_unserialize_object_type(
    zval **return_value, msgpack_unserialize_data *mpsd,
    php_unserialize_data_t *var_hash, zend_bool is_ref TSRMLS_DC)
{
    int ret = MSGPACK_UNPACK_SUCCESS;
    zval *key, *val, **rval;

    ALLOC_INIT_ZVAL(key);

    if (msgpack_unserialize_zval(&key, mpsd, NULL TSRMLS_CC) <= 0)
    {
        zval_ptr_dtor(&key);

        ZVAL_BOOL(*return_value, 0);

        return MSGPACK_UNPACK_PARSE_ERROR;
    }

    ALLOC_INIT_ZVAL(val);

    if (is_ref)
    {
        ret = msgpack_unserialize_zval(&val, mpsd, NULL TSRMLS_CC);
    }
    else
    {
        ret = msgpack_unserialize_zval(&val, mpsd, var_hash TSRMLS_CC);
    }

    if (ret <= 0)
    {
        zval_ptr_dtor(&val);
        zval_ptr_dtor(&key);

        ZVAL_BOOL(*return_value, 0);

        return MSGPACK_UNPACK_PARSE_ERROR;
    }

    if (!var_hash ||
        msgpack_var_access(var_hash, Z_LVAL_P(val) - 1, &rval) != SUCCESS)
    {
        if (MSGPACK_G(error_display))
        {
            zend_error(E_WARNING,
                       "[msgpack] (msgpack_unserialize_object_key) "
                       "Invalid references value: %ld",
                       Z_LVAL_P(val) - 1);
        }
        ret = MSGPACK_UNPACK_CONTINUE;
    }
    else
    {
        if (*return_value != NULL)
        {
            zval_ptr_dtor(return_value);
        }

        *return_value = *rval;

        Z_ADDREF_PP(return_value);

        if (is_ref)
        {
            Z_SET_ISREF_PP(return_value);
        }
        else
        {
            Z_UNSET_ISREF_PP(return_value);
        }
    }

    zval_ptr_dtor(&key);
    zval_ptr_dtor(&val);

    return ret;
}

inline static int msgpack_unserialize_object(
    zval **return_value, msgpack_unserialize_data *mpsd,
    ulong ct, php_unserialize_data_t *var_hash TSRMLS_DC)
{
    int ret = MSGPACK_UNPACK_SUCCESS;

    zend_class_entry *ce, **pce;
    bool incomplete_class = false;
    zval *user_func, *retval_ptr, **args[1], *arg_func_name;
    HashTable *ht;

    zval *key, *val;

    int object = 1;
    int custom_object = 0;

    /* Get class */
    ALLOC_INIT_ZVAL(key);

    if (msgpack_unserialize_zval(&key, mpsd, NULL TSRMLS_CC) <= 0)
    {
        if (MSGPACK_G(error_display))
        {
            zend_error(E_WARNING,
                       "[msgpack] (msgpack_unserialize_object) "
                       "Invalid sign key");
        }

        zval_ptr_dtor(&key);

        ZVAL_BOOL(*return_value, 0);

        return MSGPACK_UNPACK_PARSE_ERROR;
    }

    ct--;

    if (Z_TYPE_P(key) == IS_NULL)
    {
        ALLOC_INIT_ZVAL(val);

        if (msgpack_unserialize_zval(&val, mpsd, NULL TSRMLS_CC) <= 0)
        {
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (msgpack_unserialize_object) "
                           "Invalid sign value");
            }

            zval_ptr_dtor(&val);
            zval_ptr_dtor(&key);

            ZVAL_BOOL(*return_value, 0);

            return MSGPACK_UNPACK_PARSE_ERROR;
        }

        if (Z_TYPE_P(val) == IS_LONG)
        {
            switch (Z_LVAL_P(val))
            {
                case MSGPACK_SERIALIZE_TYPE_REFERENCE:
                    ret = msgpack_unserialize_object_type(
                        return_value, mpsd, var_hash, 1 TSRMLS_CC);

                    zval_ptr_dtor(&key);
                    zval_ptr_dtor(&val);

                    return ret;
                case MSGPACK_SERIALIZE_TYPE_OBJECT:
                    ret = msgpack_unserialize_object_type(
                        return_value, mpsd, var_hash, 0 TSRMLS_CC);

                    zval_ptr_dtor(&key);
                    zval_ptr_dtor(&val);

                    return ret;
                case MSGPACK_SERIALIZE_TYPE_CUSTOM_OBJECT:
                    custom_object = 1;

                    zval_ptr_dtor(&val);

                    ALLOC_INIT_ZVAL(val);

                    if (msgpack_unserialize_zval(
                            &val, mpsd, NULL TSRMLS_CC) <= 0)
                    {
                        zval_ptr_dtor(&key);
                        zval_ptr_dtor(&val);

                        ZVAL_BOOL(*return_value, 0);

                        return MSGPACK_UNPACK_PARSE_ERROR;
                    }
                    break;
                default:
                    zval_ptr_dtor(&key);
                    zval_ptr_dtor(&val);

                    ZVAL_BOOL(*return_value, 0);

                    return MSGPACK_UNPACK_PARSE_ERROR;
            }
        }
    }
    else
    {
        object = 0;

        msgpack_var_push(var_hash, return_value);

        if (Z_TYPE_PP(return_value) != IS_ARRAY)
        {
            array_init(*return_value);
        }

        ht = HASH_OF(*return_value);

        ALLOC_INIT_ZVAL(val);

        if (msgpack_unserialize_zval(&val, mpsd, var_hash TSRMLS_CC) <= 0)
        {
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (msgpack_unserialize_object) "
                           "Invalid sign value");
            }

            zval_ptr_dtor(&val);
            zval_ptr_dtor(&key);

            return MSGPACK_UNPACK_PARSE_ERROR;
        }

        /* update */
        switch (Z_TYPE_P(key))
        {
            case IS_LONG:
                zend_hash_index_update(
                    ht, Z_LVAL_P(key), &val, sizeof(zval *), NULL);
                break;
            case IS_STRING:
                zend_symtable_update(
                    ht, Z_STRVAL_P(key), Z_STRLEN_P(key) + 1,
                    &val, sizeof(zval *), NULL);
                break;
            default:
                zval_ptr_dtor(&key);
                zval_ptr_dtor(&val);

                return MSGPACK_UNPACK_PARSE_ERROR;
        }
    }

    zval_ptr_dtor(&key);

    if (object)
    {
        convert_to_string(val);

        do {
            /* Try to find class directly */
            if (zend_lookup_class(
                    Z_STRVAL_P(val), Z_STRLEN_P(val), &pce TSRMLS_CC) == SUCCESS)
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
            ZVAL_STRING(arg_func_name, Z_STRVAL_P(val), 1);
            if (call_user_function_ex(
                    CG(function_table), NULL, user_func, &retval_ptr,
                    1, args, 0, NULL TSRMLS_CC) != SUCCESS)
            {
                if (MSGPACK_G(error_display))
                {
                    zend_error(E_WARNING,
                               "[msgpack] (msgpack_unserialize_object) "
                               "defined (%s) but not found", Z_STRVAL_P(val));
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
            if (zend_lookup_class(
                    Z_STRVAL_P(val), Z_STRLEN_P(val), &pce TSRMLS_CC) == SUCCESS)
            {
                ce = *pce;
            }
            else
            {
                if (MSGPACK_G(error_display))
                {
                    zend_error(E_WARNING,
                               "[msgpack] (msgpack_unserialize_object) "
                               "Function %s() hasn't defined the class"
                               "it was called for", Z_STRVAL_P(val));
                }

                incomplete_class = true;
                ce = PHP_IC_ENTRY;
            }

            zval_ptr_dtor(&user_func);
            zval_ptr_dtor(&arg_func_name);
        } while(0);

        if (EG(exception))
        {
            if (MSGPACK_G(error_display))
            {
                zend_error(E_WARNING,
                           "[msgpack] (msgpack_unserialize_object) "
                           "Exception error");
            }

            zval_ptr_dtor(&val);

            ZVAL_BOOL(*return_value, 0);

            return MSGPACK_UNPACK_PARSE_ERROR;
        }

        msgpack_var_push(var_hash, return_value);

        object_init_ex(*return_value, ce);

        /* store incomplete class name */
        if (incomplete_class)
        {
            php_store_class_name(
                *return_value, Z_STRVAL_P(val), Z_STRLEN_P(val));
        }

        zval_ptr_dtor(&val);

        /* implementing Serializable */
        if (custom_object)
        {
            zval *rval;

            if (ce->unserialize == NULL)
            {
                if (MSGPACK_G(error_display))
                {
                    zend_error(E_WARNING,
                               "[msgpack] (msgpack_unserialize_object) "
                               "Class %s has no unserializer", ce->name);
                }

                return MSGPACK_UNPACK_PARSE_ERROR;
            }

            /* value */
            ALLOC_INIT_ZVAL(rval);

            if (msgpack_unserialize_zval(&rval, mpsd, var_hash TSRMLS_CC) <= 0)
            {
                zval_ptr_dtor(&rval);

                return MSGPACK_UNPACK_PARSE_ERROR;
            }

            ce->unserialize(
                return_value, ce,
                (const unsigned char *)Z_STRVAL_P(rval), Z_STRLEN_P(rval) + 1,
                (zend_unserialize_data *)var_hash TSRMLS_CC);

            zval_ptr_dtor(&key);
            zval_ptr_dtor(&rval);

            return ret;
        }

        ht = HASH_OF(*return_value);
    }

    /* object property */
    while (ct-- > 0)
    {
        zval *rval;

        /* key */
        ALLOC_INIT_ZVAL(key);

        if (msgpack_unserialize_zval(&key, mpsd, NULL TSRMLS_CC) <= 0)
        {
            zval_ptr_dtor(&key);

            return MSGPACK_UNPACK_PARSE_ERROR;
        }

        /* value */
        ALLOC_INIT_ZVAL(rval);

        if (msgpack_unserialize_zval(&rval, mpsd, var_hash TSRMLS_CC) <= 0)
        {
            zval_ptr_dtor(&rval);
            zval_ptr_dtor(&key);

            return MSGPACK_UNPACK_PARSE_ERROR;

        }

        /* update */
        switch (Z_TYPE_P(key))
        {
            case IS_LONG:
                zend_hash_index_update(
                    ht, Z_LVAL_P(key), &rval, sizeof(zval *), NULL);
                break;
            case IS_STRING:
                zend_symtable_update(
                    ht, Z_STRVAL_P(key), Z_STRLEN_P(key) + 1,
                    &rval, sizeof(zval *), NULL);
                break;
            default:
                zval_ptr_dtor(&key);
                zval_ptr_dtor(&rval);

                return MSGPACK_UNPACK_PARSE_ERROR;
        }

        zval_ptr_dtor(&key);
    }

    /* wakeup */
    if (object && Z_OBJCE_PP(return_value) != PHP_IC_ENTRY &&
        zend_hash_exists(&Z_OBJCE_PP(return_value)->function_table,
                         "__wakeup", sizeof("__wakeup")))
    {
        zval f, *h = NULL;

        INIT_PZVAL(&f);
        ZVAL_STRINGL(&f, "__wakeup", sizeof("__wakeup") - 1, 0);
        call_user_function_ex(
            CG(function_table), return_value, &f, &h, 0, 0, 1, NULL TSRMLS_CC);
        if (h)
        {
            zval_ptr_dtor(&h);
        }

        if (EG(exception))
        {
            ret = MSGPACK_UNPACK_PARSE_ERROR;
        }
    }

    return ret;
}

int msgpack_unserialize_zval(
    zval **return_value, msgpack_unserialize_data *mpsd,
    php_unserialize_data_t *var_hash TSRMLS_DC)
{
    const unsigned char* data = mpsd->data;
    const unsigned char* const pe = mpsd->data + mpsd->length;
    const void* n = NULL;

    unsigned int trail = 0;
    unsigned int cs = CS_HEADER;

    int ret;
    unsigned int ct;

#define next_cs(p) ((unsigned int)*p & 0x1f)

#define finish_zval_long(val_) \
    msgpack_var_push(var_hash, return_value); \
    ZVAL_LONG(*return_value, val_); \
    goto _finish

#define finish_zval_null() \
    msgpack_var_push(var_hash, return_value); \
    ZVAL_NULL(*return_value); \
    goto _finish

#define finish_zval_bool(val_) \
    msgpack_var_push(var_hash, return_value); \
    ZVAL_BOOL(*return_value, val_); \
    goto _finish

#define finish_zval_double(val_) \
    msgpack_var_push(var_hash, return_value); \
    ZVAL_DOUBLE(*return_value, val_); \
    goto _finish

#define finish_zval_string(val_, len_) \
    msgpack_var_push(var_hash, return_value); \
    if (len_ == 0) { ZVAL_STRINGL(*return_value, "", 0, 1); } \
    else { ZVAL_STRINGL(*return_value, val_, len_, 1); } \
    goto _finish

#define finish_zval_array(count_) \
    ct = count_; \
    cs = CS_HEADER; \
    ++(mpsd->data); \
    mpsd->length = (pe - mpsd->data); \
    if (msgpack_unserialize_array(return_value, mpsd, ct, var_hash TSRMLS_CC) <= 0) { goto _failed; } \
    goto _finish_end

#define finish_zval_object(count_) \
    ct = count_; \
    cs = CS_HEADER; \
    ++(mpsd->data); \
    mpsd->length = (pe - mpsd->data); \
    if (msgpack_unserialize_object(return_value, mpsd, ct, var_hash TSRMLS_CC) <= 0) { goto _failed; } \
    goto _finish_end

#define again_fixed_trail(_cs, trail_len) \
    trail = trail_len; \
    cs = _cs; \
    goto _fixed_trail_again

#define again_fixed_trail_if_zero(_cs, trail_len, ifzero) \
    trail = trail_len; \
    if(trail == 0) { goto ifzero; } \
    cs = _cs; \
    goto _fixed_trail_again

    if (mpsd->length <= 0)
    {
        goto _failed;
    }

    if (mpsd->data == pe)
    {
        goto _out;
    }
    do
    {
        switch (cs)
        {
            case CS_HEADER:
                switch (*(mpsd->data))
                {
                    case 0x00 ... 0x7f: /* Positive Fixnum */
                        finish_zval_long(*(uint8_t*)mpsd->data);
                    case 0xe0 ... 0xff: /* Negative Fixnum */
                        finish_zval_long(*(int8_t*)mpsd->data);
                    case 0xc0 ... 0xdf: /* Variable */
                        switch (*(mpsd->data))
                        {
                            case 0xc0:  /* nil */
                                finish_zval_null();
                            case 0xc2:  /* false */
                                finish_zval_bool(0);
                            case 0xc3:  /* true */
                                finish_zval_bool(1);
                            case 0xca:  /* float */
                            case 0xcb:  /* double */
                            case 0xcc:  /* unsigned int  8 */
                            case 0xcd:  /* unsigned int 16 */
                            case 0xce:  /* unsigned int 32 */
                            case 0xcf:  /* unsigned int 64 */
                            case 0xd0:  /* signed int  8 */
                            case 0xd1:  /* signed int 16 */
                            case 0xd2:  /* signed int 32 */
                            case 0xd3:  /* signed int 64 */
                                again_fixed_trail(
                                    next_cs(mpsd->data),
                                    1 << (((unsigned int)*(mpsd->data)) & 0x03));
                            case 0xda:  /* raw 16 */
                            case 0xdb:  /* raw 32 */
                            case 0xdc:  /* array 16 */
                            case 0xdd:  /* array 32 */
                            case 0xde:  /* map 16 */
                            case 0xdf:  /* map 32 */
                                again_fixed_trail(
                                    next_cs(mpsd->data),
                                    2 << (((unsigned int)*(mpsd->data)) & 0x01));
                            default:
                                goto _failed;
                        }
                    case 0xa0 ... 0xbf: /* FixRaw */
                        again_fixed_trail_if_zero(
                            ACS_RAW_VALUE, (unsigned int)*(mpsd->data) & 0x1f,
                            _raw_zero);
                    case 0x90 ... 0x9f: /* FixArray */
                        finish_zval_array(((unsigned int)*(mpsd->data)) & 0x0f);
                    case 0x80 ... 0x8f: /* FixMap */
                        finish_zval_object(((unsigned int)*(mpsd->data)) & 0x0f);
                    default:
                        goto _failed;
                }
_fixed_trail_again:
                ++(mpsd->data);
            default:
                if ((size_t)(pe - (mpsd->data)) < trail)
                {
                    goto _out;
                }
                n = (mpsd->data);
                mpsd->data += trail - 1;
                switch (cs)
                {
                    case CS_FLOAT:
                    {
                        union { uint32_t i; float f; } mem;
                        mem.i = _msgpack_load32(uint32_t, n);
                        finish_zval_double(mem.f);
                    }
                    case CS_DOUBLE:
                    {
                        union { uint64_t i; double f; } mem;
                        mem.i = _msgpack_load64(uint64_t, n);
                        finish_zval_double(mem.f);
                    }
                    case CS_UINT_8:
                        finish_zval_long(*(uint8_t*)n);
                    case CS_UINT_16:
                        finish_zval_long(_msgpack_load16(uint16_t, n));
                    case CS_UINT_32:
                        finish_zval_long(_msgpack_load32(uint32_t, n));
                    case CS_UINT_64:
                        finish_zval_long(_msgpack_load64(uint64_t, n));
                    case CS_INT_8:
                        finish_zval_long(*(int8_t*)n);
                    case CS_INT_16:
                        finish_zval_long(_msgpack_load16(int16_t, n));
                    case CS_INT_32:
                        finish_zval_long(_msgpack_load32(int32_t, n));
                    case CS_INT_64:
                        finish_zval_long(_msgpack_load64(int64_t, n));
                    case CS_RAW_16:
                        again_fixed_trail_if_zero(
                            ACS_RAW_VALUE, _msgpack_load16(uint16_t, n),
                            _raw_zero);
                    case CS_RAW_32:
                        again_fixed_trail_if_zero(
                            ACS_RAW_VALUE, _msgpack_load32(uint32_t, n),
                            _raw_zero);
                    case ACS_RAW_VALUE:
_raw_zero:
                        finish_zval_string(n, trail);
                    case CS_ARRAY_16:
                        finish_zval_array(_msgpack_load16(uint16_t, n));
                    case CS_ARRAY_32:
                        finish_zval_array(_msgpack_load32(uint32_t, n));
                    /* FIXME security guard */
                    case CS_MAP_16:
                        finish_zval_object(_msgpack_load16(uint16_t, n));
                    case CS_MAP_32:
                        finish_zval_object(_msgpack_load32(uint32_t, n));
                    /* FIXME security guard */
                    default:
                        goto _failed;
                }
        }
        cs = CS_HEADER;
        ++(mpsd->data);
    }
    while (mpsd->data != pe);
    goto _out;

_finish:
    ++(mpsd->data);
_finish_end:
    ret = MSGPACK_UNPACK_EXTRA_BYTES;
    goto _end;

_failed:
    ret = MSGPACK_UNPACK_PARSE_ERROR;
    goto _end;

_out:
    ret = MSGPACK_UNPACK_CONTINUE;
    goto _end;

_end:
    mpsd->offset = mpsd->data - data;
    mpsd->length = pe - mpsd->data;

    if (ret == MSGPACK_UNPACK_EXTRA_BYTES && mpsd->length == 0)
    {
        ret = MSGPACK_UNPACK_SUCCESS;
    }

    return ret;
}

#undef finish_zval_long
#undef finish_zval_null
#undef finish_zval_bool
#undef finish_zval_double
#undef finish_zval_string
#undef finish_zval_array
#undef finish_zval_object
#undef again_fixed_trail
#undef again_fixed_trail_if_zero

#undef next_cs
