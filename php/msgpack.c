/*
  +----------------------------------------------------------------------+
  | PHP Version 5                                                        |
  +----------------------------------------------------------------------+
  | Copyright (c) 1997-2007 The PHP Group                                |
  +----------------------------------------------------------------------+
  | This source file is subject to version 3.01 of the PHP license,      |
  | that is bundled with this package in the file LICENSE, and is        |
  | available through the world-wide-web at the following url:           |
  | http://www.php.net/license/3_01.txt                                  |
  | If you did not receive a copy of the PHP license and are unable to   |
  | obtain it through the world-wide-web, please send a note to          |
  | license@php.net so we can mail you a copy immediately.               |
  +----------------------------------------------------------------------+
  | Author: Hideyuki TAKEI                                               |
  +----------------------------------------------------------------------+
*/

/* $Id: header 226204 2007-01-01 19:32:10Z iliaa $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "php.h"
#include "php_ini.h"
#include "ext/standard/info.h"
#include "ext/standard/php_smart_str.h"
#include "php_msgpack.h"

#define PHP_EXT_VERSION "0.01"

#ifndef TRUE
# define TRUE 1
# define FALSE 0
#endif


/* pack */
#include "msgpack/pack_define.h"

#define msgpack_pack_inline_func(name) \
	    static inline void msgpack_pack ## name

#define msgpack_pack_inline_func_cint(name) \
	    static inline void msgpack_pack ## name

#define msgpack_pack_user smart_str*

#define msgpack_pack_append_buffer(user, buf, len) \
	    smart_str_appendl(user, (const void*)buf, len)

#include "msgpack/pack_template.h"


/* unpack */
#include "msgpack/unpack_define.h"

typedef struct {
	    int finished;
		char* source;
} unpack_user;

#define msgpack_unpack_struct(name) \
	    struct template ## name

#define msgpack_unpack_func(ret, name) \
	    ret template ## name

#define msgpack_unpack_callback(name) \
	    template_callback ## name

#define msgpack_unpack_object zval*

#define msgpack_unpack_user unpack_user

struct template_context;
typedef struct template_context msgpack_unpack_t;

static void template_init(msgpack_unpack_t* u);
static msgpack_unpack_object template_data(msgpack_unpack_t* u);
static int template_execute(msgpack_unpack_t* u,
		        const char* data, size_t len, size_t* off);

ZEND_BEGIN_MODULE_GLOBALS(msgpack)
	msgpack_unpack_t *global_mp;
ZEND_END_MODULE_GLOBALS(msgpack)

#ifdef ZTS
#define MSGPACK_G(v) TSRMG(msgpack_globals_id, zend_msgpack_globals *, v)
#else
#define MSGPACK_G(v) (msgpack_globals.v)
#endif

static inline msgpack_unpack_object template_callback_root(unpack_user* u)
{
	msgpack_unpack_object data;
	ALLOC_INIT_ZVAL(data);
	ZVAL_NULL(data);
	return data;
}

static inline int template_callback_uint8(unpack_user* u, uint8_t d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_LONG(*o, d); return 0; }

static inline int template_callback_uint16(unpack_user* u, uint16_t d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_LONG(*o, d); return 0; }

static inline int template_callback_uint32(unpack_user* u, uint32_t d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_LONG(*o, d); return 0; }

static inline int template_callback_uint64(unpack_user* u, uint64_t d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_LONG(*o, d); return 0; }

static inline int template_callback_int8(unpack_user* u, int8_t d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_LONG(*o, (long)d); return 0; }

static inline int template_callback_int16(unpack_user* u, int16_t d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_LONG(*o, (long)d); return 0; }

static inline int template_callback_int32(unpack_user* u, int32_t d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_LONG(*o, (long)d); return 0; }

static inline int template_callback_int64(unpack_user* u, int64_t d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_LONG(*o, d); return 0; }

static inline int template_callback_float(unpack_user* u, float d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_DOUBLE(*o, d); return 0; }

static inline int template_callback_double(unpack_user* u, double d, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_DOUBLE(*o, d); return 0; }

static inline int template_callback_nil(unpack_user* u, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_NULL(*o); return 0; }

static inline int template_callback_true(unpack_user* u, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_BOOL(*o, 1); return 0; }

static inline int template_callback_false(unpack_user* u, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); ZVAL_BOOL(*o, 0); return 0;}

static inline int template_callback_array(unpack_user* u, unsigned int n, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); array_init(*o); return 0; }

static inline int template_callback_array_item(unpack_user* u, msgpack_unpack_object* c, msgpack_unpack_object o)
{ add_next_index_zval(*c, o); return 0; }

static inline int template_callback_map(unpack_user* u, unsigned int n, msgpack_unpack_object* o)
{ ALLOC_INIT_ZVAL(*o); array_init(*o); return 0; }

static inline int template_callback_map_item(unpack_user* u, msgpack_unpack_object* c, msgpack_unpack_object k, msgpack_unpack_object v)
{
	switch(k->type) {
		case IS_LONG:
	   	    add_index_zval(*c, Z_LVAL(*k), v);
			break;
		case IS_STRING:
	   		add_assoc_zval_ex(*c, Z_STRVAL(*k), Z_STRLEN(*k)+1, v);
			break;
		default:
			zend_error(E_WARNING, "[msgpack] (php_msgpack_decode) illegal offset type, skip this decoding");
			break;
	}
    return 0;
}
			

static inline int template_callback_raw(unpack_user* u, const char* b, const char* p, unsigned int l, msgpack_unpack_object* o)
{
	ALLOC_INIT_ZVAL(*o);
	if (l == 0) {
		ZVAL_STRINGL(*o, "", 0, 1);
	} else {
		ZVAL_STRINGL(*o, p, l, 1);
	}
	return 0;
}

#include "msgpack/unpack_template.h"

static PHP_GINIT_FUNCTION(msgpack);

ZEND_DECLARE_MODULE_GLOBALS(msgpack)

/* True global resources - no need for thread safety here */
static int le_msgpack;

/* {{{ msgpack_functions[]
 *
 * Every user visible function must have an entry in msgpack_functions[].
 */
zend_function_entry msgpack_functions[] = {
	PHP_FE(msgpack_pack, NULL)
	PHP_FE(msgpack_unpack, NULL)
	PHP_FE(msgpack_unpack_limit, NULL)
	PHP_ME(msgpack, initialize, NULL, 0)
	PHP_ME(msgpack, execute, NULL, 0)
	PHP_ME(msgpack, execute_limit, NULL, 0)
	PHP_ME(msgpack, finished, NULL, 0)
	PHP_ME(msgpack, data, NULL, 0)
	{NULL, NULL, NULL}	/* Must be the last line in msgpack_functions[] */
};
/* }}} */

/* {{{ msgpack_module_entry
 */
zend_module_entry msgpack_module_entry = {
#if ZEND_MODULE_API_NO >= 20010901
	STANDARD_MODULE_HEADER,
#endif
	"msgpack",
	msgpack_functions,
	PHP_MINIT(msgpack),
	PHP_MSHUTDOWN(msgpack),
	PHP_RINIT(msgpack),		/* Replace with NULL if there's nothing to do at request start */
	PHP_RSHUTDOWN(msgpack),	/* Replace with NULL if there's nothing to do at request end */
	PHP_MINFO(msgpack),
#if ZEND_MODULE_API_NO >= 20010901
	"0.1", /* Replace with version number for your extension */
#endif
	PHP_MODULE_GLOBALS(msgpack),
	PHP_GINIT(msgpack),
	NULL,
	NULL,
	STANDARD_MODULE_PROPERTIES_EX
};
/* }}} */

#ifdef COMPILE_DL_MSGPACK
ZEND_GET_MODULE(msgpack)
#endif

/* {{{ PHP_GINIT_FUNCTION */
static PHP_GINIT_FUNCTION(msgpack)
{
	msgpack_globals->global_mp = NULL;
}
/* }}} */

/* {{{ PHP_MINIT_FUNCTION
 */
PHP_MINIT_FUNCTION(msgpack)
{
	zend_class_entry ce;
	INIT_CLASS_ENTRY(ce, "MessagePack", msgpack_functions);
	msgpack_ce = zend_register_internal_class(&ce TSRMLS_CC);

	return SUCCESS;
}
/* }}} */

/* {{{ PHP_MSHUTDOWN_FUNCTION
 */
PHP_MSHUTDOWN_FUNCTION(msgpack)
{
	/* uncomment this line if you have INI entries
	UNREGISTER_INI_ENTRIES();
	*/
	if (MSGPACK_G(global_mp)) {
		efree(MSGPACK_G(global_mp));
		MSGPACK_G(global_mp) = NULL;
	}

	return SUCCESS;
}
/* }}} */

/* Remove if there's nothing to do at request start */
/* {{{ PHP_RINIT_FUNCTION
 */
PHP_RINIT_FUNCTION(msgpack)
{
	return SUCCESS;
}
/* }}} */

/* Remove if there's nothing to do at request end */
/* {{{ PHP_RSHUTDOWN_FUNCTION
 */
PHP_RSHUTDOWN_FUNCTION(msgpack)
{
	return SUCCESS;
}
/* }}} */

/* {{{ PHP_MINFO_FUNCTION
 */
PHP_MINFO_FUNCTION(msgpack)
{
	php_info_print_table_start();
	php_info_print_table_header(2, "msgpack support", "enabled");
	php_info_print_table_row(2, "php extension version", PHP_EXT_VERSION);
	php_info_print_table_row(2, "author", "Hideyuki TAKEI");
	php_info_print_table_row(2, "homepage", "http://msgpack.sourceforge.net");
	php_info_print_table_row(2, "open sourced by", "KLab inc.");
	php_info_print_table_end();
}
/* }}} */

PHP_MSGPACK_API int msgpack_determine_array_type(zval **val TSRMLS_DC)  /* {{{ */
{
	int i;
	HashTable *myht = HASH_OF(*val);

	i = myht ? zend_hash_num_elements(myht) : 0;
	if (i > 0) {
		char *key;
		ulong index, idx;
		uint key_len;
		HashPosition pos;

		zend_hash_internal_pointer_reset_ex(myht, &pos);
		idx = 0;
		for (;; zend_hash_move_forward_ex(myht, &pos)) {
			i = zend_hash_get_current_key_ex(myht, &key, &key_len, &index, 0, &pos);
			if (i == HASH_KEY_NON_EXISTANT)
				break;
			if (i == HASH_KEY_IS_STRING) {
				return 1;
			} else {
				if (index != idx) {
					return 1;
				}
			}
			idx++;
		}
	}
	return 0;
}
/* }}} */

PHP_MSGPACK_API void msgpack_pack_array_hash(smart_str *pk, zval **val TSRMLS_DC) /* {{{ */	
{
	int i, r;
	HashTable *myht;

	if(Z_TYPE_PP(val) == IS_ARRAY){
		myht = HASH_OF(*val);
		r = msgpack_determine_array_type(val TSRMLS_CC);
	}
	else{
		myht = Z_OBJPROP_PP(val);
		r = 1;
	}

	i = myht ? zend_hash_num_elements(myht) : 0;

	if(r == 0){
		msgpack_pack_array(pk, i);
	}
	else{
		msgpack_pack_map(pk, i);
	}

	if(i>0){
		char *key;
		zval **data;
		ulong index;
		uint key_len;
		HashPosition pos;
		HashTable *tmp_ht;
		int need_comma = 0;

		zend_hash_internal_pointer_reset_ex(myht, &pos);
		for(;; zend_hash_move_forward_ex(myht, &pos)){
			i = zend_hash_get_current_key_ex(myht, &key, &key_len, &index, 0, &pos);
			if(i==HASH_KEY_NON_EXISTANT)
				break;
			if(zend_hash_get_current_data_ex(myht, (void **) &data, &pos) == SUCCESS){
				tmp_ht = HASH_OF(*data);
				if (tmp_ht)
					tmp_ht->nApplyCount++;

				if(r==0)
					php_msgpack_pack(pk, *data TSRMLS_CC);
				else if(r==1){
					if(i==HASH_KEY_IS_STRING){
						if(key[0]=='\0' && Z_TYPE_PP(val)==IS_OBJECT){
							// Skip protected and private members.
							if(tmp_ht)
								tmp_ht->nApplyCount--;
							continue;
						}
						msgpack_pack_raw(pk, key_len-1);
						msgpack_pack_raw_body(pk, key, key_len-1);
						php_msgpack_pack(pk, *data TSRMLS_CC);
					}
					else{
						msgpack_pack_long(pk, index);
						php_msgpack_pack(pk, *data TSRMLS_CC);
					}
				}

				if(tmp_ht){
					tmp_ht->nApplyCount--;
				}
			}
		}

	}
}
/* }}} */

PHP_MSGPACK_API void php_msgpack_pack(smart_str *pk, zval *val TSRMLS_DC) /* {{{ */
{
	switch(Z_TYPE_P(val)){
		case IS_NULL:
			msgpack_pack_nil(pk);
			break;
		case IS_BOOL:
			if (Z_BVAL_P(val))
				msgpack_pack_true(pk);
			else
				msgpack_pack_false(pk);
			break;
		case IS_LONG:
			msgpack_pack_long(pk, Z_LVAL_P(val));
			break;
		case IS_DOUBLE:
			{
				double dbl = Z_DVAL_P(val);
				if (zend_isinf(dbl) || zend_isnan(dbl)) {
					zend_error(E_WARNING, "[msgpack] (php_msgpack_pack) double %.9g does not conform to the MSGPACK spec, encoded as 0", dbl);
					ZVAL_LONG(val, 0);
				}
				msgpack_pack_double(pk, Z_DVAL_P(val));
			}
			break;
		case IS_STRING:
			msgpack_pack_raw(pk, Z_STRLEN_P(val));
			msgpack_pack_raw_body(pk, Z_STRVAL_P(val), Z_STRLEN_P(val));
			break;
		case IS_ARRAY:
		case IS_OBJECT:
			msgpack_pack_array_hash(pk, &val TSRMLS_CC);
			break;
		defalut:
			zend_error(E_WARNING, "[msgpack] (php_msgpack_pack) type is unsupported, encoded as null");
			msgpack_pack_nil(pk);
			break;
	}

	return;
}
/* }}} */

PHP_MSGPACK_API void php_msgpack_unpack_limit(zval *return_value, const char *buf, int len, zend_bool assoc TSRMLS_DC) /* {{{ */
{
	if (len<=0) {
		RETURN_NUL();
	}

	msgpack_unpack_t mp;
	template_init(&mp);
	unpack_user u = {0, ""};

	size_t from = 0;
	char* dptr = (char*)buf;
	long dlen = len;
	int ret;

	(&mp)->user.source = (char*)buf;
	ret = template_execute(&mp, dptr, (size_t)dlen, &from);
	(&mp)->user.source = "";

	if(ret < 0) {
		zend_error(E_WARNING, "[msgpack] (php_msgpack_unpack) parse error");
	} else if(ret == 0) {
		zend_error(E_WARNING, "[msgpack] (php_msgpack_unpack) insufficient bytes");
	} else {
		if(from < dlen) {
			zend_error(E_WARNING, "[msgpack] (php_msgpack_unpack) extra bytes");
		}

		*return_value = *template_data(&mp);
		FREE_ZVAL(template_data(&mp));
	}
}	
/* }}} */


PHP_FUNCTION(msgpack_pack)
{
	zval *parameter;
	smart_str buf = {0};

	if (zend_parse_parameters(ZEND_NUM_ARGS() TSRMLS_CC, "z", &parameter) == FAILURE) {
		return;
	}

	php_msgpack_pack(&buf, parameter TSRMLS_CC);

	ZVAL_STRINGL(return_value, buf.c, buf.len, 1);

	smart_str_free(&buf);
}

PHP_FUNCTION(msgpack_unpack)
{
	char *parameter;
	int parameter_len;
	zend_bool assoc = 0;

	if (zend_parse_parameters(ZEND_NUM_ARGS() TSRMLS_CC, "s|b",
	   &parameter, &parameter_len, &assoc) == FAILURE) {
		return;
	}

	if (!parameter_len) {
		RETURN_NULL();
	}

	php_msgpack_unpack_limit(return_value, parameter, parameter_len, assoc TSRMLS_CC);
}

PHP_FUNCTION(msgpack_unpack_limit)
{
	char *parameter;
	int parameter_len;
	int limit;
	zend_bool assoc = 0;

	if (zend_parse_parameters(ZEND_NUM_ARGS() TSRMLS_CC, "sl|b",
	   &parameter, &parameter_len, &limit, &assoc) == FAILURE) {
		return;
	}

	if (!parameter_len) {
		RETURN_NULL();
	}
	else if (parameter_len < limit) {
		zend_error(E_WARNING, "[msgpack] (php_msgpack_unpack) limit greater than data_len");
		limit = parameter_len;
	}

	php_msgpack_unpack_limit(return_value, parameter, limit, assoc TSRMLS_CC);
}


PHP_MSGPACK_API void php_msgpack_unpacker_execute_limit(zval *return_value, const char *buf, int off, int len, zend_bool assoc TSRMLS_DC) /* {{{ */
{
	if (len<=0) {
		RETURN_NUL();
	}

	size_t from = off;
	char* dptr = (char*)buf;
	long dlen = len;
	int ret;

	if(from >= dlen) {
		zend_error(E_WARNING, "[msgpack] (php_msgpack_unpacker_execute_limit) offset is bigger than data buffer size");
    }

	MSGPACK_G(global_mp)->user.source = (char*)buf;
	ret = template_execute(MSGPACK_G(global_mp), dptr, (size_t)dlen, &from);
	MSGPACK_G(global_mp)->user.source = "";

	if(ret < 0) {
		zend_error(E_WARNING, "[msgpack] (php_msgpack_unpacker_execute_limit) parse error");
	} else if(ret > 0) {
		MSGPACK_G(global_mp)->user.finished = 1;
		RETVAL_LONG(from);
	} else {
		MSGPACK_G(global_mp)->user.finished = 0;
		RETVAL_LONG(from);
	}
}
/* }}} */

PHP_MSGPACK_API void php_msgpack_unpacker_reset(TSRMLS_D) /* {{{ */
{
	if(MSGPACK_G(global_mp)) {
		efree(MSGPACK_G(global_mp));
		MSGPACK_G(global_mp) = NULL;
	}
	MSGPACK_G(global_mp) = safe_emalloc(sizeof(msgpack_unpack_t), 1, 0);

	template_init(MSGPACK_G(global_mp));
	unpack_user u = {0, ""};
	MSGPACK_G(global_mp)->user = u;
	return;
}
/* }}} */

PHP_METHOD(msgpack, initialize)
{
	php_msgpack_unpacker_reset(TSRMLS_C);
	return;
}

PHP_METHOD(msgpack, execute)
{
	char *data;
	int off;
	int data_len;
	zend_bool assoc = 0;

	if (zend_parse_parameters(ZEND_NUM_ARGS() TSRMLS_CC, "sl|b",
	   &data, &data_len, &off, &assoc) == FAILURE) {
		return;
	}

	if (!data_len) {
		RETURN_NULL();
	}

	php_msgpack_unpacker_execute_limit(return_value, data, off, data_len, assoc TSRMLS_CC);
}

PHP_METHOD(msgpack, execute_limit)
{
	char *data;
	int off;
	int data_len;
	int limit;
	zend_bool assoc = 0;

	if (zend_parse_parameters(ZEND_NUM_ARGS() TSRMLS_CC, "sll|b",
	   &data, &data_len, &off, &limit, &assoc) == FAILURE) {
		return;
	}

	if (!data_len) {
		RETURN_NULL();
	}
	else if (data_len < limit) {
		zend_error(E_WARNING, "[msgpack] (php_msgpack_unpack) limit greater than (data+off)_len");
		limit = data_len;
	}

	php_msgpack_unpacker_execute_limit(return_value, data, off, limit, assoc TSRMLS_CC);
}

PHP_METHOD(msgpack, finished)
{
	if(MSGPACK_G(global_mp)->user.finished == 1) {
		RETURN_TRUE;
	}
	RETURN_FALSE;
}

PHP_METHOD(msgpack, data)
{
	*return_value = *template_data(MSGPACK_G(global_mp));
	return;
}

/*
 * Local variables:
 * tab-width: 4
 * c-basic-offset: 4
 * End:
 * vim600: noet sw=4 ts=4 fdm=marker
 * vim<600: noet sw=4 ts=4
 */
