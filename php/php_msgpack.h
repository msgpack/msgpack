
#ifndef PHP_MSGPACK_H
#define PHP_MSGPACK_H

#define MSGPACK_EXTENSION_VERSION "0.5.2"

#include "ext/standard/php_smart_str.h"

extern zend_module_entry msgpack_module_entry;
#define phpext_msgpack_ptr &msgpack_module_entry

#ifdef PHP_WIN32
#   define PHP_MSGPACK_API __declspec(dllexport)
#elif defined(__GNUC__) && __GNUC__ >= 4
#   define PHP_MSGPACK_API __attribute__ ((visibility("default")))
#else
#   define PHP_MSGPACK_API
#endif

#ifdef ZTS
#include "TSRM.h"
#endif

ZEND_BEGIN_MODULE_GLOBALS(msgpack)
    zend_bool error_display;
    zend_bool php_only;
    zend_bool illegal_key_insert;
ZEND_END_MODULE_GLOBALS(msgpack)

ZEND_EXTERN_MODULE_GLOBALS(msgpack)

#ifdef ZTS
#define MSGPACK_G(v) TSRMG(msgpack_globals_id, zend_msgpack_globals *, v)
#else
#define MSGPACK_G(v) (msgpack_globals.v)
#endif

PHP_MSGPACK_API void php_msgpack_serialize(
    smart_str *buf, zval *val TSRMLS_DC);
PHP_MSGPACK_API void php_msgpack_unserialize(
    zval *return_value, char *str, size_t str_len TSRMLS_DC);

#endif  /* PHP_MSGPACK_H */
