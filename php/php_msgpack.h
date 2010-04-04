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
  | Author:                                                              |
  +----------------------------------------------------------------------+
*/

/* $Id: header 226204 2007-01-01 19:32:10Z iliaa $ */

#ifndef PHP_MSGPACK_H
#define PHP_MSGPACK_H

extern zend_module_entry msgpack_module_entry;
#define phpext_msgpack_ptr &msgpack_module_entry

#ifdef PHP_WIN32
#define PHP_MSGPACK_API __declspec(dllexport)
#else
#define PHP_MSGPACK_API
#endif

#ifdef ZTS
#include "TSRM.h"
#endif

PHP_MINIT_FUNCTION(msgpack);
PHP_MSHUTDOWN_FUNCTION(msgpack);
PHP_RINIT_FUNCTION(msgpack);
PHP_RSHUTDOWN_FUNCTION(msgpack);
PHP_MINFO_FUNCTION(msgpack);

PHP_FUNCTION(msgpack_pack);
PHP_FUNCTION(msgpack_unpack);
PHP_FUNCTION(msgpack_unpack_limit);

PHP_METHOD(msgpack, initialize);
PHP_METHOD(msgpack, execute);
PHP_METHOD(msgpack, execute_limit);
PHP_METHOD(msgpack, finished);
PHP_METHOD(msgpack, data);

static zend_class_entry *msgpack_ce;

/* 
  	Declare any global variables you may need between the BEGIN
	and END macros here:     

ZEND_BEGIN_MODULE_GLOBALS(msgpack)
	long  global_value;
	char *global_string;
ZEND_END_MODULE_GLOBALS(msgpack)
*/

/* In every utility function you add that needs to use variables 
   in php_msgpack_globals, call TSRMLS_FETCH(); after declaring other 
   variables used by that function, or better yet, pass in TSRMLS_CC
   after the last function argument and declare your utility function
   with TSRMLS_DC after the last declared argument.  Always refer to
   the globals in your function as MSGPACK_G(variable).  You are 
   encouraged to rename these macros something shorter, see
   examples in any other php module directory.
*/


#endif	/* PHP_MSGPACK_H */


/*
 * Local variables:
 * tab-width: 4
 * c-basic-offset: 4
 * End:
 * vim600: noet sw=4 ts=4 fdm=marker
 * vim<600: noet sw=4 ts=4
 */
