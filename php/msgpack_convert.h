
#ifndef MSGPACK_CONVERT_H
#define MSGPACK_CONVERT_H

int msgpack_convert_object(zval *return_value, zval *object, zval **value);
int msgpack_convert_array(zval *return_value, zval *tpl, zval **value);
int msgpack_convert_template(zval *return_value, zval *tpl, zval **value);

#endif
