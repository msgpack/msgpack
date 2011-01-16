
#ifndef MSGPACK_ERRORS_H
#define MSGPACK_ERRORS_H

#define MSGPACK_NOTICE(...)                \
    if (MSGPACK_G(error_display)) {        \
        zend_error(E_NOTICE, __VA_ARGS__); \
    }

#define MSGPACK_WARNING(...)                \
    if (MSGPACK_G(error_display)) {         \
        zend_error(E_WARNING, __VA_ARGS__); \
    }

#define MSGPACK_ERROR(...) zend_error(E_ERROR, __VA_ARGS__)

#endif
