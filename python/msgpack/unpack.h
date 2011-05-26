/*
 * MessagePack for Python unpacking routine
 *
 * Copyright (C) 2009 Naoki INADA
 *
 *    Licensed under the Apache License, Version 2.0 (the "License");
 *    you may not use this file except in compliance with the License.
 *    You may obtain a copy of the License at
 *
 *        http://www.apache.org/licenses/LICENSE-2.0
 *
 *    Unless required by applicable law or agreed to in writing, software
 *    distributed under the License is distributed on an "AS IS" BASIS,
 *    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *    See the License for the specific language governing permissions and
 *    limitations under the License.
 */

#define MSGPACK_MAX_STACK_SIZE  (1024)
#include "unpack_define.h"

typedef struct unpack_user {
    int use_list;
    PyObject *object_hook;
    PyObject *list_hook;
    const char *encoding;
    const char *unicode_errors;
} unpack_user;


#define msgpack_unpack_struct(name) \
	struct template ## name

#define msgpack_unpack_func(ret, name) \
	static inline ret template ## name

#define msgpack_unpack_callback(name) \
	template_callback ## name

#define msgpack_unpack_object PyObject*

#define msgpack_unpack_user unpack_user


struct template_context;
typedef struct template_context template_context;

static inline msgpack_unpack_object template_callback_root(unpack_user* u)
{
    return NULL;
}

static inline int template_callback_uint16(unpack_user* u, uint16_t d, msgpack_unpack_object* o)
{
    PyObject *p = PyInt_FromLong((long)d);
    if (!p)
        return -1;
    *o = p;
    return 0;
}
static inline int template_callback_uint8(unpack_user* u, uint8_t d, msgpack_unpack_object* o)
{
    return template_callback_uint16(u, d, o);
}


static inline int template_callback_uint32(unpack_user* u, uint32_t d, msgpack_unpack_object* o)
{
    PyObject *p;
    if (d > LONG_MAX) {
        p = PyLong_FromUnsignedLong((unsigned long)d);
    } else {
        p = PyInt_FromLong((long)d);
    }
    if (!p)
        return -1;
    *o = p;
    return 0;
}

static inline int template_callback_uint64(unpack_user* u, uint64_t d, msgpack_unpack_object* o)
{
    PyObject *p = PyLong_FromUnsignedLongLong(d);
    if (!p)
        return -1;
    *o = p;
    return 0;
}

static inline int template_callback_int32(unpack_user* u, int32_t d, msgpack_unpack_object* o)
{
    PyObject *p = PyInt_FromLong(d);
    if (!p)
        return -1;
    *o = p;
    return 0;
}

static inline int template_callback_int16(unpack_user* u, int16_t d, msgpack_unpack_object* o)
{
    return template_callback_int32(u, d, o);
}

static inline int template_callback_int8(unpack_user* u, int8_t d, msgpack_unpack_object* o)
{
    return template_callback_int32(u, d, o);
}

static inline int template_callback_int64(unpack_user* u, int64_t d, msgpack_unpack_object* o)
{
    PyObject *p = PyLong_FromLongLong(d);
    if (!p)
        return -1;
    *o = p;
    return 0;
}

static inline int template_callback_double(unpack_user* u, double d, msgpack_unpack_object* o)
{
    PyObject *p = PyFloat_FromDouble(d);
    if (!p)
        return -1;
    *o = p;
    return 0;
}

static inline int template_callback_float(unpack_user* u, float d, msgpack_unpack_object* o)
{
    return template_callback_double(u, d, o);
}

static inline int template_callback_nil(unpack_user* u, msgpack_unpack_object* o)
{ Py_INCREF(Py_None); *o = Py_None; return 0; }

static inline int template_callback_true(unpack_user* u, msgpack_unpack_object* o)
{ Py_INCREF(Py_True); *o = Py_True; return 0; }

static inline int template_callback_false(unpack_user* u, msgpack_unpack_object* o)
{ Py_INCREF(Py_False); *o = Py_False; return 0; }

static inline int template_callback_array(unpack_user* u, unsigned int n, msgpack_unpack_object* o)
{
    PyObject *p = u->use_list ? PyList_New(n) : PyTuple_New(n);

    if (!p)
        return -1;
    *o = p;
    return 0;
}

static inline int template_callback_array_item(unpack_user* u, unsigned int current, msgpack_unpack_object* c, msgpack_unpack_object o)
{
    if (u->use_list)
        PyList_SET_ITEM(*c, current, o);
    else
        PyTuple_SET_ITEM(*c, current, o);
    return 0;
}

static inline int template_callback_array_end(unpack_user* u, msgpack_unpack_object* c)
{
    if (u->list_hook) {
        PyObject *arglist = Py_BuildValue("(O)", *c);
        *c = PyEval_CallObject(u->list_hook, arglist);
        Py_DECREF(arglist);
    }
    return 0;
}

static inline int template_callback_map(unpack_user* u, unsigned int n, msgpack_unpack_object* o)
{
    PyObject *p = PyDict_New();
    if (!p)
        return -1;
    *o = p;
    return 0;
}

static inline int template_callback_map_item(unpack_user* u, msgpack_unpack_object* c, msgpack_unpack_object k, msgpack_unpack_object v)
{
    if (PyDict_SetItem(*c, k, v) == 0) {
        Py_DECREF(k);
        Py_DECREF(v);
        return 0;
    }
    return -1;
}

static inline int template_callback_map_end(unpack_user* u, msgpack_unpack_object* c)
{
    if (u->object_hook) {
        PyObject *arglist = Py_BuildValue("(O)", *c);
        *c = PyEval_CallObject(u->object_hook, arglist);
        Py_DECREF(arglist);
    }
    return 0;
}

static inline int template_callback_raw(unpack_user* u, const char* b, const char* p, unsigned int l, msgpack_unpack_object* o)
{
    PyObject *py;
    if(u->encoding) {
        py = PyUnicode_Decode(p, l, u->encoding, u->unicode_errors);
    } else {
        py = PyBytes_FromStringAndSize(p, l);
    }
    if (!py)
        return -1;
    *o = py;
    return 0;
}

#include "unpack_template.h"
