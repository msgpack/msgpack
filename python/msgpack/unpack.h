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

#include <map>
#include <string>
#include <stack>

#define MSGPACK_MAX_STACK_SIZE  (1024)
#include "msgpack/unpack_define.h"

using namespace std;

struct unpack_user {
    stack<unsigned int> array_stack;
    map<string, PyObject*> str_cache;

    ~unpack_user() {
        map<string, PyObject*>::iterator it, itend;
        itend = str_cache.end();
        for (it = str_cache.begin(); it != itend; ++it) {
            Py_DECREF(it->second);
        }
    }
};


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

static inline int template_callback_uint8(unpack_user* u, uint8_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong((long)d); return 0; }

static inline int template_callback_uint16(unpack_user* u, uint16_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong((long)d); return 0; }

static inline int template_callback_uint32(unpack_user* u, uint32_t d, msgpack_unpack_object* o)
{
    if (d > LONG_MAX) {
        *o = PyLong_FromUnsignedLong((unsigned long)d);
    } else {
        *o = PyInt_FromLong((long)d);
    }
    return 0;
}

static inline int template_callback_uint64(unpack_user* u, uint64_t d, msgpack_unpack_object* o)
{ *o = PyLong_FromUnsignedLongLong(d); return 0; }

static inline int template_callback_int8(unpack_user* u, int8_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong(d); return 0; }

static inline int template_callback_int16(unpack_user* u, int16_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong(d); return 0; }

static inline int template_callback_int32(unpack_user* u, int32_t d, msgpack_unpack_object* o)
{ *o = PyInt_FromLong(d); return 0; }

static inline int template_callback_int64(unpack_user* u, int64_t d, msgpack_unpack_object* o)
{ *o = PyLong_FromLongLong(d); return 0; }

static inline int template_callback_float(unpack_user* u, float d, msgpack_unpack_object* o)
{ *o = PyFloat_FromDouble((double)d); return 0; }

static inline int template_callback_double(unpack_user* u, double d, msgpack_unpack_object* o)
{ *o = PyFloat_FromDouble(d); return 0; }

static inline int template_callback_nil(unpack_user* u, msgpack_unpack_object* o)
{ Py_INCREF(Py_None); *o = Py_None; return 0; }

static inline int template_callback_true(unpack_user* u, msgpack_unpack_object* o)
{ Py_INCREF(Py_True); *o = Py_True; return 0; }

static inline int template_callback_false(unpack_user* u, msgpack_unpack_object* o)
{ Py_INCREF(Py_False); *o = Py_False; return 0; }

static inline int template_callback_array(unpack_user* u, unsigned int n, msgpack_unpack_object* o)
{
    if (n > 0) {
        u->array_stack.push(0);
        *o = PyList_New(n);
    }
    else {
        *o = PyList_New(0);
    }
    return 0;
}

static inline int template_callback_array_item(unpack_user* u, msgpack_unpack_object* c, msgpack_unpack_object o)
{
    unsigned int &last = u->array_stack.top();
    PyList_SET_ITEM(*c, last, o);
    last++;

    Py_ssize_t len = PyList_GET_SIZE(*c);
    if (last >= len) {
        u->array_stack.pop();
    }
    return 0;
}

static inline int template_callback_map(unpack_user* u, unsigned int n, msgpack_unpack_object* o)
{
    *o = PyDict_New();
    return 0;
}

static inline int template_callback_map_item(unpack_user* u, msgpack_unpack_object* c, msgpack_unpack_object k, msgpack_unpack_object v)
{
    PyDict_SetItem(*c, k, v);
    Py_DECREF(k);
    Py_DECREF(v);
    return 0;
}

static inline int template_callback_raw(unpack_user* u, const char* b, const char* p, unsigned int l, msgpack_unpack_object* o)
{
    if (l < 16) {
        string s(p, l);
        map<string,PyObject*>::iterator it = u->str_cache.find(s);
        if (it != u->str_cache.end()) {
            *o = it->second;
            Py_INCREF(*o);
        }
        else {
            *o = PyString_FromStringAndSize(p, l);
            Py_INCREF(*o);
            u->str_cache[s] = *o;
        }
    }
    else {
        *o = PyString_FromStringAndSize(p, l);
    }
    return 0;
}

#include "msgpack/unpack_template.h"
