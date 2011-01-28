# coding: utf-8

from cpython cimport *
cdef extern from "Python.h":
    ctypedef char* const_char_ptr "const char*"
    ctypedef char* const_void_ptr "const void*"
    ctypedef struct PyObject
    cdef int PyObject_AsReadBuffer(object o, const_void_ptr* buff, Py_ssize_t* buf_len) except -1

from libc.stdlib cimport *
from libc.string cimport *

cdef extern from "pack.h":
    struct msgpack_packer:
        char* buf
        size_t length
        size_t buf_size

    int msgpack_pack_int(msgpack_packer* pk, int d)
    int msgpack_pack_nil(msgpack_packer* pk)
    int msgpack_pack_true(msgpack_packer* pk)
    int msgpack_pack_false(msgpack_packer* pk)
    int msgpack_pack_long(msgpack_packer* pk, long d)
    int msgpack_pack_long_long(msgpack_packer* pk, long long d)
    int msgpack_pack_unsigned_long_long(msgpack_packer* pk, unsigned long long d)
    int msgpack_pack_double(msgpack_packer* pk, double d)
    int msgpack_pack_array(msgpack_packer* pk, size_t l)
    int msgpack_pack_map(msgpack_packer* pk, size_t l)
    int msgpack_pack_raw(msgpack_packer* pk, size_t l)
    int msgpack_pack_raw_body(msgpack_packer* pk, char* body, size_t l)

cdef int DEFAULT_RECURSE_LIMIT=511

cdef class Packer(object):
    """MessagePack Packer
    
    usage:

        packer = Packer()
        astream.write(packer.pack(a))
        astream.write(packer.pack(b))
    """
    cdef msgpack_packer pk
    cdef object _default

    def __cinit__(self):
        cdef int buf_size = 1024*1024
        self.pk.buf = <char*> malloc(buf_size);
        if self.pk.buf == NULL:
            raise MemoryError("Unable to allocate internal buffer.")
        self.pk.buf_size = buf_size
        self.pk.length = 0

    def __init__(self, default=None):
        if default is not None:
            if not PyCallable_Check(default):
                raise TypeError("default must be a callable.")
        self._default = default

    def __dealloc__(self):
        free(self.pk.buf);

    cdef int _pack(self, object o, int nest_limit=DEFAULT_RECURSE_LIMIT) except -1:
        cdef long long llval
        cdef unsigned long long ullval
        cdef long longval
        cdef double fval
        cdef char* rawval 
        cdef int ret
        cdef dict d

        if nest_limit < 0:
            raise ValueError("Too deep.")

        if o is None:
            ret = msgpack_pack_nil(&self.pk)
        elif isinstance(o, bool):
            if o:
                ret = msgpack_pack_true(&self.pk)
            else:
                ret = msgpack_pack_false(&self.pk)
        elif PyLong_Check(o):
            if o > 0:
                ullval = o
                ret = msgpack_pack_unsigned_long_long(&self.pk, ullval)
            else:
                llval = o
                ret = msgpack_pack_long_long(&self.pk, llval)
        elif PyInt_Check(o):
            longval = o
            ret = msgpack_pack_long(&self.pk, longval)
        elif PyFloat_Check(o):
            fval = o
            ret = msgpack_pack_double(&self.pk, fval)
        elif PyBytes_Check(o):
            rawval = o
            ret = msgpack_pack_raw(&self.pk, len(o))
            if ret == 0:
                ret = msgpack_pack_raw_body(&self.pk, rawval, len(o))
        elif PyUnicode_Check(o):
            o = PyUnicode_AsUTF8String(o)
            rawval = o
            ret = msgpack_pack_raw(&self.pk, len(o))
            if ret == 0:
                ret = msgpack_pack_raw_body(&self.pk, rawval, len(o))
        elif PyDict_Check(o):
            d = o
            ret = msgpack_pack_map(&self.pk, len(d))
            if ret == 0:
                for k,v in d.items():
                    ret = self._pack(k, nest_limit-1)
                    if ret != 0: break
                    ret = self._pack(v, nest_limit-1)
                    if ret != 0: break
        elif PySequence_Check(o):
            ret = msgpack_pack_array(&self.pk, len(o))
            if ret == 0:
                for v in o:
                    ret = self._pack(v, nest_limit-1)
                    if ret != 0: break
        elif self._default is not None:
            o = self._default(o)
            ret = self._pack(o, nest_limit)
        else:
            raise TypeError("can't serialize %r" % (o,))
        return ret

    def pack(self, object obj):
        cdef int ret
        ret = self._pack(obj, DEFAULT_RECURSE_LIMIT)
        if ret:
            raise TypeError
        buf = PyBytes_FromStringAndSize(self.pk.buf, self.pk.length)
        self.pk.length = 0
        return buf


def pack(object o, object stream, default=None):
    """pack an object `o` and write it to stream)."""
    packer = Packer(default=default)
    stream.write(packer.pack(o))

def packb(object o, default=None):
    """pack o and return packed bytes."""
    packer = Packer(default=default)
    return packer.pack(o)

dumps = packs = packb

cdef extern from "unpack.h":
    ctypedef struct msgpack_user:
        int use_list
        PyObject* object_hook
        PyObject* list_hook

    ctypedef struct template_context:
        msgpack_user user
        PyObject* obj
        size_t count
        unsigned int ct
        PyObject* key

    int template_execute(template_context* ctx, const_char_ptr data,
                         size_t len, size_t* off)
    void template_init(template_context* ctx)
    object template_data(template_context* ctx)


def unpackb(object packed, object object_hook=None, object list_hook=None, bint use_list=0):
    """Unpack packed_bytes to object. Returns an unpacked object."""
    cdef template_context ctx
    cdef size_t off = 0
    cdef int ret

    cdef char* buf
    cdef Py_ssize_t buf_len
    PyObject_AsReadBuffer(packed, <const_void_ptr*>&buf, &buf_len)

    template_init(&ctx)
    ctx.user.use_list = use_list
    ctx.user.object_hook = ctx.user.list_hook = NULL
    if object_hook is not None:
        if not PyCallable_Check(object_hook):
            raise TypeError("object_hook must be a callable.")
        ctx.user.object_hook = <PyObject*>object_hook
    if list_hook is not None:
        if not PyCallable_Check(list_hook):
            raise TypeError("list_hook must be a callable.")
        ctx.user.list_hook = <PyObject*>list_hook
    ret = template_execute(&ctx, buf, buf_len, &off)
    if ret == 1:
        return template_data(&ctx)
    else:
        return None

loads = unpacks = unpackb

def unpack(object stream, object object_hook=None, object list_hook=None, bint use_list=0):
    """unpack an object from stream."""
    return unpackb(stream.read(), use_list=use_list,
                   object_hook=object_hook, list_hook=list_hook)

cdef class UnpackIterator(object):
    cdef object unpacker

    def __init__(self, unpacker):
        self.unpacker = unpacker

    def __next__(self):
        return self.unpacker.unpack()

    def __iter__(self):
        return self

cdef class Unpacker(object):
    """Unpacker(read_size=1024*1024)

    Streaming unpacker.
    read_size is used like file_like.read(read_size)

    example:
        unpacker = Unpacker()
        while 1:
            buf = astream.read()
            unpacker.feed(buf)
            for o in unpacker:
                do_something(o)
    """
    cdef template_context ctx
    cdef char* buf
    cdef size_t buf_size, buf_head, buf_tail
    cdef object file_like
    cdef object file_like_read
    cdef Py_ssize_t read_size
    cdef bint use_list
    cdef object object_hook

    def __cinit__(self):
        self.buf = NULL

    def __dealloc__(self):
        free(self.buf);
        self.buf = NULL;

    def __init__(self, file_like=None, Py_ssize_t read_size=0, bint use_list=0,
                 object object_hook=None, object list_hook=None):
        if read_size == 0:
            read_size = 1024*1024
        self.use_list = use_list
        self.file_like = file_like
        if file_like:
            self.file_like_read = file_like.read
            if not PyCallable_Check(self.file_like_read):
                raise ValueError("`file_like.read` must be a callable.")
        self.read_size = read_size
        self.buf = <char*>malloc(read_size)
        if self.buf == NULL:
            raise MemoryError("Unable to allocate internal buffer.")
        self.buf_size = read_size
        self.buf_head = 0
        self.buf_tail = 0
        template_init(&self.ctx)
        self.ctx.user.use_list = use_list
        self.ctx.user.object_hook = self.ctx.user.list_hook = <PyObject*>NULL
        if object_hook is not None:
            if not PyCallable_Check(object_hook):
                raise TypeError("object_hook must be a callable.")
            self.ctx.user.object_hook = <PyObject*>object_hook
        if list_hook is not None:
            if not PyCallable_Check(list_hook):
                raise TypeError("list_hook must be a callable.")
            self.ctx.user.list_hook = <PyObject*>list_hook

    def feed(self, object next_bytes):
        cdef char* buf
        cdef Py_ssize_t buf_len
        if self.file_like is not None:
            raise AssertionError(
                    "unpacker.feed() is not be able to use with`file_like`.")
        PyObject_AsReadBuffer(next_bytes, <const_void_ptr*>&buf, &buf_len)
        self.append_buffer(buf, buf_len)

    cdef append_buffer(self, void* _buf, Py_ssize_t _buf_len):
        cdef:
            char* buf = self.buf
            size_t head = self.buf_head
            size_t tail = self.buf_tail
            size_t buf_size = self.buf_size
            size_t new_size

        if tail + _buf_len > buf_size:
            if ((tail - head) + _buf_len)*2 < buf_size:
                # move to front.
                memmove(buf, buf + head, tail - head)
                tail -= head
                head = 0
            else:
                # expand buffer.
                new_size = tail + _buf_len
                if new_size < buf_size*2:
                    new_size = buf_size*2
                buf = <char*>realloc(buf, new_size) 
                if buf == NULL:
                    # self.buf still holds old buffer and will be freed during
                    # obj destruction
                    raise MemoryError("Unable to enlarge internal buffer.")
                buf_size = new_size

        memcpy(buf + tail, <char*>(_buf), _buf_len)
        self.buf = buf
        self.buf_head = head
        self.buf_size = buf_size
        self.buf_tail = tail + _buf_len

    # prepare self.buf from file_like
    cdef fill_buffer(self):
        if self.file_like is not None:
            next_bytes = self.file_like_read(self.read_size)
            if next_bytes:
                self.append_buffer(PyBytes_AsString(next_bytes),
                                   PyBytes_Size(next_bytes))
            else:
                self.file_like = None

    cpdef unpack(self):
        """unpack one object"""
        cdef int ret
        while 1:
            ret = template_execute(&self.ctx, self.buf, self.buf_tail, &self.buf_head)
            if ret == 1:
                o = template_data(&self.ctx)
                template_init(&self.ctx)
                return o
            elif ret == 0:
                if self.file_like is not None:
                    self.fill_buffer()
                    continue
                raise StopIteration("No more unpack data.")
            else:
                raise ValueError("Unpack failed: error = %d" % (ret,))

    def __iter__(self):
        return UnpackIterator(self)

    # for debug.
    #def _buf(self):
    #    return PyString_FromStringAndSize(self.buf, self.buf_tail)

    #def _off(self):
    #    return self.buf_head
