# coding: utf-8

import cStringIO

cdef extern from "Python.h":
    ctypedef char* const_char_ptr "const char*"
    ctypedef struct PyObject

    cdef object PyString_FromStringAndSize(const_char_ptr b, Py_ssize_t len)
    cdef PyObject* Py_True
    cdef PyObject* Py_False

    cdef char* PyString_AsString(object o)
    cdef long long PyLong_AsLongLong(object o)
    cdef unsigned long long PyLong_AsUnsignedLongLong(object o)

    cdef int PyMapping_Check(object o)
    cdef int PySequence_Check(object o)
    cdef int PyLong_Check(object o)
    cdef int PyInt_Check(object o)
    cdef int PyFloat_Check(object o)
    cdef int PyString_Check(object o)
    cdef int PyUnicode_Check(object o)

cdef extern from "stdlib.h":
    void* malloc(size_t)
    void* realloc(void*, size_t)
    void free(void*)

cdef extern from "string.h":
    void* memcpy(char* dst, char* src, size_t size)
    void* memmove(char* dst, char* src, size_t size)

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


cdef class Packer(object):
    """MessagePack Packer
    
    usage:

        packer = Packer()
        astream.write(packer.pack(a))
        astream.write(packer.pack(b))
    """
    cdef msgpack_packer pk

    def __cinit__(self):
        cdef int buf_size = 1024*1024
        self.pk.buf = <char*> malloc(buf_size);
        self.pk.buf_size = buf_size
        self.pk.length = 0

    def __dealloc__(self):
        free(self.pk.buf);

    cdef int __pack(self, object o) except -1:
        cdef long long llval
        cdef unsigned long long ullval
        cdef long longval
        cdef double fval
        cdef char* rawval 
        cdef int ret

        if o is None:
            ret = msgpack_pack_nil(&self.pk)
        elif <PyObject*>o == Py_True:
            ret = msgpack_pack_true(&self.pk)
        elif <PyObject*>o == Py_False:
            ret = msgpack_pack_false(&self.pk)
        elif PyLong_Check(o):
            if o > 0:
                ullval = PyLong_AsUnsignedLongLong(o)
                ret = msgpack_pack_unsigned_long_long(&self.pk, ullval)
            else:
                llval = PyLong_AsLongLong(o)
                ret = msgpack_pack_long_long(&self.pk, llval)
        elif PyInt_Check(o):
            longval = o
            ret = msgpack_pack_long(&self.pk, longval)
        elif PyFloat_Check(o):
            fval = o
            ret = msgpack_pack_double(&self.pk, fval)
        elif PyString_Check(o):
            rawval = o
            ret = msgpack_pack_raw(&self.pk, len(o))
            if ret == 0:
                ret = msgpack_pack_raw_body(&self.pk, rawval, len(o))
        elif PyUnicode_Check(o):
            o = o.encode('utf-8')
            rawval = o
            ret = msgpack_pack_raw(&self.pk, len(o))
            if ret == 0:
                ret = msgpack_pack_raw_body(&self.pk, rawval, len(o))
        elif PyMapping_Check(o):
            ret = msgpack_pack_map(&self.pk, len(o))
            if ret == 0:
                for k,v in o.iteritems():
                    ret = self.__pack(k)
                    if ret != 0: break
                    ret = self.__pack(v)
                    if ret != 0: break
        elif PySequence_Check(o):
            ret = msgpack_pack_array(&self.pk, len(o))
            if ret == 0:
                for v in o:
                    ret = self.__pack(v)
                    if ret != 0: break
        else:
            # TODO: Serialize with defalt() like simplejson.
            raise TypeError, "can't serialize %r" % (o,)
        return ret

    def pack(self, object obj):
        cdef int ret
        ret = self.__pack(obj)
        if ret:
            raise TypeError
        buf = PyString_FromStringAndSize(self.pk.buf, self.pk.length)
        self.pk.length = 0
        return buf


def pack(object o, object stream):
    """pack an object `o` and write it to stream)."""
    packer = Packer()
    stream.write(packer.pack(o))

def packb(object o):
    """pack o and return packed bytes."""
    packer = Packer()
    return packer.pack(o)

packs = packb

cdef extern from "unpack.h":
    ctypedef struct msgpack_user:
        int use_list

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


def unpackb(object packed_bytes):
    """Unpack packed_bytes to object. Returns an unpacked object."""
    cdef const_char_ptr p = packed_bytes
    cdef template_context ctx
    cdef size_t off = 0
    cdef int ret
    template_init(&ctx)
    ctx.user.use_list = 0
    ret = template_execute(&ctx, p, len(packed_bytes), &off)
    if ret == 1:
        return template_data(&ctx)
    else:
        return None

unpacks = unpackb

def unpack(object stream):
    """unpack an object from stream."""
    packed = stream.read()
    return unpackb(packed)

cdef class UnpackIterator(object):
    cdef object unpacker

    def __init__(self, unpacker):
        self.unpacker = unpacker

    def __next__(self):
        return self.unpacker.unpack()

    def __iter__(self):
        return self

cdef class Unpacker(object):
    """Unpacker(file_like=None, read_size=1024*1024)

    Streaming unpacker.
    file_like must have read(n) method.
    read_size is used like file_like.read(read_size)

    If file_like is None, you can ``feed()`` bytes. ``feed()`` is
    useful for unpacking from non-blocking stream.

    exsample 1:
        unpacker = Unpacker(afile)
        for o in unpacker:
            do_something(o)

    example 2:
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
    cdef int read_size
    cdef object waiting_bytes
    cdef int use_list

    def __cinit__(self):
        self.buf = NULL

    def __dealloc__(self):
        if self.buf:
            free(self.buf);

    def __init__(self, file_like=None, int read_size=0, use_list=0):
        if read_size == 0:
            read_size = 1024*1024
        self.use_list = use_list
        self.file_like = file_like
        self.read_size = read_size
        self.waiting_bytes = []
        self.buf = <char*>malloc(read_size)
        self.buf_size = read_size
        self.buf_head = 0
        self.buf_tail = 0
        template_init(&self.ctx)
        self.ctx.user.use_list = use_list

    def feed(self, next_bytes):
        if not isinstance(next_bytes, str):
           raise ValueError, "Argument must be bytes object"
        self.waiting_bytes.append(next_bytes)

    cdef append_buffer(self):
        cdef char* buf = self.buf
        cdef Py_ssize_t tail = self.buf_tail
        cdef Py_ssize_t l

        for b in self.waiting_bytes:
            l = len(b)
            memcpy(buf + tail, PyString_AsString(b), l)
            tail += l
        self.buf_tail = tail
        del self.waiting_bytes[:]

    # prepare self.buf
    cdef fill_buffer(self):
        cdef Py_ssize_t add_size

        if self.file_like is not None:
            next_bytes = self.file_like.read(self.read_size)
            if next_bytes:
                self.waiting_bytes.append(next_bytes)
            else:
                self.file_like = None

        if not self.waiting_bytes:
            return

        add_size = 0
        for b in self.waiting_bytes:
            add_size += len(b)

        cdef char* buf = self.buf
        cdef size_t head = self.buf_head
        cdef size_t tail = self.buf_tail
        cdef size_t size = self.buf_size

        if self.buf_tail + add_size <= self.buf_size:
            # do nothing.
            pass
        if self.buf_tail - self.buf_head + add_size < self.buf_size:
            # move to front.
            memmove(buf, buf + head, tail - head)
            tail -= head
            head = 0
        else:
            # expand buffer
            size = tail + add_size
            buf = <char*>realloc(<void*>buf, size)

        self.buf = buf
        self.buf_head = head
        self.buf_tail = tail
        self.buf_size = size

        self.append_buffer()

    cpdef unpack(self):
        """unpack one object"""
        cdef int ret
        self.fill_buffer()
        ret = template_execute(&self.ctx, self.buf, self.buf_tail, &self.buf_head)
        if ret == 1:
            o = template_data(&self.ctx)
            template_init(&self.ctx)
            return o
        elif ret == 0:
            if self.file_like is not None:
                return self.unpack()
            raise StopIteration, "No more unpack data."
        else:
            raise ValueError, "Unpack failed."

    def __iter__(self):
        return UnpackIterator(self)

    # for debug.
    #def _buf(self):
    #    return PyString_FromStringAndSize(self.buf, self.buf_tail)

    #def _off(self):
    #    return self.buf_head
