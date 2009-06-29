# coding: utf-8

from cStringIO import StringIO

cdef extern from "Python.h":
    ctypedef char* const_char_ptr "const char*"
    ctypedef struct PyObject
    cdef object PyString_FromStringAndSize(const_char_ptr b, Py_ssize_t len)
    char* PyString_AsString(object o)
    int PyMapping_Check(object o)
    int PySequence_Check(object o)
    long long PyLong_AsLongLong(object o)
    unsigned long long PyLong_AsUnsignedLongLong(object o)

cdef extern from "stdlib.h":
    void* malloc(size_t)
    void* realloc(void*, size_t)
    void free(void*)

cdef extern from "string.h":
    void* memcpy(char* dst, char* src, size_t size)
    void* memmove(char* dst, char* src, size_t size)

cdef extern from "pack.h":
    ctypedef int (*msgpack_packer_write)(void* data, const_char_ptr buf, unsigned int len)

    struct msgpack_packer:
        void *data
        msgpack_packer_write callback

    void msgpack_packer_init(msgpack_packer* pk, void* data, msgpack_packer_write callback)
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
    """Packer that pack data into strm.

    strm must have `write(bytes)` method.
    size specifies local buffer size.
    """
    cdef char* buff
    cdef unsigned int length
    cdef unsigned int allocated
    cdef msgpack_packer pk
    cdef object strm

    def __init__(self, strm, int size=4*1024):
        self.strm = strm
        self.buff = <char*> malloc(size)
        self.allocated = size
        self.length = 0

        msgpack_packer_init(&self.pk, <void*>self, <msgpack_packer_write>_packer_write)

    def __del__(self):
        free(self.buff)

    def flush(self):
        """Flash local buffer and output stream if it has 'flush()' method."""
        if self.length > 0:
            self.strm.write(PyString_FromStringAndSize(self.buff, self.length))
            self.length = 0
        if hasattr(self.strm, 'flush'):
            self.strm.flush()

    def pack_list(self, len):
        """Start packing sequential objects.

        Example:

            packer.pack_list(2)
            packer.pack('foo')
            packer.pack('bar')

        This is same to:

            packer.pack(['foo', 'bar'])
        """
        msgpack_pack_array(&self.pk, len)

    def pack_dict(self, len):
        """Start packing key-value objects.

        Example:

            packer.pack_dict(1)
            packer.pack('foo')
            packer.pack('bar')

        This is same to:

            packer.pack({'foo': 'bar'})
        """
        msgpack_pack_map(&self.pk, len)

    cdef __pack(self, object o):
        cdef long long llval
        cdef unsigned long long ullval
        cdef long longval
        cdef double fval
        cdef char* rawval 

        if o is None:
            msgpack_pack_nil(&self.pk)
        elif o is True:
            msgpack_pack_true(&self.pk)
        elif o is False:
            msgpack_pack_false(&self.pk)
        elif isinstance(o, long):
            if o > 0:
                ullval = PyLong_AsUnsignedLongLong(o)
                msgpack_pack_unsigned_long_long(&self.pk, ullval)
            else:
                llval = PyLong_AsLongLong(o)
                msgpack_pack_long_long(&self.pk, llval)
        elif isinstance(o, int):
            longval = o
            msgpack_pack_long(&self.pk, longval)
        elif isinstance(o, float):
            fval = o
            msgpack_pack_double(&self.pk, fval)
        elif isinstance(o, str):
            rawval = o
            msgpack_pack_raw(&self.pk, len(o))
            msgpack_pack_raw_body(&self.pk, rawval, len(o))
        elif isinstance(o, unicode):
            o = o.encode('utf-8')
            rawval = o
            msgpack_pack_raw(&self.pk, len(o))
            msgpack_pack_raw_body(&self.pk, rawval, len(o))
        elif PyMapping_Check(o):
            msgpack_pack_map(&self.pk, len(o))
            for k,v in o.iteritems():
                self.__pack(k)
                self.__pack(v)
        elif PySequence_Check(o):
            msgpack_pack_array(&self.pk, len(o))
            for v in o:
                self.__pack(v)
        else:
            # TODO: Serialize with defalt() like simplejson.
            raise TypeError, "can't serialize %r" % (o,)

    def pack(self, obj, flush=True):
        self.__pack(obj)
        if flush:
            self.flush()

    close = flush

cdef int _packer_write(Packer packer, const_char_ptr b, unsigned int l):
    if packer.length + l > packer.allocated:
        if packer.length > 0:
            packer.strm.write(PyString_FromStringAndSize(packer.buff, packer.length))
        if l > packer.allocated/4:
            packer.strm.write(PyString_FromStringAndSize(b, l))
            packer.length = 0
        else:
            memcpy(packer.buff, b, l)
            packer.length = l
    else:
        memcpy(packer.buff + packer.length, b, l)
        packer.length += l
    return 0

def pack(object o, object stream):
    u"""pack o and write to stream)."""
    packer = Packer(stream)
    packer.pack(o)
    packer.flush()

def packb(object o):
    u"""pack o and return packed bytes."""
    buf = StringIO()
    packer = Packer(buf)
    packer.pack(o)
    return buf.getvalue()

packs = packb

cdef extern from "unpack.h":
    ctypedef struct template_context:
        PyObject* obj
        size_t count
        unsigned int ct
        PyObject* key

    int template_execute(template_context* ctx, const_char_ptr data,
            size_t len, size_t* off)
    void template_init(template_context* ctx)
    object template_data(template_context* ctx)


def unpacks(object packed_bytes):
    """Unpack packed_bytes to object. Returns unpacked object."""
    cdef const_char_ptr p = packed_bytes
    cdef template_context ctx
    cdef size_t off = 0
    cdef int ret
    template_init(&ctx)
    ret = template_execute(&ctx, p, len(packed_bytes), &off)
    if ret == 1:
        return template_data(&ctx)
    else:
        return None

def unpack(object stream):
    """unpack from stream."""
    packed = stream.read()
    return unpacks(packed)

cdef class UnpackIterator(object):
    cdef object unpacker

    def __init__(self, unpacker):
        self.unpacker = unpacker

    def __next__(self):
        return self.unpacker.unpack()

    def __iter__(self):
        return self

cdef class Unpacker(object):
    """Unpacker(file_like=None, read_size=4096)

    Streaming unpacker.
    file_like must have read(n) method.
    read_size is used like file_like.read(read_size)

    If file_like is None, you can feed() bytes. feed() is useful
    for unpack from non-blocking stream.

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

    def __init__(self, file_like=None, int read_size=4096):
        self.file_like = file_like
        self.read_size = read_size
        self.waiting_bytes = []
        self.buf = <char*>malloc(read_size)
        self.buf_size = read_size
        self.buf_head = 0
        self.buf_tail = 0
        template_init(&self.ctx)

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
            self.waiting_bytes.append(self.file_like.read(self.read_size))

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
            return template_data(&self.ctx)
        elif ret == 0:
            raise StopIteration, "No more unpack data."
        else:
            raise ValueError, "Unpack failed."

    def __iter__(self):
        return UnpackIterator(self)
