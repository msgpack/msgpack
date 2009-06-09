# coding: utf-8

from cStringIO import StringIO

cdef extern from "Python.h":
    ctypedef char* const_char_ptr "const char*"
    ctypedef struct PyObject
    cdef object PyString_FromStringAndSize(const_char_ptr b, Py_ssize_t len)

cdef extern from "stdlib.h":
    void* malloc(int)
    void free(void*)

cdef extern from "string.h":
    int memcpy(char*dst, char*src, unsigned int size)

cdef extern from "pack.h":
    ctypedef int (*msgpack_packer_write)(void* data, const_char_ptr buf, unsigned int len)

    struct msgpack_packer:
        void *data
        msgpack_packer_write callback

    void msgpack_packer_init(msgpack_packer* pk, void* data, msgpack_packer_write callback)
    void msgpack_pack_int(msgpack_packer* pk, int d)
    void msgpack_pack_nil(msgpack_packer* pk)
    void msgpack_pack_true(msgpack_packer* pk)
    void msgpack_pack_false(msgpack_packer* pk)
    void msgpack_pack_long_long(msgpack_packer* pk, long long d)
    void msgpack_pack_double(msgpack_packer* pk, double d)
    void msgpack_pack_array(msgpack_packer* pk, size_t l)
    void msgpack_pack_map(msgpack_packer* pk, size_t l)
    void msgpack_pack_raw(msgpack_packer* pk, size_t l)
    void msgpack_pack_raw_body(msgpack_packer* pk, char* body, size_t l)


cdef int BUFF_SIZE=2*1024

cdef class Packer:
    """Packer that pack data into strm.

    strm must have `write(bytes)` method.
    size specifies local buffer size.
    """
    cdef char* buff
    cdef unsigned int length
    cdef unsigned int allocated
    cdef msgpack_packer pk
    cdef object strm

    def __init__(self, strm, int size=0):
        if size <= 0:
            size = BUFF_SIZE

        self.strm = strm
        self.buff = <char*> malloc(size)
        self.allocated = size
        self.length = 0

        msgpack_packer_init(&self.pk, <void*>self, <msgpack_packer_write>_packer_write)

    def __del__(self):
        free(self.buff);

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

        This code is same as below code:

            packer.pack(['foo', 'bar'])
        """
        msgpack_pack_array(&self.pk, len)

    def pack_dict(self, len):
        """Start packing key-value objects.

        Example:

            packer.pack_dict(1)
            packer.pack('foo')
            packer.pack('bar')

        This code is same as below code:

            packer.pack({'foo', 'bar'})
        """
        msgpack_pack_map(&self.pk, len)

    cdef __pack(self, object o):
        cdef long long intval
        cdef double fval
        cdef char* rawval 

        if o is None:
            msgpack_pack_nil(&self.pk)
        elif o is True:
            msgpack_pack_true(&self.pk)
        elif o is False:
            msgpack_pack_false(&self.pk)
        elif isinstance(o, long):
            intval = o
            msgpack_pack_long_long(&self.pk, intval)
        elif isinstance(o, int):
            intval = o
            msgpack_pack_long_long(&self.pk, intval)
        elif isinstance(o, float):
            fval = 9
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
        elif isinstance(o, dict):
            msgpack_pack_map(&self.pk, len(o))
            for k,v in o.iteritems():
                self.pack(k)
                self.pack(v)
        elif isinstance(o, tuple) or isinstance(o, list):
            msgpack_pack_array(&self.pk, len(o))
            for v in o:
                self.pack(v)
        else:
            # TODO: Serialize with defalt() like simplejson.
            raise TypeError, "can't serialize %r" % (o,)

    def pack(self, obj, flush=True):
        self.__pack(obj)
        if flush:
            self.flush()

cdef int _packer_write(Packer packer, const_char_ptr b, unsigned int l):
    if packer.length + l > packer.allocated:
        if packer.length > 0:
            packer.strm.write(PyString_FromStringAndSize(packer.buff, packer.length))
        if l > 64:
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
    packer = Packer(stream)
    packer.pack(o)
    packer.flush()

def packs(object o):
    buf = StringIO()
    packer = Packer(buf)
    packer.pack(o)
    packer.flush()
    return buf.getvalue()

cdef extern from "unpack.h":
    ctypedef struct template_context:
        pass
    int template_execute(template_context* ctx, const_char_ptr data,
            size_t len, size_t* off)
    void template_init(template_context* ctx)
    object template_data(template_context* ctx)


def unpacks(object packed_bytes):
    """Unpack packed_bytes to object. Returns unpacked object."""
    cdef const_char_ptr p = packed_bytes
    cdef template_context ctx
    cdef size_t off = 0
    template_init(&ctx)
    template_execute(&ctx, p, len(packed_bytes), &off)
    return template_data(&ctx)

def unpack(object stream):
    """unpack from stream."""
    packed = stream.read()
    return unpacks(packed)

cdef class Unpacker:
    """Do nothing. This function is for symmetric to Packer"""
    unpack = staticmethod(unpacks)
