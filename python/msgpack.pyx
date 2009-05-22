# coding: utf-8


cdef extern from "Python.h":
    ctypedef char* const_char_ptr "const char*"
    cdef object PyString_FromStringAndSize(const_char_ptr b, Py_ssize_t len)

cdef extern from "stdlib.h":
    void* malloc(int)
    void free(void*)
cdef extern from "string.h":
    int memcpy(char*dst, char*src, unsigned int size)

cdef extern from "msgpack/pack.h":
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

cdef extern from "msgpack/unpack.h":
    ctypedef struct msgpack_unpacker


cdef int BUFF_SIZE=2*1024

cdef class Packer:
    cdef char* buff
    cdef unsigned int length
    cdef unsigned int allocated
    cdef msgpack_packer pk
    cdef object strm

    def __init__(self, strm, int size=0):
        """Make packer that pack data into strm.

        strm must have `write(bytes)` method.
        size specifies local buffer size.
        """
        if size <= 0:
            size = BUFF_SIZE

        self.strm = strm
        self.buff = <char*> malloc(size)
        self.allocated = size
        self.length = 0

        msgpack_packer_init(&self.pk, <void*>self, <msgpack_packer_write>_packer_write)


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

    def __call__(self, object o):
        cdef long long intval
        cdef double fval
        cdef char* rawval 

        if o is None:
            msgpack_pack_nil(&self.pk)
        elif o is True:
            msgpack_pack_true(&self.pk)
        elif o is False:
            msgpack_pack_false(&self.pk)
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
            # todo
            pass
        elif isinstance(o, dict):
            msgpack_pack_map(&self.pk, len(o))
            for k,v in o.iteritems():
                self(k)
                self(v)
        elif isinstance(o, tuple):
            msgpack_pack_array(&self.pk, len(o))
            for v in o:
                self(v)
        elif isinstance(o, list):
            msgpack_pack_array(&self.pk, len(o))
            for v in o:
                self(v)
        elif hasattr(o, "__msgpack__"):
            o.__msgpack__(self)
        else:
            raise TypeError, "can't serialize %r" % (o,)

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

cdef class Unpacker:
    def __init__(self):
        pass
    def unpack(strm):
        pass
