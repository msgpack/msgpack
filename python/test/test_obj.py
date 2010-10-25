#!/usr/bin/env python
# coding: utf-8

from nose import main
from nose.tools import *

from msgpack import packs, unpacks

def _decode_complex(obj):
    if '__complex__' in obj:
        return complex(obj['real'], obj['imag'])
    return obj

def _encode_complex(obj):
    if isinstance(obj, complex):
        return {'__complex__': True, 'real': 1, 'imag': 2}
    return obj

def test_encode_hook():
    packed = packs([3, 1+2j], default=_encode_complex)
    unpacked = unpacks(packed)
    eq_(unpacked[1], {'__complex__': True, 'real': 1, 'imag': 2})

def test_decode_hook():
    packed = packs([3, {'__complex__': True, 'real': 1, 'imag': 2}])
    unpacked = unpacks(packed, object_hook=_decode_complex)
    eq_(unpacked[1], 1+2j)

if __name__ == '__main__':
    #main()
    test_decode_hook()
