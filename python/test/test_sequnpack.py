#!/usr/bin/env python
# coding: utf-8

from __future__ import unicode_literals, print_function

from msgpack import Unpacker

def test_foobar():
    unpacker = Unpacker(read_size=3)
    unpacker.feed(b'foobar')
    assert unpacker.unpack() == ord('f')
    assert unpacker.unpack() == ord('o')
    assert unpacker.unpack() == ord('o')
    assert unpacker.unpack() == ord('b')
    assert unpacker.unpack() == ord('a')
    assert unpacker.unpack() == ord('r')
    try:
        o = unpacker.unpack()
        print("Oops!", o)
        assert 0
    except StopIteration:
        assert 1
    else:
        assert 0
    unpacker.feed(b'foo')
    unpacker.feed(b'bar')

    k = 0
    for o, e in zip(unpacker, b'foobarbaz'):
        assert o == ord(e)
        k += 1
    assert k == len(b'foobar')

if __name__ == '__main__':
    test_foobar()

