#!/usr/bin/env python
# coding: utf-8

from msgpack import Unpacker

def test_foobar():
    unpacker = Unpacker(read_size=3)
    unpacker.feed('foobar')
    assert unpacker.unpack() == ord('f')
    assert unpacker.unpack() == ord('o')
    assert unpacker.unpack() == ord('o')
    assert unpacker.unpack() == ord('b')
    assert unpacker.unpack() == ord('a')
    assert unpacker.unpack() == ord('r')
    try:
        o = unpacker.unpack()
        print "Oops!", o
        assert 0
    except StopIteration:
        assert 1
    else:
        assert 0
    unpacker.feed('foo')
    unpacker.feed('bar')

    k = 0
    for o, e in zip(unpacker, 'foobarbaz'):
        assert o == ord(e)
        k += 1
    assert k == len('foobar')

if __name__ == '__main__':
    test_foobar()

