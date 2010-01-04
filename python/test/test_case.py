#!/usr/bin/env python
# coding: utf-8

from nose import main
from nose.tools import *
from msgpack import packs, unpacks


def check(length, obj):
    v = packs(obj)
    assert_equal(len(v), length, "%r length should be %r but get %r" % (obj, length, len(v)))
    assert_equal(unpacks(v), obj)

def test_1():
    for o in [None, True, False, 0, 1, (1 << 6), (1 << 7) - 1, -1,
              -((1<<5)-1), -(1<<5)]:
        check(1, o)

def test_2():
    for o in [1 << 7, (1 << 8) - 1,
              -((1<<5)+1), -(1<<7)
             ]:
        check(2, o)

def test_3():
    for o in [1 << 8, (1 << 16) - 1,
              -((1<<7)+1), -(1<<15)]:
        check(3, o)

def test_5():
    for o in [1 << 16, (1 << 32) - 1,
              -((1<<15)+1), -(1<<31)]:
        check(5, o)

def test_9():
    for o in [1 << 32, (1 << 64) - 1,
              -((1<<31)+1), -(1<<63),
              1.0, 0.1, -0.1, -1.0]:
        check(9, o)


def check_raw(overhead, num):
    check(num + overhead, " " * num)

def test_fixraw():
    check_raw(1, 0)
    check_raw(1, (1<<5) - 1)

def test_raw16():
    check_raw(3, 1<<5)
    check_raw(3, (1<<16) - 1)

def test_raw32():
    check_raw(5, 1<<16)


def check_array(overhead, num):
    check(num + overhead, (None,) * num)

def test_fixarray():
    check_array(1, 0)
    check_array(1, (1 << 4) - 1)

def test_array16():
    check_array(3, 1 << 4)
    check_array(3, (1<<16)-1)

def test_array32():
    check_array(5, (1<<16))


def match(obj, buf):
    assert_equal(packs(obj), buf)
    assert_equal(unpacks(buf), obj)

def test_match():
    cases = [
        (None, '\xc0'),
        (False, '\xc2'),
        (True, '\xc3'),
        (0, '\x00'),
        (127, '\x7f'),
        (128, '\xcc\x80'),
        (256, '\xcd\x01\x00'),
        (-1, '\xff'),
        (-33, '\xd0\xdf'),
        (-129, '\xd1\xff\x7f'),
        ({1:1}, '\x81\x01\x01'),
        (1.0, "\xcb\x3f\xf0\x00\x00\x00\x00\x00\x00"),
        ((), '\x90'),
        (tuple(range(15)),"\x9f\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e"),
        (tuple(range(16)),"\xdc\x00\x10\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f"),
        ({}, '\x80'),
        (dict([(x,x) for x in range(15)]), '\x8f\x00\x00\x01\x01\x02\x02\x03\x03\x04\x04\x05\x05\x06\x06\x07\x07\x08\x08\t\t\n\n\x0b\x0b\x0c\x0c\r\r\x0e\x0e'),
        (dict([(x,x) for x in range(16)]), '\xde\x00\x10\x00\x00\x01\x01\x02\x02\x03\x03\x04\x04\x05\x05\x06\x06\x07\x07\x08\x08\t\t\n\n\x0b\x0b\x0c\x0c\r\r\x0e\x0e\x0f\x0f'),
        ]

    for v, p in cases:
        match(v, p)

if __name__ == '__main__':
    main()
