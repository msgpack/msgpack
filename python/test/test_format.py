#!/usr/bin/env python
# coding: utf-8

from nose import main
from nose.tools import *
from msgpack import unpacks

def check(src, should):
    assert_equal(unpacks(src), should)

def testSimpleValue():
    check("\x93\xc0\xc2\xc3", 
            (None, False, True,))

def testFixnum():
    check("\x92\x93\x00\x40\x7f\x93\xe0\xf0\xff",
          ((0,64,127,), (-32,-16,-1,),)
          )

def testFixArray():
    check("\x92\x90\x91\x91\xc0",
          ((),((None,),),),
          )

def testFixRaw():
    check("\x94\xa0\xa1a\xa2bc\xa3def",
          ("", "a", "bc", "def",),
          )

def testFixMap():
    check(
          "\x82\xc2\x81\xc0\xc0\xc3\x81\xc0\x80",
          {False: {None: None}, True:{None:{}}},
          )

def testUnsignedInt():
    check(
          "\x99\xcc\x00\xcc\x80\xcc\xff\xcd\x00\x00\xcd\x80\x00"
          "\xcd\xff\xff\xce\x00\x00\x00\x00\xce\x80\x00\x00\x00"
          "\xce\xff\xff\xff\xff",
          (0, 128, 255, 0, 32768, 65535, 0, 2147483648, 4294967295,),
          )

def testSignedInt():
    check("\x99\xd0\x00\xd0\x80\xd0\xff\xd1\x00\x00\xd1\x80\x00"
          "\xd1\xff\xff\xd2\x00\x00\x00\x00\xd2\x80\x00\x00\x00"
          "\xd2\xff\xff\xff\xff",
          (0, -128, -1, 0, -32768, -1, 0, -2147483648, -1,))

def testRaw():
    check("\x96\xda\x00\x00\xda\x00\x01a\xda\x00\x02ab\xdb\x00\x00"
        "\x00\x00\xdb\x00\x00\x00\x01a\xdb\x00\x00\x00\x02ab",
        ("", "a", "ab", "", "a", "ab"))

def testArray():
    check("\x96\xdc\x00\x00\xdc\x00\x01\xc0\xdc\x00\x02\xc2\xc3\xdd\x00"
        "\x00\x00\x00\xdd\x00\x00\x00\x01\xc0\xdd\x00\x00\x00\x02"
        "\xc2\xc3",
        ((), (None,), (False,True), (), (None,), (False,True))
        )

def testMap():
    check(
        "\x96"
            "\xde\x00\x00"
            "\xde\x00\x01\xc0\xc2"
            "\xde\x00\x02\xc0\xc2\xc3\xc2"
            "\xdf\x00\x00\x00\x00"
            "\xdf\x00\x00\x00\x01\xc0\xc2"
            "\xdf\x00\x00\x00\x02\xc0\xc2\xc3\xc2",
        ({}, {None: False}, {True: False, None: False}, {},
            {None: False}, {True: False, None: False}))

if __name__ == '__main__':
    main()
