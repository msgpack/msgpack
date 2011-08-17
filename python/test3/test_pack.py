#!/usr/bin/env python
# coding: utf-8

from nose import main
from nose.tools import *

from msgpack import packs, unpacks, Unpacker, Packer

from io import BytesIO

def check(data):
    re = unpacks(packs(data))
    assert_equal(re, data)

def testPack():
    test_data = [
            0, 1, 127, 128, 255, 256, 65535, 65536,
            -1, -32, -33, -128, -129, -32768, -32769,
            1.0,
        b"", b"a", b"a"*31, b"a"*32,
        None, True, False,
        (), ((),), ((), None,),
        {None: 0},
        (1<<23),
        ]
    for td in test_data:
        check(td)

def testPackUnicode():
    test_data = [
        "", "abcd", ("defgh",), "Русский текст",
        ]
    for td in test_data:
        re = unpacks(packs(td, encoding='utf-8'), encoding='utf-8')
        assert_equal(re, td)
        packer = Packer(encoding='utf-8')
        data = packer.pack(td)
        re = Unpacker(BytesIO(data), encoding='utf-8').unpack()
        assert_equal(re, td)

def testPackUTF32():
    test_data = [
        "", "abcd", ("defgh",), "Русский текст",
        ]
    for td in test_data:
        re = unpacks(packs(td, encoding='utf-32'), encoding='utf-32')
        assert_equal(re, td)

def testPackBytes():
    test_data = [
        b"", b"abcd", (b"defgh",),
        ]
    for td in test_data:
        check(td)

def testIgnoreUnicodeErrors():
    re = unpacks(packs(b'abc\xeddef'),
        encoding='utf-8', unicode_errors='ignore')
    assert_equal(re, "abcdef")

@raises(UnicodeDecodeError)
def testStrictUnicodeUnpack():
    unpacks(packs(b'abc\xeddef'), encoding='utf-8')

@raises(UnicodeEncodeError)
def testStrictUnicodePack():
    packs("abc\xeddef", encoding='ascii', unicode_errors='strict')

def testIgnoreErrorsPack():
    re = unpacks(packs("abcФФФdef", encoding='ascii', unicode_errors='ignore'), encoding='utf-8')
    assert_equal(re, "abcdef")

@raises(TypeError)
def testNoEncoding():
    packs("abc", encoding=None)

def testDecodeBinary():
    re = unpacks(packs("abc"), encoding=None)
    assert_equal(re, b"abc")

if __name__ == '__main__':
    main()
