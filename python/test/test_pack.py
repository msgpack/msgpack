#!/usr/bin/env python
# coding: utf-8

from nose import main
from nose.tools import *
from nose.plugins.skip import SkipTest

from msgpack import packs, unpacks

def check(data):
    re = unpacks(packs(data))
    assert_equal(re, data)

def testPack():
    test_data = [
            0, 1, 127, 128, 255, 256, 65535, 65536,
            -1, -32, -33, -128, -129, -32768, -32769,
            1.0,
        "", "a", "a"*31, "a"*32,
        None, True, False,
        (), ((),), ((), None,),
        {None: 0},
        (1<<23),
        ]
    for td in test_data:
        check(td)

def testPackUnicode():
    test_data = [
        u"", u"abcd", (u"defgh",), u"Русский текст",
        ]
    for td in test_data:
        re = unpacks(packs(td, encoding='utf-8'), encoding='utf-8')
        assert_equal(re, td)

def testPackUTF32():
    try:
        test_data = [
            u"", u"abcd", (u"defgh",), u"Русский текст",
            ]
        for td in test_data:
            re = unpacks(packs(td, encoding='utf-32'), encoding='utf-32')
            assert_equal(re, td)
    except LookupError:
        raise SkipTest

def testPackBytes():
    test_data = [
        "", "abcd", ("defgh",),
        ]
    for td in test_data:
        check(td)

def testIgnoreUnicodeErrors():
    re = unpacks(packs('abc\xeddef'),
        encoding='ascii', unicode_errors='ignore')
    assert_equal(re, "abcdef")

@raises(UnicodeDecodeError)
def testStrictUnicodeUnpack():
    unpacks(packs('abc\xeddef'), encoding='utf-8')

@raises(UnicodeEncodeError)
def testStrictUnicodePack():
    packs(u"abc\xeddef", encoding='ascii', unicode_errors='strict')

def testIgnoreErrorsPack():
    re = unpacks(
            packs(u"abcФФФdef", encoding='ascii', unicode_errors='ignore'),
            encoding='utf-8')
    assert_equal(re, u"abcdef")

@raises(TypeError)
def testNoEncoding():
    packs(u"abc", encoding=None)

def testDecodeBinary():
    re = unpacks(packs(u"abc"), encoding=None)
    assert_equal(re, "abc")

if __name__ == '__main__':
    main()
