#!/usr/bin/env python
# coding: utf-8

from nose import main
from nose.tools import *

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

if __name__ == '__main__':
    main()
