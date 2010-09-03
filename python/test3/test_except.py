#!/usr/bin/env python
# coding: utf-8

from nose.tools import *
from msgpack import packs, unpacks

import datetime

def test_raise_on_find_unsupported_value():
    assert_raises(TypeError, packs, datetime.datetime.now())

if __name__ == '__main__':
    from nose import main
    main()
