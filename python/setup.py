#!/usr/bin/env python
# coding: utf-8

from distutils.core import setup, Extension
from Cython.Distutils import build_ext
import os

version = '0.0.1dev'

PACKAGE_ROOT = os.getcwdu()
INCLUDE_PATH = os.path.join(PACKAGE_ROOT, 'include')
msgpack_mod = Extension('msgpack._msgpack',
                        sources=['msgpack/_msgpack.pyx'],
                        include_dirs=[INCLUDE_PATH])

desc = 'MessagePack serializer/desirializer.'
long_desc = desc + """

Python binding of MessagePack_.

This package is under development.

.. _MessagePack: http://msgpack.sourceforge.jp/

What's MessagePack? (from http://msgpack.sourceforge.jp/)

 MessagePack is a binary-based efficient data interchange format that is
 focused on high performance. It is like JSON, but very fast and small.
"""

setup(name='msgpack',
      author='Naoki INADA',
      author_email='songofacandy@gmail.com',
      version=version,
      cmdclass={'build_ext': build_ext},
      ext_modules=[msgpack_mod],
      packages=['msgpack'],
      description=desc,
      long_description=long_desc,
      )
