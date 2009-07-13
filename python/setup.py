#!/usr/bin/env python
# coding: utf-8

from distutils.core import setup, Extension
#from Cython.Distutils import build_ext
import os

version = '0.1.1'

msgpack_mod = Extension('msgpack._msgpack',
                        #sources=['msgpack/_msgpack.pyx']
                        sources=['msgpack/_msgpack.c']
                        )

desc = 'MessagePack (de)serializer.'
long_desc = desc + """

MessagePack_ (de)serializer for Python.

.. _MessagePack: http://msgpack.sourceforge.jp/

What's MessagePack? (from http://msgpack.sourceforge.jp/)

 MessagePack is a binary-based efficient data interchange format that is
 focused on high performance. It is like JSON, but very fast and small.
"""

setup(name='msgpack',
      author='Naoki INADA',
      author_email='songofacandy@gmail.com',
      version=version,
      #cmdclass={'build_ext': build_ext},
      ext_modules=[msgpack_mod],
      packages=['msgpack'],
      description=desc,
      long_description=long_desc,
      classifiers=[
          'Development Status :: 4 - Beta',
          'Intended Audience :: Developers',
          'License :: OSI Approved :: Apache Software License',
          ]
      )
