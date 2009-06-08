from distutils.core import setup, Extension

version = '0.0.1'

msgpack_mod = Extension('msgpack', sources=['msgpack.c'])

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
      ext_modules=[msgpack_mod],
      description=desc,
      long_description=long_desc,
      )
