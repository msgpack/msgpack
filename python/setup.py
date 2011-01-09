#!/usr/bin/env python
# coding: utf-8
version = (0, 1, 8, 'final')

import os
import sys
from glob import glob
from distutils.core import setup, Extension
from distutils.command.sdist import sdist

try:
    from Cython.Distutils import build_ext
    import Cython.Compiler.Main as cython_compiler
    have_cython = True
except ImportError:
    from distutils.command.build_ext import build_ext
    have_cython = False

# make msgpack/__verison__.py
f = open('msgpack/__version__.py', 'w')
f.write("version = %r\n" % (version,))
f.close()
del f

version_str = '.'.join(str(x) for x in version[:3])
if len(version) > 3 and version[3] != 'final':
    version_str += version[3]

# take care of extension modules.
if have_cython:
    sources = ['msgpack/_msgpack.pyx']

    class Sdist(sdist):
        def __init__(self, *args, **kwargs):
            for src in glob('msgpack/*.pyx'):
                cython_compiler.compile(glob('msgpack/*.pyx'),
                                        cython_compiler.default_options)
            sdist.__init__(self, *args, **kwargs)
else:
    sources = ['msgpack/_msgpack.c']

    for f in sources:
        if not os.path.exists(f):
            raise ImportError("Building msgpack from VCS needs Cython. Install Cython or use sdist package.")

    Sdist = sdist

libraries = ['ws2_32'] if sys.platform == 'win32' else []

msgpack_mod = Extension('msgpack._msgpack',
                        sources=sources,
                        libraries=libraries,
                        )
del sources, libraries


desc = 'MessagePack (de)serializer.'
long_desc = """MessagePack (de)serializer for Python.

What's MessagePack? (from http://msgpack.org/)

 MessagePack is a binary-based efficient data interchange format that is
 focused on high performance. It is like JSON, but very fast and small.
"""

setup(name='msgpack-python',
      author='INADA Naoki',
      author_email='songofacandy@gmail.com',
      version=version_str,
      cmdclass={'build_ext': build_ext, 'sdist': Sdist},
      ext_modules=[msgpack_mod],
      packages=['msgpack'],
      description=desc,
      long_description=long_desc,
      url='http://msgpack.org/',
      download_url='http://pypi.python.org/pypi/msgpack/',
      classifiers=[
          'Programming Language :: Python :: 2',
          'Programming Language :: Python :: 3',
          'Development Status :: 4 - Beta',
          'Intended Audience :: Developers',
          'License :: OSI Approved :: Apache Software License',
          ]
      )
