#!/usr/bin/env python
# coding: utf-8
version = (0, 1, 5, 'final')

import os
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

msgpack_mod = Extension('msgpack._msgpack',
                        sources=sources,
                        )
del sources


desc = 'MessagePack (de)serializer.'
long_desc = """MessagePack (de)serializer for Python.

What's MessagePack? (from http://msgpack.sourceforge.net/)

 MessagePack is a binary-based efficient data interchange format that is
 focused on high performance. It is like JSON, but very fast and small.
"""

setup(name='msgpack-python',
      author='INADA Naoki',
      author_email='songofacandy@gmail.com',
      version=''.join(str(x) for x in version),
      cmdclass={'build_ext': build_ext, 'sdist': Sdist},
      ext_modules=[msgpack_mod],
      packages=['msgpack'],
      description=desc,
      long_description=long_desc,
      url='http://msgpack.sourceforge.net/',
      download_url='http://pypi.python.org/pypi/msgpack/',
      classifiers=[
          'Development Status :: 4 - Beta',
          'Intended Audience :: Developers',
          'License :: OSI Approved :: Apache Software License',
          ]
      )
