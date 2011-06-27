0.1.10
======
:release date: NOT RELEASED YET

New feature
-----------
* Add ``encoding`` and ``unicode_errors`` option to packer and unpacker.
  When this option is specified, (un)packs unicode object instead of bytes.
  This enables using msgpack as a replacement of json.

0.1.9
======
:release date: 2011-01-29

New feature
-----------
* ``use_list`` option is added to unpack(b) like Unpacker.
  (Use keyword argument because order of parameters are different)

Bugs fixed
----------
* Fix typo.
* Add MemoryError check.

0.1.8
======
:release date: 2011-01-10

New feature
------------
* Support ``loads`` and ``dumps`` aliases for API compatibility with
  simplejson and pickle.

* Add *object_hook* and *list_hook* option to unpacker. It allows you to
  hook unpacing mapping type and array type.

* Add *default* option to packer. It allows you to pack unsupported types.

* unpacker accepts (old) buffer types.

Bugs fixed
----------
* Fix segv around ``Unpacker.feed`` or ``Unpacker(file)``.


0.1.7
======
:release date: 2010-11-02

New feature
------------
* Add *object_hook* and *list_hook* option to unpacker. It allows you to
  hook unpacing mapping type and array type.

* Add *default* option to packer. It allows you to pack unsupported types.

* unpacker accepts (old) buffer types.

Bugs fixed
----------
* Compilation error on win32.
