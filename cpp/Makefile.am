SUBDIRS = src test

DOC_FILES = \
		README.md \
		LICENSE \
		NOTICE \
		msgpack_vc8.vcproj \
		msgpack_vc8.sln \
		msgpack_vc2008.vcproj \
		msgpack_vc2008.sln \
		msgpack_vc.postbuild.bat

EXTRA_DIST = \
		$(DOC_FILES)

doxygen:
	./preprocess clean
	cd src && $(MAKE) doxygen
	./preprocess

