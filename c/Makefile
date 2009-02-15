
CFLAGS = -I.. -Wall -g -O4
LDFLAGS = -L.

all: bench

bench: pack.o unpack.o unpack_inline.o bench.o pack.h pack_inline.h unpack.h unpack_context.h
	$(CC) $(LDFLAGS) unpack.o unpack_inline.o pack.o bench.o -lyajl_s -o $@

bench_inline: pack.o bench_inline.o pack.h pack_inline.h
	$(CC) $(LDFLAGS) pack.o bench_inline.o -lyajl_s -o $@

.PHONY: clean
clean:
	$(RM) unpack.o unpack_inline.o pack.o test.o bench.o bench_inline.o
	$(RM) bench bench_inline

