
CFLAGS  += -Wall -g -I. -I.. -O4
LDFLAGS += -lyajl

all: bench

bench: bench.o pack.o unpack.o pack.h unpack.h
	$(CC) bench.o pack.o unpack.o $(CFLAGS) $(LDFLAGS) -o $@

