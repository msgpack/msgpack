
#CXXFLAGS = -I.. -I. -Wall -g
CXXFLAGS = -I.. -I. -Wall -g -O4
LDFLAGS = -L. $(CXXFLAGS)

NEED_PREPROCESS = zone.hpp

all: test bench

%.hpp: %.hpp.erb
	erb $< > $@

test: $(NEED_PREPROCESS) unpack.o unpack_inline.o object.o zone.o test.o object.hpp unpack.hpp pack.hpp
	$(CXX) $(LDFLAGS) unpack.o unpack_inline.o zone.o object.o test.o -o $@

bench: $(NEED_PREPROCESS) unpack.o unpack_inline.o object.o zone.o bench.o object.hpp unpack.hpp pack.hpp
	$(CXX) $(LDFLAGS) unpack.o unpack_inline.o zone.o object.o bench.o -o $@

.PHONY: clean
clean:
	$(RM) unpack.o unpack_inline.o object.o zone.o
	$(RM) test.o test
	$(RM) bench.o bench
	$(RM) $(NEED_PREPROCESS)

