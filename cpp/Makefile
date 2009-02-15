
CXXFLAGS = -I.. -I. -Wall -g
#CXXFLAGS = -I.. -I. -Wall -g -O4
LDFLAGS = -L.

NEED_PREPROCESS = zone.hpp

all: test

%.hpp: %.hpp.erb
	erb $< > $@

test: $(NEED_PREPROCESS) unpack.o unpack_inline.o object.o zone.o test.o object.hpp unpack.hpp pack.hpp
	$(CXX) $(LDFLAGS) unpack.o unpack_inline.o zone.o object.o test.o -o $@

.PHONY: clean
clean:
	$(RM) unpack.o unpack_inline.o object.o zone.o
	$(RM) test.o
	$(RM) test
	$(RM) $(NEED_PREPROCESS)

