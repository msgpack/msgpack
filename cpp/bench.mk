
CXXFLAGS  += -Wall -g -I. -I.. -O4
LDFLAGS +=

all: bench

bench: bench.o unpack.o zone.o object.o pack.hpp unpack.hpp zone.hpp object.hpp
	$(CXX) bench.o unpack.o zone.o object.o $(CXXFLAGS) $(LDFLAGS) -o $@

