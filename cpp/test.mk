
CXXFLAGS  += -Wall -g -I. -I.. -O4
LDFLAGS +=

all: test

test: test.o unpack.o zone.o object.o pack.hpp unpack.hpp zone.hpp object.hpp
	$(CXX) test.o unpack.o zone.o object.o $(CXXFLAGS) $(LDFLAGS) -o $@

