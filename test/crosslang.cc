//
// MessagePack cross-language test tool
//
// $ cd ../cpp && ./configure && make && make install
// or
// $ port install msgpack  # MacPorts
//
// $ g++ -Wall -lmsgpack crosslang.cc
//
#include <msgpack.hpp>
#include <iostream>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>

static int run(int infd, int outfd)
try {
	msgpack::unpacker pac;

	while(true) {
		pac.reserve_buffer(32*1024);

		ssize_t count =
			read(infd, pac.buffer(), pac.buffer_capacity());

		if(count <= 0) {
			if(count == 0) {
				return 0;
			}
			if(errno == EAGAIN || errno == EINTR) {
				continue;
			}
			return 1;
		}

		pac.buffer_consumed(count);

		msgpack::unpacked result;
		while(pac.next(&result)) {
			msgpack::sbuffer sbuf;
			msgpack::pack(sbuf, result.get());

			const char* p = sbuf.data();
			const char* const pend = p + sbuf.size();
			while(p < pend) {
				ssize_t bytes = write(outfd, p, pend-p);

				if(bytes <= 0) {
					if(count == 0) {
						return 0;
					}
					if(errno == EAGAIN || errno == EINTR) {
						continue;
					}
					return 1;
				}

				p += bytes;
			}

		}
	}

	return 0;

} catch (std::exception& e) {
	std::cerr << e.what() << std::endl;
	return 1;
}

static void usage(const char* prog)
{
	printf(
		"Usage: %s [in-file] [out-file]\n"
		"\n"
		"This tool is for testing of MessagePack implementation.\n"
		"This does following behavior:\n"
		"\n"
		"  1. Reads objects serialized by MessagePack from <in-file> (default: stdin)\n"
		"  2. Re-serializes the objects using C++ implementation of MessagePack (Note that C++ implementation is considered valid)\n"
		"  3. Writes the re-serialized objects into <out-file> (default: stdout)\n"
		"\n"
		, prog);
	exit(1);
}

int main(int argc, char* argv[])
{
	int infd = 0;
	int outfd = 1;

	if(argc < 1 || argc > 3) {
		usage(argv[0]);
	}

	for(int i=1; i < argc; ++i) {
		if(strlen(argv[i]) > 1 && argv[i][0] == '-') {
			usage(argv[0]);
		}
	}

	if(argc >= 2) {
		const char* fname = argv[1];
		if(strcmp(fname, "-") != 0) {
			infd = open(fname, O_RDONLY);
			if(infd < 0) {
				perror("can't open input file");
				exit(1);
			}
		}
	}

	if(argc >= 3) {
		const char* fname = argv[2];
		if(strcmp(fname, "-") != 0) {
			outfd = open(fname, O_WRONLY | O_CREAT| O_TRUNC, 0666);
			if(outfd < 0) {
				perror("can't open output file");
				exit(1);
			}
		}
	}

	int code = run(infd, outfd);

	close(infd);
	close(outfd);

	return code;
}

