#
# MessagePack cross-language test tool
#
# $ gem install msgpack
# or
# $ port install rb_msgpack   # MacPorts
#
begin
require 'rubygems'
rescue LoadError
end
require 'msgpack'

def run(inio, outio)
	pac = MessagePack::Unpacker.new(inio)

	begin
		pac.each {|obj|
			outio.write MessagePack.pack(obj)
			outio.flush
		}
	rescue EOFError
		return 0
	rescue
		$stderr.puts $!
		return 1
	end

	return 0
end

def usage
	puts <<EOF
Usage: #{$0} [in-file] [out-file]

This tool is for testing of MessagePack implementation.
This does following behavior:

  1. Reads objects serialized by MessagePack from <in-file> (default: stdin)
  2. Re-serializes the objects using Ruby implementation of MessagePack (Note that Ruby implementation is considered valid)
  3. Writes the re-serialized objects into <out-file> (default: stdout)

EOF
	exit 1
end

inio = $stdin
outio = $stdout

if ARGV.length > 2
	usage
end

ARGV.each {|str|
	if str.size > 1 && str[0] == ?-
		usage
	end
}

if fname = ARGV[0]
	unless fname == "-"
		begin
			inio = File.open(fname)
		rescue
			puts "can't open output file: #{$!}"
			exit 1
		end
	end
end

if fname = ARGV[1]
	unless fname == "-"
		begin
			outio = File.open(fname, "w")
		rescue
			puts "can't open output file: #{$!}"
			exit 1
		end
	end
end

code = run(inio, outio)

inio.close
outio.close

exit code

