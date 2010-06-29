begin
require 'rubygems'
rescue LoadError
end
require 'msgpack'

def usage
	puts <<EOF
Usage: #{$0} [out-file]

This tool is for testing of accepting MessagePack random-term.
This does following behavior:

  1. serializes the objects in this file, using Ruby implementation
     of MessagePack (Note that Ruby implementation is considered valid)
  2. Writes the serialized binaries into <out-file> (default: stdout)

EOF
	exit 1
end

code = 1
outio = $stdout

if ARGV.length > 2
	usage
end

if fname = ARGV[0]
	unless fname == "-"
		begin
			outio = File.open(fname, "w")
		rescue
			puts "can't open output file: #{$!}"
			exit 1
		end
	end
end

objs = [0, 1, 2, 123, 512, 1230, 678908,
        -1, -23, -512, -1230, -567898,
        "hogehoge", "243546rf7g68h798j",
        123.123,
       -234.4355, 1.0e-34, 1.0e64,
        [23, 234, 0.23],
        [0,42,"sum", [1,2]], [1,42, nil, [3]],
        { 1 => 2, "hoge" => nil },
        -234, -50000,
        42
       ]
begin
  objs.each do |obj|
    outio.write MessagePack.pack(obj)
    outio.flush
  end
rescue EOFError
  code=0
rescue
  $stderr.puts $!
  code=1
end

outio.close
exit code

