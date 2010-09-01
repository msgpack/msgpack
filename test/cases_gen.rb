#
# MessagePack format test case
#
begin
require 'rubygems'
rescue LoadError
end
require 'msgpack'
require 'json'

source = <<EOF
c2                          # false
c3                          # true
c0                          # nil
00                          # 0 Positive FixNum
cc 00                       # 0 uint8
cd 00 00                    # 0 uint16
ce 00 00 00 00              # 0 uint32
cf 00 00 00 00 00 00 00 00  # 0 uint64
d0 00                       # 0 int8
d1 00 00                    # 0 int16
d2 00 00 00 00              # 0 int32
d3 00 00 00 00 00 00 00 00  # 0 int64
ff                          # -1 Negative FixNum
d0 ff                       # -1 int8
d1 ff ff                    # -1 int16
d2 ff ff ff ff              # -1 int32
d3 ff ff ff ff ff ff ff ff  # -1 int64
7f                          # 127 Positive FixNum
cc 7f                       # 127 uint8
cd 00 ff                    # 255 uint16
ce 00 00 ff ff              # 65535 uint32
cf 00 00 00 00 ff ff ff ff  # 4294967295 uint64
e0                          # -32 Negative FixNum
d0 e0                       # -32 int8
d1 ff 80                    # -128 int16
d2 ff ff 80 00              # -32768 int32
d3 ff ff ff ff 80 00 00 00  # -2147483648 int64
#ca 00 00 00 00              # 0.0 float
cb 00 00 00 00 00 00 00 00  # 0.0 double
#ca 80 00 00 00              # -0.0 float
cb 80 00 00 00 00 00 00 00  # -0.0 double
cb 3f f0 00 00 00 00 00 00  # 1.0 double
cb bf f0 00 00 00 00 00 00  # -1.0 double
a1 61                       # "a" FixRaw
da 00 01 61                 # "a" raw 16
db 00 00 00 01 61           # "a" raw 32
a0                          # "" FixRaw
da 00 00                    # "" raw 16
db 00 00 00 00              # "" raw 32
91 00                       # [0] FixArray
dc 00 01 00                 # [0] array 16
dd 00 00 00 01 00           # [0] array 32
90                          # [] FixArray
dc 00 00                    # [] array 16
dd 00 00 00 00              # [] array 32
80                          # {} FixMap
de 00 00                    # {} map 16
df 00 00 00 00              # {} map 32
81 a1 61 61                 # {"a"=>97} FixMap
de 00 01 a1 61 61           # {"a"=>97} map 16
df 00 00 00 01 a1 61 61     # {"a"=>97} map 32
91 90                       # [[]]
91 91 a1 61                 # [["a"]]
EOF

source.gsub!(/\#.+$/,'')
bytes = source.strip.split(/\s+/).map {|x| x.to_i(16) }.pack('C*')

objs = []
compact_bytes = ""

pac = MessagePack::Unpacker.new
pac.feed(bytes)
pac.each {|obj|
	p obj
	objs << obj
	compact_bytes << obj.to_msgpack
}

json = objs.to_json

# self check
cpac = MessagePack::Unpacker.new
cpac.feed(compact_bytes)
cpac.each {|cobj|
	obj = objs.shift
	if obj != cobj
		puts "** SELF CHECK FAILED **"
		puts "expected: #{obj.inspect}"
		puts "actual: #{cobj.inspect}"
		exit 1
	end
}

File.open("cases.mpac","w") {|f| f.write(bytes) }
File.open("cases_compact.mpac","w") {|f| f.write(compact_bytes) }
File.open("cases.json","w") {|f| f.write(json) }

