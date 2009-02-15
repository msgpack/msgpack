require 'msgpack'

def check(data)
	puts "---"
	pack = data.to_msgpack
	p data
	puts pack.unpack('C*').map{|x|"%02x"%x}.join(' ')
	re = MessagePack::unpack(pack)
	if re != data
		p re
		puts "** TEST FAILED **"
	end
end

check 0
check 1
check 127
check 128
check 255
check 256
check 65535
check 65536
check -1
check -128
check -129
check -32768
check -32769

check 1.0

check ""
check "a"
check "a"*31
check "a"*32

check nil
check true
check false

check []
check [[]]
check [[], nil]

check( {nil=>0} )

check (1<<23)
__END__

ary = []
i = 0
while i < (1<<16)
	ary << i
	i += 1
end
check ary

