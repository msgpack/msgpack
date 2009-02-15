require 'rubygems'
require 'json'
require 'msgpack'

def show10(str)
	puts "#{str.length/1024} KB"
	puts str[0, 10].unpack('C*').map{|x|"%02x"%x}.join(' ') + " ..."
end

ary = []
i = 0
while i < (1<<24)
	#ary << (1<<24)
	ary << i
	i += 1
end

GC.start

puts "----"
puts "MessagePack"
a = Time.now
packed = MessagePack::pack(ary)
b = Time.now
show10(packed)
sec = b - a
puts "#{sec} sec."
puts "#{packed.length.to_f / sec / 1024 / 1024 * 8} Mbps"

GC.start

=begin
puts "----"
puts "JSON"
a = Time.now
json = ary.to_json
b = Time.now
show10(json)
puts "#{b-a} sec."

ary = nil
GC.start
=end


puts "----"
puts "MessagePack"
a = Time.now
ary = MessagePack::unpack(packed)
b = Time.now
sec = b - a
puts "#{sec} sec."
puts "#{packed.length.to_f / sec / 1024 / 1024 * 8} Mbps"

p ary.size
p (1<<24)

ary = nil
GC.start


=begin
puts "----"
puts "JSON"
a = Time.now
ary = JSON::load(json)
b = Time.now
puts "#{b-a} sec."
=end

