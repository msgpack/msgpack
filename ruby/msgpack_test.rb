#!/usr/bin/env ruby
require 'msgpack'
require 'test/unit'

class MessagePackTestFormat < Test::Unit::TestCase
	def self.it(name, &block)
		define_method("test_#{name}", &block)
	end

	it "nil" do
		check 1, nil
	end

	it "true" do
		check 1, true
	end

	it "false" do
		check 1, false
	end

	it "zero" do
		check 1, 0
	end

	it "positive fixnum" do
		check 1, 1
		check 1, (1<<6)
		check 1, (1<<7)-1
	end

	it "positive int 8" do
		check 1, -1
		check 2, (1<<7)
		check 2, (1<<8)-1
	end

	it "positive int 16" do
		check 3, (1<<8)
		check 3, (1<<16)-1
	end

	it "positive int 32" do
		check 5, (1<<16)
		check 5, (1<<32)-1
	end

	it "positive int 64" do
		check 9, (1<<32)
		check 9, (1<<64)-1
	end

	it "negative fixnum" do
		check 1, -1
		check 1, -((1<<5)-1)
		check 1, -(1<<5)
	end

	it "negative int 8" do
		check 2, -((1<<5)+1)
		check 2, -(1<<7)
	end

	it "negative int 16" do
		check 3, -((1<<7)+1)
		check 3, -(1<<15)
	end

	it "negative int 32" do
		check 5, -((1<<15)+1)
		check 5, -(1<<31)
	end

	it "negative int 64" do
		check 9, -((1<<31)+1)
		check 9, -(1<<63)
	end

	it "double" do
		check 9, 1.0
		check 9, 0.1
		check 9, -0.1
		check 9, -1.0
	end

	it "fixraw" do
		check_raw 1, 0
		check_raw 1, (1<<5)-1
	end

	it "raw 16" do
		check_raw 3, (1<<5)
		check_raw 3, (1<<16)-1
	end

	it "raw 32" do
		check_raw 5, (1<<16)
		#check_raw 5, (1<<32)-1  # memory error
	end

	it "fixarray" do
		check_array 1, 0
		check_array 1, (1<<4)-1
	end

	it "array 16" do
		check_array 3, (1<<4)
		check_array 3, (1<<16)-1
	end

	it "array 32" do
		check_array 5, (1<<16)
		#check_array 5, (1<<32)-1  # memory error
	end

	it "nil" do
		match nil, "\xc0"
	end

	it "false" do
		match false, "\xc2"
	end

	it "true" do
		match true, "\xc3"
	end

	it "0" do
		match 0, "\x00"
	end

	it "127" do
		match 127, "\x7f"
	end

	it "128" do
		match 128, "\xcc\x80"
	end

	it "256" do
		match 256, "\xcd\x01\x00"
	end

	it "-1" do
		match -1, "\xff"
	end

	it "-33" do
		match -33, "\xd0\xdf"
	end

	it "-129" do
		match -129, "\xd1\xff\x7f"
	end

	it "{1=>1}" do
		match ({1=>1}), "\x81\x01\x01"
	end

	it "1.0" do
		match 1.0, "\xcb\x3f\xf0\x00\x00\x00\x00\x00\x00"
	end

	it "[]" do
		match [], "\x90"
	end

	it "[0, 1, ..., 14]" do
		match (0..14).to_a, "\x9f\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e"
	end

	it "[0, 1, ..., 15]" do
		match (0..15).to_a, "\xdc\x00\x10\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f"
	end

	it "{}" do
		match ({}), "\x80"
	end

	it "{0=>0, 1=>1, ..., 14=>14}" do
		a = (0..14).to_a;
		match Hash[*a.zip(a).flatten], "\x8f\x05\x05\x0b\x0b\x00\x00\x06\x06\x0c\x0c\x01\x01\x07\x07\x0d\x0d\x02\x02\x08\x08\x0e\x0e\x03\x03\x09\x09\x04\x04\x0a\x0a"
	end

	it "{0=>0, 1=>1, ..., 15=>15}" do
		a = (0..15).to_a;
		match Hash[*a.zip(a).flatten], "\xde\x00\x10\x05\x05\x0b\x0b\x00\x00\x06\x06\x0c\x0c\x01\x01\x07\x07\x0d\x0d\x02\x02\x08\x08\x0e\x0e\x03\x03\x09\x09\x0f\x0f\x04\x04\x0a\x0a"
	end

#	it "fixmap" do
#		check_map 1, 0
#		check_map 1, (1<<4)-1
#	end
#
#	it "map 16" do
#		check_map 3, (1<<4)
#		check_map 3, (1<<16)-1
#	end
#
#	it "map 32" do
#		check_map 5, (1<<16)
#		#check_map 5, (1<<32)-1  # memory error
#	end

	it "gc mark" do
		obj = [{["a","b"]=>["c","d"]}, ["e","f"], "d"]
		pac = MessagePack::Unpacker.new
		parsed = 0
		obj.to_msgpack.split(//).each do |b|
			pac.feed(b)
			pac.each {|o|
				GC.start
				assert_equal(obj, o)
				parsed += 1
			}
			GC.start
		end
		assert_equal(parsed, 1)
	end

	private
	def check(len, obj)
		v = obj.to_msgpack
		assert_equal(v.length, len)
		assert_equal(MessagePack.unpack(v), obj)
	end

	def check_raw(overhead, num)
		check num+overhead, " "*num
	end

	def check_array(overhead, num)
		check num+overhead, Array.new(num)
	end

	def match(obj, buf)
		assert_equal(obj.to_msgpack, buf)
		assert_equal(MessagePack::unpack(buf), obj)
	end
end

