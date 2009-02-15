require 'test/unit'
require 'msgpack'

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

	def check_map(overhead, num)
		# FIXME
	end
end

