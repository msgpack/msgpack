require 'msgpack'

class Server
	def initialize(sock)
		@sock = sock
		@pk = MessagePack::Unpacker.new
		@buffer = ''
		@nread = 0
	end

	def run
		while true
			begin
				data = @sock.sysread(1024)
			rescue
				puts "connection closed (#{$!})"
				return
			end
			receive_data(data)
		end
	end

	private
	def receive_data(data)
		@buffer << data

		while true
			@nread = @pk.execute(@buffer, @nread)

			if @pk.finished?
				msg = @pk.data
				process_message(msg)

				@pk.reset
				@buffer.slice!(0, @nread)
				@nread = 0

				next unless @buffer.empty?
			end

			break
		end

		if @buffer.length > 10*1024*1024
			raise "message is too large"
		end

	rescue
		puts "error while processing client packet: #{$!}"
	end

	def process_message(msg)
		puts "message reached: #{msg.inspect}"
	end
end


rpipe, wpipe = IO.pipe

# run server thread
thread = Thread.new(Server.new(rpipe)) {|srv|
	srv.run
}

# client thread:
wpipe.write ["put", "apple", "red"].to_msgpack
wpipe.write ["put", "lemon", "yellow"].to_msgpack
wpipe.write ["get", "apple"].to_msgpack
wpipe.close

thread.join

