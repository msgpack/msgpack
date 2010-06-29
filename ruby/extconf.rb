require 'mkmf'
require './version.rb'
$CFLAGS << %[ -I.. -Wall -O4 -DMESSAGEPACK_VERSION=\\"#{MessagePack::VERSION}\\"]
create_makefile('msgpack')

