require 'mkmf'
require './version.rb'
$CFLAGS << %[ -I.. -Wall -O3 -DMESSAGEPACK_VERSION=\\"#{MessagePack::VERSION}\\" -g]
have_header("ruby/st.h")
create_makefile('msgpack')

