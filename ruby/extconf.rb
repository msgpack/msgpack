require 'mkmf'
$CFLAGS << " -I.. -Wall -O4"
create_makefile('msgpack')

