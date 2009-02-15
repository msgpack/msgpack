require 'mkmf'
$CFLAGS << " -I.. -Wall -O9"
create_makefile('msgpack')

