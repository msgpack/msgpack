use strict;
use warnings;
use Test::More tests => 1;

use_ok 'Data::MessagePack';
diag ( $INC{'Data/MessagePack/PP.pm'} ? 'PP' : 'XS' );
