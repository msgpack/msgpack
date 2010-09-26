use strict;
use warnings;
use Test::More tests => 1;

use_ok 'Data::MessagePack';
diag ( "Testing Data::MessagePack/$Data::MessagePack::VERSION (",
    $INC{'Data/MessagePack/PP.pm'} ? 'PP' : 'XS', ")" );
