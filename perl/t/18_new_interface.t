#!perl
use strict;
use warnings;

use Test::More;

use Data::MessagePack;

my $mp = Data::MessagePack->new();

is_deeply $mp->decode( $mp->encode(\%ENV) ), \%ENV;


done_testing;

