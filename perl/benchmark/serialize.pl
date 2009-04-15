use strict;
use warnings;
use Data::MessagePack;
use JSON::XS;
use Benchmark ':all';

my $a = [0..2**24];

print "-- serialize\n";
print "JSON::XS: $JSON::XS::VERSION\n";
print "Data::MessagePack: $Data::MessagePack::VERSION\n";
cmpthese(
    -1 => {
        json => sub { JSON::XS::encode_json($a)   },
        mp   => sub { Data::MessagePack->pack($a) },
    }
);

