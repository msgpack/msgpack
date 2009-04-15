use strict;
use warnings;
use Data::MessagePack;
use JSON::XS;
use Benchmark ':all';

my $a = [0..2**24];
my $j = JSON::XS::encode_json($a);
my $m = Data::MessagePack->pack($a);

print "-- deserialize\n";
print "JSON::XS: $JSON::XS::VERSION\n";
print "Data::MessagePack: $Data::MessagePack::VERSION\n";
cmpthese(
    -1 => {
        json => sub { JSON::XS::decode_json($j)     },
        mp   => sub { Data::MessagePack->unpack($m) },
    }
);

