use strict;
use warnings;
use Data::MessagePack;
use JSON::XS;
use Benchmark ':all';
use Storable;

my $a = {
    "method" => "handleMessage",
    "params" => [ "user1", "we were just talking" ],
    "id"     => undef,
    "array"  => [ 1, 11, 234, -5, 1e5, 1e7, 1, 0 ]
};
my $j = JSON::XS::encode_json($a);
my $m = Data::MessagePack->pack($a);
my $s = Storable::freeze($a);

print "-- deserialize\n";
print "JSON::XS: $JSON::XS::VERSION\n";
print "Data::MessagePack: $Data::MessagePack::VERSION\n";
print "Storable: $Storable::VERSION\n";
timethese(
    1000000 => {
        json     => sub { JSON::XS::decode_json($j)     },
        mp       => sub { Data::MessagePack->unpack($m) },
        storable => sub { Storable::thaw($s) },
    }
);

