use strict;
use warnings;
use Data::MessagePack;
use JSON::XS;
use Storable;
use Benchmark ':all';

my $a = {
    "method" => "handleMessage",
    "params" => [ "user1", "we were just talking" ],
    "id"     => undef,
    "array"  => [ 1, 1024, 70000, -5, 1e5, 1e7, 1, 0, 3.14, sqrt(2) ],
};

print "-- serialize\n";
print "JSON::XS: $JSON::XS::VERSION\n";
print "Data::MessagePack: $Data::MessagePack::VERSION\n";
print "Storable: $Storable::VERSION\n";
cmpthese timethese(
    -1 => {
        json     => sub { JSON::XS::encode_json($a) },
        storable => sub { Storable::freeze($a) },
        mp       => sub { Data::MessagePack->pack($a) },
    }
);

