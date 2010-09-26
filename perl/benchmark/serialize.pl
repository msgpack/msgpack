use strict;
use warnings;
use Data::MessagePack;
use JSON;
use Storable;
use Benchmark ':all';

my $a = do 'benchmark/data.pl';

print "-- serialize\n";
print "$JSON::Backend: ", $JSON::Backend->VERSION, "\n";
print "Data::MessagePack: $Data::MessagePack::VERSION\n";
print "Storable: $Storable::VERSION\n";
cmpthese timethese(
    -1 => {
        json     => sub { JSON::encode_json($a) },
        storable => sub { Storable::freeze($a) },
        mp       => sub { Data::MessagePack->pack($a) },
    }
);

