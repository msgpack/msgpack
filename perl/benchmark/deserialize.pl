use strict;
use warnings;
use Data::MessagePack;
use JSON;
use Storable;
use Benchmark ':all';

#$Data::MessagePack::PreferInteger = 1;

my $a = do 'benchmark/data.pl';

my $j = JSON::encode_json($a);
my $m = Data::MessagePack->pack($a);
my $s = Storable::freeze($a);

print "-- deserialize\n";
print "$JSON::Backend: ", $JSON::Backend->VERSION, "\n";
print "Data::MessagePack: $Data::MessagePack::VERSION\n";
print "Storable: $Storable::VERSION\n";
cmpthese timethese(
    -1 => {
        json     => sub { JSON::decode_json($j)     },
        mp       => sub { Data::MessagePack->unpack($m) },
        storable => sub { Storable::thaw($s) },
    }
);

