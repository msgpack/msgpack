use strict;
use warnings;
use Test::More;
use Data::MessagePack;

my @data = ( [ 1, 2, 3 ], [ 4, 5, 6 ] );

# serialize
my $buffer = '';
for my $d (@data) {
    $buffer .= Data::MessagePack->pack($d);
}

# deserialize
my $cb = sub {
    my ($data) = @_;

    my $d = shift @data;
    is_deeply $data, $d;
};
my $unpacker = Data::MessagePack::Unpacker->new();
my $nread = 0;
while (1) {
    $nread = $unpacker->execute( $buffer, $nread );
    if ( $unpacker->is_finished ) {
        my $ret = $unpacker->data;
        $cb->( $ret );
        $unpacker->reset;

        $buffer = substr( $buffer, $nread );
        $nread = 0;
        next if length($buffer) != 0;
    }
    last;
}
is scalar(@data), 0;

done_testing;

