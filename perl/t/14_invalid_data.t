use strict;
use warnings;
use Data::MessagePack;
use Test::More;
use t::Util;

my $nil = Data::MessagePack->pack(undef);

my @data = do 't/data.pl';
while(my($dump, $data) = splice @data, 0, 2) {
    my $s = Data::MessagePack->pack($data);
    eval {
        Data::MessagePack->unpack($s . $nil);
    };
    like $@, qr/extra bytes/, "dump $dump";
}

done_testing;
