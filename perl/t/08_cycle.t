use t::Util;
use Test::More;
use Data::MessagePack;

plan tests => 6;

my $aref = [0];
$aref->[1] = $aref;
eval { Data::MessagePack->pack($aref) };
ok $@, $@;

my $href = {};
$href->{cycle} = $href;
eval { Data::MessagePack->pack($aref) };
ok $@, $@;

$aref = [0,[1,2]];
eval { Data::MessagePack->pack($aref) };
ok !$@;

eval { Data::MessagePack->pack($aref, 3) };
ok !$@;

eval { Data::MessagePack->pack($aref, 2) };
ok $@, $@;

eval { Data::MessagePack->pack($aref, -1) };
ok $@, $@;
