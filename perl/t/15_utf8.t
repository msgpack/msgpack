#!perl -w
use strict;
use Test::More;
use Data::MessagePack;
use utf8;

my $data = [42, undef, 'foo', "\x{99f1}\x{99dd}"];
my $packed = Data::MessagePack->pack($data);

my $u = Data::MessagePack::Unpacker->new()->utf8();
ok $u->get_utf8();
$u->execute($packed);
my $d = $u->data();
$u->reset();
is_deeply $d, $data, 'decoded';

is $u->utf8(0), $u, 'utf8(0)';
ok !$u->get_utf8();
$u->execute($packed);
$d = $u->data();
$u->reset();
my $s = $data->[3];
utf8::encode($s);
is_deeply $d->[3], $s, 'not decoded';

done_testing;

