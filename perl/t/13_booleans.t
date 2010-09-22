#!perl -w
use strict;
use Test::More tests => 6;
use Data::MessagePack;

ok defined(Data::MessagePack::true()), 'true (1)';
ok defined(Data::MessagePack::true()), 'true (2)';
ok Data::MessagePack::true(),          'true is true';

ok defined(Data::MessagePack::false()), 'false (1)';
ok defined(Data::MessagePack::false()), 'false (2)';
ok !Data::MessagePack::false(),         'false is false';
