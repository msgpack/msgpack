
use strict;
use warnings;
use Test::More;
use Data::MessagePack;

$Data::MessagePack::Canonical = 1;

my $data = {
	'foo' => {
		'a' => '',
		'b' => '',
		'c' => '',
		'd' => '',
		'e' => '',
		'f' => '',
		'g' => '',
	}
};

my $packed1 = +Data::MessagePack->pack($data);
my $packed2 = +Data::MessagePack->pack(Data::MessagePack->unpack($packed1));
my $packed3 = +Data::MessagePack->pack(Data::MessagePack->unpack($packed2));
my $packed4 = +Data::MessagePack->pack(Data::MessagePack->unpack($packed3));
my $packed5 = +Data::MessagePack->pack(Data::MessagePack->unpack($packed4));

is $packed1, $packed2;
is $packed1, $packed3;
is $packed1, $packed4;
is $packed1, $packed5;

done_testing;
