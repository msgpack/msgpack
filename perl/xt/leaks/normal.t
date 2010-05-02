use strict;
use warnings;
use Test::More;
use Data::MessagePack;
use Devel::Peek;

plan skip_all => '$ENV{LEAK_TEST} is required' unless $ENV{LEAK_TEST};

my $input = [
    {
        "ZCPGBENCH-1276933268" =>
            { "1271859210" => [ "\x14\x02\x07\x00\x00", 1 ] },
        "VDORBENCH-5637665303" =>
            { "1271859210" => [ "\x00\x01\x00\x01\x00", 1 ] },
        "ZVTHBENCH-7648578738" => {
            "1271859210" => [
                "\x0a\x02\x04\x00\x00", "2600",
                "\x0a\x05\x04\x00\x00", "4600"
            ]
        },
        "VMVTBENCH-5237337637" =>
            { "1271859210" => [ "\x00\x01\x00\x01\x00", 1 ] },
        "ZPLSBENCH-1823993880" =>
            { "1271859210" => [ "\x01\x07\x07\x03\x06", "10001" ] },
        "ZCPGBENCH-1995524375" =>
            { "1271859210" => [ "\x14\x02\x07\x00\x00", 1 ] },
        "ZCPGBENCH-2330423245" =>
            { "1271859210" => [ "\x14\x02\x07\x00\x00", 1 ] },
        "ZCPGBENCH-2963065090" =>
            { "1271859210" => [ "\x14\x02\x07\x00\x00", 1 ] },
        "MINT0" => { "1271859210" => [ "\x00\x01\x00\x01\x00", "D" ] }
    }
];
my $r = Data::MessagePack->pack($input);
my $n1 = trace(10);
my $n2 = trace(10000);
diag("$n1, $n2");

cmp_ok abs($n2-$n1), '<', 100;

done_testing;

sub trace {
    my $n = shift;
    my $before = memoryusage();
    for ( 1 .. $n ) {
        my $x = Data::MessagePack->unpack($r);
        # is_deeply($x, $input);
    }
    my $after  = memoryusage();
    diag("$n\t: $after - $before");
    return $after - $before;
}

sub memoryusage {
    my $status = `cat /proc/$$/status`;
    my @lines = split( "\n", $status );
    foreach my $line (@lines) {
        if ( $line =~ /^VmRSS:/ ) {
            $line =~ s/.*:\s*(\d+).*/$1/;
            return int($line);
        }
    }
    return -1;
}

__END__
    [
        {
            "ZCPGBENCH-1276933268" =>
              { "1271859210" => [ "\x14\x02\x07\x00\x00", 1 ] },
            "VDORBENCH-5637665303" =>
              { "1271859210" => [ "\x00\x01\x00\x01\x00", 1 ] },
            "ZVTHBENCH-7648578738" => {
                "1271859210" => [
                    "\x0a\x02\x04\x00\x00", "2600",
                    "\x0a\x05\x04\x00\x00", "4600"
                ]
            },
            "VMVTBENCH-5237337637" =>
              { "1271859210" => [ "\x00\x01\x00\x01\x00", 1 ] },
            "ZPLSBENCH-1823993880" =>
              { "1271859210" => [ "\x01\x07\x07\x03\x06", "10001" ] },
            "ZCPGBENCH-1995524375" =>
              { "1271859210" => [ "\x14\x02\x07\x00\x00", 1 ] },
            "ZCPGBENCH-2330423245" =>
              { "1271859210" => [ "\x14\x02\x07\x00\x00", 1 ] },
            "ZCPGBENCH-2963065090" =>
              { "1271859210" => [ "\x14\x02\x07\x00\x00", 1 ] },
            "MINT0" => { "1271859210" => [ "\x00\x01\x00\x01\x00", "D" ] }
        }
    ]

