package Data::MessagePack;
use strict;
use warnings;
use XSLoader;
use 5.008001;

our $VERSION = '0.03';
our $PreferInteger = 0;

XSLoader::load(__PACKAGE__, $VERSION);

1;
__END__

=head1 NAME

Data::MessagePack - messagepack

=head1 SYNOPSIS

    my $packed = Data::MessagePack->pack($dat);
    my $unpacked = Data::MessagePack->unpack($dat);

=head1 DESCRIPTION

Data::MessagePack is a binary packer for perl.

=head1 Configuration Variables

=over 4

=item $Data::MessagePack::PreferInteger

Pack the string as int when the value looks like int(EXPERIMENTAL).

=back

=head1 AUTHORS

Tokuhiro Matsuno

=head1 SEE ALSO

L<http://msgpack.sourceforge.jp/>

