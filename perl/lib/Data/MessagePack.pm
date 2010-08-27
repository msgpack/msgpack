package Data::MessagePack;
use strict;
use warnings;
use XSLoader;
use 5.008001;

our $VERSION = '0.14';
our $PreferInteger = 0;

our $true  = do { bless \(my $dummy = 1), "Data::MessagePack::Boolean" };
our $false = do { bless \(my $dummy = 0), "Data::MessagePack::Boolean" };
sub true  () { $true  }
sub false () { $false }

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

=head1 METHODS

=over 4

=item my $packed = Data::MessagePack->pack($data);

pack the $data to messagepack format string.

=item my $unpacked = Data::MessagePack->unpack($msgpackstr);

unpack the $msgpackstr to messagepack format string.

=back

=head1 Configuration Variables

=over 4

=item $Data::MessagePack::PreferInteger

Pack the string as int when the value looks like int(EXPERIMENTAL).

=back

=head1 AUTHORS

Tokuhiro Matsuno

=head1 THANKS TO

Jun Kuriyama

=head1 LICENSE

This library is free software; you can redistribute it and/or modify
it under the same terms as Perl itself.


=head1 SEE ALSO

L<http://msgpack.sourceforge.jp/>

