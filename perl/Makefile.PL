use inc::Module::Install;
name 'Data-MessagePack';
all_from 'lib/Data/MessagePack.pm';
readme_from('lib/Data/MessagePack.pm');

perl_version '5.008005';
license 'perl';
can_cc or die "This module requires a C compiler";

tests 't/*.t';
recursive_author_tests('xt');
use_ppport 3.19;

clean_files qw{
    *.stackdump
    *.gcov *.gcda *.gcno
    *.out
    nytprof
    cover_db
};

if ($ENV{DEBUG}) {
    cc_append_to_ccflags '-g';
}

# copy modules
if ($Module::Install::AUTHOR && -d File::Spec->catfile('..', 'msgpack')) {
    mkdir 'msgpack' unless -d 'msgpack';
    require File::Copy;
    for my $src (<../msgpack/*.h>) {
        File::Copy::copy($src, 'msgpack/') or die "copy failed: $!";
    }
}

requires 'Test::More' => 0.95; # done_testing
test_requires('Test::Requires');

auto_set_repository();
build_requires 'Test::More';
auto_include;
WriteAll;

