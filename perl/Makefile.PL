use inc::Module::Install;
name 'Data-MessagePack';
all_from 'lib/Data/MessagePack.pm';

perl_version '5.008005';
license 'perl';
can_cc or die "This module requires a C compiler";

my $ccflags = '-I../ ';

makemaker_args(
    OBJECT => '$(O_FILES)',
    LIBS => [''],
    CCFLAGS => $ccflags,
    clean => {
        FILES => q{
            *.stackdump
            *.gcov *.gcda *.gcno
            *.out
            nytprof
            cover_db
        },
    },
);

tests 't/*.t';
author_tests('xt');

auto_set_repository;
build_requires 'Test::More';
use_test_base;
auto_include;
WriteAll;

