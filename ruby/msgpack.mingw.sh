#!/bin/sh
if [ -z "$1" ];then
	echo "usage: $0 <version>"
	exit 1
fi

version=$1
build=msgpack-mingw-build

./makegem.sh
gem build msgpack.mingw.gemspec
rm -rf $build
mkdir $build
cd $build
tar xvf ../msgpack-$version-x86-mingw32.gem
gunzip metadata.gz
sed s/x86-mingw32/mswin32/ metadata > metadata.tmp
mv metadata.tmp metadata
gzip metadata
tar cvf msgpack-$version-mswin32.gem metadata.gz data.tar.gz

