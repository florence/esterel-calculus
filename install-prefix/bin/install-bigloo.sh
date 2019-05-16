#!/bin/sh -ex

cd "$(dirname "$0")/.."

PREFIX="$(pwd)"
BIGLOO=bigloo-unstable
TARBALL=$BIGLOO.tar.gz

mkdir -p "$PREFIX/src"
cd "$PREFIX/src"

if [ ! -f $TARBALL ]; then
  curl ftp://ftp-sop.inria.fr/indes/fp/Bigloo/$BIGLOO.tar.gz > $TARBALL
fi

BIGLOODIR=`tar tfz $TARBALL | head -n 1`

tar -zxf $TARBALL
cd $BIGLOODIR

./configure --prefix="$PREFIX/bigloo"
make -j4
make install
