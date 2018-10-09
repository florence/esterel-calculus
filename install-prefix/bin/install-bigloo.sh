#!/bin/sh -ex

cd "$(dirname "$0")/.."

PREFIX="$(pwd)"
BIGLOO=bigloo4.3c

mkdir -p "$PREFIX/src"
cd "$PREFIX/src"

curl ftp://ftp-sop.inria.fr/indes/fp/Bigloo/$BIGLOO.tar.gz > $BIGLOO.tar.gz

tar -zxf $BIGLOO.tar.gz
cd $BIGLOO

./configure --prefix="$PREFIX/bigloo"
make -j4
make install
