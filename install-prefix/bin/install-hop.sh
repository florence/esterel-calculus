#!/bin/sh -ex

cd "$(dirname "$0")/.."

PREFIX="$(pwd)"
HOP=hop-3.2.0-pre2
mkdir -p "$PREFIX/src"
cd "$PREFIX/src"

curl ftp://ftp-sop.inria.fr/indes/fp/Hop/$HOP.tar.gz > $HOP.tar.gz
tar -zxf $HOP.tar.gz
cd $HOP

./configure --prefix="$PREFIX/hop" \
            --bigloo-unistring=no \
            --bigloo="$PREFIX/bigloo/bin/bigloo"
make -j4
make install
