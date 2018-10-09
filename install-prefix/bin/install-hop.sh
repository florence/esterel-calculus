#!/bin/sh -ex

cd "$(dirname "$0")/.."

PREFIX="$(pwd)"
HOP=hop-3.1.0-pre1

mkdir -p "$PREFIX/src"
cd "$PREFIX/src"

curl http://www-sop.inria.fr/members/Colin.Vidal/$HOP.tar.gz > $HOP.tar.gz
tar -zxf $HOP.tar.gz
cd $HOP

./configure --prefix="$PREFIX/hop" \
            --bigloo-unistring=no \
            --bigloo="$PREFIX/bigloo/bin/bigloo"
make -j4
make install
