#!/usr/bin/env bash
shopt -s extglob
raco test "$1"/model/*rkt
raco test "$1"/test/*rkt

