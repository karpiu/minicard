#!/bin/bash
#
# stats.sh -- Run tests for plotting
#
# script accepts two parameters:
# $1 : a directory with test files;
#      a test file is either plain or gziped DIMACS file (CNF or CNF+)
# $2 : encoding type (currently number from 1 to 8;
#      check ../encodings/Encodings.h for list of all encoding types)
# $3 : number of cardinality constraints for each test in the given directory

types="1 2 3 4 5 6 7 8"

if [ $# -ne 3 ]
then
    echo "USAGE: ./stats.sh <input-directory> <encoding-type> <number-of-variables>"
    exit 1
fi

if [ ! -d $1 ]
then
    echo "ERROR: $1 is not a directory"
    exit 1
fi

if [[ ! $types == *$2* ]]
then
    echo "ERROR: type $2 is not supported"
    exit 1
fi

for file in $(find $1 -maxdepth 1 -type f); do
    echo "$3 $(../minicard_encodings/minicard_encodings_static -warn=0 -verb=3 -encode-type=$2 $file)"
done
