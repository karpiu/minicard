#!/bin/bash

if [ $# -ne 1 ]; then
    exit 1
fi

msu_dir=$1

for file in $(find $msu_dir -type f -name "*.cnfp.gz"); do
    dirname $file
done | sort -u

