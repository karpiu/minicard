#!/bin/bash

output_dir="converted/"
e=$1

mkdir $output_dir

for file in $(find msu4-suite -type f -name "*.cnfp.gz"); do

    dir_path=$output_dir$(dirname $file)

    if [ ! -e $dir_path ]; then
	echo "Creating $dir_path"
	mkdir -p $dir_path
    fi

    echo "Processing "$(basename $file)
    
    file_path=$output_dir$file".cnf"

    ../minicard_encodings/minicard_encodings_static -warn=0 -verb=3 -encode-type=$e -convert-to=1 $file > $file_path
    gzip $file_path
done
