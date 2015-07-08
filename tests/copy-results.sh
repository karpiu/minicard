#!/bin/bash

input_dir="msu4-suite"
output_dir="results/"

mkdir $output_dir

for file in $(find $input_dir -name "*.wcnf"); do
    output_path=$output_dir$file
    
    if [ -f ${file}/test1.cnfp.gz ]; then
	if [ ! -e $output_path ]; then
	    echo "Creating $output_path"
	    mkdir -p $output_path
	fi

        cp ${file}/ll-results $output_path
	cp ${file}/mc-results $output_path
	cp ${file}/me-results $output_path
    fi
done 
