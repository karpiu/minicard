#!/bin/bash

dir=$1
n=$2
k=$3
c=$4
f=$5

if [ -d $1 ] ; then
    read -p "Directory $dir already exists. Remove and generate new tests? (Y/N) "
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo "Exiting."
        exit 1
    fi
    rm -r $dir
fi

echo "Creating directory $dir"
mkdir $dir
ret=$?

if [ $ret -gt 0 ] ; then
    echo "Error occured while trying to create directory $dir"
    exit 1
fi

for ((u=1;u<=f;u++)); do
    test_name=$dir/rand_"$n"_"$k"_"$c"_"$u".cnfp

    touch $test_name

    echo "c Randomly generated cnf+ instance" >> $test_name
    echo "c n:$n k:$k c:$c" >> $test_name
    echo "p cnf+ $n $c" >> $test_name

    for ((v=1;v<=c;v++)); do
	constr=""
	for ((w=1;w<=k;w++)); do
	    if [ $(( RANDOM % 2 )) -eq 0 ]; then minus="-"; else minus="";fi
	    constr="${constr}${minus}$(( (RANDOM % n) + 1)) "
	done
	constr="${constr}<= $(( ( RANDOM % k) + 1))"
	echo $constr >> $test_name
    done
done
