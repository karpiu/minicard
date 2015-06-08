#!/bin/bash

if [ -e codish_data ]; then rm codish_data; fi
if [ -e pwbit_data ]; then rm pwbit_data; fi

touch codish_data
touch pwbit_data

./stats.sh in_100 7 100 >> codish_data
./stats.sh in_200 7 200 >> codish_data
./stats.sh in_500 7 500 >> codish_data
./stats.sh in_1000 7 1000 >> codish_data

./stats.sh in_100 8 100 >> pwbit_data
./stats.sh in_200 8 200 >> pwbit_data
./stats.sh in_500 8 500 >> pwbit_data
./stats.sh in_1000 8 1000 >> pwbit_data
