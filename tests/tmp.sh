#!/bin/bash

if [ -e codish_data ]; then rm codish_data; fi
if [ -e pwbit_data ]; then rm pwbit_data; fi

touch codish_data
touch pwbit_data

./stats.sh in_100_40 7 100 >> codish_data
./stats.sh in_200_40 7 200 >> codish_data
./stats.sh in_500_40 7 500 >> codish_data
./stats.sh in_1000_40 7 1000 >> codish_data
./stats.sh in_2000_40 7 2000 >> codish_data
./stats.sh in_5000_40 7 5000 >> codish_data

./stats.sh in_100_40 8 100 >> pwbit_data
./stats.sh in_200_40 8 200 >> pwbit_data
./stats.sh in_500_40 8 500 >> pwbit_data
./stats.sh in_1000_40 8 1000 >> pwbit_data
./stats.sh in_2000_40 8 2000 >> pwbit_data
./stats.sh in_5000_40 8 5000 >> pwbit_data
