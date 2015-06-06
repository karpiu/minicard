#!/bin/bash

gnuplot clauses.gnuplot > tmp.eps
epstopdf tmp.eps --outfile="clauses.pdf"
rm -f tmp.eps
