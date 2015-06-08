#!/bin/bash

gnuplot clauses.gnuplot > tmp.eps
epstopdf tmp.eps --outfile="times.pdf"
rm -f tmp.eps
