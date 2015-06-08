set autoscale
set terminal postscript eps
set size 0.5,0.5
set multiplot
set style line 1 lt 1 pt 8 lc rgb "red" lw 1
set style line 2 lt 1 pt 6 lc rgb "blue" lw 1
set style line 3 lt 1 pt 5 lc rgb "green" lw 1
set logscale x 2
set xrange [64:6000]
set yrange [0:1]
plot 'codish_data' using 1:5 smooth unique title 'codish' with linespoints ls 1, \
     'pwbit_data' using 1:5 smooth unique title 'pw_bit' with linespoints ls 2