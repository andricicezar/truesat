set xlabel 'n-th fastest result'
set ylabel "CPU time (s)" offset 2

set xrange [0:200]
set yrange [0.01:125]

set logscale y 10

set key left top Left reverse
#set key bottom right

set output "cdcl-150.gp.pdf"
set terminal pdf

set style data linespoints

plot \
     "truesat150.csv" using 1:4 title "TrueSAT" with linespoints pointinterval -500, \
     "versat150.csv" using 1:4 title "versat" with linespoints pointinterval -500, \
     "isasat_ml150.csv" using 1:4 title "IsaSAT" with linespoints pointinterval -500, \
     "minisat150.csv" using 1:4 title "MiniSat" with linespoints pointinterval -500
