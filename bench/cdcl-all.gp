set xlabel 'n-th fastest result'
set ylabel "CPU time (s)" offset 2

set xrange [0:2599]
set yrange [0.01:125]

set logscale y 10

set key left top Left reverse

set output "cdcl-all.gp.pdf"
set terminal pdf

set style data linespoints

plot \
     "truesatall.csv" using 1:4 title "TrueSAT" with linespoints pointinterval -500, \
     "isasat_mlall.csv" using 1:4 title "IsaSAT" with linespoints pointinterval -500, \
     "minisatall.csv" using 1:4 title "MiniSat" with linespoints pointinterval -500, \
     "versatall.csv" using 1:4 title "versat" with linespoints pointinterval -500