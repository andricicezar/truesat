set xlabel 'n-th fastest result'
set ylabel "CPU time (s)" offset 2

set xrange [0:2599]
set yrange [0.01:125]

set logscale y 10

#set key left top Left reverse
set key bottom right

set output "ts-vs-tsb-all.gp.pdf"
set terminal pdf

set style data linespoints

plot \
     "truesatall.csv" using 1:4 title "TrueSAT" with linespoints pointinterval -500, \
     "truesatbigall.csv" using 1:4 title "TrueSAT (BigInteger)" with linespoints pointinterval -500
