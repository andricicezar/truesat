set xlabel 'n-th fastest result'
set ylabel "CPU time (s)" offset 2

set xrange [0:2000]
set yrange [0.01:125]

set logscale y 10

#set key left top Left reverse
set key bottom right

set output "ts-vs-tsb-100.gp.pdf"
set terminal pdf

set style data linespoints

plot \
     "truesat100.csv" using 1:4 title "TrueSAT" with linespoints pointinterval -500, \
     "truesatbig100.csv" using 1:4 title "TrueSAT (BigInteger)" with linespoints pointinterval -500
