set xlabel 'n-th fastest result'
set ylabel "CPU time (s)" offset 2

set xrange [0:2000]
set yrange [0.01:125]

set logscale y 10

set key left top Left reverse
#set key bottom right

set output "dpll-100.gp.pdf"
set terminal pdf

set style data linespoints

plot \
     "truesat100.csv" using 1:4 title "TrueSAT" with linespoints pointinterval -500, \
     "cpp100.csv" using 1:4 title "C++ solver" with linespoints pointinterval -500, \
     "cs100.csv" using 1:4 title "C# solver" with linespoints pointinterval -500, \
     "swansea100.csv" using 1:4 title "Minlog solver" with linespoints pointinterval -500
