set size 1.0,0.6
set border 3

set term postscript eps color solid enhanced "Helvetica" 20

set key top center horizontal outside
unset key

set xrange [0:1]
set yrange [0:1]

set ytics 0,1,1 nomirror
set xtics nomirror

set out 'lec16-example1.eps'

f(x,n) = ((x > 1.0 / (n+1)) & (x <= 1.0 / n)) ? 1.0 / n : 1/0

plot \
f(x,1) w l lw 5 lc 1, \
f(x,2) w l lw 5 lc 1, \
f(x,3) w l lw 5 lc 1, \
f(x,4) w l lw 5 lc 1, \
f(x,5) w l lw 5 lc 1, \
f(x,6) w l lw 5 lc 1, \
f(x,7) w l lw 5 lc 1, \
f(x,8) w l lw 5 lc 1, \
f(x,9) w l lw 5 lc 1, \
f(x,10) w l lw 5 lc 1

! epstopdf lec16-example1.eps


set out 'lec16-example2.eps'

f(x,n) = ((x >= (n-1)/(1.0*n)) & (x < (1.0*n) / (n+1))) ? 1.0 / n : 1/0

plot \
f(x,1) w l lw 5 lc 1, \
f(x,2) w l lw 5 lc 1, \
f(x,3) w l lw 5 lc 1, \
f(x,4) w l lw 5 lc 1, \
f(x,5) w l lw 5 lc 1, \
f(x,6) w l lw 5 lc 1, \
f(x,7) w l lw 5 lc 1, \
f(x,8) w l lw 5 lc 1, \
f(x,9) w l lw 5 lc 1, \
f(x,10) w l lw 5 lc 1

! epstopdf lec16-example2.eps


! rm lec16-*.eps
