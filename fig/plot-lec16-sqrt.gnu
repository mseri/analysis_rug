set size 1.0,0.6
set border 3

set term postscript eps color solid enhanced "Helvetica" 20

set key top center horizontal outside
unset key

set xrange [0:10]
set yrange [0:*]

set ytics 0,1,3 nomirror
set xtics 0,1,10 nomirror

f(x) = sqrt(x)
p(x) = 1 + 0.5*(x-1)-(x-1)**2 / 8.
q(x) = 2 + (x-4)/4. - (x-4)**2 / 64.

set out 'lec16-sqrt.eps'

set samples 1000

plot f(x) w l lw 5 lc -1, p(x) w l lw 5 lc 3, q(x) w l lw 5 lc 1

! epstopdf lec16-sqrt.eps
! rm lec16-sqrt.eps

