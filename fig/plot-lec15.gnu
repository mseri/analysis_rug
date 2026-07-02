unset key

set linestyle 1 lt -1 lw 1
set linestyle 2 lt  9 lw 2
set linestyle 3 lt  3 lw 5
set linestyle 4 lt  1 lw 5

set xzeroaxis ls 1
set yzeroaxis ls 1

set border 0

set size ratio 0.35

set xtics axis nomirror
set ytics axis nomirror

set term postscript eps color solid enhanced "Helvetica" 25

unset xtics
unset ytics

set xtics axis ("-2{/Symbol p}" -2*pi, "-{/Symbol p}" -pi, "{/Symbol p}" pi, "2{/Symbol p}" 2*pi)
set ytics axis -1,2,1

set xrange [-3*pi:3*pi]
set yrange [-2:2]


f(x)  = sin(x)
t1(x) = x
t2(x) = t1(x) - exp(3*log(x)) / 6
t3(x) = t2(x) + exp(5*log(x)) / 120
t4(x) = t3(x) - exp(7*log(x)) / 5040

set out 'lec15-taylor-sin1.eps'
plot f(x) w l ls 3, t1(x) w l ls 4

set out 'lec15-taylor-sin2.eps'
plot f(x) w l ls 3, t2(x) w l ls 4

set out 'lec15-taylor-sin3.eps'
plot f(x) w l ls 3, t3(x) w l ls 4

set out 'lec15-taylor-sin4.eps'
plot f(x) w l ls 3, t4(x) w l ls 4

f(x)  = cos(x)
t1(x) = 1
t2(x) = t1(x) - exp(2*log(x)) / 2
t3(x) = t2(x) + exp(4*log(x)) / 24
t4(x) = t3(x) - exp(6*log(x)) / 720
t5(x) = t4(x) + exp(7*log(x)) / 5040

set out 'lec15-taylor-cos1.eps'
plot f(x) w l ls 3, t1(x) w l ls 4

set out 'lec15-taylor-cos2.eps'
plot f(x) w l ls 3, t2(x) w l ls 4

set out 'lec15-taylor-cos3.eps'
plot f(x) w l ls 3, t3(x) w l ls 4

set out 'lec15-taylor-cos4.eps'
plot f(x) w l ls 3, t4(x) w l ls 4

set out 'lec15-taylor-cos5.eps'
plot f(x) w l ls 3, t5(x) w l ls 4


f(x)  = exp(x)
t0(x) = 1
t1(x) = t0(x) + x
t2(x) = t1(x) + exp(2*log(x)) / 2
t3(x) = t2(x) + exp(3*log(x)) / 6
t4(x) = t3(x) + exp(4*log(x)) / 24
t5(x) = t4(x) + exp(5*log(x)) / 120
t6(x) = t5(x) + exp(6*log(x)) / 720

set out 'lec15-taylor-exp0.eps'

set xrange [-2:3]
set yrange [-5:20]

set size square

set xtics axis ("-1" -1, "1" 1)
set ytics axis ("-5" -5, "5" 5, "10" 10, "15" 15)

plot f(x) w l ls 3, t0(x) w l ls 4

set out 'lec15-taylor-exp1.eps'
plot f(x) w l ls 3, t1(x) w l ls 4

set out 'lec15-taylor-exp2.eps'
plot f(x) w l ls 3, t2(x) w l ls 4

set out 'lec15-taylor-exp3.eps'
plot f(x) w l ls 3, t3(x) w l ls 4

set out 'lec15-taylor-exp4.eps'
plot f(x) w l ls 3, t4(x) w l ls 4

set out 'lec15-taylor-exp5.eps'
plot f(x) w l ls 3, t5(x) w l ls 4


set out 'lec15-counterexample.eps'
set term postscript eps color solid enhanced "Helvetica" 20

set size ratio 0.25


set xtics -5,5,5
set ytics -1,2,1

f(x) = (x == 0) ? 0 : exp(-1/(x*x))

plot[-5:5][0:1] f(x) w l ls 3




! epstopdf lec15-taylor-sin1.eps
! epstopdf lec15-taylor-sin2.eps
! epstopdf lec15-taylor-sin3.eps
! epstopdf lec15-taylor-sin4.eps

! epstopdf lec15-taylor-cos1.eps
! epstopdf lec15-taylor-cos2.eps
! epstopdf lec15-taylor-cos3.eps
! epstopdf lec15-taylor-cos4.eps
! epstopdf lec15-taylor-cos5.eps

! epstopdf lec15-taylor-exp1.eps
! epstopdf lec15-taylor-exp2.eps
! epstopdf lec15-taylor-exp3.eps
! epstopdf lec15-taylor-exp4.eps
! epstopdf lec15-taylor-exp5.eps

! epstopdf lec15-counterexample.eps

! rm lec15-*.eps


