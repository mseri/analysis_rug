set size 1.0,0.6
set border 3

set term postscript eps color solid enhanced "Helvetica" 20

set key top center horizontal outside

# EXAMPLE 1

set xrange [0:1]
set yrange [0:1]

set xtics 0,1,1 nomirror
set ytics 0,1,1 nomirror

fn(x,n) = x**n
f(x)    = (x < 1) ? 0 : 1
eps     = 0.25
fp(x)   = f(x) + eps
fm(x)   = f(x) - eps

set out 'lec12-example1a.eps'
plot \
fn(x,1) w l lw 5 title 'n = 1', \
fn(x,2) w l lw 5 title 'n = 2', \
fn(x,3) w l lw 5 title 'n = 3'

! epstopdf lec12-example1a.eps

set out 'lec12-example1b.eps'
set yrange [0:1+eps]
plot \
fn(x,1) w l lw 5 title 'n = 1', \
fn(x,2) w l lw 5 title 'n = 2', \
fn(x,3) w l lw 5 title 'n = 3', \
fp(x)    w p pt 5 ps 0.6 lc 9 title '', \
fm(x)    w p pt 5 ps 0.6 lc 9 title ''

! epstopdf lec12-example1b.eps




# EXAMPLE 2

set xrange [0:1]
set yrange [0:1]

set xtics 0,1,1 nomirror
set ytics 0,1,1 nomirror

fn(x,n) = (x < 1.0/n) ? ((x <= 0.5/n) ? 2*n*x : 2-2*n*x) : 0.005
f(x)    = 0
eps     = 0.5
fp(x)   = f(x)+eps
fm(x)   = f(x)-eps

set samples 1000

set out 'lec12-example2a.eps'
plot \
fn(x,1) w l lw 5 title 'n = 1', \
fn(x,2) w l lw 5 title 'n = 2', \
fn(x,3) w l lw 5 title 'n = 3'

! epstopdf lec12-example2a.eps

set samples 100

set out 'lec12-example2b.eps'
set yrange [0:1]
plot \
fn(x,1) w l lw 5 title 'n = 1', \
fn(x,2) w l lw 5 title 'n = 2', \
fn(x,3) w l lw 5 title 'n = 3', \
fp(x)    w p pt 5 ps 0.4 lc 9 title '', \
fm(x)    w p pt 5 ps 0.4 lc 9 title ''

! epstopdf lec12-example2b.eps





# EXAMPLE 3

set xrange [0:1]
set yrange [0:0.3]

set xtics 0,1,1 nomirror
set ytics 0,0.25,0.25 nomirror

fn(x,n) = (1-x)*(x**n)

set out 'lec12-example3a.eps'
plot \
fn(x,1) w l lw 5 title 'n = 1', \
fn(x,2) w l lw 5 title 'n = 2', \
fn(x,3) w l lw 5 title 'n = 3'

! epstopdf lec12-example3a.eps



# EXAMPLE 4

set xrange [-2:2]
set yrange [0:*]

set xtics -2,1,2 nomirror
set ytics 0,0.8,3 nomirror

fn(x,n) = x*x / (1 + n*x*x)

set out 'lec12-example4a.eps'
plot \
fn(x,1) w l lw 5 title 'n = 1', \
fn(x,2) w l lw 5 title 'n = 2', \
fn(x,3) w l lw 5 title 'n = 3'

! epstopdf lec12-example4a.eps



# EXAMPLE 5

set xrange [-1:1]
set yrange [0:1]

set xtics -1,1,1 nomirror
set ytics 0,1,1 nomirror

fn(x,n) = (x == 0) ? 0.0 : exp(2*n*log(abs(x)) / (2*n-1))
f(x) = abs(x)

set out 'lec12-example5a.eps'
plot \
fn(x,1) w l lw 5 title 'n = 1', \
fn(x,2) w l lw 5 title 'n = 2', \
fn(x,3) w l lw 5 title 'n = 3', \
f(x) w l lw 5 lc 9 title 'limit'

! epstopdf lec12-example5a.eps



# EXAMPLE 6

set xrange [-1:1]
set yrange [0:*]

fn(x,n) = sqrt(x**2 + 1.0/n)
f(x) = abs(x)

set samples 1000

set out 'lec12-example6a.eps'
plot \
fn(x,1)  w l lw 5 title 'n = 1', \
fn(x,5)  w l lw 5 title 'n = 5', \
fn(x,20) w l lw 5 title 'n = 20', \
f(x) w l lw 5 lc 9 title 'limit'

! epstopdf lec12-example6a.eps



! rm lec12-*.eps
