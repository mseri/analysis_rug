---
title: "Analysis"
author: "Marcello Seri, m.seri@rug.nl, slides by Alef Sterk"
date: "Lecture 14, Wednesday 15 January 2025"
---

Topics:
- Abbott §6.6: Taylor series

Formalization: [`Taylor.v`](docs/rocq/RUG.Analysis.Taylor.html)

---

# Taylor series

## Taylor series

**Recap:**
$$
\sum_{n=0}^\infty a_n x^n \to f(x) \text{ on } (-R,R)
\quad\Rightarrow\quad
f : (-R,R) \to \mathbb{R} \text{ is infinitely often differentiable}
$$

**Converse question:**

Can we write any inf. often differentiable function as a power series?

---

## Taylor series

| | | | | |
|---|---|---|---|---|
| $f(x)$ | $=$ | $a_0 + a_1 x + a_2 x^2 + a_3 x^3 + \cdots$ | $\Rightarrow$ | $f(0) = a_0$ |
| $f'(x)$ | $=$ | $a_1 + 2a_2 x + 3a_3 x^2 + \cdots$ | $\Rightarrow$ | $f'(0) = a_1$ |
| $f''(x)$ | $=$ | $2a_2 + 6a_3 x + \cdots$ | $\Rightarrow$ | $f''(0) = 2a_2$ |
| $f'''(x)$ | $=$ | $6a_3 + \cdots$ | $\Rightarrow$ | $f'''(0) = 6a_3$ |

Taylor's formula: $\displaystyle \quad a_n = \frac{f^{(n)}(0)}{n!}$

---

## Taylor series

Assume $f$ is inf. often differentiable on interval around $x=0$

**Definition:** the Taylor series of $f$ around $x=0$ is given by
$$
\sum_{n=0}^\infty \frac{f^{(n)}(0)}{n!} x^n
$$

**Question:** does the series converge to $f$?

---

# Lagrange remainder

## Lagrange remainder

**Definition:**
$$\begin{aligned}
s_n(x) & = \sum_{k=0}^n \frac{f^{(k)}(0)}{k!}x^k \hspace{28mm}\text{(partial sum)} \\[4mm]
E_n(x) & = f(x) - s_n(x) \hspace{30mm}\text{(remainder)}
\end{aligned}$$

**Theorem:** for $n \in \mathbb{N}$ and $x > 0$ there exists $c \in (0,x)$ such that
$$
E_n(x) = \frac{f^{(n+1)}(c)}{(n+1)!} x^{n+1}
$$

**Note:** $c$ depends on both $n$ and $x$!

*If $x<0$, then $c \in (x,0)$*

---

## Lagrange remainder

**Lemma:** assume that

- $x>0$ and $h(t)$ is $n+1$ times differentiable on $[0,x]$
- $h(x)=0$ and $h^{(k)}(0) = 0$ for all $k = 0,\dots,n$

Then $h^{(n+1)}(c) = 0$ for some $c \in (0,x)$

**Proof:** repeated application of Rolle's theorem gives
$$\begin{aligned}
h(0) = h(x) & \Rightarrow h'(c_1) = 0 \text{ for some } c_1 \in (0,x) \\
h'(0) = h'(c_1) & \Rightarrow h''(c_2) = 0 \text{ for some } c_2 \in (0,c_1) \\
& \vdots \\
h^{(n)}(0) = h^{(n)}(c_n) & \Rightarrow h^{(n+1)}(c_{n+1}) = 0 \text{ for some } c_{n+1} \in (0,c_n)
\end{aligned}$$

---

## Lagrange remainder

**Theorem:** for $n \in \mathbb{N}$ and $x > 0$ there exists $c \in (0,x)$ such that
$$
E_n(x) = \frac{f^{(n+1)}(c)}{(n+1)!} x^{n+1}
$$

**Proof:** fix $x>0$ and consider
$$
h(t) = f(t) - s_n(t) - \left(\frac{f(x) - s_n(x)}{x^{n+1}}\right)t^{n+1}
$$

Note that:
$$
h(x) = 0
\quad\text{and}\quad
h^{(k)}(0) = 0, \quad k = 0,\dots,n
$$

*If $x<0$, then $c \in (x,0)$*

---

## Lagrange remainder

**Proof (ctd):** the lemma gives $c \in (0,x)$ such that
$$
f^{(n+1)}(c) - \underbrace{s_n^{(n+1)}(c)}_{= \, 0} - (n+1)! \left(\frac{f(x) - s_n(x)}{x^{n+1}}\right) = 0
$$

Rearranging gives
$$
f(x) - s_n(x) = \frac{f^{(n+1)}(c)}{(n+1)!} x^{n+1}
$$

---

## Taylor series around different points

Assume $f$ is inf. often differentiable on interval around $a$

**Definition:** the Taylor series of $f$ around $x=a$ is given by
$$
\sum_{n=0}^\infty \frac{f^{(n)}(a)}{n!} (x-a)^n
$$

**Lagrange remainder:** for $x>a$ there exists $c \in (a,x)$ such that
$$
E_n(x) = f(x) - s_n(x) = \frac{f^{(n+1)}(c)}{(n+1)!}(x-a)^{n+1}
$$

*If $x<a$, then $c \in (x,a)$*

---

# Examples

## Taylor series for $f(x) = e^x$

| $n$ | $f^{(n)}(x)$ | $a_n = f^{(n)}(0) / n!$ |
|---|---|---|
| $0$ | $e^x$ | $1$ |
| $1$ | $e^x$ | $1$ |
| $2$ | $e^x$ | $1/2!$ |
| $3$ | $e^x$ | $1/3!$ |
| $4$ | $e^x$ | $1/4!$ |
| $\vdots$ | $\vdots$ | $\vdots$ |

---

## Taylor series for $f(x) = e^x$

For $x \neq 0$ there exists $c \in (-|x|,|x|)$ such that
$$
e^x = \sum_{k=0}^n \frac{1}{k!}x^k + \frac{e^c}{(n+1)!}x^{n+1}
$$

For any $a>0$ we have
$$
\sup_{x \in [-a,a]} \bigg|e^x - \sum_{k=0}^n \frac{1}{k!}x^k\bigg|\leq e^a\cdot\frac{a^{n+1}}{(n+1)!} \to 0
\quad\text{as}\quad n\to\infty
$$

The Taylor series of $f$ converges uniformly to $f$ on $[-a,a]$!

---

## Taylor series for $f(x) = e^x$

![](../fig/lec15-taylor-exp1.pdf)

$f(x) = e^x$, $s_1(x) = 1+x$

---

## Taylor series for $f(x) = e^x$

![](../fig/lec15-taylor-exp2.pdf)

$f(x) = e^x$, $s_2(x) = 1+x+\dfrac{x^2}{2!}$

---

## Taylor series for $f(x) = e^x$

![](../fig/lec15-taylor-exp3.pdf)

$f(x) = e^x$, $s_3(x) = 1+x+\dfrac{x^2}{2!}+\dfrac{x^3}{3!}$

---

## Taylor series for $f(x) = e^x$

![](../fig/lec15-taylor-exp4.pdf)

$f(x) = e^x$, $s_4(x) = 1+x+\dfrac{x^2}{2!}+\dfrac{x^3}{3!}+\dfrac{x^4}{4!}$

---

## Taylor series for $f(x) = \sin(x)$

| $n$ | $f^{(n)}(x)$ | $a_n = f^{(n)}(0) / n!$ |
|---|---|---|
| $0$ | $\phantom{-}\sin(x)$ | $\phantom{-}0$ |
| $1$ | $\phantom{-}\cos(x)$ | $\phantom{-}1$ |
| $2$ | $-\sin(x)$ | $\phantom{-}0$ |
| $3$ | $-\cos(x)$ | $-1/3!$ |
| $4$ | $\phantom{-}\sin(x)$ | $\phantom{-}0$ |
| $5$ | $\phantom{-}\cos(x)$ | $\phantom{-}1/5!$ |
| $\vdots$ | $\phantom{--}\vdots$ | $\phantom{-}\vdots$ |

---

## Taylor series for $f(x) = \sin(x)$

For $x \neq 0$ there exists $c \in (-|x|,|x|)$ such that
$$
|E_n(x)|
=
\left|\frac{f^{(n+1)}(c)}{(n+1)!}x^{n+1}\right|
\leq
\frac{|x|^{n+1}}{(n+1)!}
$$

Remainder converges to 0 uniformly on any interval $[-a,a]$:
$$
\sup_{x\in[-a,a]} |E_n(x)| \leq  \frac{a^{n+1}}{(n+1)!} \to 0
\quad\text{as}\quad
n\to\infty
$$

Conclusion:
$$
\sin(x) = x - \frac{1}{3!}x^3 + \frac{1}{5!}x^5 - \frac{1}{7!}x^7 + \cdots \qquad\forall\,x\in\mathbb{R}
$$

---

## Taylor series for $f(x) = \sin(x)$

![](../fig/lec15-taylor-sin1.pdf)

$f(x) = \sin(x)$, $s_1(x) = x$

---

## Taylor series for $f(x) = \sin(x)$

![](../fig/lec15-taylor-sin2.pdf)

$f(x) = \sin(x)$, $s_3(x) = x - \dfrac{x^3}{3!}$

---

## Taylor series for $f(x) = \sin(x)$

![](../fig/lec15-taylor-sin3.pdf)

$f(x) = \sin(x)$, $s_5(x) = x - \dfrac{x^3}{3!} + \dfrac{x^5}{5!}$

---

## Taylor series for $f(x) = \sin(x)$

![](../fig/lec15-taylor-sin4.pdf)

$f(x) = \sin(x)$, $s_7(x) = x - \dfrac{x^3}{3!} + \dfrac{x^5}{5!} - \dfrac{x^7}{7!}$

---

## Taylor series for $f(x) = \ln(1+x)$

$$
f(x) = \ln(1+x)
\quad\Rightarrow\quad
f^{(n)}(x) = \frac{(-1)^{n+1} (n-1)!}{(1+x)^n} \qquad \forall\, n \in \mathbb{N}
$$

For $x>0$ there exists $c \in (0,x)$ such that
$$
\ln(1+x) = \sum_{k=1}^n \frac{(-1)^{k+1}}{k}x^k + \frac{(-1)^n}{(n+1)(1+c)^{n+1}}\,x^{n+1}
$$

**Exercise:** prove that

1. the Taylor series converges uniformly to $f$ on $[0,1]$
2. $\ln(2) = 1 - \tfrac{1}{2} + \tfrac{1}{3} - \tfrac{1}{4} + \cdots$

---

## Taylor series for $f(x)=\arctan(x)$

On $[-1,1]$ we have
$$
\arctan(x) = x - \frac{1}{3} x^3 + \frac{1}{5}x^5 - \frac{1}{7}x^7 + \cdots
$$

The convergence is uniform on $[-1,1]$

For $x=1$ we get
$$
\frac{\pi}{4} = 1 - \frac{1}{3} + \frac{1}{5} - \frac{1}{7} + \cdots
$$

---

## A counter example

![](../fig/lec15-counterexample.pdf)

$$
f(x) = \begin{cases} e^{-1/x^2} & \text{if } x \neq 0 \\ 0 & \text{if } x = 0 \end{cases}
\qquad\Rightarrow\qquad
f^{(n)}(0)=0 \quad\forall\,n\in\mathbb{N}
$$

The Taylor series of $f$ does **NOT** converge to $f$!

---

# Applications

## Approximating square roots

2nd order approximation of $\sqrt{5} = 2.236...$

$$\begin{aligned}
\sqrt{x} & = 1 + \tfrac{1}{2}(x-1) - \tfrac{1}{8}(x-1)^2 + E_3(x) \\[2mm]
\sqrt{5} & \approx 1 + \tfrac{4}{2} - \tfrac{16}{8} \;\; = \;\; 1 \\[6mm]
\sqrt{x} & = 2 + \tfrac{1}{4}(x-4) - \tfrac{1}{64}(x-4)^2 + \widetilde{E}_3(x) \\[2mm]
\sqrt{5} & \approx 2 + \tfrac{1}{4} - \tfrac{1}{64} \;\; = \;\; 2.234375
\end{aligned}$$

Truncated Taylor series around $x=4$ much more accurate!

---

## Approximating integrals

According to Wolfram Alpha:

$$
\int_0^1 \frac{e^x-1}{x}\,dx = \text{Ei}(1) - \gamma \approx 1.3179
$$

---

## Approximating integrals

For $x > 0$ there exists $c \in (0,x)$ such that
$$\begin{aligned}
e^x & = \sum_{k=0}^n \frac{x^k}{k!} + \frac{e^{c}}{(n+1)!}x^{n+1} \\[5mm]
\frac{e^x-1}{x} & = \sum_{k=1}^n \frac{x^{k-1}}{k!} + \frac{e^{c}}{(n+1)!}x^{n} \\[5mm]
\int_0^1 \frac{e^x-1}{x}\,dx & = \sum_{k=1}^n \frac{1}{k!\,k} + \int_0^1 \frac{e^{c}}{(n+1)!}x^{n}\,dx
\end{aligned}$$

---

## Approximating integrals

Upper bound for remainder term:
$$\begin{aligned}
R_n
& = \int_0^1 \frac{e^{c}}{(n+1)!}x^{n}\,dx \\
& < \int_0^1 \frac{3}{(n+1)!}x^{n}\,dx \\
& = \frac{3}{(n+1)!\,(n+1)}
\end{aligned}$$

Approximation with $n=5$:
$$
\int_0^1 \frac{e^x-1}{x}\,dx
\approx
\sum_{k=1}^5\frac{1}{k!\,k} =
1.31763...
\qquad (R_5 < 0.001)
$$
