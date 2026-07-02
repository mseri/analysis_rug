---
title: "Analysis"
author: "Marcello Seri, m.seri@rug.nl, slides by Alef Sterk"
date: "Lecture 13, Wednesday 8 January 2025"
---

Topics:

- Abbott §6.5: Power series

---

# Pointwise convergence

## Power series

General form of a PS:

$$
\sum_{n=0}^\infty a_n x^n = a_0 + a_1 x + a_2 x^2 + a_3 x^3 + \cdots
$$

Convergence?

Continuity / differentiability of the limit?

---

## Pointwise convergence

**Theorem:**
$$
\sum_{n=0}^\infty a_n x^n \text{ converges at } c\neq 0
\;\;\Rightarrow\;\;
\sum_{n=0}^\infty \big|a_n x^n\big| \text{ converges for } |x| < |c|
$$

**Proof:**
$$\begin{aligned}
\sum_{n=0}^\infty a_n c^n \;\text{ converges}
& \Rightarrow  \lim a_n c^n = 0 \\[2mm]
& \Rightarrow  \big(a_n c^n\big) \text{ is bounded} \\[4mm]
& \Rightarrow  \exists\,M>0 \quad\text{s.t.}\quad \big|a_n c^n\big| \leq M \quad\forall\,n\in\mathbb{N}
\end{aligned}$$

---

## Pointwise convergence

**Proof (ctd):**
$$
\big|a_n x^n\big|
=
\left|a_n\left(c\cdot\frac{x}{c}\right)^n\right|
=
\big|a_n c^n\big| \cdot \left|\frac{x}{c}\right|^n
\leq
M\cdot \left|\frac{x}{c}\right|^n \qquad \forall\,n\in\mathbb{N}
$$

Note: $|x| < |c| \;\Rightarrow\; \left|\displaystyle\frac{x}{c}\right|<1$

Apply comparison test:
$$
\sum_{n=0}^\infty M\left|\frac{x}{c}\right|^n \text{ converges}
\quad\Rightarrow\quad
\sum_{n=0}^\infty \big|a_n x^n\big| \text{ converges}
$$

---

## Radius of convergence

**Corollary:** there exists $R \geq 0$ such that

- $|x| < R \;\;\Rightarrow\;\;$ PS converges at $x$
- $|x| > R \;\;\Rightarrow\;\;$ PS diverges at $x$

$R$ is called the **radius of convergence**

---

## Radius of convergence

Methods for **computing** $R$ from the $a_n$'s

**Root test:** if $L = \lim \sqrt[n]{|a_n|}$ exists, then $R = 1/L$

**Ratio test:** if $L = \lim \left|\displaystyle\frac{a_{n+1}}{a_n}\right|$ exists, then $R = 1/L$

*[interpret $L = 0$ as $R = \infty$]*

---

## Root test

**Proof:** $\lim \sqrt[n]{|a_n x^n|} = L|x| \qquad\forall\,x\in\mathbb{R}$ fixed

For all $\epsilon>0$ there exists $N\in\mathbb{N}$ s.t.
$$\begin{aligned}
n \geq N
& \Rightarrow  \left|\sqrt[n]{|a_nx^n|} - L|x|\right| < \epsilon \\[5mm]
& \Rightarrow  L|x|-\epsilon < \sqrt[n]{|a_nx^n|} < L|x| + \epsilon \\[7mm]
& \Rightarrow  (L|x|-\epsilon)^n < |a_n x^n| < (L|x|+\epsilon)^n
\end{aligned}$$

---

## Root test

**Proof (ctd):** if $|x| < 1/L$ then pick $\epsilon < 1 - L|x|$

Apply comparison test:
$$\begin{aligned}
L|x|+\epsilon < 1
& \quad\Rightarrow\quad
\sum_{n=0}^\infty (L|x|+\epsilon)^n \text{ converges} \\
& \quad\Rightarrow\quad
\sum_{n=0}^\infty |a_n x^n| \text{ converges} \\
& \quad\Rightarrow\quad
\sum_{n=0}^\infty a_n x^n \text{ converges}
\end{aligned}$$

---

## Root test

**Proof (ctd):** if $|x| > 1/L$ then pick $\epsilon < L|x|-1$:

$$\begin{aligned}
L|x|-\epsilon > 1
& \quad\Rightarrow\quad
(L|x|-\epsilon)^n \text{ unbounded} \\[4mm]
& \quad\Rightarrow\quad
|a_n x^n| \text{ unbounded} \\[3mm]
& \quad\Rightarrow\quad
\sum_{n=0}^\infty a_n x^n \text{ diverges}
\end{aligned}$$

---

## Root test

**Example:** $\displaystyle\sum_{n=0}^\infty \frac{x^n}{5^{n^2}}$

Radius of convergence:
$$\begin{aligned}
a_n = \frac{1}{5^{n^2}}
& \quad\Rightarrow\quad \sqrt[n]{|a_n|} = \frac{1}{5^n} \\[4mm]
& \quad\Rightarrow\quad L = 0 \\[4mm]
& \quad\Rightarrow\quad R = \infty
\end{aligned}$$

---

## Ratio test

**Example:** $\displaystyle\sum_{n=1}^\infty \frac{x^n}{n^2}$

Radius of convergence:
$$\begin{aligned}
a_n = \frac{1}{n^2}
& \quad\Rightarrow\quad \frac{a_{n+1}}{a_n} = \frac{n^2}{(n+1)^2} \\[4mm]
& \quad\Rightarrow\quad L = 1 \\[4mm]
& \quad\Rightarrow\quad R = 1
\end{aligned}$$

---

## Beware of the boundary points!

| Example | Radius | at $x=-R$ | at $x=R$ |
|---|---|---|---|
| $\displaystyle\sum_{n=1}^\infty x^n$ | $R=1$ | **divergent** | **divergent** |
| $\displaystyle\sum_{n=1}^\infty \frac{1}{n}x^n$ | $R=1$ | convergent | **divergent** |
| $\displaystyle\sum_{n=1}^\infty \frac{(-1)^n}{n}x^n$ | $R=1$ | **divergent** | convergent |
| $\displaystyle\sum_{n=1}^\infty \frac{1}{n^2}x^n$ | $R=1$ | convergent | convergent |

---

# Uniform convergence

## Uniform convergence

**Theorem:**
$$
\sum_{n=0}^\infty |a_n c^n| \text{ convergent}
\;\;\Rightarrow\;\;
\sum_{n=0}^\infty a_n x^n \text{ uniformly conv.~on } [-|c|,|c|]
$$

**Proof:** for $|x| \leq |c|$ we have
$$
|a_n x^n| = |a_n|\cdot |x|^n \leq |a_n|\cdot |c|^n = |a_n c^n| =: M_n
$$

Apply Weierstrass' test:
$$
\sum_{n=0}^\infty M_n \quad\text{conv.}
\quad\Rightarrow\quad
\sum_{n=0}^\infty a_n x^n \quad\text{unif.~conv.~on } [-|c|,|c|]
$$

---

## Recall: preservation of continuity

**Theorem:** assume

1. $\sum_{n=1}^\infty f_n \to f$ uniformly on $A$
2. $f_n$ is continuous on $A$ for all $n$

Then $f$ is continuous on $A$

---

## Continuity of the limit

**Corollary:** $\displaystyle\sum_{n=0}^\infty a_n x^n$ is a continuous function on $(-R,R)$

**Proof:** take $x_0 \in (-R,R)$ and $|x_0| < c < d < R$, then
$$\begin{aligned}
\text{PS convergent at } d
& \Rightarrow  \text{PS absolutely convergent at } c \\[3mm]
& \Rightarrow  \text{PS uniformly convergent on } [-c,c]\\[3mm]
& \Rightarrow  \text{PS continuous on } [-c,c] \\[1mm]
&              \quad\textit{[each term $a_n x^n$ is continuous!]}\\[3mm]
& \Rightarrow  \text{PS continuous at } x_0
\end{aligned}$$

---

## Continuity of the limit

**Corollary:**
$$
\sum_{n=0}^\infty |a_n R^n| \text{ convergent}
\;\;\Rightarrow\;\;
\sum_{n=0}^\infty a_n x^n \text{ uniformly conv.~on } [-R,R]
$$
In particular, the PS is continuous on $[-R,R]$

What if convergence is **conditional** at $x=R$ or $x=-R$?

---

## Summation by parts

**Lemma:** if $s_n = u_1 + \dots + u_n$, then
$$
\sum_{k=1}^n u_k v_k = s_n v_{n+1} + \sum_{k=1}^n s_k(v_k - v_{k+1})
$$

**Proof:** set $s_0 = 0$, then
$$\begin{aligned}
u_k v_k
& =  (s_k-s_{k-1})v_k \\[4mm]
& =  s_k (v_k-v_{k+1}) + \underbrace{s_k v_{k+1} - s_{k-1}v_k}_{\text{telescoping terms!}} \qquad \forall\, k=1,\dots,n
\end{aligned}$$

---

## Abel's lemma

**Lemma:** assume that $(u_n)$ and $(v_n)$ satisfy

- $|u_1 + \dots + u_n| \leq C \quad \forall\,n\in\mathbb{N}$
- $0 \leq v_{n+1} \leq v_n \quad \forall\,n\in\mathbb{N}$

Then
$$
\bigg|\sum_{k=1}^n u_k v_k \bigg| \leq C v_{1} \qquad\forall\,n\in\mathbb{N}
$$

---

## Abel's lemma

**Proof:** if $s_n = u_1 + \dots + u_n$, then
$$\begin{aligned}
\left|\sum_{k=1}^n u_k v_k \right|
& =     \left|s_n v_{n+1} + \sum_{k=1}^n s_k(v_k - v_{k+1})\right| \\[3mm]
& \leq  |s_n| v_{n+1} + \sum_{k=1}^n |s_k|(v_k - v_{k+1}) \\[3mm]
& \leq  C\left(v_{n+1} + \sum_{k=1}^n (v_k - v_{k+1})\right) \\[4mm]
& =     Cv_{1}
\end{aligned}$$

---

## Abel's theorem

**Theorem:**

1. PS converges at $x=R \;\;\Rightarrow\;\;$ PS conv.~uniformly on $[0,R]$
2. PS converges at $x=-R \;\;\Rightarrow\;\;$ PS conv.~uniformly on $[-R,0]$

---

## Abel's theorem

**Proof (1):** for all $\epsilon>0$ there exists $N\in\mathbb{N}$ s.t.
$$
n > m \geq N \quad\Rightarrow\quad
\bigg|\sum_{k=m+1}^n a_k R^k\bigg| < \epsilon
$$

Take any $x\in[0,R]$ and set
$$
v_k = \left(\frac{x}{R}\right)^k, \qquad
u_k
=
\begin{cases}
a_k R^k & \text{if } k \geq m+1, \\
0       & \text{otherwise}
\end{cases}
$$

From Abel's lemma we get the Cauchy criterion:
$$
\bigg|\sum_{k=m+1}^n a_k x^k \bigg|
=
\bigg|\sum_{k=1}^n u_k v_k\bigg|
<
\epsilon \cdot \frac{x}{R} \leq \epsilon \qquad \forall\, x\in[0,R]
$$

---

# Term-wise differentiation

## Differentiation does not change $R$!

**Theorem:**
$$
\sum_{n=0}^\infty a_n x^n \text{ conv.~on } (-R,R)
\;\;\Rightarrow\;\;
\sum_{n=0}^\infty na_n x^{n-1} \text{ conv.~on } (-R,R)
$$

**Proof:** if $|c|<1$, then there exists $M > 0$ s.t.
$$
|nc^{n-1}| \leq M \quad\forall\,n\in\mathbb{N}
$$

Let $|x| < t < R$, then
$$
|na_n x^{n-1}|
=
\frac{1}{t}\left(n\left|\frac{x}{t}\right|^{n-1}\right)|a_n t^n|
\leq
\frac{M}{t} |a_n t^n|
$$

Apply comparison test

---

## Recall: preservation of differentiability

**Theorem:** assume

1. $f_n : [a,b] \to \mathbb{R}$ is differentiable for all $n$
2. $\sum_{n=1}^\infty f_n' \to g$ uniformly on $[a,b]$
3. $\sum_{n=1}^\infty f_n(x_0)$ converges for some $x_0\in[a,b]$

Then there exists a differentiable $f : [a,b]\to\mathbb{R}$ s.t.
$$
\sum_{n=1}^\infty f_n \to f \quad\text{uniformly}
\qquad\text{and}\qquad
f' = \sum_{n=1}^\infty f_n'
$$

*[Term-wise Differentiability Theorem]*

---

## Differentiation can be done term-by-term!

**Theorem:** for any PS with radius $R$ we have
$$
\bigg(\sum_{n=0}^\infty a_n x^n\bigg)' = \sum_{n=1}^\infty na_n x^{n-1} \qquad \forall\,x \in (-R,R)
$$

**Proof:** let $0 \leq c < R$, then

- $\sum_{n=0}^\infty na_n x^{n-1} \text{ converges uniformly on } [-c,c]$
- $\sum_{n=0}^\infty a_n x^n \text{ converges at } x = 0$

Now apply Term-wise Differentiability Theorem

*[Note: we can apply the theorem any number of times!]*

---

## Differentiation

**Example:** for all $x \in (-1,1)$ we have
$$\begin{aligned}
\sum_{n=1}^\infty \frac{(-1)^{n+1}}{n}x^n & \to f(x) \tag{$*$} \\[3mm]
\sum_{n=1}^\infty (-1)^{n+1}x^{n-1}       & \to \frac{1}{1+x} = f'(x) \;\;\Rightarrow\;\; f(x) = \log|1+x| + C
\end{aligned}$$

Note that:

- $C = f(0) = 0$ so $f(x) = \log|1+x|$
- Abel's Theorem $\;\Rightarrow\;$ PS in ($*$) converges uniformly on $[0,1]$
- Hence, PS in ($*$) is continuous at $x=1$

---

## Differentiation

**Example (ctd):**
$$
\sum_{n=1}^\infty \frac{(-1)^{n+1}}{n}
=
\lim_{x \to 1} \sum_{n=1}^\infty \frac{(-1)^{n+1}}{n}x^n
=
\lim_{x \to 1} f(x)
=
f(1)
=
\log 2
$$

Conclusion:
$$
\log 2 = 1 - \frac{1}{2} + \frac{1}{3} - \frac{1}{4} + \cdots
$$
