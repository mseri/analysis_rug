---
title: "Analysis"
author: "Marcello Seri, m.seri@rug.nl, slides by Alef Sterk"
date: "Lecture 12, Friday 20 December 2024"
---

Topics:
- Abbott §6.3: Uniform convergence and differentiation
- Abbott §6.4: Series of functions

Formalization: [`FunctionSequences.v`](docs/rocq/RUG.Analysis.FunctionSequences.html), [`Series.v`](docs/rocq/RUG.Analysis.Series.html)

---

# Uniform convergence

## Recap

Consider a **sequence of functions** $f_n : A \to \mathbb{R}$

1. What does "$f = \lim f_n$" mean?
2. Which properties of $f_n$ carry over to $f$?

---

## Recap

**Definitions:**

$(f_n)$ **converges pointwise** on $A$ to $f$ if for all $x \in A$ we have:
$$
\forall\,\epsilon>0 \quad
\exists\,N_{\epsilon, x} \in \mathbb{N}
\quad\text{s.t.}\quad
n \geq N_{\epsilon, x}
\quad\Rightarrow\quad
|f_n(x)-f(x)| < \epsilon
$$

$(f_n)$ **converges uniformly** on $A$ to $f$ if:
$$
\forall\,\epsilon>0\quad
\exists\,N_\epsilon\in\mathbb{N}
\quad\text{s.t.}\quad
n \geq N_\epsilon
\quad\Rightarrow\quad
|f_n(x)-f(x)| < \epsilon
\quad
\forall\, x \in A
$$

---

## Cauchy criterion

**Theorem:** the following statements are equivalent:

1. $f_n$ converges uniformly on $A$
2. for all $\epsilon>0$ there exists $N_\epsilon\in\mathbb{N}$ s.t.
$$
n, m \geq N_\epsilon
\quad\Rightarrow\quad
|f_n(x)-f_m(x)| < \epsilon
\qquad\forall\,x\in A
$$

---

## Cauchy criterion

**Proof ($1\Rightarrow 2$):** assume $f_n\to f$ uniformly

For all $\epsilon>0$ there exists $N_\epsilon \in \mathbb{N}$ s.t.
$$\begin{aligned}
  n \geq N_\epsilon & \Rightarrow |f_n(x)-f(x)| < \frac{\epsilon}{2} \qquad\forall\,x\in A \\[7mm]
n,m \geq N_\epsilon & \Rightarrow |f_n(x)-f_m(x)| = |f_n(x)-f(x) + f(x)-f_m(x)| \\[3mm]
 & \hspace{25mm} \leq |f_n(x)-f(x)| + |f(x)-f_m(x)| \\[3mm]
 & \hspace{25mm} < \frac{\epsilon}{2} + \frac{\epsilon}{2} = \epsilon \qquad\forall\,x\in A
\end{aligned}$$

---

## Cauchy criterion

**Proof ($1\Leftarrow 2$):** for all $\epsilon>0$ there exists $N_\epsilon \in \mathbb{N}$ s.t.
$$\begin{aligned}
n,m \geq N_\epsilon & \Rightarrow |f_n(x)-f_m(x)| < \epsilon \quad\forall\,x \in A \\[3mm]
           & \Rightarrow f(x) := \lim f_n(x) \quad\text{exists } \forall\,x \in A \\[7mm]
n,m \geq N_\epsilon & \Rightarrow f_n(x) - \epsilon < f_m(x) < f_n(x) + \epsilon \quad\forall\,x \in A \\[7mm]
n \geq N_\epsilon   & \Rightarrow f_n(x) - \epsilon \leq f(x) \leq f_n(x) + \epsilon \quad\forall\,x \in A \quad (m\to\infty) \\[3mm]
           & \Rightarrow |f_n(x)-f(x)| \leq \epsilon \quad\forall\,x \in A
\end{aligned}$$

---

## Preservation of continuity

**Theorem:** if $f_n\to f$ uniformly on $A$, then
$$
f_n \text{ continuous on $A$ for all $n$}
\quad\Rightarrow\quad
f \text{ continuous on $A$}
$$

**Question:** does uniform convergence preserve differentiability?

---

## A counter example

![](../fig/lec12-example6a.pdf)

**Exercise:** $f_n(x) = \sqrt{x^2 + 1/n} \to |x|$ uniformly on $[-1,1]$

Every $f_n$ is differentiable at $x=0$, but the limit is **NOT**!

---

## Preservation of differentiability

**Lemma:** assume that

1. $f_n : [a,b] \to \mathbb{R}$ differentiable for all $n$
2. $f_n'$ converges uniformly on $[a,b]$ *(note the prime!)*
3. $f_n(x_0)$ converges for some $x_0\in [a,b]$

Then $f_n$ converges uniformly on $[a,b]$

---

## Preservation of differentiability

**Proof:** for each $\epsilon>0$ there exists $N_1, N_2\in\mathbb{N}$ such that
$$\begin{aligned}
n,m \geq N_1
 & \;\;\Rightarrow\;\;
|f_n'(x)-f_m'(x)| < \frac{\epsilon}{2(b-a)}\qquad\forall\,x\in [a,b]  \\[5mm]
n,m \geq N_2
 & \;\;\Rightarrow\;\; \big|f_n(x_0)-f_m(x_0)\big| < \frac{\epsilon}{2}
\end{aligned}$$

**Claim:**
$$
n,m \geq \max\{N_1,N_2\}
\quad\Rightarrow\quad
|f_n(x) - f_m(x)| < \epsilon \qquad\forall\,x\in [a,b]
$$

---

## Preservation of differentiability

**Proof of claim:** apply MVT to $g = f_n - f_m$:

$$\begin{aligned}
g(x)
& = g(x) - g(x_0) + g(x_0) \\[3mm]
& = g'(c)(x-x_0) + g(x_0) \qquad\text{$c$ between $x$ and $x_0$} \\[6mm]
|g(x)| & \leq |g'(c)|\cdot|x-x_0| + |g(x_0)| \\[3mm]
& \leq |g'(c)|\cdot(b-a) + |g(x_0)| \\[6mm]
|f_n(x) - f_m(x)| & \leq |f_n'(c)-f_m'(c)|\cdot(b-a) + |f_n(x_0) - f_m(x_0)|
\end{aligned}$$

---

## Preservation of differentiability

**Theorem:** assume that

1. $f_n : [a,b] \to \mathbb{R}$ differentiable for all $n$
2. $f_n'\to g$ uniformly on $[a,b]$
3. $f_n(x_0)$ converges for some $x_0\in [a,b]$

Then there exists a differentiable $f : [a,b]\to\mathbb{R}$ such that
$$
f_n \to f \quad\text{uniformly} \qquad\text{and}\qquad f'=g
$$

**Moral:** $(\lim f_n)' = \lim (f_n')$ *— limit and derivative can be swapped*

---

## Preservation of differentiability

**Proof:** Lemma $\;\Rightarrow\; f_n\to f$ uniformly on $[a,b]$ for some $f$

Let $c \in [a,b]$ and $\epsilon>0$ be arbitrary

To prove: there exists $\delta>0$ such that
$$
0 < |x-c|<\delta
\quad\Rightarrow\quad
\left|\frac{f(x)-f(c)}{x-c}-g(c)\right| < \epsilon
$$

---

## Preservation of differentiability

**Proof (ctd):** show there exists $n\in\mathbb{N}$ and $\delta>0$ s.t.
$$\begin{aligned}
\left|\frac{f(x)-f(c)}{x-c}-\frac{f_n(x)-f_n(c)}{x-c}\right| & \leq \epsilon / 3 \\[5mm]
\left|\frac{f_n(x)-f_n(c)}{x-c}-f_n'(c)\right| & < \epsilon / 3 \quad\text{for}\quad 0 < |x-c| < \delta \\[5mm]
\left|f_n'(c)-g(c)\right| & < \epsilon / 3 \\[5mm]
\Longrightarrow\quad\left|\frac{f(x)-f(c)}{x-c}-g(c)\right| & < \epsilon \qquad \text{by triangle inequality}
\end{aligned}$$

---

## Preservation of differentiability

**Proof (ctd):** MVT $\;\Rightarrow\;$ there exists $\alpha$ between $x$ and $c$ s.t.
$$
\left|\frac{(f_m(x)-f_n(x)) - (f_m(c)-f_n(c))}{x-c}\right| = |f_m'(\alpha) - f_n'(\alpha)|
$$

There exists $N_1\in\mathbb{N}$ s.t.
$$
n,m \geq N_1 \;\;\Rightarrow\;\; |f_m'(x) - f_n'(x)| < \frac{\epsilon}{3}\qquad\forall\,x \in [a,b]
$$

Order Limit Theorem with $m\to\infty$ gives
$$
n \geq N_1 \;\;\Rightarrow\;\;
\left|\frac{f(x)-f(c)}{x-c} - \frac{f_n(x)-f_n(c)}{x-c}\right| \leq \frac{\epsilon}{3}
$$

---

## Preservation of differentiability

**Proof (ctd):** there exists $N_2\in\mathbb{N}$ s.t.
$$
n \geq N_2 \quad\Rightarrow\quad |f_n'(c)-g(c)| < \frac{\epsilon}{3}
$$

Now fix $n = \max\{N_1,N_2\}$ and pick $\delta>0$ s.t.
$$
0 < |x-c| < \delta
\quad\Rightarrow\quad
\left|\frac{f_n(x)-f_n(c)}{x-c}-f_n'(c)\right| < \frac{\epsilon}{3}
$$

---

# Series of functions

## Series of functions

**Definition:** let $f_n : A \to \mathbb{R}$ and $s_n = f_1 + \dots + f_n$, then

$$\begin{aligned}
\sum_{n=1}^\infty f_n \to f \text{ pointwise} & \quad\text{means}\quad s_n \to f \text{ pointwise} \\[5mm]
\sum_{n=1}^\infty f_n \to f \text{ uniformly} & \quad\text{means}\quad s_n \to f \text{ uniformly}
\end{aligned}$$

---

## Cauchy criterion

**Theorem:** the following statements are equivalent

1. $\sum_{n=1}^\infty f_n$ converges uniformly on $A$
2. for all $\epsilon>0$ there exists $N\in\mathbb{N}$ s.t.
$$
n > m \geq N \quad\Rightarrow\quad |f_{m+1}(x) + \dots + f_n(x)| < \epsilon \quad\text{for all } x\in A
$$

**Proof:** follows from
$$
|s_m(x) - s_n(x)| = |f_{m+1}(x) + \dots + f_n(x)|
$$

---

## The Weierstrass test

**Theorem:** assume that

1. $|f_n(x)| \leq C_n$ for all $x\in A$
2. $\sum_{n=1}^\infty C_n$ converges

Then $\sum_{n=1}^\infty f_n$ converges uniformly on $A$

**Proof:** for all $x \in A$ we have
$$
|s_n(x) - s_m(x)| = |f_{m+1}(x) + \dots + f_n(x)| \leq C_{m+1} + \dots + C_n
$$

Cauchy criterion for $\sum_{n=1}^\infty C_n \;\Rightarrow\;$ Cauchy criterion for $s_n$

---

## Preservation of continuity

**Theorem:** assume

1. $\sum_{n=1}^\infty f_n \to f$ uniformly on $A$
2. $f_n$ is continuous on $A$ for all $n$

Then $f$ is continuous on $A$

**Proof:**

$s_n=f_1+\dots+f_n$ is continuous on $A$ for all $n\in\mathbb{N}$

$s_n\to f$ uniformly $\;\Rightarrow\; f$ is continuous on $A$

---

## Preservation of continuity

![](../fig/lec11-saw1.pdf)

Define the continuous(!) function $h : \mathbb{R} \to \mathbb{R}$ by
- $h(x) = |x|$ for $x \in [-1,1]$
- $h(x+2) = h(x)$ for all $x \in \mathbb{R}$

---

## Preservation of continuity

![](../fig/lec11-saw3.pdf)

Graphs of $\displaystyle \sum_{n=0}^m \frac{1}{2^n}h(2^n x)$

---

## Preservation of continuity

![](../fig/lec11-saw4.pdf)

**Claim:** $f(x) = \displaystyle \sum_{n=0}^\infty \frac{1}{2^n}h(2^n x)$ is continuous on $\mathbb{R}$

---

## Preservation of continuity

**Proof:**

$f_n(x) := \displaystyle \frac{1}{2^n}h(2^n x) \;\Rightarrow\; |f_n(x)| \leq \displaystyle\frac{1}{2^n}$
for all $x\in\mathbb{R}$

$\displaystyle\sum_{n=0}^\infty \frac{1}{2^n}$ converges

Weierstrass test $\;\Rightarrow\; \displaystyle\sum_{n=0}^\infty f_n$ converges uniformly on $\mathbb{R}$

$f_n$ continuous on $\mathbb{R}$ for all $n\in\mathbb{N} \;\Rightarrow\; f$ continuous on $\mathbb{R}$

---

## Preservation of differentiability

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

*Term-wise Differentiability Theorem*

---

## Preservation of differentiability

**Example:** $f(x)=\displaystyle\sum_{n=0}^\infty \frac{\sin(2^n x)}{3^n}$ is
differentiable on every $[-c,c]$

- $f_n(x) = \sin(2^n x) / 3^n$ is differentiable for all $n \in \mathbb{N}$

- $|f_n'(x)| \leq (\tfrac{2}{3})^n \quad\forall\,x\in[-c,c]$

  Weierstrass $\;\Rightarrow\; \sum_{n=1}^\infty f_n'(x)$ converges uniformly on $[-c,c]$

- $\sum_{n=1}^\infty f_n(x)$ converges at $x=0$

Apply "Term-wise Differentiability Theorem" *(needs compact intervals!)*
