(** * RUG.Analysis.SequenceExamples — Examples of sequence limits.

  #<a href="../../index.html##lecture03">Lecture 3</a>#.

  Contains examples from Lecture 3: specific limit computations and standard limits.
  Formalizes examples from Abbott §2.2–2.3.

  Note: All proofs are admitted and will be filled in later.
  Note: In Rocq/Coq, natural numbers start from 0, but our sequences correspond
  to Abbott's sequences starting from n=1. We use (n+1) or (INR n + 1) consistently. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.SeqProp.
From Stdlib Require Import Reals.Rpower.
From Stdlib Require Import Arith.Factorial.

From Waterproof Require Export Libs.Analysis.Sequences.
Require Export RUG.Analysis.Sequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".


(** ** Basic limit examples from lecture 3 *)


(** ** Example: limit of (6n+7)/(3n+1)

  Claim: $\displaystyle\lim_{n\to\infty} \frac{6n+7}{3n+1} = 2$ (where n starts from 1 in Abbott).

  In Rocq, we use (n+1) to match Abbott's indexing: the sequence is
  $$\frac{6(n+1)+7}{3(n+1)+1} = \frac{6n+13}{3n+4}$$ for n:ℕ.

  Proof sketch:
  $\begin{aligned}
  \left|\frac{6(n+1)+7}{3(n+1)+1} - 2\right| 
  &= \left|\frac{6n+13}{3n+4} - 2\right|
  = \left|\frac{6n+13 - 6n - 8}{3n+4}\right| 
  = \frac{5}{3n+4} < \frac{5}{3(n+1)}. 
  \end{aligned}$

  For any ε > 0, choose N such that 1/(N+1) < 3ε/5. Then for n ≥ N,
  $$\frac{5}{3(n+1)} \leq \frac{5}{3(N+1)} < \varepsilon.$$ *)
Lemma limit_6n_plus_7_over_3n_plus_1 : 
    (fun n : ℕ => (6 * (INR n + 1) + 7) / (3 * (INR n + 1) + 1)) ⟶ 2.
Proof.
  Admitted.


(** ** Standard limits from lecture 3 *)


(** ** Standard limit: 1/n → 0 

  Claim: $\displaystyle\lim_{n\to\infty} \frac{1}{n} = 0$ (where n starts from 1 in Abbott).

  In Rocq, we use (n+1) to match Abbott's indexing: the sequence is 1/(n+1).

  Proof sketch: For ε > 0, by Archimedean property, there exists N such that
  N > 1/ε. Then for n ≥ N, we have n+1 > N ≥ 1/ε, so 1/(n+1) < ε. *)
Lemma standard_limit_1_over_n : 
    (fun n : ℕ => 1 / (INR n + 1)) ⟶ 0.
Proof.
  Admitted.


(** ** Standard limit: 1/n^2 → 0

  Claim: $\displaystyle\lim_{n\to\infty} \frac{1}{n^2} = 0$ (where n starts from 1 in Abbott).

  In Rocq, we use (n+1) to match Abbott's indexing: the sequence is 1/(n+1)^2.

  Proof sketch: For ε > 0, by Archimedean property, there exists N such that
  N > 1/√ε. Then for n ≥ N, we have n+1 > N ≥ 1/√ε, so (n+1)^2 > 1/ε,
  and thus 1/(n+1)^2 < ε. *)
Lemma standard_limit_1_over_n_squared : 
    (fun n : ℕ => 1 / (INR n + 1)^2) ⟶ 0.
Proof.
  Admitted.


(** ** Standard limit: c^n → 0 for |c| < 1

  Claim: $\displaystyle\lim_{n\to\infty} c^n = 0$ when -1 < c < 1.

  Note: In Rocq, we start from n=0, but the behavior for large n is the same.
  The sequence c^0, c^1, c^2, ... converges to 0.

  Proof sketch: Let |c| = 1/(1+δ) where δ > 0. Then |c^n| = 1/(1+δ)^n.
  By Bernoulli's inequality, (1+δ)^n ≥ 1 + n·δ ≥ n·δ (for n ≥ 1),
  so |c^n| ≤ 1/(n·δ) → 0. *)
Lemma standard_limit_c_to_n (c : ℝ) :
    -1 < c → c < 1 → (fun n : ℕ => c^n) ⟶ 0.
Proof.
  Admitted.


(** ** Standard limit: nth root of c → 1 for c > 0

  Claim: $\displaystyle\lim_{n\to\infty} \sqrt[n]{c} = 1$ for any c > 0 (where n starts from 1 in Abbott).

  In Rocq, we use (n+1) to match Abbott's indexing. Note that Rpower is used for real exponentiation.

  Proof sketch: If c = 1, trivial. If c > 1, let c = 1+h with h > 0.
  By Bernoulli, (1+h)^n ≥ 1 + n·h, so √[n+1]{c} = (1+h)^(1/(n+1)) ≤ (1 + n·h)^(1/(n+1)).
  Taking logs and using l'Hôpital's rule shows the limit is 1.
  For 0 < c < 1, use 1/c > 1 and √[n+1]{c} = 1/√[n+1]{1/c}. *)
Lemma standard_limit_nth_root_of_c (c : ℝ) :
    c > 0 → (fun n : ℕ => Rpower c (1 / (INR n + 1))) ⟶ 1.
Proof.
  Admitted.


(** ** Standard limit: nth root of n → 1

  Claim: $\displaystyle\lim_{n\to\infty} \sqrt[n]{n} = 1$ (where n starts from 1 in Abbott).

  In Rocq, we use (n+1) to match Abbott's indexing. Note that Rpower is used for real exponentiation.

  Proof sketch: For n ≥ 1, we have 1 < √[n+1]{n+1}. Consider ln(√[n+1]{n+1}) = ln(n+1)/(n+1) → 0,
  so √[n+1]{n+1} = e^(ln(n+1)/(n+1)) → e^0 = 1. *)
Lemma standard_limit_nth_root_of_n : 
    (fun n : ℕ => Rpower (INR n + 1) (1 / (INR n + 1))) ⟶ 1.
Proof.
  Admitted.


(** ** Standard limit: n! / n^n → 0

  Claim: $\displaystyle\lim_{n\to\infty} \frac{n!}{n^n} = 0$ (where n starts from 1 in Abbott).

  In Rocq, we use (n+1) to match Abbott's indexing. We use Stdlib.Arith.Factorial.fact
  which computes factorial of natural numbers.

  Proof sketch: Note that n! / n^n = ∏_{k=1}^n (k/n) ≤ (1/√n)^(n/2) by pairing
  terms k and n-k: (k/n)·((n-k)/n) = k(n-k)/n^2 ≤ 1/4 for k = n/2.
  So n! / n^n ≤ (1/4)^(n/2) → 0. *)
Lemma standard_limit_n_factorial_over_n_to_n : 
    (fun n : ℕ => INR (Stdlib.Arith.Factorial.fact (S n)) / (INR (S n))^(S n)) ⟶ 0.
Proof.
  Admitted.
