(** * RUG.Analysis.FunctionSequences — Sequences of functions.

  #<a href="../../index.html##lecture11">Lecture 11</a># and #<a href="../../index.html##lecture12">Lecture 12</a>#.

  Formalizes Abbott §6.2–6.4: pointwise and uniform convergence,
  the Weierstrass M-test, and the interchange of limits with
  continuity and integration for uniformly convergent sequences. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import micromega.Lra.
Require Export RUG.Analysis.Continuity.
Require Export RUG.Analysis.Lib.UniformConvergence.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Pointwise convergence *)

(** The sequence of functions [fₙ(x) = x/n]. *)
Definition fx_over_n : ℕ → ℝ → ℝ := fun n x => x / INR n.

(** The constant zero function. *)
Definition zero_fn : ℝ → ℝ := fun _ => 0.

(** [(fₙ)] converges pointwise to [g] on [A] iff for each [x ∈ A], [fₙ(x) → g(x)]. *)
(** This is [converges_pointwise fn g A] from [Analysis.Lib.UniformConvergence]. *)

(** The sequence [fₙ(x) = x/n] converges pointwise to [0].

    Proof idea: for each fixed [x] and [ε > 0], the Archimedean property gives
    [N > |x|/ε]; then for [n ≥ N ≥ 1], [|fₙ(x)| = |x|/n ≤ |x|/N < ε]. Here the
    threshold [N] depends on [x]. *)
Lemma x_over_n_pointwise :
    converges_pointwise (fun n x => x / INR n) (fun _ => 0) (fun _ => True).
Proof.
  Admitted.

(** Pointwise limit of continuous functions need not be continuous. *)
(** (illustrated by fₙ(x) = xⁿ on [0,1]; limit is the step function) *)

(** ** Uniform convergence *)

(** Uniform convergence on a set implies pointwise convergence.

    Proof idea: for a fixed [x ∈ A], the uniform threshold [N] (which works for
    all points simultaneously) works in particular for the single point [x]. *)
Lemma uniform_implies_pointwise (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ)
    (H : converges_uniformly fn g A) :
    converges_pointwise fn g A.
Proof.
  Admitted.

(** ** Cauchy criterion for uniform convergence *)

(** Theorem 12.4: [(fₙ)] converges uniformly on [A] iff it is uniformly Cauchy:
    for every ε > 0 there exists N such that for all [n, m ≥ N] and all [x ∈ A],
    [|fₙ(x) - fₘ(x)| < ε].

    Proof idea (⇒): by the triangle inequality
    [|fₙ(x) - fₘ(x)| ≤ |fₙ(x) - g(x)| + |g(x) - fₘ(x)| < ε/2 + ε/2 = ε]. *)
Lemma uniform_cauchy_criterion (fn : ℕ → ℝ → ℝ) (A : subset ℝ) :
    (∃ g : ℝ → ℝ, converges_uniformly fn g A) ⇔
    (∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
      Rabs (fn n x - fn m x) < ε).
Proof.
  Admitted.

(** ** Uniform limit of continuous functions is continuous *)

(** Theorem 12.1: if each [fₙ] is continuous at [a] and [(fₙ) ⇉ g] uniformly on
    a neighborhood of [a], then [g] is continuous at [a].

    Proof idea (3ε argument): given [ε > 0], (1) uniform convergence gives [N]
    with [|f_N(x) - g(x)| < ε/3] for all [x]; (2) continuity of [f_N] at [a]
    gives [δ] with [|f_N(x) - f_N(a)| < ε/3] for [|x - a| < δ]; (3) then
    [|g(x) - g(a)| ≤ |g(x) - f_N(x)| + |f_N(x) - f_N(a)| + |f_N(a) - g(a)| < ε]. *)
Theorem uniform_limit_continuous (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a : ℝ)
    (Hfn : ∀ n ∈ ℕ, continuity_pt (fn n) a)
    (Hunif : ∃ A : subset ℝ, A a ∧ converges_uniformly fn g A) :
    continuity_pt g a.
Proof.
  Admitted.

(** ** Weierstrass M-test *)

(** Theorem 12.2 (Weierstrass M-test): if [|fₙ(x)| ≤ Mₙ] for all [x ∈ A] and
    [∑ Mₙ] converges, then [∑ fₙ] converges uniformly on [A].

    Proof idea: use the Cauchy criterion. Since [∑ Mₙ] converges, for [ε > 0]
    there is an [N] such that for [m > n ≥ N],
    [|∑_{k=n+1}^m fₖ(x)| ≤ ∑_{k=n+1}^m |fₖ(x)| ≤ ∑_{k=n+1}^m Mₖ < ε],
    uniformly in [x]. *)
Theorem weierstrass_M_test (fn : ℕ → ℝ → ℝ) (M : ℕ → ℝ) (A : subset ℝ)
    (Hbound : ∀ n ∈ ℕ, ∀ x ∈ A, Rabs (fn n x) ≤ M n)
    (HM : ∃ L ∈ ℝ, (fun n => sum_f_R0 M n) ⟶ L) :
    ∃ g : ℝ → ℝ, converges_uniformly (fun n x => sum_f_R0 (fun k => fn k x) n) g A.
Proof.
  Admitted.

(** ** Term-by-term integration *)

(** If [(fₙ) ⇉ g] uniformly on [[a, b]] and each [fₙ] is integrable,
    then the integrals converge to [∫ g]. *)
Theorem uniform_limit_integral (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ)
    (Hunif : converges_uniformly fn g A)
    (Hfn : ∀ n ∈ ℕ, ∀ x ∈ A, continuity_pt (fn n) x) :
    ∀ x ∈ A, continuity_pt g x.
Proof.
  Admitted.

(** ** Uniform convergence of [x/n] on a bounded interval *)

(** [fₙ(x) = x/n] converges uniformly to [0] on [[−R, R]].

    Proof idea: for [x ∈ [−R, R]] and [n ≥ 1], [|fₙ(x)| = |x|/n ≤ R/n]. The
    bound [R/n] is independent of [x] and tends to [0], giving a uniform
    threshold. *)
Lemma x_over_n_uniform (bR : ℝ) (HR : bR > 0) :
    converges_uniformly fx_over_n zero_fn (fun x => -bR ≤ x ∧ x ≤ bR).
Proof.
  Admitted.

(** ** A pointwise-only example *)

(** [fₙ(0) = 0ⁿ → 0] (pointwise value at the origin).

    For [fₙ(x) = xⁿ] on [[0,1]] and the point [x = 0], [fₙ(0) = 0ⁿ = 0] for all
    [n ≥ 1], so the sequence is eventually the constant [0]. (More generally
    [xⁿ → 0] for [0 ≤ x < 1] and [1ⁿ → 1], so the pointwise limit is the
    indicator of [{1}], which is not continuous.) *)
Lemma zero_pow_to_zero : (fun n : ℕ => (0 : ℝ) ^ n) ⟶ 0.
Proof.
  Admitted.

(** ** Uniform convergence of the geometric series on [[−r, r]] *)

(** Theorem 12.3: for [0 ≤ r < 1], the partial sums [∑ xᵏ] converge uniformly on
    [[−r, r]].

    Proof idea: apply the Weierstrass M-test with [Mₙ = rⁿ]. For [x ∈ [−r, r]],
    [|xⁿ| = |x|ⁿ ≤ rⁿ], and [∑ rⁿ = 1/(1 - r) < ∞]. The uniform limit is
    [g(x) = 1/(1 - x)]. *)
Lemma geometric_series_uniform (r : ℝ) (Hr0 : 0 ≤ r) (Hr1 : r < 1) :
    ∃ g : ℝ → ℝ,
      converges_uniformly
        (fun n x => sum_f_R0 (fun k => x ^ k) n) g (fun x => -r ≤ x ∧ x ≤ r).
Proof.
  Admitted.
