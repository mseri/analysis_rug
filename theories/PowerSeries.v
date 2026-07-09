(** * RUG.Analysis.PowerSeries — Power series and radius of convergence.

  #<a href="../../index.html##lecture13">Lecture 13</a>#.

  Formalizes Abbott §6.5: radius of convergence, Abel's theorem,
  term-by-term differentiation and integration of power series. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.PSeries_reg.
From Stdlib Require Import micromega.Lra.
From Waterproof Require Import Libs.Analysis.Series.
From Waterproof Require Import Libs.Analysis.Subsequences.
Require Export RUG.Analysis.FunctionSequences.
Require Export RUG.Analysis.Series.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

Notation "∑" := partial_sums (at level 50) : R_scope.

(** ** Radius of convergence *)

(** The radius of convergence of [∑ aₙ xⁿ] is the supremum of all [r ≥ 0]
    for which the series converges. *)

(** A power series converging at [x₀] converges absolutely on [(-|x₀|, |x₀|)].

    Proof idea: from convergence at [x₀] the terms [aₙ x₀ⁿ] are bounded, say
    [|aₙ x₀ⁿ| ≤ M]. Then [|aₙ xⁿ| = |aₙ x₀ⁿ| · |x/x₀|ⁿ ≤ M · |x/x₀|ⁿ], and
    [|x/x₀| < 1] gives a convergent geometric bound. *)
Lemma abel_lemma (a : ℕ → ℝ) (x0 : ℝ)
    (H : ∃ L : ℝ, ∑ (fun n => a n * x0 ^ n) ⟶ L)
    (x : ℝ) (Hx : Rabs x < Rabs x0) :
    ∃ L : ℝ, ∑ (fun n => Rabs (a n * x ^ n)) ⟶ L.
Proof.
  Admitted.

(** ** Uniform convergence on compact sub-intervals *)

(** Theorem 13.3: if the radius of convergence is [R > 0], then [∑ aₙ xⁿ]
    converges uniformly on every [[−r, r]] with [r < R].

    Proof idea: pick [r'] with [r < r' < R]. The series converges absolutely at
    [r'], so [∑ |aₙ| (r')ⁿ < ∞]. For [x ∈ [−r, r]],
    [|aₙ xⁿ| ≤ |aₙ| rⁿ ≤ |aₙ| (r')ⁿ], so the Weierstrass M-test gives uniform
    convergence. *)
Lemma power_series_uniform_on_compact (a : ℕ → ℝ) (R r : ℝ)
    (HR : R > 0) (Hr0 : 0 < r) (HrR : r < R)
    (Hconv : ∀ x : ℝ, Rabs x < R →
      ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L) :
    ∃ g : ℝ → ℝ,
      converges_uniformly
        (fun N x => sum_f_R0 (fun n => a n * x ^ n) N)
        g
        (fun x => Rabs x ≤ r).
Proof.
  Admitted.

(** ** Continuity of power series *)
(* TODO: This part needs to be formalized properly still.
         The limiting function, denoted Series below, is
         still not defined.

(** A power series is continuous on its open interval of convergence. *)
Lemma power_series_continuous (a : ℕ → ℝ) (R : ℝ) (HR : R > 0)
    (Hconv : ∀ x : ℝ, Rabs x < R →
      ∃ L : ℝ, Series (fun n => a n * x ^ n) ⟶ L)
    (x : ℝ) (Hx : Rabs x < R) :
    continuity_pt (fun x => Series (fun n => a n * x ^ n)) x.
Proof.
  Admitted.

(** ** Term-by-term differentiation *)

(** Theorem 13.4 (term-by-term differentiation): the derivative of [∑ aₙ xⁿ] is
    [∑ n aₙ xⁿ⁻¹], with the same radius of convergence.

    Proof idea: (1) the differentiated series converges for [|x| < R] — pick [t]
    with [|x| < t < R]; since [n(|x|/t)ⁿ⁻¹] is bounded by some [M], we have
    [|n aₙ xⁿ⁻¹| ≤ (M/t)|aₙ tⁿ|] and [∑ |aₙ tⁿ|] converges; (2) it converges
    uniformly on [[−r, r]] for [r < R] (M-test as in 13.3); (3) apply the
    term-wise differentiability theorem (Abbott 6.5.3). *)
Lemma power_series_termwise_derivative (a : ℕ → ℝ) (R : ℝ)
    (HR : R > 0)
    (Hconv : ∀ x : ℝ, Rabs x < R →
      ∃ L : ℝ, Series (fun n => a n * x ^ n) ⟶ L)
    (x : ℝ) (Hx : Rabs x < R) :
    derivable_pt (fun x => Series (fun n => a n * x ^ n)) x.
Proof.
  Admitted.

(** ** Absolute convergence strictly inside the radius *)

(** Theorem 13.2: if the radius of convergence is [R > 0] (so the series
    converges at every [r] with [0 < r < R]), then it converges absolutely at
    every [x] with [|x| < R].

    Proof idea: pick [r] with [|x| < r < R] (e.g. [r = (|x| + R)/2]); the series
    converges at [r], so Abel's lemma with [x₀ = r] gives absolute convergence
    at [x]. *)
Lemma power_series_abs_convergent (a : ℕ → ℝ) (R : ℝ) (HR : R > 0)
    (Hcv_inside : ∀ r : ℝ, 0 < r → r < R →
      ∃ L : ℝ, Series (fun n => a n * r ^ n) ⟶ L)
    (x : ℝ) (Hx : Rabs x < R) :
    ∃ L : ℝ, Series (fun n => Rabs (a n * x ^ n)) ⟶ L.
Proof.
  Admitted.
*)