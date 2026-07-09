(** * RUG.Analysis.Taylor — Taylor's theorem and Taylor series.

  #<a href="../../index.html##lecture14">Lecture 14</a>#.

  Formalizes Abbott §6.6 and §8.6: Taylor polynomials, the Lagrange
  remainder formula, and Taylor series for exp, sin, cos. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.Ranalysis1.
From Stdlib Require Import Reals.Rtrigo_def.
From Stdlib Require Import Reals.Exp_prop.
From Stdlib Require Import micromega.Lra.
Require Export RUG.Analysis.Derivatives.
Require Export RUG.Analysis.PowerSeries.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Taylor polynomials for exp *)

(** The Taylor polynomial of degree [n] for [f] around [0] is
    [sₙ(x) = ∑_{k=0}^n f^{(k)}(0)/k! · xᵏ]; the Lagrange remainder is
    [Eₙ(x) = f(x) - sₙ(x)]. For [f(x) = eˣ] all derivatives at [0] equal [1],
    so [sₙ(x) = ∑_{k=0}^n xᵏ/k!]. *)

(** The [n]-th Taylor polynomial of exp at 0. *)
(* TODO: introduce fact before uncommenting 

  Fixpoint T_exp (n : nat) (x : R) : R :=
  match n with
  | O    => 1
  | S n' => T_exp n' x + x ^ n / INR (fact n)
  end.

Lemma T_exp_0 (x : R) : T_exp 0%nat x = 1.
Proof. reflexivity. Qed.

Lemma T_exp_1 (x : R) : T_exp 1%nat x = 1 + x.
Proof. simpl. lra. Qed.

Lemma T_exp_2 (x : R) : T_exp 2%nat x = 1 + x + x ^ 2 / 2.
Proof. simpl. lra. Qed.


(** ** Taylor's theorem with Lagrange remainder *)

(** Theorem 14.2 (Lagrange remainder): if [f] is [(n+1)] times differentiable on
    [[a,b]], then for all [x ∈ [a,b]] there exists [c] between [a] and [x] such
    that [f(x) = Tₙ(x) + f^{(n+1)}(c) / (n+1)! · (x-a)^{n+1}].

    Proof idea: apply Rolle's theorem [n+1] times to an auxiliary function that
    interpolates [f] and its Taylor polynomial. For [eˣ] this yields
    [eˣ = ∑_{k=0}^n xᵏ/k! + e^c/(n+1)! · x^{n+1}] with [c ∈ (0,x)]; since
    [e^c ≤ eˣ], the remainder [≤ eˣ · x^{n+1}/(n+1)! → 0]. *)
Theorem lagrange_remainder_bound (f : R → R) (a x : R) (n : nat)
    (Hn : ∀ k, (k ≤ n)%nat → derivable f) :
    ∃ c : R, (Rmin a x < c < Rmax a x) ∧
    f x = sum_f_R0 (fun k =>
        derive_pt f^{(k)} a (Hn k (Nat.le_refl k)) / INR (fact k) * (x - a) ^ k
      ) n +
    derive_pt f^{(S n)} c (Hn (S n) (Nat.le_refl (S n))) /
      INR (fact (S n)) * (x - a) ^ (S n).
Proof.
  Admitted.
*)

(** ** Sinusoidal bounds *)

(** The first-order Taylor polynomial of [sin] at [0]. *)
Definition T_sin1 (x : R) : R := x.

(** Theorem 14.3 (upper bound): [sin x < x] for [x > 0]. The degree-1 Taylor
    polynomial of [sin] at [0] is [s₁(x) = x], and this is the Stdlib lemma
    [sin_lt_x]. *)
Lemma sin_lt_x (x : R) (Hx : 0 < x) : sin x < x.
Proof.
  Admitted.

(** Theorem 14.3 (lower bound): [x - x³/6 ≤ sin x] for [0 ≤ x ≤ π/2].

    Proof idea: this follows from the alternating series estimate for
    [sin x = x - x³/3! + x⁵/5! - ⋯]; truncating after the cubic term gives a
    lower bound on [[0, π/2]]. *)
Lemma sin_ge_taylor (x : R) (Hx0 : 0 ≤ x) (HxPI : x ≤ PI / 2) :
    x - x ^ 3 / 6 ≤ sin x.
Proof.
  Admitted.

(** ** Error bound for the linear approximation of sin *)

(** Theorem 14.4: [|sin x - x| ≤ x³/6] for [0 < x ≤ π/2], so the linear
    approximation [sin x ≈ x] has error at most [x³/6].

    Proof idea: the upper bound [sin x < x] gives [sin x - x < 0], so
    [|sin x - x| = x - sin x]; the lower bound [sin x ≥ x - x³/6] then gives
    [x - sin x ≤ x³/6]. *)
Lemma sin_approx_error (x : R) (Hx0 : 0 < x) (HxPI : x ≤ PI / 2) :
    Rabs (sin x - x) ≤ x ^ 3 / 6.
Proof.
  Admitted.
