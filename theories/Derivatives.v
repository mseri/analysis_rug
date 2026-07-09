(** * RUG.Analysis.Derivatives — Differentiability and the mean value theorem.

  #<a href="../../index.html##lecture10">Lecture 10</a>#.

  Formalizes Abbott §5.2–5.3: differentiability at a point,
  differentiable implies continuous, Fermat's theorem on local extrema,
  the mean value theorem, and Darboux's intermediate value theorem for
  derivatives. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.Ranalysis1.
From Stdlib Require Import Reals.Ranalysis5.
From Stdlib Require Import Reals.MVT.
From Stdlib Require Import micromega.Lra.
Require Export RUG.Analysis.Continuity.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Differentiable implies continuous *)

(** Theorem 10.2: if [g] is differentiable at [x₀] then [g] is continuous at
    [x₀]. *)
Lemma differentiable_implies_continuous (g : ℝ → ℝ) (x0 : ℝ)
    (Hd : derivable_pt g x0) :
    continuity_pt g x0.
Proof.
  By derivable_continuous_pt we conclude that continuity_pt g x0.
Qed.

(** ** Fermat's theorem *)

(** If [h] is differentiable on [(a,b)] and has a local extremum at [c ∈ (a,b)],
    then [h'(c) = 0]. *)
Lemma fermat (h : ℝ → ℝ) (a b c : ℝ)
    (Hab : a < b) (Hac : a < c) (HcB : c < b)
    (Hd : ∀ x, a < x < b → derivable_pt h x)
    (Hloc : (∃ δ > 0, ∀ x, Rabs (x - c) < δ → h x ≤ h c) ∨
            (∃ δ > 0, ∀ x, Rabs (x - c) < δ → h c ≤ h x)) :
    derive_pt h c (Hd c (conj Hac HcB)) = 0.
Proof.
  Admitted.

(** ** Mean value theorem *)

(** Theorem 10.4 (mean value theorem): if [h] is continuous on [[a,b]] and
    differentiable on [(a,b)], then there exists [c ∈ (a,b)] with
    [h'(c) = (h(b) - h(a))/(b - a)].

    Proof idea: subtract the secant line from [h] to obtain a function with equal
    values at [a] and [b], then apply Rolle's theorem. *)
Theorem mean_value_theorem (h : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hcont : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt h x)
    (Hdiff : ∀ x, a < x ∧ x < b → derivable_pt h x) :
    ∃ c, a < c ∧ c < b ∧
      ∃ Hc : derivable_pt h c,
        derive_pt h c Hc = (h b - h a) / (b - a).
Proof.
  Admitted.

(** ** Consequence: zero derivative implies constant *)

(** If [φ] is differentiable with [φ'(x) = 0] everywhere, then [φ] is constant. *)
Lemma zero_derivative_constant (phi : ℝ → ℝ) (Hd : derivable phi)
    (Hz : ∀ x ∈ ℝ, derive_pt phi x (Hd x) = 0) :
    ∀ x ∈ ℝ, ∀ y ∈ ℝ, phi x = phi y.
Proof.
  Admitted.

(** ** MVT consequence: bound on function growth *)

(** If [|φ'| ≤ M] on an interval, then [|φ(b) - φ(a)| ≤ M · |b - a|]. *)
Lemma mvt_bound (psi : ℝ → ℝ) (Hd : derivable psi) (a v : ℝ)
    (M : ℝ) (HM : ∀ x : ℝ, Rabs (derive_pt psi x (Hd x)) ≤ M) :
    Rabs (psi v - psi a) ≤ M * Rabs (v - a).
Proof.
  Admitted.

(** ** Derivative of the squaring function *)

(** Theorem 10.1: the derivative of [x ↦ x²] at [x₀] is [2·x₀].

    Proof idea: apply the power rule [d/dx xⁿ = n·xⁿ⁻¹] with [n = 2]. *)
Lemma sq_derivative (x0 : ℝ) :
    derive_pt (fun y => y ^ 2) x0 (derivable_pt_pow 2 x0) = 2 * x0.
Proof.
  ltac1:(rewrite derive_pt_pow; simpl; ring).
Qed.

(** ** Rolle's theorem *)

(** Theorem 10.3 (Rolle's theorem): if [h] is continuous on [[a,b]],
    differentiable on [(a,b)] and [h a = h b], then [h'(c) = 0] for some
    [c ∈ (a,b)].

    Proof idea: by the extreme value theorem [h] attains a maximum and a minimum
    on [[a,b]]. If both occur at the endpoints then [h] is constant and any
    interior point works; otherwise an interior extremum has, by Fermat's
    theorem, a vanishing derivative. *)
Lemma rolle_theorem (h : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hcont : ∀ c : ℝ, a ≤ c ∧ c ≤ b → continuity_pt h c)
    (Hd : ∀ c : ℝ, a < c ∧ c < b → derivable_pt h c)
    (Heq : h a = h b) :
    ∃ c : ℝ, a < c ∧ c < b ∧ ∃ Hc : a < c ∧ c < b, derive_pt h c (Hd c Hc) = 0.
Proof.
  Admitted.

(** ** Positive derivative implies strictly increasing *)

(** Theorem 10.5: if [ψ' > 0] on [(a,v)] then [ψ] is strictly increasing on
    [[a,v]].

    Proof idea: for [a ≤ x < y ≤ v], the mean value theorem gives a point
    [c ∈ (x,y) ⊂ (a,v)] with [ψ(y) - ψ(x) = ψ'(c)·(y - x)]. Since [ψ'(c) > 0]
    and [y - x > 0], we get [ψ(y) > ψ(x)]. *)
Lemma positive_derivative_strictly_increasing (psi : ℝ → ℝ) (Hd : derivable psi)
    (a v : ℝ)
    (Hderiv_pos : ∀ x : ℝ, a < x ∧ x < v → 0 < derive_pt psi x (Hd x)) :
    ∀ x ∈ ℝ, ∀ y ∈ ℝ, a ≤ x → x < y → y ≤ v → psi x < psi y.
Proof.
  Admitted.
