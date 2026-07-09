(** * RUG.Analysis.FTC — The fundamental theorem of calculus.

  #<a href="../../index.html##lecture16">Lecture 16</a>#.

  Formalizes Abbott §7.5: the two parts of the fundamental theorem,
  the Cauchy-Schwarz inequality for integrals, and integration by parts. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.RiemannInt.
From Stdlib Require Import Reals.Ranalysis1.
From Stdlib Require Import micromega.Lra.
Require Export RUG.Analysis.Integration.
Require Export RUG.Analysis.Derivatives.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Additivity (Chasles property) *)

(** Theorem 16.1 (Chasles / additivity): if [f] is integrable on [[a,b]],
    [[b,c]] and [[a,c]], then [∫_a^b f + ∫_b^c f = ∫_a^c f], regardless of the
    ordering of [a], [b], [c]. *)
Lemma integral_additive (f : R → R) (a b c : R)
    (pr1 : Riemann_integrable f a b)
    (pr2 : Riemann_integrable f b c)
    (pr3 : Riemann_integrable f a c) :
    RiemannInt pr3 = RiemannInt pr1 + RiemannInt pr2.
Proof.
  Admitted.

(** ** Fundamental theorem of calculus, Part 2 (derivative of the integral)

    Theorem 16.3: if [f] is continuous on [[a,b]], then the integral function
    [F(x) = ∫_a^x f(t) dt] is differentiable on [[a,b]] and [F'(x) = f(x)].

    Proof idea: for [x ≠ c],
    [(F(x) - F(c))/(x - c) - f(c) = 1/(x - c) · ∫_c^x (f(t) - f(c)) dt]. Given
    [ε > 0], continuity of [f] at [c] gives [δ] with [|f(t) - f(c)| < ε] for
    [|t - c| < δ]; then for [|x - c| < δ] the difference quotient is within [ε]
    of [f(c)]. *)

(* TODO: formalize properly

Theorem integral_derivative (f : R → R) (a b x : R)
    (Hx : a ≤ x ∧ x ≤ b)
    (Hf : ∀ t, a ≤ t ∧ t ≤ b → continuity_pt f t) :
    let F := fun x => RiemannInt (continuous_integrable f a x
                       (fun t Ht => Hf t (conj (proj1 Hx) (Rle_trans _ _ _ (proj1 Ht) (proj2 Hx))))) in
    derivable_pt F x ∧ ∀ Hd : derivable_pt F x, derive_pt F x Hd = f x.
Proof.
  Admitted.
  *)

(** ** Fundamental theorem of calculus, Part 1 (antiderivative formula)

    Theorem 16.2: if [f] is continuous on [[a,b]] and [g] is an antiderivative of
    [f] (so [g' = f] on [[a,b]]), then [∫_a^b f = g(b) - g(a)].

    Proof idea: the canonical integral function [G(x) = ∫_a^x f] is an
    antiderivative of [f] (by Part 2), and [∫_a^b f = G(b) - G(a)]. Since [G] and
    [g] are both antiderivatives of the continuous [f], they differ by a constant,
    so [G(b) - G(a) = g(b) - g(a)]. *)
(* TODO: formalize properly

Theorem antiderivative_formula (f g : R → R) (a b : R) (Hab : a ≤ b)
    (prf  : Riemann_integrable f a b)
    (Hf   : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x)
    (Hder : ∀ x, a < x ∧ x < b → derivable_pt g x)
    (Hant : ∀ x (Hx : a < x ∧ x < b),
              derive_pt g x (Hder x Hx) = f x) :
    RiemannInt prf = g b - g a.
Proof.
  Admitted.
  *)

(** ** Integration by parts *)

(** Theorem 16.4 (integration by parts): if [f] and [g] are continuously
    differentiable on [[a, b]], then
    [∫_a^b f g' = f(b)g(b) - f(a)g(a) - ∫_a^b f' g].

    Proof idea: apply Part 1 to the product [f·g], whose derivative is
    [f'·g + f·g'] by the product rule; splitting the integral by linearity and
    rearranging gives the formula. *)
Theorem integration_by_parts (f g : R → R) (a b : R) (Hab : a ≤ b)
    (Hf : derivable f) (Hg : derivable g)
    (Hfcont : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt (fun x => derive_pt f x (Hf x)) x)
    (Hgcont : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt (fun x => derive_pt g x (Hg x)) x) :
    ∃ (pr1 : Riemann_integrable (fun x => f x * derive_pt g x (Hg x)) a b),
    ∃ (pr2 : Riemann_integrable (fun x => derive_pt f x (Hf x) * g x) a b),
      RiemannInt pr1 = f b * g b - f a * g a - RiemannInt pr2.
Proof.
  Admitted.

(** ** Application: ∫₀¹ x dx = 1/2

    Theorem 16.5: [∫₀¹ x dx = 1/2], by Part 1 with antiderivative
    [F(x) = x²/2]: [F(1) - F(0) = 1/2 - 0 = 1/2]. *)

Lemma integral_id_unit (pr : Riemann_integrable id 0 1) :
    RiemannInt pr = 1 / 2.
Proof.
  Admitted.
