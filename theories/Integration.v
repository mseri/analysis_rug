(** * RUG.Analysis.Integration — The Riemann integral.

  #<a href="../../index.html##lecture15">Lecture 15</a>#.

  Formalizes Abbott §7.2–7.4: the definition of the Riemann integral via
  upper and lower sums, integrability of continuous functions, and basic
  properties (linearity, monotonicity, additivity over intervals). *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.RiemannInt.
From Stdlib Require Import micromega.Lra.
Require Export RUG.Analysis.Continuity.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** The Riemann integral and the Darboux criterion

    For a partition [P = {x₀ < ⋯ < xₙ}] of [[a,b]] and a bounded [f], the upper
    and lower sums are [U(f,P) = ∑ (sup_{[xᵢ₋₁,xᵢ]} f)(xᵢ - xᵢ₋₁)] and
    [L(f,P) = ∑ (inf_{[xᵢ₋₁,xᵢ]} f)(xᵢ - xᵢ₋₁)].

    Darboux criterion (Abbott 7.2.8): a bounded [f] is Riemann integrable on
    [[a,b]] iff for every [ε > 0] there is a partition [P] with
    [U(f,P) - L(f,P) < ε]. (For example the Dirichlet function [𝟙_ℚ] is not
    integrable on [[0,1]], since [U = 1] and [L = 0] for every partition.) *)

(** ** Constant functions are integrable *)

(** Theorem 15.1: the constant function [x ↦ c] is Riemann integrable on
    [[a, b]], for any [a] and [b]. *)
Lemma constant_integrable (a b c : R) :
    Riemann_integrable (fct_cte c) a b.
Proof.
  (* TODO: Error: Could not verify that (Riemann_integrable(fct_cte(c), a, b)).
  By RiemannInt_P6 we conclude that Riemann_integrable (fct_cte c) a b.
Qed. *)
  Admitted.

(** Theorem 15.2: the integral of a constant is [∫_a^b c = c · (b - a)]. *)
Lemma integral_constant (a b c : R)
    (pr : Riemann_integrable (fct_cte c) a b) :
    RiemannInt pr = c * (b - a).
Proof.
  Admitted.

(** ** Continuous functions are integrable *)

(** Theorem 15.3: if [f] is continuous on [[a, b]] (with [a ≤ b]), then [f] is
    Riemann integrable.

    Proof idea: a continuous function on a compact interval is uniformly
    continuous (Heine), so for [ε > 0] a fine enough uniform partition makes each
    oscillation small, giving [U(f,P) - L(f,P) < ε]; apply the Darboux
    criterion. *)
Theorem continuous_integrable (f : R → R) (a b : R)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x) :
    Riemann_integrable f a b.
Proof.
  Admitted.

(** ** Linearity of the integral *)

(** Theorem 15.4(a): the sum of two integrable functions is integrable. *)
Lemma sum_integrable (f g : R → R) (a b : R)
    (pr1 : Riemann_integrable f a b)
    (pr2 : Riemann_integrable g a b) :
    Riemann_integrable (fun x => f x + g x) a b.
Proof.
  Admitted.

(** Theorem 15.4(b): [∫(f + g) = ∫f + ∫g]. *)
Lemma integral_sum (f g : R → R) (a b : R)
    (prf : Riemann_integrable f a b)
    (prg : Riemann_integrable g a b) :
    ∃ prfg : Riemann_integrable (fun x => f x + g x) a b,
      RiemannInt prfg = RiemannInt prf + RiemannInt prg.
Proof.
  Admitted.

(** [∫(c · f) = c · ∫f]. *)
Lemma integral_scalar (f : R → R) (a b c : R)
    (prf : Riemann_integrable f a b) :
    ∃ prcf : Riemann_integrable (fun x => c * f x) a b,
      RiemannInt prcf = c * RiemannInt prf.
Proof.
  Admitted.

(** ** Monotonicity *)

(** Theorem 15.5 (monotonicity): if [f ≤ g] on [(a, b)] then [∫f ≤ ∫g]. *)
Lemma integral_monotone (f g : R → R) (a b : R)
    (prf : Riemann_integrable f a b)
    (prg : Riemann_integrable g a b)
    (Hle : ∀ x, a ≤ x ∧ x ≤ b → f x ≤ g x) :
    RiemannInt prf ≤ RiemannInt prg.
Proof.
  Admitted.

(** ** Additivity over sub-intervals *)

(** [∫_a^b f = ∫_a^c f + ∫_c^b f] for [a ≤ c ≤ b]. *)
Lemma integral_split (f : R → R) (a b c : R)
    (Hac : a ≤ c) (Hcb : c ≤ b)
    (prf : Riemann_integrable f a b) :
    ∃ (pr1 : Riemann_integrable f a c),
    ∃ (pr2 : Riemann_integrable f c b),
      RiemannInt prf = RiemannInt pr1 + RiemannInt pr2.
Proof.
  Admitted.
