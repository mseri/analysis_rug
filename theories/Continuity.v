(** * RUG.Analysis.Continuity — Continuous functions and their consequences.

  #<a href="../../index.html##lecture09">Lecture 9</a>#.

  Formalizes Abbott §4.3–4.5: continuity at a point, continuity on sets,
  the extreme value theorem, the intermediate value theorem, and uniform
  continuity. Uses [Analysis.Compactness] for compact domain results. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.Ranalysis5.
From Stdlib Require Import Reals.Rtopology.
From Stdlib Require Import Logic.ClassicalDescription.

From Waterproof Require Export Notations.Common.
From Waterproof Require Export Notations.Reals.
From Waterproof Require Export Notations.Sets.

From Waterproof Require Import Libs.Analysis.ContinuityDomainR.
Require Export RUG.Analysis.Lib.Compactness.
Require Export RUG.Analysis.Compactness.
Require Export RUG.Analysis.Limits.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Continuity at a point *)

(** Theorem 9.1: the squaring function [x ↦ x²] is continuous at every point [c].

    Proof idea: use the ε–δ definition. The factorization
    [|x² - c²| = |x - c| · |x + c|] is key. If [|x - c| < 1] then
    [|x + c| = |(x - c) + 2c| ≤ |x - c| + 2|c| < 1 + 2|c|]. Taking
    [δ = min(1, ε / (2|c| + 1))] ensures [|x² - c²| < ε]. *)
Lemma sq_continuous (c : ℝ) :
    _limit_ of (fun x => x * x) in c is (c * c).
Proof.
  Admitted.

(** Composition of continuous functions is continuous. *)
Lemma continuous_composition (g : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hg : ∀ x ∈ (fun x => a < x < b), continuity_pt g x) :
    ∀ x ∈ (fun x => a < x < b), continuity_pt g x.
Proof.
  Admitted.

(** A Lipschitz function is continuous. *)
Lemma lipschitz_is_continuous (h : ℝ → ℝ) (x y : ℝ) (M : ℝ)
    (HM : ∀ s ∈ ℝ, ∀ t ∈ ℝ, Rabs (h s - h t) ≤ M * Rabs (s - t)) :
    continuity h.
Proof.
  Admitted.

(** Continuous image of a compact set is compact. *)
Lemma continuous_image_compact (phi : ℝ → ℝ) (X : ℝ → Prop)
    (HX : X is _compact_)
    (Hphi : ∀ x ∈ X, continuity_pt phi x) :
    (fun y => ∃ x ∈ X, y = phi x) is _compact_.
Proof.
  Admitted.

(** ** Sequential characterization of continuity *)

(** Continuity of [f] at [c] is the ε–δ statement
    [∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ ⇒ |f(x) - f(c)| < ε], which in the
    Stdlib is [continuity_pt f c]. *)

(** *Sequential criterion for continuity*: [f] is continuous at [c] iff for
    every sequence [xₙ → c] one has [f(xₙ) → f(c)].

    Proof idea: (⇒) given [ε], continuity yields [δ]; convergence of [xₙ] puts
    the tail within [δ], hence [f(xₙ)] within [ε]. (⇐) contrapositive: a failure
    of continuity produces, taking [δ = 1/n], a sequence [xₙ → c] with
    [|f(xₙ) - f(c)|] bounded below. *)
Lemma continuity_sequential_characterization (f : ℝ → ℝ) (c : ℝ) :
    continuity_pt f c ⇔
    (∀ a : ℕ → ℝ, a ⟶ c → (fun n => f (a n)) ⟶ (f c)).
Proof.
  Admitted.

(** *Algebraic continuity theorem*: sums, products, scalar multiples and (where
    the denominator is nonzero) quotients of functions continuous at [c] are
    continuous at [c].

    Proof idea: immediate from the algebraic limit theorem for functional
    limits, or from the sequential criterion together with the algebraic limit
    theorem for sequences. *)
Lemma algebraic_continuity_theorem (f g : ℝ → ℝ) (c k : ℝ)
    (Hf : continuity_pt f c) (Hg : continuity_pt g c) :
    continuity_pt (fun x => f x + g x) c ∧
    continuity_pt (fun x => f x * g x) c ∧
    continuity_pt (fun x => k * f x) c.
Proof.
  Admitted.

(** ** Pathologies: the Dirichlet and Thomae functions *)

(** A real number is *rational* if it can be written [p/q] with [q ≠ 0]. *)
Definition is_rational (x : ℝ) : Prop :=
    ∃ p : Z, ∃ q : Z, (q <> 0)%Z ∧ x = IZR p / IZR q.

(** The *Dirichlet function* is [𝟙_ℚ]: it equals [1] at rationals and [0] at
    irrationals. (Defined classically, using the decidability oracle
    [excluded_middle_informative].) *)
Definition dirichlet_function (x : ℝ) : ℝ :=
    if excluded_middle_informative (is_rational x) then 1 else 0.

(** The Dirichlet function is continuous at *no* point.

    Proof idea: every neighbourhood of any [c] contains both a rational and an
    irrational (density of [ℚ] and of the irrationals), so [f] takes both
    values [0] and [1] arbitrarily close to [c] and cannot have a limit. *)
Lemma dirichlet_nowhere_continuous :
    ∀ c : ℝ, ¬ continuity_pt dirichlet_function c.
Proof.
  Admitted.

(** *Thomae's function* [t] (the "popcorn function") vanishes at every
    irrational, satisfies [t(0) = 1], and equals [1/q] at a rational [p/q] in
    lowest terms. We characterize it by its defining values. *)

(** Thomae's function is continuous at every irrational point.

    Proof idea: fix an irrational [c] and [ε > 0]. Only finitely many rationals
    in a bounded neighbourhood have denominator [q ≤ 1/ε], so [c] has a
    neighbourhood on which [t < ε]; since [t(c) = 0], this is continuity. *)
Lemma thomae_continuous_at_irrationals (t : ℝ → ℝ)
    (Hirr : ∀ x : ℝ, ¬ is_rational x → t x = 0)
    (Hpos : ∀ x : ℝ, is_rational x → t x > 0)
    (Hsmall : ∀ ε > 0, ∀ M : ℝ, ∃ δ > 0, ∀ x : ℝ,
        Rabs (x - M) < δ → is_rational x → t x < ε ∨ t x = t M) :
    ∀ c : ℝ, ¬ is_rational c → continuity_pt t c.
Proof.
  Admitted.

(** Thomae's function is discontinuous at every rational point.

    Proof idea: at a rational [c], [t(c) > 0], but every neighbourhood contains
    irrationals where [t = 0], so [t] cannot be continuous at [c]. *)
Lemma thomae_discontinuous_at_rationals (t : ℝ → ℝ)
    (Hirr : ∀ x : ℝ, ¬ is_rational x → t x = 0)
    (Hpos : ∀ x : ℝ, is_rational x → t x > 0) :
    ∀ c : ℝ, is_rational c → ¬ continuity_pt t c.
Proof.
  Admitted.

(** ** Extreme value theorem *)

(** Theorem 9.2 (extreme value theorem): a continuous function on a closed
    interval [[a,b]] attains its maximum.

    Proof idea: the image [f([a,b])] is compact, as the continuous image of the
    compact set [[a,b]]. By the definition of compactness the supremum of the
    image is attained at some point in the image, giving a point where the
    maximum is achieved. *)
Theorem extreme_value_theorem (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f x ≤ f c.
Proof.
  Admitted.

(** A continuous function on a closed interval attains its minimum. *)
Theorem extreme_value_theorem_min (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f c ≤ f x.
Proof.
  Admitted.

(** ** Intermediate value theorem *)

(** Theorem 9.3 (intermediate value theorem): if [f] is continuous on [[a,b]]
    and [f(a) < v < f(b)], then there exists [c ∈ (a,b)] with [f(c) = v].

    Proof idea: the bisection method constructs nested intervals
    [Iₙ = [aₙ, bₙ]] with [f(aₙ) < v] and [f(bₙ) ≥ v]. The nested interval
    property yields a point [c] in all intervals. Continuity gives
    [f(c) = limₙ f(aₙ) = limₙ f(bₙ)], and the order limit theorem forces
    [f(c) ≤ v] and [f(c) ≥ v], so [f(c) = v]. *)
Theorem intermediate_value_theorem (f : ℝ → ℝ) (a b v : ℝ)
    (Hab : a < b)
    (Hf  : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x)
    (Hfa : f a < v) (Hfb : v < f b) :
    ∃ c, a < c ∧ c < b ∧ f c = v.
Proof.
  Admitted.

(** ** Uniform continuity *)

(** Theorem 9.4 (Heine's theorem): a continuous function on a compact set is
    uniformly continuous.

    Proof idea: for each point [c] of the set, continuity gives a neighborhood
    on which [f] varies by less than [ε/2]. These neighborhoods form an open
    cover; by compactness a finite subcover exists, and the minimum of the
    corresponding radii provides a uniform [δ]. *)
Theorem continuous_on_compact_uniformly_continuous (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      a ≤ x ∧ x ≤ b → a ≤ y ∧ y ≤ b →
      Rabs (x - y) < δ → Rabs (f x - f y) < ε.
Proof.
  Admitted.

(** [f] is *uniformly continuous* on a set [A] if a single [δ] works for all
    points simultaneously:
    [∀ ε > 0, ∃ δ > 0, ∀ x y ∈ A, |x - y| < δ ⇒ |f(x) - f(y)| < ε]. *)
Definition uniformly_continuous_on (f : ℝ → ℝ) (A : ℝ → Prop) : Prop :=
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      A x → A y → Rabs (x - y) < δ → Rabs (f x - f y) < ε.

(** *Sequential criterion for non-uniform continuity*: [f] fails to be
    uniformly continuous on [A] iff there exist sequences [(xₙ), (yₙ)] in [A]
    with [|xₙ - yₙ| → 0] but [|f(xₙ) - f(yₙ)|] bounded away from [0].

    Proof idea: negate the ε–δ definition and, for the "only if" direction, take
    [δ = 1/n] to build the offending sequences. *)
Lemma non_uniform_continuity_sequential_criterion (f : ℝ → ℝ) (A : ℝ → Prop) :
    ¬ uniformly_continuous_on f A ⇔
    (∃ x : ℕ → ℝ, ∃ y : ℕ → ℝ, ∃ ε0 : ℝ,
      ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
      (fun n => x n - y n) ⟶ 0 ∧
      (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0)).
Proof.
  Admitted.

(** Exercise: [x ↦ √x] is uniformly continuous on [[0, ∞)].

    Proof idea: use the inequality [|√x - √y| ≤ √|x - y|] (which follows from
    [(√x - √y)² ≤ |x - y|] for [x, y ≥ 0]). Given [ε > 0], choosing [δ = ε²]
    makes [|x - y| < δ ⇒ |√x - √y| < ε], with the same [δ] everywhere. *)
Lemma sqrt_uniformly_continuous :
    uniformly_continuous_on sqrt (fun x => 0 ≤ x).
Proof.
  Admitted.
