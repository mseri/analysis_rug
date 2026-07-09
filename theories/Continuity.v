(** * RUG.Analysis.Continuity — Continuous functions and their consequences.

  Lecture 9 (lecture09_continuity.mv).

  Formalizes Abbott §4.3–4.5: continuity at a point, continuity on sets,
  the extreme value theorem, the intermediate value theorem, and uniform
  continuity. Uses [Analysis.Compactness] for compact domain results. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.Ranalysis5.
From Stdlib Require Import Reals.Rtopology.

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
