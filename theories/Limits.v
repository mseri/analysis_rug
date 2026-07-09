(** * RUG.Analysis.Limits — Functional limits (ε-δ definition).

  Lecture 8 (lecture08_limits.mv).

  Formalizes Abbott §4.2: the ε-δ definition of [lim_{x→c} f(x) = L],
  uniqueness of limits, algebraic limit theorem for functions, and
  the sequential characterization of functional limits. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import micromega.Lra.
From Waterproof Require Import Libs.Analysis.ContinuityDomainR.
Require Export RUG.Analysis.Sequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** The ε–δ definition of a functional limit

    For [f : A → ℝ] and [c] a limit point of [A], we write [lim_{x→c} f(x) = L]
    when
    [∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, 0 < |x - c| < δ ⇒ |f(x) - L| < ε].

    In Waterproof this is written [_limit_ of f in c is L]. Note that the value
    [f(c)] need not be defined or equal to [L]. *)

(** ** A linear function has a limit

    Theorem: [lim_{x→2} (3x - 1) = 5].

    Proof strategy: apply the ε–δ definition. Since
    [|f(x) - 5| = |(3x - 1) - 5| = |3x - 6| = 3|x - 2|], if [|x - 2| < δ] then
    [|f(x) - 5| < 3δ]. Choosing [δ = ε/3] makes [|f(x) - 5| < ε]. *)
Lemma limit_linear_example :
    _limit_ of (fun x => 3 * x - 1) in 2 is 5.
Proof.
  Admitted.

(** ** Algebraic limit theorem: sum of limits

    Theorem: if [lim_{x→c} f(x) = L] and [lim_{x→c} g(x) = M], then
    [lim_{x→c} (f + g)(x) = L + M].

    Proof strategy: given [ε > 0], apply the limit definitions for [f] and [g]
    with [ε/2] to obtain [δ₁] and [δ₂]. Taking [δ = min(δ₁, δ₂)] ensures that
    both [|f(x) - L| < ε/2] and [|g(x) - M| < ε/2] hold whenever [0 < |x - c| < δ].
    The triangle inequality then gives [|(f + g)(x) - (L + M)| < ε]. *)
Lemma functional_limit_sum (f g : ℝ → ℝ) (c L M : ℝ)
    (Hf : _limit_ of f in c is L)
    (Hg : _limit_ of g in c is M) :
    _limit_ of (fun x => f x + g x) in c is (L + M).
Proof.
  Admitted.

(** If [lim_{x→c} f(x) = L] and [lim_{x→c} g(x) = M], then
    [lim_{x→c} (f · g)(x) = L · M]. *)
Lemma lim_product (f g : ℝ → ℝ) (c L M : ℝ)
    (Hf : _limit_ of f in c is L)
    (Hg : _limit_ of g in c is M) :
    _limit_ of (fun x => f x * g x) in c is (L * M).
Proof.
  Admitted.

(** ** Sequential characterization *)

(** [lim_{x→c} f(x) = L] iff for every sequence [(xₙ) → c] with [xₙ ≠ c],
    [f(xₙ) → L]. *)
Lemma sequential_limit_characterization (f : ℝ → ℝ) (c L : ℝ) :
    (_limit_ of f in c is L) ⇔
    (∀ a : ℕ → ℝ,
      (∀ n ∈ ℕ, a n ≠ c) → a ⟶ c → (fun n => f (a n)) ⟶ L).
Proof.
  Admitted.

(** ** Divergence criterion *)

(** If two sequences approaching [c] give different limits for [f], then
    [lim_{x→c} f(x)] does not exist. *)
Lemma divergence_criterion (f : ℝ → ℝ) (c : ℝ)
    (a b : ℕ → ℝ) (L M : ℝ) (HLM : L ≠ M)
    (Ha_ne : ∀ n ∈ ℕ, a n ≠ c) (Ha : a ⟶ c)
    (Hb_ne : ∀ n ∈ ℕ, b n ≠ c) (Hb : b ⟶ c)
    (Hfa : (fun n => f (a n)) ⟶ L)
    (Hfb : (fun n => f (b n)) ⟶ M) :
    ¬ (∃ L' : ℝ, _limit_ of f in c is L').
Proof.
  Admitted.

(** ** Absolute value is continuous

    Theorem: the function [f(x) = |x|] is continuous at every point [c ∈ ℝ].

    Proof strategy: use the key inequality [||x| - |c|| ≤ |x - c|], which follows
    from the reverse triangle inequality. For any [ε > 0], taking [δ = ε] ensures
    that [|x - c| < δ] implies [||x| - |c|| < ε]. *)
Lemma abs_continuous (c : ℝ) :
    _limit_ of Rabs in c is (Rabs c).
Proof.
  Admitted.

(** ** Unfolding the limit definition

    Lemma: if [lim_{x→c} f(x) = L], then for every [ε > 0] there exists [δ > 0]
    such that for all [x] with [0 < |x - c| < δ] we have [|f(x) - L| < ε].

    Proof: this is a direct unfolding of the limit definition. *)
Lemma limit_epsilon_delta (f : ℝ → ℝ) (c L : ℝ)
    (Hf : _limit_ of f in c is L) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ ⇒ |f x - L| < ε.
Proof.
  Admitted.
