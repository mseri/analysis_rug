(** * RUG.Analysis.Compactness — Compact subsets of ℝ.

  Lecture 7 (lecture07_compactness.mv).

  Formalizes Abbott §3.3: the Heine-Borel theorem (compact ↔ closed and bounded),
  properties of compact sets, and the nested compact sets property. *)

From Stdlib Require Import Reals.Reals.

From Waterproof Require Export Notations.Common.
From Waterproof Require Export Notations.Reals.
From Waterproof Require Export Notations.Sets.
From Waterproof Require Import Libs.Analysis.OpenAndClosed.
Require Export RUG.Analysis.Topology.
Require Export RUG.Analysis.Lib.Compactness.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Closed intervals are compact *)

(** Every closed bounded interval is compact (Heine-Borel, one direction).

    Proof idea: given a sequence in [[a,b]], Bolzano–Weierstrass provides a
    convergent subsequence, and the order limit theorem places its limit in
    [[a,b]] (from [a ≤ xₙ ≤ b]). *)
Theorem segment_compact (a b : ℝ) :
    [a, b] is _compact_.
Proof.
  By closed_interval_is_compact we conclude that [a, b] is _compact_.
Qed.

(** ** Compact sets are closed and bounded *)

(** Every compact set is closed.

    Proof idea: if [x] is a limit point of [K], take a sequence in [K] converging
    to [x]. By compactness it has a subsequence converging to some [y ∈ K]; but
    subsequences of a convergent sequence share its limit, so [x = y ∈ K]. *)
Theorem compact_is_closed (K : ℝ → Prop) (HK : K is _compact_) :
    K is _closed_.
Proof.
  Admitted.

(** Every compact set is bounded.

    Proof idea: if [K] were unbounded, pick [xₙ ∈ K] with [|xₙ| > n]; this
    sequence has no convergent subsequence (convergent sequences are bounded),
    contradicting compactness. *)
Theorem compact_is_bounded (K : ℝ → Prop) (HK : K is _compact_) :
    K is _bounded_.
Proof.
  Admitted.

(** ** Closed subsets of compact sets are compact *)

(** A closed subset of a compact set is compact.

    Proof idea: a sequence in [F ⊆ K] has, by compactness of [K], a subsequence
    converging to some [y ∈ K]; since [F] is closed and the subsequence lies in
    [F], the limit [y ∈ F]. *)
Theorem closed_subset_of_compact_is_compact
    (K F : ℝ → Prop)
    (HK : K is _compact_) (HF : F is _closed_)
    (Hinc : ∀ x : ℝ, F x → K x) :
    F is _compact_.
Proof.
  Admitted.

(** ** Heine-Borel theorem *)

(** Heine–Borel theorem: a subset of ℝ is compact iff it is closed and bounded.

    Proof idea: (⇒) is the two theorems above. (⇐) given a sequence in a bounded
    [K], Bolzano–Weierstrass gives a convergent subsequence, and closedness
    places its limit in [K]. *)
Theorem heine_borel (K : ℝ → Prop) :
    (K is _compact_) ⇔ (K is _closed_ ∧ K is _bounded_).
Proof.
  Admitted.

(** ** Nested compact sets *)

(** A decreasing sequence of nonempty compact sets has nonempty intersection.

    Proof idea: a generalization of the nested interval property. Picking a point
    [xₙ ∈ Kₙ], compactness of [K₀] gives a subsequence converging to some [x];
    since each [Kₙ] is closed and eventually contains the tail of the
    subsequence, [x ∈ Kₙ] for every [n]. *)
(* TODO: Fix formalization
    Theorem nested_compact_intersection_nonempty
    (K : ℕ → (ℝ → Prop))
    (HK_nonempty : ∀ n : ℕ, K n ≠ ∅)
    (HK_compact  : ∀ n : ℕ, K n is _compact_)
    (HK_nested   : ∀ n m : ℕ, (n ≤ m)%nat → ∀ x : ℝ, K m x → K n x) :
    ∃ x : ℝ, ∀ n : ℕ, K n x.
Proof.
  Admitted.
*)