(** * RUG.Analysis.Topology — Open sets, closed sets, and limit points.

  Lecture 6 (lecture06_topology.mv).

  Formalizes Abbott §3.2–3.3: open and closed subsets of ℝ, limit points,
  closures, and the relationship between open/closed sets. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import micromega.Lra.
From Waterproof Require Import Libs.Analysis.OpenAndClosed.
Require Export RUG.Analysis.Sequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** A set [O ⊆ ℝ] is *open* if every point of [O] is interior:
    [∀ a ∈ O, ∃ ε > 0, V_ε(a) ⊆ O], where [V_ε(a) = {x : |x - a| < ε}].
    A set [F] is *closed* if its complement is open, equivalently if it contains
    all its limit points. *)

(** ** Open intervals are open *)

(** Theorem 6.1: the open interval [(a, b)] is an open set.

    Proof idea: for [x ∈ (a,b)], set [ε = min(x - a, b - x) > 0]. Any [y] with
    [|y - x| < ε] satisfies [y > x - ε ≥ a] and [y < x + ε ≤ b], so
    [V_ε(x) ⊆ (a,b)]. *)
Lemma open_interval_is_open (a b : ℝ) (Hab : a < b) :
    (fun x => a < x < b) is _open_.
Proof.
  Admitted.

(** ** Open sets are closed under finite intersection *)

(** Theorem 6.3: the intersection of two open sets is open.

    Proof idea: for [x ∈ A ∩ B], openness gives [ε₁] with [V_{ε₁}(x) ⊆ A] and
    [ε₂] with [V_{ε₂}(x) ⊆ B]; then [ε = min(ε₁, ε₂)] gives [V_ε(x) ⊆ A ∩ B].
    (This fails for infinite intersections: [⋂ₙ (-1/n, 1/n) = {0}] is not
    open.) *)
Lemma open_inter (A B : ℝ → Prop)
    (HA : A is _open_) (HB : B is _open_) :
    (fun x => A x ∧ B x) is _open_.
Proof.
  Admitted.

(** ** Open sets are closed under arbitrary union *)

(** Theorem 6.2: the union of two open sets is open.

    Proof idea: for [x ∈ A ∪ B], say [x ∈ A]; openness of [A] gives [ε > 0] with
    [V_ε(x) ⊆ A ⊆ A ∪ B]. (The same argument works for arbitrary unions.) *)
Lemma open_union (A B : ℝ → Prop)
    (HA : A is _open_) (HB : B is _open_) :
    (fun x => A x ∨ B x) is _open_.
Proof.
  Admitted.

(** ** Closed intervals are closed *)

(** Theorem 6.4: the closed interval [[a, b]] is a closed set.

    Proof idea: the complement [(-∞, a) ∪ (b, ∞)] is open — for [x < a] the ball
    [V_{a-x}(x)] lies in [(-∞, a)], and for [x > b] the ball [V_{x-b}(x)] lies in
    [(b, ∞)]. *)
Lemma closed_interval_is_closed (a b : ℝ) (Hab : a ≤ b) :
    closed_set (fun x => a ≤ x ∧ x ≤ b).
Proof.
  Admitted.

(** ** Closed sets under finite union *)

(** Theorem 6.5: the union of two closed sets is closed.

    Proof idea: by de Morgan the complement is [Fᶜ ∩ Gᶜ], an intersection of two
    open sets, hence open (Theorem 6.3). *)
Lemma closed_union (F G : ℝ → Prop)
    (HF : F is _closed_) (HG : G is _closed_) :
    (fun x => F x ∨ G x) is _closed_.
Proof.
  Admitted.

(** ** Closed sets under arbitrary intersection *)

(** Theorem 6.6: an arbitrary intersection of closed sets is closed.

    Proof idea: by de Morgan the complement is [⋃ᵢ Fᵢᶜ], an arbitrary union of
    open sets, hence open (Theorem 6.2). *)
Lemma closed_inter_arbitrary (I : Type) (F : I → (ℝ → Prop))
    (HF : ∀ i : I, F i is _closed_) :
    (fun x => ∀ i : I, F i x) is _closed_.
Proof.
  Admitted.

(** ** Limit points *)

(** A point [x] is a limit point of [A] iff every neighbourhood contains a
    point of [A] other than [x] itself; equivalently, iff there is a sequence in
    [A \ {x}] converging to [x].

    Proof idea: (⇒) taking [ε = 1/n] gives points [aₙ ∈ A] with
    [0 < |aₙ - x| < 1/n], so [aₙ → x]. (⇐) given such a sequence and [ε > 0],
    convergence provides a term within [ε] of [x] and distinct from it. *)
Lemma limit_point_characterization (A : ℝ → Prop) (x : ℝ) :
    (∀ ε > 0, ∃ y ∈ A, 0 < Rabs (y - x) < ε) ⇔
    (∃ a : ℕ → ℝ, (∀ n ∈ ℕ, a n ∈ A) ∧ (∀ n ∈ ℕ, a n ≠ x) ∧ a ⟶ x).
Proof.
  Admitted.

(** ** Open/closed duality *)

(** Complementation: [A] is open iff its complement is closed. This is immediate
    from the definition of closed as "complement is open". *)
Lemma open_iff_complement_closed (A : ℝ → Prop) :
    A is _open_ ⇔ closed_set (fun x => ¬ A x).
Proof.
  Admitted.

(** ** Closure characterization *)

(** [A] is closed iff [A] contains all its limit points.

    Proof idea (⇒): if [A] is closed and [x] is a limit point with [x ∉ A], then
    [x ∈ Aᶜ] which is open, giving a ball [V_ε(x) ⊆ Aᶜ] disjoint from [A] —
    contradicting that [x] is a limit point. *)
Lemma closed_iff_contains_limit_points (A : ℝ → Prop) :
    A is _closed_ ⇔
    (∀ x : ℝ, (∀ ε > 0, ∃ y ∈ A, 0 < Rabs (y - x) < ε) → A x).
Proof.
  Admitted.
