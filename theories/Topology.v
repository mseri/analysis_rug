(** * RUG.Analysis.Topology — Open sets, closed sets, and limit points.

  #<a href="../../index.html##lecture06">Lecture 6</a>#.

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
  We need to show that
    ∀ y ∈ (fun x => a < x < b), ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => a < x < b).
  Take y ∈ (fun x => a < x < b).
  It holds that a < y < b as (Hy).
  Choose r := Rmin (y - a) (b - y).
  - Indeed, Rmin (y - a) (b - y) > 0.
  - We need to show that ∀ x ∈ (open_ball y r), x ∈ (fun x => a < x < b).
    Take x ∈ (open_ball y r).
    It holds that | x - y | < r as (Hxy).
    By Rabs_def2 it holds that x - y < r ∧ - r < x - y as (Hbd).
    By Rmin_l it holds that Rmin (y - a) (b - y) ≤ y - a.
    By Rmin_r it holds that Rmin (y - a) (b - y) ≤ b - y.
    We conclude that a < x < b.
Qed.

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
  We need to show that
    ∀ y ∈ (fun x => A x ∧ B x),
      ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∧ B x).
  Take y ∈ (fun x => A x ∧ B x).
  It holds that A y ∧ B y as (Hy).
  It holds that A y as (HAy). It holds that B y as (HBy).
  By HA it holds that is_interior_point y A as (HiA).
  It holds that (∃ r1 > 0, ∀ x ∈ (open_ball y r1), x ∈ A) as (HiA').
  Obtain such a r1.
  By HB it holds that is_interior_point y B as (HiB).
  It holds that (∃ r2 > 0, ∀ x ∈ (open_ball y r2), x ∈ B) as (HiB').
  Obtain such a r2.
  Choose r := Rmin r1 r2.
  - Indeed, Rmin r1 r2 > 0.
  - We need to show that
      ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∧ B x).
    Take x ∈ (open_ball y r).
    It holds that | x - y | < r as (Hxy).
    By Rmin_l it holds that Rmin r1 r2 ≤ r1.
    By Rmin_r it holds that Rmin r1 r2 ≤ r2.
    It holds that | x - y | < r1. It holds that | x - y | < r2.
    It holds that x ∈ (open_ball y r1) as (HxA).
    It holds that x ∈ (open_ball y r2) as (HxB).
    By HiA' it holds that x ∈ A.
    By HiB' it holds that x ∈ B.
    We conclude that x ∈ (fun x => A x ∧ B x).
Qed.

(** ** Open sets are closed under arbitrary union *)

(** Theorem 6.2: the union of two open sets is open.

    Proof idea: for [x ∈ A ∪ B], say [x ∈ A]; openness of [A] gives [ε > 0] with
    [V_ε(x) ⊆ A ⊆ A ∪ B]. (The same argument works for arbitrary unions.) *)
Lemma open_union (A B : ℝ → Prop)
    (HA : A is _open_) (HB : B is _open_) :
    (fun x => A x ∨ B x) is _open_.
Proof.
  We need to show that
    ∀ y ∈ (fun x => A x ∨ B x),
      ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∨ B x).
  Take y ∈ (fun x => A x ∨ B x).
  It holds that A y ∨ B y as (Hy).
  Either (A y) or (B y).
  - Case (A y).
    By HA it holds that is_interior_point y A as (HiA).
    It holds that (∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ A) as (HiA').
    Obtain such a r.
    Choose (r).
    + Indeed, r > 0.
    + We need to show that
        ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∨ B x).
      Take x ∈ (open_ball y r).
      By HiA' it holds that x ∈ A.
      We conclude that x ∈ (fun x => A x ∨ B x).
  - Case (B y).
    By HB it holds that is_interior_point y B as (HiB).
    It holds that (∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ B) as (HiB').
    Obtain such a r.
    Choose (r).
    + Indeed, r > 0.
    + We need to show that
        ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∨ B x).
      Take x ∈ (open_ball y r).
      By HiB' it holds that x ∈ B.
      We conclude that x ∈ (fun x => A x ∨ B x).
Qed.

(** ** Open sets under arbitrary union *)

(** An arbitrary union of open sets is open.

    Proof idea: for [x] in the union, [x ∈ U i] for some index [i]; openness of
    [U i] gives a ball [V_ε(x) ⊆ U i], which is contained in the union. *)
Lemma open_union_arbitrary (Idx : Type) (U : Idx → (ℝ → Prop))
    (HU : ∀ i : Idx, (U i) is _open_) :
    (fun x => ∃ i : Idx, U i x) is _open_.
Proof.
  We need to show that
    ∀ y ∈ (fun x => ∃ i : Idx, U i x),
      ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => ∃ i : Idx, U i x).
  Take y ∈ (fun x => ∃ i : Idx, U i x).
  It holds that (∃ i : Idx, U i y) as (Hy).
  Obtain such an i.
  It holds that U i y as (Hiy).
  By (HU i) it holds that is_interior_point y (U i) as (Hint).
  It holds that (∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (U i)) as (Hint').
  Obtain such a r.
  Choose (r).
  - Indeed, r > 0.
  - We need to show that
      ∀ x ∈ (open_ball y r), x ∈ (fun x => ∃ i : Idx, U i x).
    Take x ∈ (open_ball y r).
    By Hint' it holds that x ∈ (U i).
    It holds that U i x as (HUix).
    We conclude that x ∈ (fun x => ∃ i : Idx, U i x).
Qed.

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

(** ** Isolated points *)

(** [x] is a *limit point* of [A] if every neighbourhood of [x] contains a
    point of [A] distinct from [x]. *)
Definition is_limit_point (A : ℝ → Prop) (x : ℝ) : Prop :=
    ∀ ε > 0, ∃ y ∈ A, 0 < Rabs (y - x) < ε.

(** A point [x ∈ A] is *isolated* in [A] if some neighbourhood of [x] meets [A]
    only at [x] itself — equivalently, [x ∈ A] is not a limit point of [A]. *)
Definition is_isolated_point (A : ℝ → Prop) (x : ℝ) : Prop :=
    A x ∧ ∃ ε > 0, ∀ y ∈ A, Rabs (y - x) < ε → y = x.

(** ** Closure *)

(** The *closure* [Ā] of [A] is [A] together with all its limit points. *)
Definition closure (A : ℝ → Prop) : ℝ → Prop :=
    fun x => A x ∨ is_limit_point A x.

(** The closure [Ā] is a closed set.

    Proof idea: one shows [Ā] contains all of its own limit points. A limit
    point of [Ā] is approximated arbitrarily well by points of [Ā], each of
    which is either in [A] or approximated by points of [A]; a diagonal argument
    then produces points of [A] arbitrarily close, so the point is already in
    [Ā]. *)
Lemma closure_is_closed (A : ℝ → Prop) :
    (closure A) is _closed_.
Proof.
  Admitted.

(** Characterization of the closure: [x ∈ Ā] iff every neighbourhood of [x]
    contains a point of [A]. Equivalently, iff there is a sequence in [A]
    converging to [x].

    Proof idea: if [x ∈ A] every ball trivially contains [x ∈ A]; if [x] is a
    limit point every ball contains a point of [A] distinct from [x].
    Conversely, if every ball meets [A] then either [x ∈ A] or [x] is a limit
    point of [A]. *)
Lemma closure_characterization (A : ℝ → Prop) (x : ℝ) :
    closure A x ⇔ (∀ ε > 0, ∃ y ∈ A, Rabs (y - x) < ε).
Proof.
  Admitted.
