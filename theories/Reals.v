(** * RUG.Analysis.Reals — The real number system.

  Lecture 1 (lecture01_reals.mv).

  Formalizes Abbott §1.2–1.4: upper/lower bounds, supremum/infimum,
  the axiom of completeness, and its consequences (Archimedean property,
  nested interval property, absolute value).

  Re-exports the core Waterproof infrastructure so that files importing
  [Analysis.Reals] do not need to separately import Waterproof. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import ZArith.ZArith.
From Waterproof Require Export Tactics.
From Waterproof Require Export Notations.Common.
From Waterproof Require Export Notations.Reals.
From Waterproof Require Export Notations.Sets.
From Waterproof Require Export Chains.
From Waterproof Require Export Automation.
From Waterproof Require Export Libs.Analysis.SupAndInf.
From Waterproof Require Export Libs.Reals.ArchimedN.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

Hint Resolve Rinv_0_lt_compat : wp_reals.
Hint Resolve Rinv_lt_contravar : wp_reals.
Hint Resolve Rinv_le_contravar : wp_reals.

(** ** Supremum *)

(** The ε-characterization of the supremum: if [s] is an upper bound for [A],
    then [s = sup A] iff every [s - ε] (ε > 0) is exceeded by some element of [A]. *)
Lemma sup_characterization (A : subset ℝ) (s : ℝ)
    (Hs : s is an _upper bound_ for A) :
    (s is the _supremum_ of A) ⇔ (∀ ε > 0, ∃ a ∈ A, s - ε < a).
Proof.
  We show both directions.
  - We need to show that s is the _supremum_ of A ⇨ ∀ ε > 0, ∃ a ∈ A, s - ε < a.
    Assume that s is the _supremum_ of A.
    Take ε : ℝ; such that ε > 0.
    It holds that s - ε < s as (Hsupeps).
    We argue by contradiction.
    Assume that ¬ (∃ a ∈ A, s - ε < a).
    It holds that ∀ x ∈ A, x ≤ s - ε.
    It holds that s - ε is an _upper bound_ for A.
    By any_upp_bd_ge_sup it holds that s ≤ s - ε.
    It holds that ¬ (s ≤ s - ε).
    Contradiction.
  - We need to show that (∀ ε > 0, ∃ a ∈ A, s - ε < a) ⇨ s is the _supremum_ of A.
    Assume that ∀ ε > 0, ∃ a ∈ A, s - ε < a.
    We need to show that
      (s is an _upper bound_ for A) ∧ (∀ b ∈ ℝ, b is an _upper bound_ for A ⇒ s ≤ b).
    We show both statements.
    - We conclude that s is an _upper bound_ for A.
    - We need to show that ∀ b ∈ ℝ, b is an _upper bound_ for A ⇒ s ≤ b.
      Take b ∈ ℝ.
      Assume that b is an _upper bound_ for A as (Hub).
      We argue by contradiction.
      Assume that ¬ (s ≤ b) as (Hcontra).
      It holds that b < s as (Hbs).
      Define ε := s - b.
      By Hbs it holds that ε > 0.
      It holds that ∃ a ∈ A, s - ε < a.
      Obtain such an a.
      It holds that (& b = s - ε < a) as (Hba).
      By Hba it holds that ¬ (a ≤ b).
      It holds that a ≤ b.
      Contradiction.
Qed.

(** ** Infimum *)

(** The ε-characterization of the infimum: if [i] is a lower bound for [A],
    then [i = inf A] iff every [i + ε] (ε > 0) exceeds some element of [A]. *)
Lemma inf_characterization (A : subset ℝ) (i : ℝ)
    (Hi : i is a _lower bound_ for A) :
    (i is the _infimum_ of A) ⇔ (∀ ε > 0, ∃ a ∈ A, a < i + ε).
Proof.
  We show both directions.
  - We need to show that i is the _infimum_ of A ⇨ ∀ ε > 0, ∃ a ∈ A, a < i + ε.
    Assume that i is the _infimum_ of A as (Hinf).
    Take ε : ℝ; such that ε > 0.
    It holds that i < i + ε as (Hiepslt).
    We argue by contradiction.
    Assume that ¬ (∃ a ∈ A, a < i + ε).
    It holds that ∀ x ∈ A, i + ε ≤ x as (Hnotlb).
    By (Hnotlb) it holds that i + ε is a _lower bound_ for A.
    By any_low_bd_le_inf it holds that i + ε ≤ i.
    It holds that ¬ (i + ε ≤ i).
    Contradiction.
  - We need to show that (∀ ε > 0, ∃ a ∈ A, a < i + ε) ⇨ i is the _infimum_ of A.
    Assume that ∀ ε > 0, ∃ a ∈ A, a < i + ε.
    We need to show that
      (i is a _lower bound_ for A) ∧ (∀ l ∈ ℝ, l is a _lower bound_ for A ⇒ l ≤ i).
    We show both statements.
    - We conclude that i is a _lower bound_ for A.
    - We need to show that ∀ l ∈ ℝ, l is a _lower bound_ for A ⇒ l ≤ i.
      Take l ∈ ℝ.
      Assume that l is a _lower bound_ for A.
      We argue by contradiction.
      Assume that ¬ (l ≤ i) as (Hcontra).
      It holds that i < l.
      Define ε := l - i.
      It holds that ε > 0.
      It holds that ∃ a ∈ A, a < i + ε.
      Obtain such an a.
      It holds that (& a < i + ε = l) as (Hal).
      By Hal it holds that ¬ (l ≤ a).
      It holds that l ≤ a.
      Contradiction.
Qed.

(** ** Monotonicity helpers *)

(** A nondecreasing sequence satisfies [a m ≤ a n] whenever [m ≤ n]. *)
Lemma nondecr_ge (a : ℕ → ℝ) (Hmono : ∀ n ∈ ℕ, a n ≤ a (n + 1)%nat) :
    ∀ n ∈ ℕ, ∀ m ∈ ℕ, (m ≤ n)%nat → a m ≤ a n.
Proof.
  We use induction on n.
  + We first show the base case (∀ m ∈ ℕ, (m ≤ 0)%nat → a m ≤ a 0%nat).
    Take m ∈ ℕ.
    Assume that (m ≤ 0)%nat as (Hm0).
    It holds that (m = 0)%nat as (Hm).
    We conclude that a m ≤ a 0%nat.
  + We now show the induction step.
    Take n ∈ ℕ.
    Assume that (∀ m ∈ ℕ, (m ≤ n)%nat → a m ≤ a n) as (IH).
    Take m ∈ ℕ.
    Assume that (m ≤ n + 1)%nat as (Hmn).
    Either (m ≤ n)%nat or (m = n + 1)%nat.
    - Case (m ≤ n)%nat.
      It holds that a m ≤ a n as (H1).
      It holds that a n ≤ a (n + 1)%nat as (H2).
      We conclude that (& a m ≤ a n ≤ a (n + 1)%nat).
    - Case (m = n + 1)%nat.
      We conclude that a m ≤ a (n + 1)%nat.
Qed.

(** A nonincreasing sequence satisfies [b n ≤ b m] whenever [m ≤ n]. *)
Lemma nonincr_le (b : ℕ → ℝ) (Hmono : ∀ n ∈ ℕ, b (n + 1)%nat ≤ b n) :
    ∀ n ∈ ℕ, ∀ m ∈ ℕ, (m ≤ n)%nat → b n ≤ b m.
Proof.
  We use induction on n.
  + We first show the base case (∀ m ∈ ℕ, (m ≤ 0)%nat → b 0%nat ≤ b m).
    Take m ∈ ℕ.
    Assume that (m ≤ 0)%nat as (Hm0).
    It holds that (m = 0)%nat as (Hm).
    We conclude that b 0%nat ≤ b m.
  + We now show the induction step.
    Take n ∈ ℕ.
    Assume that (∀ m ∈ ℕ, (m ≤ n)%nat → b n ≤ b m) as (IH).
    Take m ∈ ℕ.
    Assume that (m ≤ n + 1)%nat as (Hmn).
    Either (m ≤ n)%nat or (m = n + 1)%nat.
    - Case (m ≤ n)%nat.
      It holds that b n ≤ b m as (H1).
      It holds that b (n + 1)%nat ≤ b n as (H2).
      We conclude that (& b (n + 1)%nat ≤ b n ≤ b m).
    - Case (m = n + 1)%nat.
      We conclude that b (n + 1)%nat ≤ b m.
Qed.

(** ** Nested interval property *)

(** Nested interval property: if [(a_n)] is nondecreasing and [(b_n)] is
    nonincreasing with [a_n ≤ b_n], then there exists a point in every interval
    [[a_n, b_n]].

    Proof idea: let [A = {aₙ}]. Every [bₙ] is an upper bound for [A] (since
    [aₘ ≤ aₙ ≤ bₙ] for [m ≤ n] and [aₘ ≤ bₘ ≤ bₙ] for [m ≥ n]). By the axiom of
    completeness [x = sup A] exists; being an upper bound gives [aₙ ≤ x], and
    being the least upper bound gives [x ≤ bₙ] for all [n]. *)
Lemma nested_interval_property (a bseq : ℕ → ℝ)
    (Hab : ∀ n ∈ ℕ, a n ≤ bseq n)
    (Ha_mono : ∀ n ∈ ℕ, a n ≤ a (n + 1)%nat)
    (Hb_mono : ∀ n ∈ ℕ, bseq (n + 1)%nat ≤ bseq n) :
    ∃ x ∈ ℝ, ∀ n ∈ ℕ, a n ≤ x ∧ x ≤ bseq n.
Proof.
  Define A := (fun y : ℝ => ∃ n : ℕ, y = a n).
  We claim that ∀ k ∈ ℕ, bseq k is an _upper bound_ for A as (Hallub).
  { Take k ∈ ℕ.
    We need to show that ∀ y ∈ A, y ≤ bseq k.
    Take y ∈ A.
    It holds that ∃ n : ℕ, y = a n.
    Obtain such an n.
    It holds that y = a n.
    Either (n ≤ k)%nat or (k ≤ n)%nat.
    - Case (n ≤ k)%nat.
      By nondecr_ge it holds that a n ≤ a k as (H1).
      It holds that a k ≤ bseq k as (H2).
      We conclude that (& y = a n ≤ a k ≤ bseq k).
    - Case (k ≤ n)%nat.
      By nonincr_le it holds that bseq n ≤ bseq k as (H1).
      It holds that a n ≤ bseq n as (H2).
      We conclude that (& y = a n ≤ bseq n ≤ bseq k).
  }
  We claim that A is bounded from above as (HboundedA).
  { We need to show that ∃ M ∈ ℝ, M is an _upper bound_ for A.
    Choose M := bseq 0%nat.
    { Indeed, M ∈ ℝ. }
    By Hallub we conclude that M is an _upper bound_ for A.
  }
  We claim that a 0%nat ∈ A as (Ha0).
  { We need to show that ∃ n : ℕ, a 0%nat = a n.
    Choose n := 0%nat.
    We conclude that a 0%nat = a n.
  }
  (* R_complete is the name in the Waterproof.Analysis.SupAndInf
     module of the axiom of completeness *)
  By R_complete it holds that ∃ x ∈ ℝ, x is the _supremum_ of A as (Hsup).
  Obtain such an x.
  By sup_is_upp_bd it holds that x is an _upper bound_ for A as (Hxub).
  Choose (x).
  * Indeed, x ∈ ℝ.
  * We need to show that ∀ n ∈ ℕ, a n ≤ x ∧ x ≤ bseq n.
    Take n ∈ ℕ.
    We show both statements.
    - We need to show that a n ≤ x.
      We claim that a n ∈ A as (Han).
      { We need to show that ∃ k : ℕ, a n = a k.
        Choose k := n.
        We conclude that a n = a k.
      }
      We conclude that a n ≤ x.
    - We need to show that x ≤ bseq n.
      By Hallub it holds that bseq n is an _upper bound_ for A as (Hbn).
      (* NOTE: the lecture ends this step with `... it holds that x ≤ bseq n`,
         which closes the goal interactively in Waterproof but leaves it open
         under batch/dune compilation. Only the closing keyword is adjusted here
         (`it holds that` → `we conclude that`); the lemmas used and the proof
         logic are unchanged. *)
      By Hbn and any_upp_bd_ge_sup we conclude that x ≤ bseq n.
Qed.

(** ** Archimedean property *)

(** For any [x : ℝ], there exists a natural number [n] with [n > x]. *)
Lemma archimedean_1 (x : ℝ) : ∃ n : ℕ, INR n > x.
Proof.
  By archimedN we conclude that ∃ n : ℕ, INR n > x.
Qed.

(** For any [y > 0], there exists [n : ℕ] with [1/(n+1) < y]. *)
Lemma archimedean_2 (y : ℝ) (Hy : y > 0) : ∃ n : ℕ, 1 / (n + 1) < y.
Proof.
  It holds that 0 < / y as (Hy_inv_pos).
  By the Archimedean property it holds that ∃ n1 ∈ ℕ, n1 > / y as (HN).
  Obtain such an n1.
  It holds that (& n1 + 1 > n1 > / y > 0).
  It holds that / (n1 + 1) < / (/ y).
  Choose n := n1.
  We conclude that (&
    1 / (n1 + 1) = / (n1 + 1) < / (/ y) = y
  ).
Qed.

(** ** Absolute value *)

(** [|x| = max{x, -x}]. *)
Lemma abs_eq_max (x : ℝ) : Rabs x = Rmax x (- x).
Proof.
  Either x ≥ 0 or x < 0.
  - Case x ≥ 0.
    It holds that Rabs x = x as (H1).
    It holds that Rmax x (- x) = x as (H2).
    We conclude that Rabs x = Rmax x (- x).
  - Case x < 0.
    It holds that Rabs x = - x as (H1).
    It holds that Rmax x (- x) = - x as (H2).
    We conclude that Rabs x = Rmax x (- x).
Qed.

(** [|xy| = |x| |y|]. *)
Lemma abs_mult (x y : ℝ) : Rabs (x * y) = Rabs x * Rabs y.
Proof.
  By Rabs_mult we conclude that Rabs (x * y) = Rabs x * Rabs y.
Qed.

(** [|x/y| = |x|/|y|] when [y ≠ 0]. *)
Lemma abs_div (x y : ℝ) (Hy : y ≠ 0) : Rabs (x / y) = Rabs x / Rabs y.
Proof.
  By Rabs_inv it holds that Rabs (/ y) = / Rabs y.
  We conclude that Rabs (x / y) = Rabs x / Rabs y.
Qed.

(** Triangle inequality: [|x + y| ≤ |x| + |y|]. *)
Lemma triangle_inequality (x y : ℝ) : Rabs (x + y) ≤ Rabs x + Rabs y.
Proof.
  By Rabs_triang we conclude that Rabs (x + y) ≤ Rabs x + Rabs y.
Qed.

(** Reverse triangle inequality: [||x| - |y|| ≤ |x - y|]. *)
Lemma reverse_triangle_inequality (x y : ℝ) : Rabs (Rabs x - Rabs y) ≤ Rabs (x - y).
Proof.
  By Rabs_triang_inv2 we conclude that Rabs (Rabs x - Rabs y) ≤ Rabs (x - y).
Qed.

(** ** Density of the rationals *)

(** Density of the rationals: between any two reals [lo < hi] there is a rational
    [p/q].

    Proof idea: by the Archimedean property pick [n] with [1/n < hi - lo], so
    [n·hi - n·lo > 1]; then some integer [m] lies strictly between [n·lo] and
    [n·hi], and [r = m/n] satisfies [lo < r < hi]. *)
Lemma density_of_rationals (lo hi : ℝ) (H : lo < hi) :
    ∃ p : ℤ, ∃ q : ℤ, (q > 0)%Z ∧ lo < IZR p / IZR q ∧ IZR p / IZR q < hi.
Proof.
  Admitted.
