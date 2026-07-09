(** * RUG.Analysis.Subsequences — Monotone convergence and Bolzano-Weierstrass.

  Lecture 4 (lecture04_subsequences.mv).

  Formalizes Abbott §2.4–2.5: the monotone convergence theorem,
  subsequences, the Bolzano-Weierstrass theorem, and Cauchy sequences. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.SeqProp.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Lra.
Require Export RUG.Analysis.Sequences.
From Waterproof Require Import Libs.Analysis.Subsequences.
From Waterproof Require Import Libs.Analysis.LimsupLiminfBolzano.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Monotone convergence theorem *)

(** Monotone convergence theorem: a nondecreasing sequence bounded above
    converges, and the limit equals the supremum of its range. This is the key
    lemma enabling [Analysis.Series].

    Proof idea: by the axiom of completeness the range has a supremum [L]. Given
    [ε > 0], [L - ε] is not an upper bound, so some [a_N > L - ε]; monotonicity
    then gives [L - ε < a_N ≤ aₙ ≤ L] for all [n ≥ N], i.e. [|aₙ - L| < ε]. *)
Theorem monotone_convergence (a : ℕ → ℝ)
    (Hbdd : a is _bounded above_)
    (Hmono : ∀ n ∈ ℕ, a n ≤ a (n + 1)%nat) :
    ∃ L ∈ ℝ, a ⟶ L.
Proof.
  Define A := (fun x0 : ℝ => ∃ k : ℕ, x0 = a k).
  We claim that A is bounded from above as (HAbdd).
  {
    We need to show that ∃ M0 ∈ ℝ, M0 is an _upper bound_ for A.
    It holds that ∃ M ∈ ℝ, ∀ n ∈ ℕ, a n ≤ M as (HMbdd).
    Obtain such an M.
    Choose (M). * Indeed, M ∈ ℝ.
    * We need to show that M is an _upper bound_ for A.
      We need to show that ∀ x ∈ A, x ≤ M.
      Take x ∈ A.
      It holds that ∃ k : ℕ, x = a k as (HkA).
      Obtain such a k.
      It holds that x = a k as (Hxk).
      It holds that (a k ≤ M).
      We conclude that x ≤ M.
  }
  We claim that a 0%nat ∈ A as (Hnotempty).
  {
    We need to show that ∃ k : ℕ, a 0%nat = a k.
    Choose (0%nat).
    We conclude that a 0%nat = a 0%nat.
  }
  By (R_complete A (a 0%nat) Hnotempty HAbdd) it holds that
    ∃ L ∈ ℝ, L is the _supremum_ of A as (HLsup).
  Obtain such an L.
  By sup_is_upp_bd it holds that L is an _upper bound_ for A as (HLup).
  Choose (L). * Indeed, L ∈ ℝ.
  * We need to show that a ⟶ L.
    We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | a n - L | < ε.
    Take ε > 0.
    By exists_almost_maximizer_ε it holds that ∃ y ∈ A, L - ε < y as (Heps).
    Obtain such a y.
    It holds that y ∈ A as (HyA).
    It holds that L - ε < y as (Hy_ineq).
    It holds that ∃ N1 : ℕ, y = a N1 as (Heq).
    Obtain such an N1.
    It holds that y = a N1 as (Heq_prop).
    Choose (N1). * Indeed, N1 ∈ ℕ.
    * We need to show that ∀ n ≥ N1, | a n - L | < ε.
      Take n ≥ N1.
      It suffices to show that -ε < a n - L < ε.
      We show both a n - L < ε and -ε < a n - L.
      - We claim that a n ∈ A as (Han).
        { We need to show that ∃ k : ℕ, a n = a k.
          Choose k := n.
          We conclude that a n = a k.
        }
        By HLup it holds that a n ≤ L.
        We conclude that a n - L < ε.
      - It holds that L - ε < a N1.
        By nondecr_ge it holds that a N1 ≤ a n.
        We conclude that -ε < a n - L.
Qed.

(** ** Subsequences *)

(** If [a ⟶ L] and [φ] is a strictly increasing index sequence,
    then [(a ∘ φ) ⟶ L]. *)
Lemma subseq_converges (a : ℕ → ℝ) (phi : ℕ → ℕ) (L : ℝ) :
    a ⟶ L → is_index_seq phi → (fun k => a (phi k)) ⟶ L.
Proof.
  Assume that a ⟶ L as (Ha).
  Assume that is_index_seq phi as (Hphi).
  We need to show that (fun k => a (phi k)) ⟶ L.
  We need to show that ∀ ε > 0, ∃ Nm ∈ ℕ, ∀ k ≥ Nm, | a (phi k) - L | < ε.
  Take ε > 0.
  Since (ε > 0) it holds that ∃ Nm ∈ ℕ, ∀ n ≥ Nm, | a n - L | < ε as (HNm).
  Obtain such an Nm.
  Choose (Nm). * Indeed, Nm ∈ ℕ.
  * We need to show that ∀ k ≥ Nm, | a (phi k) - L | < ε.
    Take k ≥ Nm.
    By index_seq_grows_0 it holds that (phi k ≥ k)%nat as (Hsub).
    It holds that (phi k ≥ Nm)%nat as (Htrans).
    We conclude that | a (phi k) - L | < ε.
Qed.

(** ** Bolzano-Weierstrass theorem *)

(** Bolzano–Weierstrass theorem: every bounded sequence has a convergent
    subsequence.

    Proof idea: repeatedly bisect an interval containing the sequence, each time
    keeping a half that contains infinitely many terms. This produces nested
    intervals shrinking to a point [l] and a subsequence converging to [l]. *)
Theorem bolzano_weierstrass (a : ℕ → ℝ) (Hub : has_ub a) (Hlb : has_lb a) :
    ∃ phi : ℕ → ℕ, ∃ l : ℝ,
      is_index_seq phi ∧ (fun k => a (phi k)) ⟶ l.
Proof.
  By Bolzano_Weierstrass we conclude that ∃ phi : ℕ → ℕ, ∃ l : ℝ,
    is_index_seq phi ∧ (fun k => a (phi k)) ⟶ l.
Qed.

(** ** Cauchy sequences *)

(** A sequence is Cauchy if its terms eventually cluster arbitrarily close. *)
Definition is_cauchy (a : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε.

Notation "a 'is' '_Cauchy_'" := (is_cauchy a) (at level 69).

(** [is_cauchy] is equivalent to Stdlib's [Cauchy_crit]. *)
Lemma cauchy_crit_equiv (a : ℕ → ℝ) :
    (a is _Cauchy_) ⇔ Cauchy_crit a.
Proof.
  unfold Cauchy_crit.
  We show both directions.
  - We need to show that a is _Cauchy_
        ⇨ ∀ eps, eps > 0 ⇨ ∃ N, ∀ n, ∀ m, (n ≥ N)%nat ⇨ (m ≥ N)%nat ⇨ ｜a(n) - a(m)｜ < eps.
    Assume that a is _Cauchy_ as (HC).
    Take eps > 0. It holds that eps > 0 as (Heps).
    destruct (HC eps Heps) as [N1 H'].
    destruct H' as [HN1_in HN1].
    exists N1.
    intros n m Hn Hm.
    unfold Rdist.
    apply HN1 with (n := n) (m := m); assumption.
  - We need to show that (∀ eps, eps > 0 ⇨ ∃ N, ∀ n, ∀ m,
          (n ≥ N)%nat ⇨ (m ≥ N)%nat ⇨ ｜a(n) - a(m)｜ < eps)
        ⇨ a is _Cauchy_.
    Assume that ∀ eps, eps > 0 ⇨ ∃ N, ∀ n, ∀ m,
          (n ≥ N)%nat ⇨ (m ≥ N)%nat ⇨ ｜a(n) - a(m)｜ < eps as (HC).
    intros eps Heps.
    destruct (HC eps Heps) as [N1 HN].
    Choose N2 := N1%nat. { Indeed, N2 ∈ ℕ. }
    We need to show that ∀ n ≥ N2, ∀ m ≥ N2, |a(n) - a(m)| < eps.
    intros n Hn m Hm.
    We conclude that | a n - a m | < eps.
Qed.

(** Every Cauchy sequence is bounded. *)
Theorem cauchy_is_bounded (a : ℕ → ℝ) : a is _Cauchy_ → a is _bounded_.
Proof.
  Assume that a is _Cauchy_.
  It holds that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε as (HC).
  We need to show that a is _bounded_.
  By is_bounded_equivalence it holds that (is_bounded a ⇔ is_bounded_equivalent a) as (Hequiv).
  By Hequiv it suffices to show that is_bounded_equivalent a.
  We need to show that ∃ M > 0, ∀ n ∈ ℕ, | a n | ≤ M.
  By HC it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, | a n - a m | < 1.
  Obtain such a N1.
  We claim that Cauchy_crit a as (HCr). { apply cauchy_crit_equiv, HC. }
  We claim that ∃ UB : ℝ, is_upper_bound (EUn a) UB as (Hub_exists).
  {
    destruct (cauchy_maj a HCr) as [UB HUB];
    unfold is_upper_bound, EUn in HUB;
    exists UB; exact HUB.
  }
  Obtain such a UB.
  It holds that (is_upper_bound (EUn a) UB) as (HUB).
  We claim that ∀ n ∈ ℕ, a n ≤ UB as (HUBn).
  {
    Take n ∈ ℕ.
    We claim that EUn a (a n) as (Heun).
    { We need to show that ∃ k : ℕ, a n = a k.
      Choose k := n. We conclude that a n = a k.
    }
    By HUB we conclude that a n ≤ UB.
  }
  We claim that ∃ LB : ℝ, is_upper_bound (EUn (opp_seq a)) LB as (Hlb_exists).
  {
    destruct (cauchy_min a HCr) as [LB HLB];
    unfold has_lb, bound in *;
    unfold is_upper_bound, EUn in HLB;
    exists LB; exact HLB.
  }
  Obtain such a LB.
  It holds that (is_upper_bound (EUn (opp_seq a)) LB) as (HLB).
  We claim that ∀ n ∈ ℕ, -LB ≤ a n as (HLBn).
  {
    Take n ∈ ℕ.
    We claim that EUn (opp_seq a) (- a n) as (Heun_lb).
    { We need to show that ∃ k : ℕ, - a n = opp_seq a k.
      Choose k := n. We conclude that - a n = opp_seq a k.
    }
    By HLB it holds that - a n ≤ LB.
    We conclude that -LB ≤ a n.
  }
  Choose M := (Rabs UB + Rabs LB + 1). { Indeed, M > 0. }
  We need to show that ∀ n ∈ ℕ, | a n | ≤ Rabs UB + Rabs LB + 1.
  Take n ∈ ℕ.
  It holds that (a n ≤ UB) as (H1).
  It holds that (-LB ≤ a n) as (H2).
  By Rle_abs it holds that UB ≤ Rabs UB as (H3).
  By Rle_abs it holds that LB ≤ Rabs LB as (H4).
  By Rle_abs it holds that -LB ≤ Rabs (-LB) as (H5).
  It holds that (Rabs (-LB) = Rabs LB) as (H6).
  We conclude that | a n | ≤ Rabs UB + Rabs LB + 1.
Qed.
