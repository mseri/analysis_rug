(** * RUG.Analysis.Sequences — Convergence of sequences.

  Lecture 3 (lecture03_sequences.mv).

  Formalizes Abbott §2.2–2.3: the ε-N definition of convergence,
  algebraic limit theorem, order limit theorem, and squeeze_theorem theorem. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.SeqProp.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Lra.
From Waterproof Require Export Libs.Analysis.Sequences.
Require Export RUG.Analysis.Reals.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Convergence of a sequence

    Definition: [(aₙ)] converges to [a] if
    [∀ ε > 0, ∃ N, ∀ n ≥ N, |aₙ - a| < ε]. We write [aₙ → a] or
    [a = lim_{n→∞} aₙ]. In Waterproof, [a_n ⟶ a] is equivalent to [Un_cv a_n a]. *)

(** ** Constant and harmonic sequences *)

(** The constant sequence with value [c]. *)
Definition constant_seq (c : ℝ) := fun (n : ℕ) => c.

(** Theorem 3.1: a constant sequence [aₙ = c] converges to [c]. *)
Lemma constant_seq_converges (c : ℝ) : (fun _ : ℕ => c) ⟶ c.
Proof.
  By lim_const_seq we conclude that (fun _ : ℕ => c) ⟶ c.
Qed.

(** The harmonic sequence. *)
Definition harmonic := fun (n : ℕ) => 1 / (n + 1).

(** Theorem 3.2: the sequence [1/(n+1)] converges to [0]. *)
Lemma harmonic_to_0 : (fun n : ℕ => Rdiv 1 (INR n + 1)) ⟶ 0.
Proof.
  By lim_d_0 we conclude that (fun n : ℕ => Rdiv 1 (INR n + 1)) ⟶ 0.
Qed.

(** ** Algebraic limit theorem *)

(** Theorem 3.3 (algebraic limit theorem, sum): if [aₙ → m] and [bₙ → l] then
    [aₙ + bₙ → m + l].

    Proof idea: the triangle inequality shows
    [|(aₙ + bₙ) - (m + l)| ≤ |aₙ - m| + |bₙ - l|]. Choosing [N₁] and [N₂] so that
    the individual errors are below [ε/2] makes the sum below [ε]. *)
Lemma algebraic_limit_theorem_sum (a b : ℕ → ℝ) (m l : ℝ) :
    a ⟶ m → b ⟶ l → (fun n => a n + b n) ⟶ (m + l).
Proof.
  Assume that a ⟶ m as (Ha).
  Assume that b ⟶ l as (Hb).
  Define c := fun n => a n + b n.
  We need to show that c ⟶ (m + l).
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | c n - (m + l) | < ε.
  Take ε > 0.
  Since (ε/2 > 0) it holds that (∃ Nm ∈ ℕ, ∀ n ≥ Nm, | a n - m | < ε/2) as (Ha').
  Obtain such Nm.
  Since (ε/2 > 0) it holds that (∃ Nl ∈ ℕ, ∀ n ≥ Nl, | b n - l | < ε/2) as (Hb').
  Obtain such Nl.
  Choose N1 := max Nm Nl. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, |c(n) - (m + l)| < ε.
  Take n ≥ N1.
  It holds that n ≥ Nm. It holds that n ≥ Nl.
  By Ha' it holds that | a n - m | < ε / 2.
  By Hb' it holds that | b n - l | < ε / 2.
  It holds that | c n - (m + l) | = | (a n + b n) - (m + l) |.
  It holds that (a n + b n) - (m + l) = (a n - m) + (b n - l).
  It holds that | c n - (m + l) | = | (a n - m) + (b n - l) |.
  By Rabs_triang it holds that (&
    | (a n - m) + (b n - l) |
    ≤ | a n - m | + | b n - l |
    < ε / 2 + ε / 2 = ε
  ).
  We conclude that (| c n - (m + l) | < ε).
Qed.

(** If [a ⟶ m] and [b ⟶ l], then [(a * b) ⟶ (m * l)]. *)
Lemma algebraic_limit_product (a b : ℕ → ℝ) (m l : ℝ) :
    a ⟶ m → b ⟶ l → (fun n => a n * b n) ⟶ (m * l).
Proof.
  intros Ha Hb.
  destruct (convergence_equivalence a m) as [fwd_a _].
  destruct (convergence_equivalence b l) as [fwd_b _].
  destruct (convergence_equivalence (fun n => a n * b n) (m * l)) as [_ bwd].
  apply bwd. apply CV_mult.
  - exact (fwd_a Ha).
  - exact (fwd_b Hb).
Qed.

(** ** Order limit theorem *)

(** Theorem 3.4 (order limit theorem): if [aₙ → L] and [aₙ ≤ M] for all [n],
    then [L ≤ M].

    Proof idea: if [L > M], then taking [ε = L - M > 0] we would have
    [|aₙ - L| < ε] for large [n], implying [aₙ > L - ε = M], contradicting the
    hypothesis. *)
Lemma order_limit_theorem (a : ℕ → ℝ) (L M : ℝ) :
    a ⟶ L → (∀ n ∈ ℕ, a n ≤ M) → L ≤ M.
Proof.
  Assume that a ⟶ L as (Ha).
  Assume that ∀ n ∈ ℕ, a n ≤ M as (HM).
  By upp_bd_seq_is_upp_bd_lim we conclude that L ≤ M.
Qed.

(** ** Squeeze theorem *)

(** Theorem 3.5 (squeeze theorem): if [a ⟶ L], [c ⟶ L], and
    [aₙ ≤ bₙ ≤ cₙ] for all [n], then [b ⟶ L].

    Proof idea: for any [ε > 0], choose [N₁] and [N₂] so that [|aₙ - L| < ε] and
    [|cₙ - L| < ε] for [n ≥ max(N₁, N₂)]. Then
    [L - ε < aₙ ≤ bₙ ≤ cₙ < L + ε], so [|bₙ - L| < ε]. *)
Lemma squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ) :
    a ⟶ L → c ⟶ L →
    (∀ n ∈ ℕ, a n ≤ b n) →
    (∀ n ∈ ℕ, b n ≤ c n) →
    b ⟶ L.
Proof.
  Assume that a ⟶ L as (Ha).
  Assume that c ⟶ L as (Hc).
  Assume that ∀ n ∈ ℕ, a n ≤ b n as (Hab).
  Assume that ∀ n ∈ ℕ, b n ≤ c n as (Hbc).
  By squeeze_theorem we conclude that b ⟶ L.
Qed.

(** ** A divergent sequence *)

(** Theorem 3.6: the alternating sequence [(-1)ⁿ] does not converge.

    Proof idea: suppose [aₙ → L]. Taking [ε = 1], there is an [N] beyond which
    [|aₙ - L| < 1]. But for even [n] we have [aₙ = 1] and for odd [n] we have
    [aₙ = -1], so both [|1 - L| < 1] and [|-1 - L| < 1] would hold. By the
    triangle inequality [2 = |1 - (-1)| ≤ |1 - L| + |L - (-1)| < 2], a
    contradiction. *)
Lemma pm_1_diverges : ¬ (∃ L ∈ ℝ, (fun n => (-1) ^ n) ⟶ L).
Proof.
  (* Due to ¬ we are already in a contradiction-like setting *)
  Assume that ∃ L ∈ ℝ, (fun n ↦ (-1)^n) ⟶ L as (H).
  Obtain such an L.
  It holds that (1 > 0).
  By H it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, | (-1)^n - L | < 1 as (HN).
  Obtain such an N1.

  (* Even case: n = 2*N1 *)
  It holds that (2 * N1)%nat ≥ N1.
  By HN it holds that (| (-1)^(2 * N1) - L | < 1).
  By (pow_1_even N1) it holds that ((-1)^(2 * N1) = 1).
  It holds that (| 1 - L | < 1).
  By Rabs_def2 it holds that (1 - L < 1 ∧ -1 < 1 - L).
  - It holds that (1 - L < 1).
  - It holds that (-1 < 1 - L).

  (* Odd case: n = 2*N1+1) *)
  It holds that (S (2 * N1)%nat ≥ N1).
  By HN it holds that (| (-1)^(S(2 * N1)%nat) - L | < 1).
  (* To remove the warning above you can instead do this: *)
  We claim that ((-1)^(S (2 * N1)%nat) = - 1).
  { apply pow_1_odd. }
  It holds that (| -1 - L | < 1).
  By Rabs_def2 it holds that (-1 - L < 1 ∧ -1 < -1 - L).
  - It holds that (-1 - L < 1).
  - It holds that (-1 < -1 - L).

  (* Contradiction: 1 - L < 1  ⇨  L > 0   and   -1 < -1 - L  ⇨  L < 0 *)
  Since (1 - L < 1) ∧ (-1 < -1 - L) it holds that (0 < L ∧ L < 0).
  Contradiction.
Qed.
