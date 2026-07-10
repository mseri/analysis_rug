(** * RUG.Analysis.Countability — Countable and uncountable sets.

  #<a href="../../index.html##lecture02">Lecture 2</a>#.

  Formalizes Abbott §1.5: injections, countability of ℕ, ℤ, ℕ×ℕ,
  and Cantor's theorem on the non-existence of a surjection A → 𝒫(A). *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Arith.Cantor.
From Stdlib Require Import micromega.Lia.
From Waterproof Require Import Notations.Functions.
From Waterproof Require Import Libs.Functions.
Require Export RUG.Analysis.Reals.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Countable sets *)

(** A type [A] is countable if there exists an injection [A → ℕ]. *)
Definition countable (A : Type) : Prop :=
  ∃ f : A → ℕ, f is injective.

(** ** ℕ ∼ 𝔼: the even numbers *)

Definition double (n : ℕ) : ℕ := 2 * n.

Lemma even_injection : double is injective.
Proof.
  We need to show that ∀ a ∈ ℕ, ∀ b ∈ ℕ,
    double(a) = double(b) ⇨ a = b.
  Take a, b ∈ ℕ.
  Assume that (2 * a)%nat = (2 * b)%nat.
  (* By Nat.mul_cancel_l *)
  We conclude that a = b.
Qed.

(** ** ℕ is countable *)

Lemma nat_countable : countable ℕ.
Proof.
  It suffices to show that ∃ f : ℕ → ℕ, f is injective.
  Choose f := (fun n : ℕ => n).
  We need to show that ∀ a ∈ ℕ, ∀ b ∈ ℕ,
    f(a) = f(b) ⇨ a = b.
  Take a, b ∈ ℕ. Assume that f(a) = f(b).
  We conclude that a = b.
Qed.

(** ** ℤ is countable *)

Definition g_Z : Z → ℕ :=
  fun n => if (n >=? 0)%Z then Z.to_nat (2 * n)%Z
           else Z.to_nat ((-2) * n - 1)%Z.

Lemma g_Z_injective : g_Z is injective.
Proof.
  (* Case analysis on integer signs; Z2Nat.inj + lia needed for each case *)
  (* WaterProof has no Z case-split or Z.to_nat reasoning tactic *)
  ltac1:(
    unfold injective, g_Z;
    intros n1 _ n2 _ H;
    destruct ((n1 >=? 0)%Z) eqn:E1; destruct ((n2 >=? 0)%Z) eqn:E2;
    try apply Z.geb_le in E1;
    try apply Z.geb_le in E2;
    try (rewrite <- Bool.not_true_iff_false in E1;
         rewrite Z.geb_le in E1; apply Z.lt_nge in E1);
    try (rewrite <- Bool.not_true_iff_false in E2;
         rewrite Z.geb_le in E2; apply Z.lt_nge in E2);
    (* Now E1, E2 are numerical: 0 ≤ n1 / n1 < 0 and 0 ≤ n2 / n2 < 0 *)
    (* apply Z2Nat.inj in H generates side goals 0≤A and 0≤B which lia closes;
       then lia closes the main goal (n1=n2 or False from parity mismatch) *)
    apply Z2Nat.inj in H; lia
  ).
Qed.

Lemma Z_countable : countable Z.
Proof.
  It suffices to show that ∃ f : Z → ℕ, f is injective.
  Choose f := g_Z.
  By g_Z_injective we conclude that g_Z is injective.
Qed.

(** ** ℕ × ℕ is countable (Cantor pairing) *)

Definition cantor_pair (mn : nat * nat) : ℕ :=
  let m := fst mn in
  let n := snd mn in
  (m + n) * (m + n + 1) / 2 + n.

Lemma NxN_countable : countable (nat * nat)%type.
Proof.
  It suffices to show that ∃ f : (nat * nat)%type → ℕ, f is injective.
  Choose f := Cantor.to_nat.
  (* Cantor.to_nat_inj : ∀ p q, to_nat p = to_nat q → p = q *)
  ltac1:(
    unfold injective;
    intros p1 _ p2 _ H;
    exact (Cantor.to_nat_inj p1 p2 H)
  ).
Qed.

(** ** Cantor's theorem *)

(** There is no surjective function [A → 𝒫(A)].

    Proof (diagonal argument): given [g : A → 𝒫(A)], define
    [B = {x ∈ A : x ∉ g(x)}]. If [B = g(x')] then [x' ∈ B ⇔ x' ∉ g(x') = B],
    a contradiction; so [g] is not surjective. *)
Lemma cantors_theorem (A : Type) (g : A → (A → Prop)) :
    ¬ g is surjective.
Proof.
  (* Diagonal argument: define B x = ¬ g x x; surjectivity gives x0 with g x0 = B,
     then g x0 x0 = B x0 = ¬ g x0 x0, a contradiction.
     ltac1 needed: WaterProof has no function extensionality or classical case-split *)
  ltac1:(
    intro Hsurj;
    unfold surjective in Hsurj;
    pose (B := fun x : A => ~ g x x);
    destruct (Hsurj B (mem_subset_full_set B)) as [x0 [_ Hx0]];
    (* g x0 = B implies (g x0) x0 = B x0, i.e., g x0 x0 = ~ g x0 x0 *)
    assert (H1 : g x0 x0 = B x0) by (rewrite Hx0; reflexivity);
    unfold B in H1; cbv beta in H1;
    (* H1 : g x0 x0 = ¬ g x0 x0
       rewrite H1 in p changes p : g x0 x0 to p : ¬ g x0 x0 = g x0 x0 -> False;
       saving a copy q first lets us apply p q : False *)
    assert (Hfn : g x0 x0 -> False) by
      (intro p; pose proof p as q; rewrite H1 in p; exact (p q));
    (* rewrite H1 in goal g x0 x0 gives ¬ g x0 x0 = g x0 x0 -> False,
       closed by Hfn *)
    assert (Hpos : g x0 x0) by (rewrite H1; exact Hfn);
    exact (Hfn Hpos)
  ).
Qed.

(** ** ℝ is uncountable *)

Axiom R_uncountable : ¬ ∃ f : ℕ → ℝ, f is surjective.
