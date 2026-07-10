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
  fun n =>
    match n with
    | Z0 => 0%nat
    | Zpos p => Z.to_nat (2 * Z.pos p)%Z
    | Zneg p => Z.to_nat ((-2) * Z.neg p - 1)%Z
    end.
  
Lemma g_Z_injective : g_Z is injective.
Proof.
  We need to show that ∀ n1 ∈ Z, ∀ n2 ∈ Z,
    g_Z(n1) = g_Z(n2) ⇨ n1 = n2.
  Take n1, n2 ∈ Z. Assume that g_Z(n1) = g_Z(n2) as (Hinj).
  destruct n1 as [|p1|p1], n2 as [|p2|p2]; try (exfalso; discriminate Hinj).
  - (* n1 = Z0, n2 = Z0 *)
    reflexivity.
  - (* n1 = Z0, n2 = Zpos p2 *)
    We argue by contradiction.
    Assume that 0%Z ≠ Z.pos p2.
    By Hinj it holds that (&
      0%nat = g_Z(0%Z) = g_Z(Z.pos p2)
    ).
    Contradiction.
  - (* n1 = Z0, n2 = Zneg p2 *)
    We argue by contradiction.
    Assume that 0%Z ≠ Z.neg p2.
        By Hinj it holds that (&
      0%nat = g_Z(0%Z) = g_Z(Z.neg p2)
    ).
    Contradiction.
  - (* n1 = Zpos p1, n2 = Z0 *)
    We argue by contradiction.
    Assume that Z.pos p1 ≠ 0%Z.
    By Hinj it holds that (&
      g_Z(Z.pos p1) = g_Z(0%Z) = 0%nat
    ).
    Contradiction.
  - (* n1 = Zpos p1, n2 = Zpos p2 *)
    It holds that g_Z (Z.pos p1) = Z.to_nat (2 * Z.pos p1)%Z.
    It holds that g_Z (Z.pos p2) = Z.to_nat (2 * Z.pos p2)%Z.
    By Hinj it holds that (&
      Z.to_nat (2 * Z.pos p1)%Z
      = g_Z(Z.pos p1) = g_Z(Z.pos p2)
      = Z.to_nat (2 * Z.pos p2)%Z
    ).
    We conclude that Z.pos p1 = Z.pos p2.
  - (* n1 = Zpos p1, n2 = Zneg p2 *)
    We argue by contradiction.
    Assume that Z.pos p1 ≠ Z.neg p2.
    It holds that g_Z (Z.pos p1) = Z.to_nat (2 * Z.pos p1)%Z.
    It holds that g_Z (Z.neg p2) = Z.to_nat ((-2) * Z.neg p2 - 1)%Z.
    It holds that
      g_Z(Z.pos p1) ≠ g_Z(Z.neg p2).
    Contradiction.
  - (* n1 = Zneg p1, n2 = Z0 *)
    We argue by contradiction.
    Assume that Z.neg p1 ≠ 0%Z.
    By Hinj it holds that (&  
      g_Z(Z.neg p1) = g_Z(0%Z) = 0%nat
    ).
    Contradiction.
  - (* n1 = Zneg p1, n2 = Zpos p2 *)
    We argue by contradiction.
    Assume that Z.neg p1 ≠ Z.pos p2.
    It holds that g_Z (Z.neg p1) = Z.to_nat ((-2) * Z.neg p1 - 1)%Z.
    It holds that g_Z (Z.pos p2) = Z.to_nat (2 * Z.pos p2)%Z.
    It holds that
      g_Z(Z.neg p1) ≠ g_Z(Z.pos p2).
    By Hinj it holds that
      g_Z(Z.neg p1) = g_Z(Z.pos p2).
    Contradiction.
  - (* n1 = Zneg p1, n2 = Zneg p2 *)
    It holds that g_Z (Z.neg p1) = Z.to_nat ((-2) * Z.neg p1 - 1)%Z.
    It holds that g_Z (Z.neg p2) = Z.to_nat ((-2) * Z.neg p2 - 1)%Z.
    By Hinj it holds that (&
      Z.to_nat ((-2) * Z.neg p1 - 1)%Z
      = g_Z(Z.neg p1) = g_Z(Z.neg p2)
      = Z.to_nat ((-2) * Z.neg p2 - 1)%Z
    ).
    We conclude that Z.neg p1 = Z.neg p2.
Qed.

Lemma Z_countable : countable Z.
Proof.
  It suffices to show that ∃ f : Z → ℕ, f is injective.
  Choose f := g_Z.
  By g_Z_injective we conclude that f is injective.
Qed.

(** ** ℕ × ℕ is countable (Cantor pairing) *)

Definition cantor_pair (mn : ℕ * ℕ) : ℕ :=
  let m := fst mn : ℕ in
  let n := snd mn : ℕ in
  (m + n) * (m + n + 1%nat) / 2 + n.

(** This is already defined in Arith.Cantor
    as [Cantor.to_nat], we are going to use that.
    The code in Rocq is not so bad, look for [Cantor.to_nat_inj].

    I was not able to do a fully-Waterproof version
    using the cantor_pair as defined above. *)

Lemma NxN_countable : countable (ℕ * ℕ).
Proof.
  It suffices to show that ∃ f : (ℕ * ℕ) → ℕ, f is injective.
  Choose f := Cantor.to_nat.
  We need to show that ∀ a ∈ (nat * nat)%type, ∀ b ∈ (nat * nat)%type,
    f(a) = f(b) ⇨ a = b.
  Take a, b ∈ (nat * nat)%type. Assume that f(a) = f(b).
  (* Cantor.to_nat_inj : ∀ p q, to_nat p = to_nat q → p = q *)
  By Cantor.to_nat_inj we conclude that a = b.
Qed.

(** ** Cantor's theorem *)

(** There is no surjective function [A → 𝒫(A)].

    Proof (diagonal argument): given [g : A → 𝒫(A)], define
    [B = {x ∈ A : x ∉ g(x)}]. If [B = g(x')] then [x' ∈ B ⇔ x' ∉ g(x') = B],
    a contradiction; so [g] is not surjective. *)
Lemma cantors_theorem (A : Type) (g : A → (A → Prop)) :
    ¬ g is surjective.
Proof.
  We argue by contradiction.
  Assume that ¬ ¬ g is surjective.
  It holds that g is surjective.
  It holds that ∀ y ∈ (A → Prop), ∃ x ∈ A, g x = y as (Hsurj).
  Define B := fun x => ¬ g x x.
  By Hsurj it holds that ∃ x0 ∈ A, g x0 = B.
  Obtain such a x0.
  It holds that g x0 = B.
  We claim that (g x0 x0 ↔ ¬ g x0 x0).
  { We show both directions. 
    - We need to show that g(x0, x0) ⇨ ¬ g(x0, x0).
      Assume that g x0 x0 as (Hg).
      It holds that (&
        g x0 x0 = B x0 = ¬ g x0 x0
      ).
      It holds that g x0 x0 = ¬ g x0 x0 as (Heq).
      rewrite Heq in Hg.
      By Hg we conclude that ¬ g x0 x0.
    - We need to show that ¬ g(x0, x0) ⇨ g(x0, x0).
      Assume that ¬ g x0 x0 as (Hng).
      It holds that (&
        (¬ g x0 x0) = B x0 = g x0 x0
      ).
      It holds that (¬ g x0 x0) = g x0 x0 as (Heq).
      rewrite Heq in Hng.
      By Hng we conclude that g x0 x0.
  }
  Contradiction.
Qed.

(** ** ℝ is uncountable *)

Axiom R_uncountable : ¬ ∃ f : ℕ → ℝ, f is surjective.
