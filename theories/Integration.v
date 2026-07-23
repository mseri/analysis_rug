(** * RUG.Analysis.Integration — The Riemann integral.

  #<a href="../../index.html##lecture15">Lecture 15</a>#.

  Formalizes Abbott §7.2–7.4: partitions and Darboux (upper/lower) sums, the
  refinement lemmas, the upper and lower integrals, the Riemann/Darboux
  criterion for integrability, integrability of continuous and of monotone
  functions, and the basic algebraic properties (linearity, monotonicity,
  additivity over intervals). *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.RiemannInt.
From Stdlib Require Import Reals.PartSum.
From Stdlib Require Import micromega.Lra.
Require Export RUG.Analysis.Continuity.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Partitions and Darboux sums

    We build the Riemann integral from Darboux's upper and lower sums, following
    Abbott §7.2. Alongside this "from scratch" development we also reuse the
    Stdlib predicate [Riemann_integrable] and its integral [RiemannInt] for the
    algebraic property lemmas at the end of the file. *)

(** A *partition* of [[a, b]] into [n] cells is a strictly increasing sequence
    of [n + 1] nodes [x₀ = a < x₁ < ⋯ < xₙ = b]. We represent the nodes by a
    function [x : ℕ → ℝ], using only the indices [0 … n]. *)
Definition is_partition (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
    x 0%nat = a ∧ x n = b ∧ (∀ i : ℕ, (i < n)%nat → x i < x (S i)).

(** [mi] is the *infimum* of [f] on the [i]-th cell [[xᵢ, xᵢ₊₁]]. *)
Definition is_inf_on_cell (f : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) (mi : ℝ) : Prop :=
    (∀ t : ℝ, x i ≤ t ∧ t ≤ x (S i) → mi ≤ f t) ∧
    (∀ w : ℝ, (∀ t : ℝ, x i ≤ t ∧ t ≤ x (S i) → w ≤ f t) → w ≤ mi).

(** [Mi] is the *supremum* of [f] on the [i]-th cell [[xᵢ, xᵢ₊₁]]. *)
Definition is_sup_on_cell (f : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) (Mi : ℝ) : Prop :=
    (∀ t : ℝ, x i ≤ t ∧ t ≤ x (S i) → f t ≤ Mi) ∧
    (∀ w : ℝ, (∀ t : ℝ, x i ≤ t ∧ t ≤ x (S i) → f t ≤ w) → Mi ≤ w).

(** The *lower sum* [L(f, P) = ∑ mᵢ · (xᵢ₊₁ - xᵢ)], where [mᵢ] is the infimum of
    [f] on the [i]-th cell. *)
Definition lower_sum (n : ℕ) (x m : ℕ → ℝ) : ℝ :=
    sum_f_R0 (fun i => m i * (x (S i) - x i)) (pred n).

(** The *upper sum* [U(f, P) = ∑ Mᵢ · (xᵢ₊₁ - xᵢ)], where [Mᵢ] is the supremum
    of [f] on the [i]-th cell. *)
Definition upper_sum (n : ℕ) (x M : ℕ → ℝ) : ℝ :=
    sum_f_R0 (fun i => M i * (x (S i) - x i)) (pred n).

(** A partition [Q] (with [m] cells, nodes [y]) *refines* [P] (with [n] cells,
    nodes [x]) if every node of [P] is also a node of [Q]. *)
Definition refines (n : ℕ) (x : ℕ → ℝ) (m : ℕ) (y : ℕ → ℝ) : Prop :=
    ∀ i : ℕ, (i ≤ n)%nat → ∃ j : ℕ, (j ≤ m)%nat ∧ y j = x i.

(** ** Refinement inequalities *)

(** _Refinement increases lower sums_: if [Q] refines [P] then
    [L(f, P) ≤ L(f, Q)].

    Proof idea: adding one node splits a cell into two; the infimum over each
    smaller cell is at least the infimum over the whole, so the corresponding
    contribution can only increase. Iterate over the added nodes. *)
Lemma refinement_increases_lower_sum (f : ℝ → ℝ) (a b : ℝ)
    (n : ℕ) (x mx : ℕ → ℝ) (m : ℕ) (y my : ℕ → ℝ)
    (HP : is_partition a b n x) (HQ : is_partition a b m y)
    (Href : refines n x m y)
    (Hmx : ∀ i : ℕ, (i < n)%nat → is_inf_on_cell f x i (mx i))
    (Hmy : ∀ j : ℕ, (j < m)%nat → is_inf_on_cell f y j (my j)) :
    lower_sum n x mx ≤ lower_sum m y my.
Proof.
  Admitted.

(** _Refinement decreases upper sums_: if [Q] refines [P] then
    [U(f, Q) ≤ U(f, P)].

    Proof idea: dual to the previous lemma — the supremum over a smaller cell is
    at most the supremum over the whole. *)
Lemma refinement_decreases_upper_sum (f : ℝ → ℝ) (a b : ℝ)
    (n : ℕ) (x Mx : ℕ → ℝ) (m : ℕ) (y My : ℕ → ℝ)
    (HP : is_partition a b n x) (HQ : is_partition a b m y)
    (Href : refines n x m y)
    (HMx : ∀ i : ℕ, (i < n)%nat → is_sup_on_cell f x i (Mx i))
    (HMy : ∀ j : ℕ, (j < m)%nat → is_sup_on_cell f y j (My j)) :
    upper_sum m y My ≤ upper_sum n x Mx.
Proof.
  Admitted.

(** _Refinement inequalities_ (corollary): for a common refinement [Q] of [P],
    [L(f, P) ≤ L(f, Q) ≤ U(f, Q) ≤ U(f, P)]. *)
Lemma refinement_inequalities (f : ℝ → ℝ) (a b : ℝ)
    (n : ℕ) (x mx Mx : ℕ → ℝ) (m : ℕ) (y my My : ℕ → ℝ)
    (HP : is_partition a b n x) (HQ : is_partition a b m y)
    (Href : refines n x m y)
    (Hmx : ∀ i : ℕ, (i < n)%nat → is_inf_on_cell f x i (mx i))
    (HMx : ∀ i : ℕ, (i < n)%nat → is_sup_on_cell f x i (Mx i))
    (Hmy : ∀ j : ℕ, (j < m)%nat → is_inf_on_cell f y j (my j))
    (HMy : ∀ j : ℕ, (j < m)%nat → is_sup_on_cell f y j (My j)) :
    lower_sum n x mx ≤ lower_sum m y my ∧
    lower_sum m y my ≤ upper_sum m y My ∧
    upper_sum m y My ≤ upper_sum n x Mx.
Proof.
  Admitted.

(** _Any lower sum is below any upper sum_: for arbitrary partitions [P₁], [P₂],
    [L(f, P₁) ≤ U(f, P₂)].

    Proof idea: take the common refinement [P₁ ∪ P₂] and chain the refinement
    inequalities:
    [L(f, P₁) ≤ L(f, P₁ ∪ P₂) ≤ U(f, P₁ ∪ P₂) ≤ U(f, P₂)]. *)
Lemma lower_sum_le_upper_sum (f : ℝ → ℝ) (a b : ℝ)
    (n1 : ℕ) (x1 m1 : ℕ → ℝ) (n2 : ℕ) (x2 M2 : ℕ → ℝ)
    (HP1 : is_partition a b n1 x1) (HP2 : is_partition a b n2 x2)
    (Hm1 : ∀ i : ℕ, (i < n1)%nat → is_inf_on_cell f x1 i (m1 i))
    (HM2 : ∀ i : ℕ, (i < n2)%nat → is_sup_on_cell f x2 i (M2 i)) :
    lower_sum n1 x1 m1 ≤ upper_sum n2 x2 M2.
Proof.
  Admitted.

(** ** Upper and lower integrals *)

(** [S] is *a lower sum of [f] on [[a, b]]*: it is [L(f, P)] for some partition
    [P] with infimum data. *)
Definition lower_sum_of (f : ℝ → ℝ) (a b s : ℝ) : Prop :=
    ∃ n : ℕ, ∃ x : ℕ → ℝ, ∃ m : ℕ → ℝ,
      is_partition a b n x ∧
      (∀ i : ℕ, (i < n)%nat → is_inf_on_cell f x i (m i)) ∧
      s = lower_sum n x m.

(** [S] is *an upper sum of [f] on [[a, b]]*. *)
Definition upper_sum_of (f : ℝ → ℝ) (a b s : ℝ) : Prop :=
    ∃ n : ℕ, ∃ x : ℕ → ℝ, ∃ M : ℕ → ℝ,
      is_partition a b n x ∧
      (∀ i : ℕ, (i < n)%nat → is_sup_on_cell f x i (M i)) ∧
      s = upper_sum n x M.

(** The *lower integral* [L(f) = sup { L(f, P) : P }] is the least upper bound of
    all lower sums. *)
Definition is_lower_integral (f : ℝ → ℝ) (a b L : ℝ) : Prop :=
    (∀ s : ℝ, lower_sum_of f a b s → s ≤ L) ∧
    (∀ W : ℝ, (∀ s : ℝ, lower_sum_of f a b s → s ≤ W) → L ≤ W).

(** The *upper integral* [U(f) = inf { U(f, P) : P }] is the greatest lower bound
    of all upper sums. *)
Definition is_upper_integral (f : ℝ → ℝ) (a b U : ℝ) : Prop :=
    (∀ s : ℝ, upper_sum_of f a b s → U ≤ s) ∧
    (∀ W : ℝ, (∀ s : ℝ, upper_sum_of f a b s → W ≤ s) → W ≤ U).

(** _The lower integral does not exceed the upper integral_: [L(f) ≤ U(f)].

    Proof idea: every lower sum is a lower bound for the set of upper sums (by
    [lower_sum_le_upper_sum]), hence at most the upper integral; taking the
    supremum over lower sums gives [L(f) ≤ U(f)]. *)
Lemma lower_integral_le_upper (f : ℝ → ℝ) (a b L U : ℝ)
    (HL : is_lower_integral f a b L) (HU : is_upper_integral f a b U) :
    L ≤ U.
Proof.
  Admitted.

(** ** Integrability and the Darboux criterion *)

(** [f] is *Darboux/Riemann integrable* on [[a, b]] when its upper and lower
    integrals coincide; the common value is [∫_a^b f]. *)
Definition riemann_integrable_darboux (f : ℝ → ℝ) (a b : ℝ) : Prop :=
    ∃ V : ℝ, is_lower_integral f a b V ∧ is_upper_integral f a b V.

(** _Darboux criterion_ (Abbott 7.2.8): [f] is integrable on [[a, b]] iff for
    every [ε > 0] there is a partition [P] with [U(f, P) - L(f, P) < ε].

    Proof idea: (⇒) if [L(f) = U(f)], choose partitions whose lower/upper sums
    approximate this common value within [ε/2], and take their common
    refinement. (⇐) the gap [U(f) - L(f) ≤ U(f, P) - L(f, P) < ε] for all [ε],
    forcing equality. (For instance the Dirichlet function [𝟙_ℚ] fails this on
    [[0,1]], since [U(f, P) = 1] and [L(f, P) = 0] for every [P].) *)
Lemma darboux_criterion (f : ℝ → ℝ) (a b : ℝ) :
    riemann_integrable_darboux f a b ⇔
    (∀ ε > 0, ∃ n : ℕ, ∃ x : ℕ → ℝ, ∃ m : ℕ → ℝ, ∃ M : ℕ → ℝ,
      is_partition a b n x ∧
      (∀ i : ℕ, (i < n)%nat → is_inf_on_cell f x i (m i)) ∧
      (∀ i : ℕ, (i < n)%nat → is_sup_on_cell f x i (M i)) ∧
      upper_sum n x M - lower_sum n x m < ε).
Proof.
  Admitted.

(** ** Constant functions are integrable *)

(** The constant function [x ↦ c] is Riemann integrable on [[a, b]], for any [a]
    and [b].

    Proof idea: for a constant every upper and lower sum equals [c · (b - a)],
    so the Darboux criterion holds trivially. *)
Lemma constant_integrable (a b c : ℝ) :
    Riemann_integrable (fct_cte c) a b.
Proof.
  Admitted.

(** The integral of a constant is [∫_a^b c = c · (b - a)]. *)
Lemma integral_constant (a b c : ℝ)
    (pr : Riemann_integrable (fct_cte c) a b) :
    RiemannInt pr = c * (b - a).
Proof.
  Admitted.

(** ** Continuous functions are integrable *)

(** If [f] is continuous on [[a, b]] (with [a ≤ b]), then [f] is Riemann
    integrable.

    Proof idea: a continuous function on a compact interval is uniformly
    continuous (Heine), so for [ε > 0] a fine enough uniform partition makes each
    oscillation small, giving [U(f, P) - L(f, P) < ε]; apply the Darboux
    criterion. *)
Theorem continuous_integrable (f : ℝ → ℝ) (a b : ℝ)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x) :
    Riemann_integrable f a b.
Proof.
  Admitted.

(** ** Monotone functions are integrable *)

(** Exercise (Abbott): a *monotone* function on [[a, b]] is Riemann integrable.

    Proof idea: for an increasing [f] and the uniform partition with mesh
    [(b - a)/n], the total oscillation telescopes:
    [∑ (Mᵢ - mᵢ)·Δx = (f(b) - f(a))·(b - a)/n → 0]. The Darboux criterion then
    applies. (The decreasing case is symmetric.) *)
Lemma monotone_integrable (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hmono : ∀ x : ℝ, ∀ y : ℝ, a ≤ x → x ≤ y → y ≤ b → f x ≤ f y) :
    Riemann_integrable f a b.
Proof.
  Admitted.

(** ** The integral test *)

(** _Integral test_ (Lecture 4): for a nonnegative decreasing [f] on [[1, ∞)],
    the series [∑ f(k)] converges iff the sequence of integrals
    [∫_1^{n} f] is bounded.

    Proof idea: monotonicity gives, on each unit interval,
    [f(k+1) ≤ ∫_k^{k+1} f ≤ f(k)]; summing sandwiches the partial sums between
    consecutive integrals, so the series and the improper integral converge
    together. (Terms indexed as [f(k+1)] to match Rocq indexing.) *)
Lemma integral_test (f : ℝ → ℝ)
    (Hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (Hdec : ∀ x : ℝ, ∀ y : ℝ, 1 ≤ x → x ≤ y → f y ≤ f x)
    (Hint : ∀ n : ℕ, Riemann_integrable f 1 (INR n + 1)) :
    (∃ L : ℝ, (fun n : ℕ => sum_f_R0 (fun k => f (INR k + 1)) n) ⟶ L) ⇔
    (∃ B : ℝ, ∀ n : ℕ, ∀ pr : Riemann_integrable f 1 (INR n + 1),
        RiemannInt pr ≤ B).
Proof.
  Admitted.

(** ** Linearity of the integral *)

(** The sum of two integrable functions is integrable. *)
Lemma sum_integrable (f g : ℝ → ℝ) (a b : ℝ)
    (pr1 : Riemann_integrable f a b)
    (pr2 : Riemann_integrable g a b) :
    Riemann_integrable (fun x => f x + g x) a b.
Proof.
  Admitted.

(** [∫(f + g) = ∫f + ∫g]. *)
Lemma integral_sum (f g : ℝ → ℝ) (a b : ℝ)
    (prf : Riemann_integrable f a b)
    (prg : Riemann_integrable g a b) :
    ∃ prfg : Riemann_integrable (fun x => f x + g x) a b,
      RiemannInt prfg = RiemannInt prf + RiemannInt prg.
Proof.
  Admitted.

(** [∫(c · f) = c · ∫f]. *)
Lemma integral_scalar (f : ℝ → ℝ) (a b c : ℝ)
    (prf : Riemann_integrable f a b) :
    ∃ prcf : Riemann_integrable (fun x => c * f x) a b,
      RiemannInt prcf = c * RiemannInt prf.
Proof.
  Admitted.

(** ** Monotonicity *)

(** _Monotonicity_ (order property): if [f ≤ g] on [(a, b)] then [∫f ≤ ∫g]. *)
Lemma integral_monotone (f g : ℝ → ℝ) (a b : ℝ)
    (prf : Riemann_integrable f a b)
    (prg : Riemann_integrable g a b)
    (Hle : ∀ x, a ≤ x ∧ x ≤ b → f x ≤ g x) :
    RiemannInt prf ≤ RiemannInt prg.
Proof.
  Admitted.

(** ** Additivity over sub-intervals *)

(** [∫_a^b f = ∫_a^c f + ∫_c^b f] for [a ≤ c ≤ b]. *)
Lemma integral_split (f : ℝ → ℝ) (a b c : ℝ)
    (Hac : a ≤ c) (Hcb : c ≤ b)
    (prf : Riemann_integrable f a b) :
    ∃ (pr1 : Riemann_integrable f a c),
    ∃ (pr2 : Riemann_integrable f c b),
      RiemannInt prf = RiemannInt pr1 + RiemannInt pr2.
Proof.
  Admitted.
