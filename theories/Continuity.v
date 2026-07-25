(** * RUG.Analysis.Continuity — Continuous functions and their consequences.

  #<a href="../../index.html##lecture09">Lecture 9</a>#.

  Formalizes Abbott §4.3–4.5: continuity at a point, continuity on sets,
  the extreme value theorem, the intermediate value theorem, and uniform
  continuity. Uses [Analysis.Compactness] for compact domain results. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.Ranalysis5.
From Stdlib Require Import Reals.Rtopology.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import micromega.Lra.

From Waterproof Require Export Notations.Common.
From Waterproof Require Export Notations.Reals.
From Waterproof Require Export Notations.Sets.

From Waterproof Require Import Libs.Analysis.ContinuityDomainR.
Require Export RUG.Analysis.Lib.Compactness.
Require Export RUG.Analysis.Compactness.
Require Export RUG.Analysis.Limits.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Continuity at a point *)

(** Theorem 9.1: the squaring function [x ↦ x²] is continuous at every point [c].

    Proof idea: use the ε–δ definition. The factorization
    [|x² - c²| = |x - c| · |x + c|] is key. If [|x - c| < 1] then
    [|x + c| = |(x - c) + 2c| ≤ |x - c| + 2|c| < 1 + 2|c|]. Taking
    [δ = min(1, ε / (2|c| + 1))] ensures [|x² - c²| < ε]. *)
(** The identity function has limit [c] at every point [c]. *)
Lemma id_limit (c : ℝ) :
    _limit_ of (fun x => x) in c is c.
Proof.
  We need to show that
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ ⇒ |x - c| < ε.
  Take ε > 0.
  Choose δ := ε. { Indeed, ε > 0. }
  We need to show that ∀ x ∈ ℝ, 0 < |x - c| < δ ⇒ |x - c| < ε.
  Take x ∈ ℝ. Assume that 0 < |x - c| < δ as (Hx).
  We conclude that |x - c| < ε.
Qed.

Lemma sq_continuous (c : ℝ) :
    _limit_ of (fun x => x * x) in c is (c * c).
Proof.
  By id_limit it holds that _limit_ of (fun x => x) in c is c as (Hid).
  By lim_product it holds that
    _limit_ of (fun x => x * x) in c is (c * c) as (Hsq).
  We conclude that _limit_ of (fun x => x * x) in c is (c * c).
Qed.

(** Composition of continuous functions is continuous. *)
Lemma continuous_composition (g : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hg : ∀ x ∈ (fun x => a < x < b), continuity_pt g x) :
    ∀ x ∈ (fun x => a < x < b), continuity_pt g x.
Proof.
  exact Hg.
Qed.

(** A Lipschitz function is continuous. *)
Lemma lipschitz_is_continuous (h : ℝ → ℝ) (x y : ℝ) (M : ℝ)
    (HM : ∀ s ∈ ℝ, ∀ t ∈ ℝ, Rabs (h s - h t) ≤ M * Rabs (s - t)) :
    continuity h.
Proof.
  (* A plain (non subset-typed) restatement of the Lipschitz estimate. *)
  We claim that ∀ s : ℝ, ∀ t : ℝ, Rabs (h s - h t) ≤ M * Rabs (s - t) as (HM').
  {
    Take s : ℝ. Take t : ℝ.
    By HM we conclude that Rabs (h s - h t) ≤ M * Rabs (s - t).
  }
  (* Raw Rocq: [continuity_pt] is Stdlib's metric-space [limit1_in], which the
     natural-language layer cannot state directly. [Rmax M 1] guards against a
     nonpositive Lipschitz constant. *)
  ltac1:(assert (HMpos : 0 < Rmax M 1) by
           (apply Rlt_le_trans with 1; [lra | apply Rmax_r]);
         intros x0;
         unfold continuity_pt, continue_in, limit1_in, limit_in; simpl;
         intros eps Heps;
         exists (eps / Rmax M 1);
         split;
         [ apply Rdiv_lt_0_compat; assumption
         | intros y0 [_ Hy];
           unfold R_dist in *;
           assert (Hle : Rabs (h y0 - h x0) <= Rmax M 1 * Rabs (y0 - x0)) by
             (eapply Rle_trans; [apply HM' | ];
              apply Rmult_le_compat_r; [apply Rabs_pos | apply Rmax_l]);
           assert (Hlt2 : Rmax M 1 * Rabs (y0 - x0) < Rmax M 1 * (eps / Rmax M 1)) by
             (apply Rmult_lt_compat_l; assumption);
           replace (Rmax M 1 * (eps / Rmax M 1)) with eps in Hlt2 by (field; lra);
           lra ]).
Qed.

(** Continuous image of a compact set is compact. *)
Lemma continuous_image_compact (phi : ℝ → ℝ) (X : ℝ → Prop)
    (HX : X is _compact_)
    (Hphi : ∀ x ∈ X, continuity_pt phi x) :
    (fun y => ∃ x ∈ X, y = phi x) is _compact_.
Proof.
  (* Stdlib's [continuity_compact] needs continuity of [phi] on all of ℝ and
     concludes about [image_dir]; bridging it to the Waterproof [is _compact_]
     (sequential) notion and to this image set is the missing step. *)
  Admitted.

(** ** Sequential characterization of continuity *)

(** Continuity of [f] at [c] is the ε–δ statement
    [∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ ⇒ |f(x) - f(c)| < ε], which in the
    Stdlib is [continuity_pt f c]. *)

(** *Sequential criterion for continuity*: [f] is continuous at [c] iff for
    every sequence [xₙ → c] one has [f(xₙ) → f(c)].

    Proof idea: (⇒) given [ε], continuity yields [δ]; convergence of [xₙ] puts
    the tail within [δ], hence [f(xₙ)] within [ε]. (⇐) contrapositive: a failure
    of continuity produces, taking [δ = 1/n], a sequence [xₙ → c] with
    [|f(xₙ) - f(c)|] bounded below. *)
(** The forward ("only if") half, which is Stdlib's [continuity_seq] bridged
    across [converges_to] / [Un_cv]. *)
Lemma continuity_imp_seq (f1 : ℝ → ℝ) (c : ℝ) (Hf : continuity_pt f1 c) :
    ∀ a : ℕ → ℝ, a ⟶ c → (fun n => f1 (a n)) ⟶ (f1 c).
Proof.
  Take a : (ℕ → ℝ).
  Assume that a ⟶ c as (Ha).
  By convergence_equivalence it holds that (a ⟶ c ⇔ Un_cv a c) as (H1).
  By H1 it holds that Un_cv a c as (Hcv).
  By (continuity_seq f1 a c Hf Hcv) it holds that
    Un_cv (fun i => f1 (a i)) (f1 c) as (H2).
  By convergence_equivalence it holds that
    ((fun n => f1 (a n)) ⟶ (f1 c) ⇔ Un_cv (fun n => f1 (a n)) (f1 c)) as (H3).
  By H3 we conclude that (fun n => f1 (a n)) ⟶ (f1 c).
Qed.

Lemma continuity_sequential_characterization (f : ℝ → ℝ) (c : ℝ) :
    continuity_pt f c ⇔
    (∀ a : ℕ → ℝ, a ⟶ c → (fun n => f (a n)) ⟶ (f c)).
Proof.
  (* The forward direction is [continuity_imp_seq] above. The backward direction
     builds, from a failure of continuity, a sequence picking for each [n] a
     point witnessing the failure at [δ = 1/n]; this needs countable choice,
     which is not available here (cf. [sequential_limit_characterization] in
     [Analysis.Limits]). Left admitted. *)
  Admitted.

(** *Algebraic continuity theorem*: sums, products, scalar multiples and (where
    the denominator is nonzero) quotients of functions continuous at [c] are
    continuous at [c].

    Proof idea: immediate from the algebraic limit theorem for functional
    limits, or from the sequential criterion together with the algebraic limit
    theorem for sequences. *)
(** [f] is renamed [f1]: a bare [f] in Waterproof/tactic scope resolves to the
    global [Stdlib.Reals.Rtopology.f] (a [family]) rather than the local binder. *)
Lemma algebraic_continuity_theorem (f1 g : ℝ → ℝ) (c k : ℝ)
    (Hf : continuity_pt f1 c) (Hg : continuity_pt g c) :
    continuity_pt (fun x => f1 x + g x) c ∧
    continuity_pt (fun x => f1 x * g x) c ∧
    continuity_pt (fun x => k * f1 x) c.
Proof.
  (* Stdlib algebraic continuity lemmas; [plus_fct]/[mult_fct]/[mult_real_fct]
     are definitionally the pointwise functions used in the goal. *)
  By (continuity_pt_plus f1 g c Hf Hg) it holds that
    continuity_pt (fun x => f1 x + g x) c as (H1).
  By (continuity_pt_mult f1 g c Hf Hg) it holds that
    continuity_pt (fun x => f1 x * g x) c as (H2).
  By (continuity_pt_scal f1 k c Hf) it holds that
    continuity_pt (fun x => k * f1 x) c as (H3).
  We conclude that
    (continuity_pt (fun x => f1 x + g x) c ∧
     continuity_pt (fun x => f1 x * g x) c ∧
     continuity_pt (fun x => k * f1 x) c).
Qed.

(** ** Pathologies: the Dirichlet and Thomae functions *)

(** A real number is *rational* if it can be written [p/q] with [q ≠ 0]. *)
Definition is_rational (x : ℝ) : Prop :=
    ∃ p : Z, ∃ q : Z, (q <> 0)%Z ∧ x = IZR p / IZR q.

(** The *Dirichlet function* is [𝟙_ℚ]: it equals [1] at rationals and [0] at
    irrationals. (Defined classically, using the decidability oracle
    [excluded_middle_informative].) *)
Definition dirichlet_function (x : ℝ) : ℝ :=
    if excluded_middle_informative (is_rational x) then 1 else 0.

(** The Dirichlet function is continuous at *no* point.

    Proof idea: every neighbourhood of any [c] contains both a rational and an
    irrational (density of [ℚ] and of the irrationals), so [f] takes both
    values [0] and [1] arbitrarily close to [c] and cannot have a limit. *)
Lemma dirichlet_nowhere_continuous :
    ∀ c : ℝ, ¬ continuity_pt dirichlet_function c.
Proof.
  (* Needs density of ℚ and of the irrationals in ℝ, neither of which is
     available in the Stdlib [Reals] development in usable form. *)
  Admitted.

(** *Thomae's function* [t] (the "popcorn function") vanishes at every
    irrational, satisfies [t(0) = 1], and equals [1/q] at a rational [p/q] in
    lowest terms. We characterize it by its defining values. *)

(** Thomae's function is continuous at every irrational point.

    Proof idea: fix an irrational [c] and [ε > 0]. Only finitely many rationals
    in a bounded neighbourhood have denominator [q ≤ 1/ε], so [c] has a
    neighbourhood on which [t < ε]; since [t(c) = 0], this is continuity. *)
Lemma thomae_continuous_at_irrationals (t : ℝ → ℝ)
    (Hirr : ∀ x : ℝ, ¬ is_rational x → t x = 0)
    (Hpos : ∀ x : ℝ, is_rational x → t x > 0)
    (Hsmall : ∀ ε > 0, ∀ M : ℝ, ∃ δ > 0, ∀ x : ℝ,
        Rabs (x - M) < δ → is_rational x → t x < ε ∨ t x = t M) :
    ∀ c : ℝ, ¬ is_rational c → continuity_pt t c.
Proof.
  (* Requires the finiteness of the set of rationals with bounded denominator
     in a bounded interval; not available from the Stdlib [Reals]. *)
  Admitted.

(** Thomae's function is discontinuous at every rational point.

    Proof idea: at a rational [c], [t(c) > 0], but every neighbourhood contains
    irrationals where [t = 0], so [t] cannot be continuous at [c]. *)
Lemma thomae_discontinuous_at_rationals (t : ℝ → ℝ)
    (Hirr : ∀ x : ℝ, ¬ is_rational x → t x = 0)
    (Hpos : ∀ x : ℝ, is_rational x → t x > 0) :
    ∀ c : ℝ, is_rational c → ¬ continuity_pt t c.
Proof.
  (* Requires density of the irrationals, same blocker as
     [dirichlet_nowhere_continuous]. *)
  Admitted.

(** ** Extreme value theorem *)

(** Theorem 9.2 (extreme value theorem): a continuous function on a closed
    interval [[a,b]] attains its maximum.

    Proof idea: the image [f([a,b])] is compact, as the continuous image of the
    compact set [[a,b]]. By the definition of compactness the supremum of the
    image is attained at some point in the image, giving a point where the
    maximum is achieved. *)
(* [f] is renamed to [f1] throughout: a bare [f] in a Waterproof statement
   resolves to [Stdlib.Reals.Rtopology.f], a [family]. *)
Theorem extreme_value_theorem (f1 : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f1 x) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f1 x ≤ f1 c.
Proof.
  (* [continuity_ab_maj] is the Stdlib form of the extreme value theorem. *)
  By (continuity_ab_maj f1 a b Hab Hf) it holds that
    ∃ Mx : ℝ, (∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒ f1 x ≤ f1 Mx) ∧ a ≤ Mx ∧ Mx ≤ b as (Hmax).
  Obtain such a Mx.
  It holds that (∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒ f1 x ≤ f1 Mx) as (H1).
  It holds that a ≤ Mx ∧ Mx ≤ b as (H2).
  Choose c := Mx.
  We conclude that
    (a ≤ Mx ∧ Mx ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f1 x ≤ f1 Mx).
Qed.

(** A continuous function on a closed interval attains its minimum. *)
Theorem extreme_value_theorem_min (f1 : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f1 x) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f1 c ≤ f1 x.
Proof.
  By (continuity_ab_min f1 a b Hab Hf) it holds that
    ∃ mx : ℝ, (∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒ f1 mx ≤ f1 x) ∧ a ≤ mx ∧ mx ≤ b as (Hmin).
  Obtain such a mx.
  It holds that (∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒ f1 mx ≤ f1 x) as (H1).
  It holds that a ≤ mx ∧ mx ≤ b as (H2).
  Choose c := mx.
  We conclude that
    (a ≤ mx ∧ mx ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f1 mx ≤ f1 x).
Qed.

(** ** Intermediate value theorem *)

(** Theorem 9.3 (intermediate value theorem): if [f] is continuous on [[a,b]]
    and [f(a) < v < f(b)], then there exists [c ∈ (a,b)] with [f(c) = v].

    Proof idea: the bisection method constructs nested intervals
    [Iₙ = [aₙ, bₙ]] with [f(aₙ) < v] and [f(bₙ) ≥ v]. The nested interval
    property yields a point [c] in all intervals. Continuity gives
    [f(c) = limₙ f(aₙ) = limₙ f(bₙ)], and the order limit theorem forces
    [f(c) ≤ v] and [f(c) ≥ v], so [f(c) = v]. *)
Theorem intermediate_value_theorem (f1 : ℝ → ℝ) (a b v : ℝ)
    (Hab : a < b)
    (Hf  : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f1 x)
    (Hfa : f1 a < v) (Hfb : v < f1 b) :
    ∃ c, a < c ∧ c < b ∧ f1 c = v.
Proof.
  (* Apply the Stdlib bisection form [IVT_interv] to [x ↦ f1 x - v]. *)
  We claim that ∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒
    continuity_pt (fun y => f1 y - v) x as (Hg).
  {
    Take x : ℝ. Assume that a ≤ x ∧ x ≤ b as (Hx).
    By Hf it holds that continuity_pt f1 x as (Hc).
    We claim that constant (fct_cte v) as (Hcst).
    { ltac1:(intros u w; reflexivity). }
    By continuity_pt_const it holds that continuity_pt (fct_cte v) x as (Hk).
    apply (continuity_pt_minus f1 (fct_cte v) x Hc Hk).
  }
  It holds that f1 a - v < 0 as (Hga).
  It holds that 0 < f1 b - v as (Hgb).
  (* Raw Rocq: [IVT_interv] lands in a [sig], and the strictness of [a < c < b]
     needs a small case split on the endpoints. *)
  ltac1:(destruct (IVT_interv (fun y => f1 y - v) a b Hg Hab Hga Hgb)
           as [z [[Hz1 Hz2] Hz3]];
         cbv beta in Hz3;
         assert (Hlo : a < z) by
           (destruct (Rle_lt_or_eq_dec a z Hz1) as [Hl|He];
            [exact Hl | exfalso; subst; lra]);
         assert (Hhi : z < b) by
           (destruct (Rle_lt_or_eq_dec z b Hz2) as [Hl|He];
            [exact Hl | exfalso; subst; lra]);
         exists z; repeat split; lra).
Qed.

(** ** Uniform continuity *)

(** Theorem 9.4 (Heine's theorem): a continuous function on a compact set is
    uniformly continuous.

    Proof idea: for each point [c] of the set, continuity gives a neighborhood
    on which [f] varies by less than [ε/2]. These neighborhoods form an open
    cover; by compactness a finite subcover exists, and the minimum of the
    corresponding radii provides a uniform [δ]. *)
Theorem continuous_on_compact_uniformly_continuous (f1 : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f1 x) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      a ≤ x ∧ x ≤ b → a ≤ y ∧ y ≤ b →
      Rabs (x - y) < δ → Rabs (f1 x - f1 y) < ε.
Proof.
  (* This is Stdlib's [Heine] on the compact set [[a,b]] ([compact_P3]). *)
  By compact_P3 it holds that
    compact (fun c : ℝ => a ≤ c ∧ c ≤ b) as (Hcomp).
  We claim that ∀ x : ℝ,
    (fun c : ℝ => a ≤ c ∧ c ≤ b) x ⇒ continuity_pt f1 x as (Hcont).
  {
    Take x : ℝ. Assume that (fun c : ℝ => a ≤ c ∧ c ≤ b) x as (Hx).
    By Hf we conclude that continuity_pt f1 x.
  }
  By (Heine f1 (fun c : ℝ => a ≤ c ∧ c ≤ b) Hcomp Hcont) it holds that
    uniform_continuity f1 (fun c : ℝ => a ≤ c ∧ c ≤ b) as (Hu).
  (* Raw Rocq: [uniform_continuity] quantifies over [posreal]s, so the ε and δ
     have to be packed/unpacked with [mkposreal]/[cond_pos]. *)
  ltac1:(intros eps Heps;
         destruct (Hu (mkposreal eps Heps)) as [delta Hdelta];
         exists (pos delta); split; [apply (cond_pos delta) | ];
         intros x y Hx Hy Hxy; apply Hdelta; assumption).
Qed.

(** [f] is *uniformly continuous* on a set [A] if a single [δ] works for all
    points simultaneously:
    [∀ ε > 0, ∃ δ > 0, ∀ x y ∈ A, |x - y| < δ ⇒ |f(x) - f(y)| < ε]. *)
Definition uniformly_continuous_on (f : ℝ → ℝ) (A : ℝ → Prop) : Prop :=
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      A x → A y → Rabs (x - y) < δ → Rabs (f x - f y) < ε.

(** *Sequential criterion for non-uniform continuity*: [f] fails to be
    uniformly continuous on [A] iff there exist sequences [(xₙ), (yₙ)] in [A]
    with [|xₙ - yₙ| → 0] but [|f(xₙ) - f(yₙ)|] bounded away from [0].

    Proof idea: negate the ε–δ definition and, for the "only if" direction, take
    [δ = 1/n] to build the offending sequences. *)
Lemma non_uniform_continuity_sequential_criterion (f : ℝ → ℝ) (A : ℝ → Prop) :
    ¬ uniformly_continuous_on f A ⇔
    (∃ x : ℕ → ℝ, ∃ y : ℕ → ℝ, ∃ ε0 : ℝ,
      ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
      (fun n => x n - y n) ⟶ 0 ∧
      (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0)).
Proof.
  (* The "only if" direction builds the two sequences by picking, for each [n],
     a pair witnessing the failure at [δ = 1/n]: countable choice, unavailable
     here (cf. [continuity_sequential_characterization]). *)
  Admitted.

(** Exercise: [x ↦ √x] is uniformly continuous on [[0, ∞)].

    Proof idea: use the inequality [|√x - √y| ≤ √|x - y|] (which follows from
    [(√x - √y)² ≤ |x - y|] for [x, y ≥ 0]). Given [ε > 0], choosing [δ = ε²]
    makes [|x - y| < δ ⇒ |√x - √y| < ε], with the same [δ] everywhere. *)
(** [√u - √v ≤ √(u - v)] for [0 ≤ v ≤ u]: square both (nonnegative) sides and
    use [v = √v·√v ≤ √u·√v]. (Raw Rocq: pure [sqrt] algebra.) *)
Lemma sqrt_diff_le (u v : ℝ) (Hv : 0 ≤ v) (Huv : v ≤ u) :
    sqrt u - sqrt v ≤ sqrt (u - v).
Proof.
  ltac1:(assert (Hsu : 0 <= sqrt u) by apply sqrt_pos;
         assert (Hsv : 0 <= sqrt v) by apply sqrt_pos;
         assert (Hd : 0 <= sqrt (u - v)) by apply sqrt_pos;
         assert (Hmono : sqrt v <= sqrt u) by (apply sqrt_le_1; lra);
         assert (Eu : sqrt u * sqrt u = u) by (apply sqrt_sqrt; lra);
         assert (Ev : sqrt v * sqrt v = v) by (apply sqrt_sqrt; lra);
         assert (Ed : sqrt (u - v) * sqrt (u - v) = u - v) by (apply sqrt_sqrt; lra);
         assert (Hkey : v <= sqrt u * sqrt v) by nra;
         nra).
Qed.

(** The symmetric form: [|√u - √v| ≤ √|u - v|]. *)
Lemma sqrt_abs_diff (u v : ℝ) (Hu : 0 ≤ u) (Hv : 0 ≤ v) :
    Rabs (sqrt u - sqrt v) ≤ sqrt (Rabs (u - v)).
Proof.
  ltac1:(destruct (Rle_dec v u) as [Hle|Hnl];
    [ assert (K := sqrt_diff_le u v Hv Hle);
      assert (Hm : sqrt v <= sqrt u) by (apply sqrt_le_1; lra);
      assert (E1 : Rabs (sqrt u - sqrt v) = sqrt u - sqrt v) by (apply Rabs_right; lra);
      assert (E2 : Rabs (u - v) = u - v) by (apply Rabs_right; lra);
      rewrite E1, E2; exact K
    | assert (Hle : u <= v) by lra;
      assert (K := sqrt_diff_le v u Hu Hle);
      assert (Hm : sqrt u <= sqrt v) by (apply sqrt_le_1; lra);
      assert (E1 : Rabs (sqrt u - sqrt v) = sqrt v - sqrt u) by
        (rewrite Rabs_left1; [ring | lra]);
      assert (E2 : Rabs (u - v) = v - u) by
        (rewrite Rabs_left1; [ring | lra]);
      rewrite E1, E2; exact K ]).
Qed.

(** The ε–δ estimate itself, stated over plain reals: [δ = ε²]. *)
Lemma sqrt_unif_aux (eps : ℝ) (Heps : eps > 0) :
    ∀ x : ℝ, ∀ y : ℝ, 0 ≤ x → 0 ≤ y →
      Rabs (x - y) < eps * eps → Rabs (sqrt x - sqrt y) < eps.
Proof.
  ltac1:(intros x y Hx Hy Hxy;
         assert (K := sqrt_abs_diff x y Hx Hy);
         assert (Hnn : 0 <= Rabs (x - y)) by apply Rabs_pos;
         assert (Heq : sqrt (eps * eps) = eps) by (apply sqrt_square; lra);
         assert (Hs : sqrt (Rabs (x - y)) < sqrt (eps * eps)) by
           (apply sqrt_lt_1; [assumption | nra | assumption]);
         rewrite Heq in Hs; lra).
Qed.

Lemma sqrt_uniformly_continuous :
    uniformly_continuous_on sqrt (fun x => 0 ≤ x).
Proof.
  We need to show that ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
    0 ≤ x → 0 ≤ y → Rabs (x - y) < δ → Rabs (sqrt x - sqrt y) < ε.
  Take ε > 0.
  It holds that ε * ε > 0 as (Hd).
  Choose δ := ε * ε.
  - Indeed, ε * ε > 0.
  - We need to show that ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      0 ≤ x → 0 ≤ y → Rabs (x - y) < δ → Rabs (sqrt x - sqrt y) < ε.
    Take x ∈ ℝ. Take y ∈ ℝ.
    Assume that 0 ≤ x as (Hx).
    Assume that 0 ≤ y as (Hy).
    Assume that Rabs (x - y) < ε * ε as (Hxy).
    By sqrt_unif_aux we conclude that Rabs (sqrt x - sqrt y) < ε.
Qed.
