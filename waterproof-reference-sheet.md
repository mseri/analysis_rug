# Waterproof User Manual

*A guide to writing proofs with the `coq-waterproof` plugin (v3.x, Coq/Rocq ≥ 8.17), based on the source at [impermeable/coq-waterproof](https://github.com/impermeable/coq-waterproof) and the official tutorial notebook.*

Waterproof is a Coq plugin (OCaml + Ltac2) that provides a controlled natural language for proof scripts, mathematical notation (ℝ, ∈, ∀, chains of inequalities), enforced signposting, and configurable automation that discharges the routine steps a written proof would omit. It is aimed at teaching analysis-style proof writing, but is a genuine Coq plugin: everything below is ordinary Coq underneath, and you can drop to raw tactics at any point.

---

## 1. Setup

### 1.1 Installation

- **VS Code extension** (recommended for students): install "Waterproof" from the marketplace; it bundles the plugin and provides the notebook (`.mv`) interface with checkboxes, hints, and input areas.
- **Plain Coq**: `opam install coq-waterproof`, then use `.v` files with any Coq IDE.

### 1.2 Standard preamble

```coq
From Stdlib Require Import Rbase Rfunctions.

Require Import Waterproof.Waterproof.        (* core *)
Require Import Waterproof.Notations.Common.  (* ∀, ∃, ⇒, ∧, ∨, ¬, f(x) *)
Require Import Waterproof.Notations.Reals.   (* ℝ, ℕ, ℤ, |x|, intervals *)
Require Import Waterproof.Notations.Sets.    (* ∈, ⊂, ∩, ∪, bounded quantifiers *)
Require Import Waterproof.Chains.            (* & 0 < x ≤ 1 chains *)
Require Import Waterproof.Tactics.           (* the natural-language tactics *)
Require Import Waterproof.Automation.        (* hint databases *)

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.
Open Scope subset_scope.
Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".
```

Optional domain libraries under `Waterproof.Libs.*`: `Analysis` (sequences, series, sup/inf, continuity, metric spaces), `Reals`, `Integers`, `Sets`, `Logic`, `Negation`, `Functions`.

### 1.3 Automation datasets

`Waterproof Enable Automation <Dataset>` loads a preset of hint databases used by the closing tactics (`We conclude that`, `It holds that`, …). Built-in datasets (see `src/hint_dataset_declarations.ml`):

| Dataset | Main databases |
|---|---|
| `Core` | `core` |
| `Algebra` | `wp_core, arith, zarith, wp_algebra, wp_integers, wp_negation_int` |
| `Integers` | `arith, zarith, wp_core, wp_integers, wp_negation_int` |
| `RealsAndIntegers` | `arith, zarith, real, wp_core, wp_definitions, wp_alt_chars, wp_integers, wp_reals, wp_negation_reals` |
| `Sets` | `arith, zarith, wp_core, wp_integers, wp_negation_int, wp_sets` |
| `Intuition` | `wp_intuition` |
| `Empty`, `ClassicalEpsilon` | special-purpose |

Related commands: `Waterproof Disable Automation X`, `Waterproof Clear Automation`, `Waterproof List Automation Databases`, and (for instructors) `Waterproof Declare Automation MySet` + `Waterproof Set Main Databases MySet db1, db2` (also `Decidability`/`Shorten` in place of `Main`). Other toggles: `Waterproof Enable/Disable Automation Shield`, `Filter Errors`, `Debug Automation`, `Hypothesis Help`, `Redirect Feedback/Errors`, `Waterproof Print Version`.

The **shield** (on by default) prevents automation from silently performing "large" logical steps such as instantiating quantifiers or splitting an iff — the point being that students must write those steps explicitly.

---

## 2. Notation primer

### 2.1 Logic

| Waterproof | Coq | Notes |
|---|---|---|
| `∀ x ..., P` / `for all x, P` | `forall` | |
| `∃ x ..., P` / `there exists x, P` | `exists` | |
| `P ⇒ Q` (also `→`, `⇨`) | `P -> Q` | `⇨` is the printing form |
| `P ⇔ Q`, `↔` | `<->` | |
| `P ∧ Q`, `P ∨ Q`, `¬ P`, `x ≠ y` | `/\ , \/ , ~ , <>` | |
| `fun x ↦ t` | `fun x => t` | |
| `f(x)`, `f(x, y)` | `f x`, `f x y` | function application with parentheses |

### 2.2 Sets and bounded quantifiers (`subset_scope`)

Sets are `Ensemble`-based: `subset X` ≔ `Ensemble X`. Notation: `x ∈ A`, `x ∉ A`, `A ⊂ B`, `A ∩ B`, `A ∪ B`, `A \ B`, `∅`, `Ω`, `𝒫(X)`, `{ x ∈ X | P }`, `A is empty`, `A is inhabited`, `A is disjoint from B`.

Bounded quantifiers combine a binder with a predicate: `∀ x ∈ A, P`, `∃ ε > 0, P`, `∀ n ≥ N, P`, `∃ y ≠ 0, P`, and `∃! x ∈ A, P`. The predicates `∈ A`, `< y`, `≤ y`, `> y`, `≥ y`, `≠ y` are first-class here; internally `∀ x > 0, P` unfolds to `∀ x, x > 0 ⇒ P` and `∃ x > 0, P` to `∃ x, x > 0 ∧ P`.

### 2.3 Numbers and analysis

`ℕ ℤ ℚ ℝ`; `≤ ≥`; `|x|` for `Rabs`; intervals `[a,b]`, `[a,b)`, `(a,b]`, `(a,b)`, `[a,∞)`, `(a,∞)` as subsets of ℝ; `a ⟶ c` for `converges_to`; `Σ Cn equals x` for `infinite_sum`. `RealsWithSubsets` provides ℤ, ℚ as subsets of ℝ.

### 2.4 Chains of (in)equalities

Prefix a chain with `&`:

```coq
We conclude that & 3 < 5 = 2 + 3 ≤ 6.
```

A chain elaborates to the conjunction of adjacent relations (and its "global" consequence, e.g. `3 ≤ 6`). Mixing `<`/`≤` with `>`/`≥` in one chain is not allowed; `=` can be mixed with either direction.

---

## 3. The tactic language

Grammar convention below: `(...)` around a statement means an arbitrary Coq term; parenthesize any statement containing spaces or operators when in doubt. The optional `as (label)` names the created hypothesis; otherwise Waterproof generates labels like `_H`, and unnamed hypotheses are best referenced via `By`/`Since` with their *statement*.

### 3.1 Managing the goal

| Sentence | Effect |
|---|---|
| `We need to show that (P).` / `To show that (P).` | Checks the goal is (convertible to) `P`; also converts the displayed goal to your phrasing. Mandatory signposting after case splits. |
| `We conclude that (P).` / `It follows that (P).` | Solves the goal `P` by automation. Accepts a chain `& a ≤ b < c`. |
| `By (lemma_or_hyp) we conclude that (P).` | Same, giving automation an extra fact to use. |
| `Since (Q) we conclude that (P).` | Same, but you cite the *statement* `Q` (must be provable from context). |
| `It suffices to show that (P).` | Backward step: replaces goal by `P` if automation proves `P ⇒ goal` (also `By ... it suffices ...`, `Since ... it suffices ...`). |
| `Indeed, (P).` | Closes a small side-goal (e.g. membership after `Choose`). |

### 3.2 Quantifiers

| Sentence | Effect |
|---|---|
| `Take x ∈ ℝ.` / `Take n : ℕ.` / `Take x, y : ℝ and n : ℕ.` | Introduce ∀-bound variables. Fails on ∃-goals. Warns if you rename bound variables. |
| `Take x : ℝ; such that (P) as (i).` | Introduce variable and immediately assume the bounding hypothesis. |
| `Choose y := (2).` / `Choose (2).` | Provide a witness for ∃. With a bounded ∃ this opens a side-goal (`y ∈ A`, `y > 0`, …) which you close with `{ Indeed, ... . }`. |
| `Obtain such an n.` / `Obtain such n, m.` | Destruct an ∃-hypothesis introduced last (e.g. right after `Assume that`). |
| `Obtain n according to (i).` | Destruct the ∃ in labeled hypothesis `(i)`. |
| `Use ε := (1/2) in (i).` | Specialize a ∀-hypothesis `(i)`; bounded ∀ opens a side-goal (`1/2 > 0`) closed with `{ Indeed, ... . }`. Multiple: `Use x := a, y := b in (i).` |

### 3.3 Assumptions and forward reasoning

| Sentence | Effect |
|---|---|
| `Assume that (P).` / `Assume that (P) as (i).` | Introduce the antecedent of an implication (or ¬). Fails if `P` isn't the actual antecedent. |
| `It holds that (P) as (i).` | Assert `P`, proved by automation. |
| `By (ref) it holds that (P).` / `Since (Q) it holds that (P).` | Assert with an extra fact / cited statement. |
| `We claim that (P) as (i).` | Assert `P` and open a subproof for it (you prove it yourself, typically in a `{ ... }` block or bullet). |
| `Define u := (t).` | Local definition. |
| `Because (i) both (P) as (h1) and (Q) as (h2).` | Destruct a conjunction hypothesis `(i)`. |
| `Because (i) either (P) or (Q).` | Case split on a disjunction hypothesis `(i)`; follow with `- Case (P). ...` bullets. |

### 3.4 Structure: cases, conjunctions, iff, contradiction, induction

```coq
Either x < y or x ≥ y.            (* case split on a decidable comparison *)
- Case x < y.  ...
- Case x ≥ y.  ...

Either x < 0, x = 0 or x > 0.     (* three-way *)

We show both statements.          (* goal A ∧ B; also: We show both (A) and (B). *)
* We need to show that (A). ...
* We need to show that (B). ...

We show both directions.          (* goal A ⇔ B *)
++ We need to show that (A ⇒ B). ...
++ We need to show that (B ⇒ A). ...

We argue by contradiction.
Assume that ¬ (P).
... Contradiction.                (* or ↯ *)

We use induction on k.
+ We first show the base case (P 0). ...
+ We now show the induction step.
  Take k ∈ ℕ. Assume that (P k). ... (* prove P (k+1) *)
```

Bullets (`-`, `+`, `*`, `++`, …) and `{ }` blocks are standard Coq; Waterproof's relaxed bullet mode plus mandatory `We need to show that` / `Case` sentences enforce signposting.

### 3.5 Definitions and help

| Sentence | Effect |
|---|---|
| `Expand the definition of (f).` / `Expand (f).` | Prints suggested `That is, write ...` reformulations of goal/hypotheses with `f` unfolded (registered definitions only). Remove from final proof. |
| `Expand All.` | Suggestions for every registered definition occurring. |
| `Help.` | Prints hints about applicable tactics for the current goal. Remove from final proof. |

---

## 4. A worked example

```coq
Lemma sequence_bound :
  ∀ x ∈ ℝ, (∀ ε > 0, x < ε) ⇒ x ≤ 0.
Proof.
Take x ∈ ℝ.
Assume that ∀ ε > 0, x < ε as (i).
We argue by contradiction.
Assume that ¬ (x ≤ 0).
It holds that x > 0.
Use ε := x in (i).
{ Indeed, x > 0. }
It holds that x < x.
Contradiction.
Qed.
```

And a chain-based conclusion:

```coq
By f_increasing we conclude that & 2 < f(0) ≤ f(1).
```

---

## 5. Common pitfalls

1. **`Take` on an ∃-goal.** `Take` only introduces universally quantified variables; for `∃` use `Choose`. Conversely `Choose` fails on ∀-goals.
2. **Renaming bound variables.** `Take y : ℝ` when the goal reads `∀ x, ...` produces a warning ("Expected variable name x instead of y") — in teaching setups treat warnings as errors. Same for `Obtain such an m` when the binder was `n`.
3. **Wrong types or too many variables in `Take`.** `Take n : bool` on `∀ n : ℕ` fails; so does taking more variables than the goal's quantifier prefix supplies.
4. **Forgetting the side-goal of bounded quantifiers.** `Choose y := 2` for `∃ y ∈ ℝ, ...` leaves a membership goal; close it immediately with `{ Indeed, y ∈ ℝ. }`. Note the required **space between `.` and `}`**. Same after `Use ε := 1/2 in (i)`.
5. **`Assume that` with the wrong statement.** The assumed statement must match the actual antecedent (up to conversion). Also, `Assume` refuses to work when the goal is not an implication/negation.
6. **Automation can't bridge a big gap.** `We conclude that ...` runs a bounded search; if it fails, either (a) insert intermediate `It holds that` steps, (b) supply the key lemma: `By lem we conclude that ...`, or (c) check the right dataset is enabled. `By magic it holds that ...` (i.e. unrestricted search) exists but signals a proof your reader wouldn't accept.
7. **The shield.** With the automation shield on, `It holds that`/`We conclude that` will not instantiate quantifiers or split iffs for you; you must `Use`, `Obtain`, `Choose`, `We show both directions`, etc., explicitly.
8. **Label reuse.** `It holds that (P) as (h)` fails if `h` already names a hypothesis.
9. **Scopes.** With `R_scope` open, natural-number statements need `%nat`: `(k ≤ n(k))%nat`. Off-by-scope errors typically show up as type errors on `≤` or `+`.
10. **Parentheses.** Statements are parsed as `lconstr`; when a sentence misparses, wrap the statement in parentheses: `We conclude that (x + 3 = 3 + x).`
11. **Chains.** `& a < b > c` (mixed directions) is rejected; split it. A chain proves the conjunction of its links — when *using* a chain hypothesis you may need the derived global inequality via `It holds that`.
12. **Case bullets without signposting.** After `Either ... or ...` each bullet must begin `Case (…).`; after `We show both statements/directions`, each bullet must begin with `We need to show that (…).` — omitting these is an error by design.
13. **`Obtain` scope.** `Obtain such an n` only destructs the most recently introduced existential hypothesis; otherwise use `Obtain n according to (label)`.
14. **Leaving `Help.` / `Expand ...` in the final script.** They are interactive aids; remove them (in graded notebooks they may be flagged).

---

## 6. Extending the library

### 6.1 Adding lemmas to the automation

The closing tactics search the hint databases of the enabled dataset. To make your own results available:

```coq
Lemma my_lemma : ∀ x ∈ ℝ, ... .
Proof. ... Qed.

#[export] Hint Resolve my_lemma : wp_reals.   (* or a fresh db, see below *)
(* also useful: Hint Extern <cost> <pattern> => <tactic> : db. *)
```

Cleaner for course material — define your own database and dataset:

```coq
Create HintDb course_db.
#[export] Hint Resolve my_lemma my_other_lemma : course_db.

Waterproof Declare Automation Course.
Waterproof Set Main Databases Course wp_core, real, wp_reals, course_db.
Waterproof Set Decidability Databases Course nocore, wp_decidability_reals.
Waterproof Set Shorten Databases Course wp_core.
Waterproof Enable Automation Course.
```

(`Main` = general closing search; `Decidability` = powering `Either ... or ...`; `Shorten` = used to keep `Since`/`By` justifications minimal.)

Keep hints cheap: prefer `Hint Resolve` over expensive `Hint Extern`; the search is depth-bounded and every hint you add slows every `We conclude that` in the file (the source itself comments that adding `eq_sym` to `wp_core` was too costly).

### 6.2 Registering definitions for `Expand`

```coq
Definition square (x : ℝ) := x^2.

Waterproof Register Expand "square";
  for square;
  as "Definition square".
```

After this, `Expand square.` and `Expand All.` will suggest natural-language reformulations, and in the VS Code UI students can click *replace*. Definitions phrased as characterizations (e.g. `a is a lower bound for A`) should also get supporting lemmas in `wp_definitions` / `wp_alt_chars` so the automation can move between the name and its unfolding.

### 6.3 Custom notation

Ordinary Coq `Notation` works; the library's own style is a good template, e.g.

```coq
Notation "'max(' x , y )" := (Rmax x y) (format "'max(' x ,  y ')'").
Notation "a 'is' 'even'" := (Nat.Even a) (at level 68).
```

For predicate-style phrases (`x is a _lower bound_ for A`) look at `theories/Libs/Analysis/SupAndInf.v` and `Notations/Sets.v` for level conventions (`is`-notations around level 68–70, set operations in `subset_scope`).

### 6.4 Contributing new tactics

Tactics live in `theories/Tactics/*.v` as **Ltac2** notations wrapping Ltac2 functions, with error/feedback helpers from `theories/Util/MessagesToUser.v`; heavy machinery (automation, backtracking search, unfolding framework) is OCaml in `src/`. To add a sentence form: write the Ltac2 function, expose it via `Ltac2 Notation "My" "sentence" x(lconstr) := ...`, export from `theories/Tactics.v`, and add a test file in `tests/tactics/` mirroring the existing ones (`Fail`-based negative tests plus `assert_feedback_with_string` for warnings; enable `Waterproof Enable Redirect Feedback` in tests). Build with `dune build` / `make`; see `Developer-instructions.md`.

---

## 7. Writing exercise notebooks (`.mv`)

A Waterproof notebook is a **markdown file** with fenced `coq` code blocks plus two special HTML-like tags, rendered by the VS Code extension:

- ` ```coq ... ``` ` — read-only checked code (visible).
- `<input-area> ```coq ... ``` </input-area>` — the editable region where students write their proof.
- `<hint title="💡 Hint (click to open/close)"> ... </hint>` — collapsible block; commonly used both for hints and to hide the import preamble.

Skeleton:

````markdown
# Homework 3: Suprema

<hint title="📦 Imports (click to open/close)">
```coq
Require Import Waterproof.Waterproof.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Chains.
Require Import Waterproof.Tactics.
Require Import Waterproof.Automation.
Waterproof Enable Automation RealsAndIntegers.
Open Scope R_scope. Open Scope subset_scope.
Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".
```
</hint>

## Exercise 1
State the exercise in prose here.

```coq
Lemma exercise_1 : ∀ x ∈ ℝ, x + 3 = 3 + x.
Proof.
```
<input-area>
```coq

```
</input-area>
```coq
Qed.
```
````

Design guidelines (taken from the official tutorial's structure):

1. **Example → exercise pairs.** Show a complete worked `Lemma example_...` proof, then a structurally identical `Lemma exercise_...` with an empty input area.
2. **Lock the statement.** Keep `Lemma ... Proof.` and `Qed.` *outside* the input area so students cannot alter what they must prove; only the proof body is editable.
3. **One new sentence form per section**, in the order: `We conclude that` → `We need to show that` → `Take` → `Choose`/`Indeed` → `Assume` → chains → `It suffices` → `It holds` → `Use` → `Obtain` → contradiction → `Either` → `∧`/`⇔` → induction → `Expand`.
4. **Definitions**: introduce them in a visible code block, register them with `Waterproof Register Expand` inside a technical-details `<hint>`, and tell students about `Expand ...`/`Help.` (and to delete those lines).
5. **Autocomplete**: remind students of Ctrl/Cmd+Space, which lists the sentence templates.
6. Test the notebook by completing every input area yourself; the whole file must compile as a Coq document when concatenated (that is exactly how the checker processes it — `tests/test-folder.py` in the repo does the analogue for `.v` tests).

For plain-Coq courses, the same pedagogy works in `.v` files: worked examples followed by `Lemma exercise ... Proof. (* your proof here *) Admitted.`, with `Admitted` to be replaced by a `Qed`-terminated proof.

---

## 8. Quick reference card

```
Take x ∈ ℝ.                     Take n, m : ℕ and b : bool.
Take x : ℝ; such that (P) as (i).
Choose y := (t).                { Indeed, (side condition). }
Assume that (P) as (i).
It holds that (P) as (i).       By (ref) it holds that (P).     Since (Q) it holds that (P).
We claim that (P) as (i).
It suffices to show that (P).   By/Since ... it suffices to show that (P).
We need to show that (P).       To show that (P).
We conclude that (P).           By (ref) we conclude that (P).  It follows that (P).
We conclude that & a < b ≤ c.
Use x := (t) in (i).            Obtain such an x.               Obtain x according to (i).
Because (i) both (P) and (Q).   Because (i) either (P) or (Q).
Either (P) or (Q).   - Case (P). ...   - Case (Q). ...
We show both statements.        We show both (P) and (Q).       We show both directions.
We argue by contradiction.      Contradiction.  (↯)
We use induction on k.          We first show the base case (P). We now show the induction step.
Define u := (t).                Expand the definition of (f).   Expand All.    Help.
```
