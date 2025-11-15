Here is the English version.

---

# LogicDissoc: Semantic obstruction and quantified incompleteness

This document explains the conceptual architecture of **LogicDissoc**:

1. A **Gödel obstruction index** `A*_Godel` which measures how much a finite extension `S` of a reference theory `Γ_ref` deforms its class of models.
2. A **measure of semantic non-locality** `delta` encapsulated in a `RefSystem`, and a finite **obstruction rank** `ObstructionRank` which discretizes the behavior of `delta`.

The goal is to help the reader understand *what is going on and why*, not to provide an API or installation guide.

---

## 0. Overview

We fix a **reference system**:

```text
(Sentence, Model, Sat, Γ_ref)
```

and look at finite extensions `Γ_ref ∪ S`. The central semantic notion is:

* The extension is **conservative** if it does not change the class of admissible models:

  ```text
  ModE(Γ_ref ∪ S) = ModE(Γ_ref).
  ```

The library associates to each finite package `S` a real number

```text
A*_Godel(S) ∈ ℝ
```

such that:

```text
A*_Godel(S) = 0   ⇔   Γ_ref ∪ S is a conservative extension
A*_Godel(S) > 0   ⇔   Γ_ref ∪ S is semantically non-conservative.
```

Moreover, the cut `0 / >0` does **not** depend on the choice of a certain linear functional; only the numerical scale changes.

Internally, for certain frameworks, this obstruction is refined via a semantic measure

```text
delta : Sentence → ℝ
```

and a finite **obstruction rank**:

```lean
inductive ObstructionRank
| local      -- delta = 0
| ilm        -- delta = 1
| transcend  -- delta ≠ 0, 1
```

which re-encodes the behavior of `delta` and is then used to classify numerical codes (cuts, bits, etc.).

---

## 1. Foundational viewpoint: reference systems, not absolute foundations

LogicDissoc starts from a simple observation:

* There is no global final theory in which everything is decided.
* In practice, one always reasons **relative to a reference system**:

  * a background theory (PA, ZFC, a type system, a fragment of QFT, …),
  * a class of admissible models,
  * a notion of internal truth.

In the library, such a reference system is represented by:

```text
(Sentence, Model, Sat, Γ_ref)
```

* `Γ_ref` is not “all of mathematics”, but a **local frame of reference**.
* Finite bundles `S` of sentences are **extensions** of this frame.

The central question becomes:

> What happens to `ModE(Γ_ref)` when we pass to `ModE(Γ_ref ∪ S)`?

In this setting:

* **Incompleteness is normal**: as soon as `S` really changes the reference system, the extension is no longer conservative.
* The index `A*_Godel` is not meant to fix incompleteness, but to **measure the obstruction** to conservativity.

---

## First part – The Gödel obstruction index

This part describes the abstract mechanism which constructs `A*_Godel`.

### 2. Basic semantic framework

A **semantic framework** consists of:

* `Sentence` : type of formulas,
* `Model`    : type of models,
* `Sat : Model → Sentence → Prop` : satisfaction,
* `Γ_ref : Set Sentence`          : reference theory.

For `Γ ⊆ Sentence`, define:

```text
ModE(Γ) := { M : Model | ∀ φ ∈ Γ, Sat M φ }.
```

For finite `S ⊆ Sentence` (code: `Battery Sentence = Finset Sentence`), the extension is **conservative** if:

```text
ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

We denote this property by:

```text
Cons_S(S) :⇔ ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

All subsequent constructions depend only on `ModE` and `Cons_S`.

---

### 3. Cone of legitimate obstructions (geometric layer)

Fix a finite set `B` of **obstruction types**.

**Counter profiles.** A profile is a function

```text
c : B → ℕ
```

that is, an element of `ℕ^B` (code: `GenCounters B`).

**Legitimate obstructions.** A legitimate obstruction on `B` is a map

```text
F : (B → ℕ) → ℝ
```

such that (as in `ObstructionGen` and `Legit`):

1. **Linearity over ℕ.** There exist coefficients `α_b > 0` such that

   ```text
   F(c) = ∑_{b ∈ B} α_b · c(b).
   ```

2. **Non-negativity.**

   ```text
   ∀ c, F(c) ≥ 0.
   ```

3. **Trivial kernel.**

   ```text
   F(c) = 0   ⇔   ∀ b, c(b) = 0.
   ```

In Lean:

```lean
LegitObstruction B
```

with functional `L.O.F`.

We obtain a **positive cone** of linear forms on `ℕ^B`:

* changing `L` renormalizes the index,
* without changing the geometry of the boundary `0 / >0`.

---

### 4. Admissible counting schemes

A **counting protocol** for the framework is a map:

```text
Count : { finite S ⊆ Sentence } → (B → ℕ).
```

It is **admissible** (class `CountSpec`) if:

```text
∀ S, (∀ b, Count(S)(b) = 0)   ⇔   Cons_S(S).
```

In other words:

* the **zero profile** (all coefficients zero) is equivalent to **semantic conservativity**.

Given:

* a semantic framework `S`,
* a legitimate obstruction `L`,
* an admissible protocol `Count`,

we define the general index:

```text
A*_{S,L,Count}(S) := F(Count(S)) ∈ ℝ,
```

with `F = L.O.F`.

In Lean:

```lean
AstarGen (Sat := Sat) (Γ_ref := Γ_ref)
         (L := L) (Count := Count) S
```

---

### 5. Gödel directions (dynamic layer)

We now encode **where** non-conservativity appears via Gödel directions.

A **Gödel direction** for the framework `S` and alphabet `B` is a predicate

```text
P : B → Model → Prop
```

such that:

1. **Local decidability.** For every finite `S` and every `b ∈ B`, the statement

   ```text
   ∃ m,
     m ∈ ModE(Γ_ref) ∧
     m ∉ ModE(Γ_ref ∪ S) ∧
     P b m
   ```

   is decidable. (Field `dec` in `GodelDirection`.)

2. **Separation.** For all finite `S`:

   ```text
   ¬Cons_S(S)
   → ∃ b m,
       m ∈ ModE(Γ_ref) ∧
       m ∉ ModE(Γ_ref ∪ S) ∧
       P b m.
   ```

   (Field `separating`.)

Gödel directions are therefore **semantic channels** along which model loss must show up.

From `P`, we define the canonical **Gödel counting**:

```text
Count^Godel(S)(b) :=
  1 if ∃ m,
       m ∈ ModE(Γ_ref),
       m ∉ ModE(Γ_ref ∪ S),
       P b m ;
  0 otherwise.
```

In Lean: `GodelDirection.CountFromGodel`.

**Admissibility.** One shows that

```text
Count^Godel : Battery Sentence → (B → ℕ)
```

satisfies:

```text
∀ S, (∀ b, Count^Godel(S)(b) = 0)   ⇔   Cons_S(S),
```

so `Count^Godel` is an admissible protocol (instance `CountSpec`).

Given a legitimate obstruction `L` and a Gödel direction `P`, we define the **Gödel index**:

```text
A*_Godel(S) := F(Count^Godel(S)).
```

In Lean: `Astar_Godel`.

---

### 6. Meta-theorem: quantitative alignment of incompleteness

Given:

* a semantic framework `S = (Sentence, Model, Sat, Γ_ref)`,
* a finite set `B`,
* a legitimate obstruction `L`,
* a Gödel direction `P`,

then for every finite `S`:

1. **Zero boundary**

   ```text
   A*_Godel(S) = 0   ⇔   Cons_S(S).
   ```

2. **Strictly positive boundary**

   ```text
   A*_Godel(S) > 0   ⇔   ¬Cons_S(S).
   ```

3. **Independence of `L`**

   For two legitimate obstructions `L1`, `L2`:

   ```text
   A*_{Godel}(S; L1) = 0  ⇔  A*_{Godel}(S; L2) = 0
   A*_{Godel}(S; L1) > 0 ⇔  A*_{Godel}(S; L2) > 0
   ```

Thus:

* the qualitative verdict “0 vs >0” is **independent** of the choice of `L` in the cone,
* only the numerical scale changes.

In Lean: `metaGodel_frontier_zero`, `metaGodel_frontier_pos`, and lemmas on `LegitObstruction` (`linear_repr`, `zero_iff_all_zero`, `F_nonneg`).

---

### 7. Conceptual hierarchy (summary of the first part)

The abstract mechanism has four layers:

1. **Level 0 – Model theory.**
   `ModE`, `Cons_S` for a framework `S`.

2. **Level 1 – Cone of obstructions.**
   Positive linear forms `L : (B → ℕ) → ℝ` with trivial kernel.

3. **Level 2 – Gödel directions.**
   `P : B → Model → Prop` with decidability and separation, yielding `Count^Godel`.

4. **Level 3 – Index A*.**
   For each `(S,B,P,L)`, the index

   ```text
   S ↦ A*_Godel(S)
   ```

   detects exactly the conservative extensions (`=0`) and non-conservative ones (`>0`), and provides a numerical measure of the obstruction’s intensity.

---

### 8. Finite example: graphs and nontrivial δ (`GraphToy`)

The file

```text
LogicDissoc/GraphToy.lean
```

provides an explicit finite instance:

* `Model  := Graph3` (undirected graphs on 3 labeled vertices),

* `Sentence := GraphSentence` with atoms `conn`, `tri`, `¬conn`, `¬tri`,

* a concrete `RefSystem`:

  ```lean
  E_graph : RefSystem Graph3 GraphSentence
  ```

  with `delta : Sentence → ℝ` such that:

  * `delta(top) = 0` for the unique local sentence that is true in every model,
  * for every non-local sentence `φ`, `1 ≤ delta φ < 2`,
  * distinct non-local formulas (`conn`, `¬conn`, `tri`, `¬tri`) have distinct real values.

* a finite type of Gödel directions `GraphDir` with `GraphGodelDirection`,

* a canonical obstruction `GraphDeltaObstruction` built from `delta`,

* a specialized index:

  ```lean
  noncomputable def graphAstar (S : GraphBattery) : ℝ := ...
  ```

`GraphToy` illustrates:

* the **local / non-local** dichotomy via `delta`,
* the **granularity** of `delta` on non-local formulas,
* the detection of non-conservativity via Gödel directions,
* the 0 / >0 meta-theorem in a finite framework fully proved in Lean.

---

## Second part – Internal justification of `RefSystem` and the obstruction rank

This part explains how the internal layer

* `RefSystem`,
* `delta : Sentence → ℝ`,
* `ObstructionRank`

is *constructed* and why it does not introduce new axioms.

### 9. Guiding idea

The main idea is:

1. First construct a **concrete system** (models, sentences, satisfaction, closure, `delta`).
2. Prove in this concrete system the key properties of `delta` (locality, non-locality, band `[1,2)`, etc.).
3. Abstract these data into a generic structure `RefSystem`.
4. From there, define a finite rank type (`ObstructionRank`) which merely **re-encodes** the information already contained in `delta`.

Nothing is postulated for free:

* the rank is not assumed; it is derived from a trichotomy of `delta`.

---

### 10. Step 1 – Concrete construction of `delta`

In a concrete file (`DeltaConstruction.lean` / `BasicSemantics.lean`), we have:

* a type `Model`,
* a type `Sentence`,
* a relation `Sat : Model → Sentence → Prop`,
* a closure operator `CloE : Set Sentence → Set Sentence` (theory closure),
* a function

  ```lean
  delta : Sentence → ℝ
  ```

  constructed explicitly (for example on a finite universe, or from a canonical measure).

On this concrete system, we prove (by construction, not as axioms):

* `delta_eq_zero_iff_mem_closure`:

  ```text
  delta φ = 0   ⇔   φ ∈ CloE ∅.
  ```

* a band lemma for non-members of the closure, of the form:

  ```text
  φ ∉ CloE ∅   ⇔   1 ≤ delta φ ∧ delta φ < 2.
  ```

We then define:

```lean
isLocal    φ := φ ∈ CloE ∅
isNonlocal φ := ¬ isLocal φ
```

and prove:

* `isLocal φ     ⇔ delta φ = 0`,
* `isNonlocal φ  ⇔ 1 ≤ delta φ ∧ delta φ < 2`.

At this stage:

* `delta = 0` characterizes **exactly** the local sentences,
* the band `[1,2)` characterizes the controlled non-local sentences,
* and all this is **explicitly** exhibited in Lean.

---

### 11. Step 2 – Abstraction into `RefSystem`

Once the concrete construction is established, we abstract it as:

```lean
structure RefSystem (Model Sentence : Type _) :=
  (Sat   : Model → Sentence → Prop)
  (CloE  : Set Sentence → Set Sentence)
  (delta : Sentence → ℝ)
  (delta_eq_zero_iff_mem_closure :
      ∀ φ, delta φ = 0 ↔ φ ∈ CloE ∅)
  (nonlocal_iff_delta_band :
      ∀ φ, isNonlocal φ ↔ 1 ≤ delta φ ∧ delta φ < 2)
  -- etc.
```

Here:

* `delta_eq_zero_iff_mem_closure` and `nonlocal_iff_delta_band` are **theorems** from Step 1, now stored as fields.
* We know that `RefSystem` is **inhabited** thanks to the explicit construction.

At the abstract level, we define:

```lean
def isLocal    (E : RefSystem Model Sentence) (φ : Sentence) :=
  φ ∈ E.CloE ∅

def isNonlocal (E : RefSystem Model Sentence) (φ : Sentence) :=
  ¬ isLocal E φ
```

And we prove in `Rank.lean`:

* `isLocal_iff_delta_zero`:

  ```text
  E.isLocal φ   ⇔   E.delta φ = 0.
  ```

* `isNonlocal_iff_delta_band`:

  ```text
  E.isNonlocal φ   ⇔   1 ≤ E.delta φ ∧ E.delta φ < 2.
  ```

So `RefSystem` is not a bundle of axioms, but the abstraction of an explicitly constructed instance.

---

### 12. Step 3 – Trichotomy of `delta` (justifying the rank)

For any `RefSystem E`, we already know:

* local `φ` ⇒ `E.delta φ = 0`,
* non-local `φ` ⇒ `1 ≤ E.delta φ < 2`.

We then refine the non-local case using classical logic (LEM) for reals:

* either `E.delta φ = 1`,
* or `E.delta φ ≠ 1`.

Combining these cases, we obtain a lemma `delta_trichotomy`:

> For every sentence `φ`, exactly one of the following three cases holds:
>
> 1. `E.delta φ = 0`
> 2. `E.delta φ = 1`
> 3. `E.delta φ ≠ 0` and `E.delta φ ≠ 1`.

This is a **pure theorem**, based on:

* the concrete properties of `delta` encapsulated in `RefSystem`,
* classical logic in Lean.

We do not postulate any rank here; we prove a three-way decomposition of `E.delta φ`.

---

### 13. Step 4 – Definition of `ObstructionRank` (TriRank)

Given the trichotomy, we introduce the finite type:

```lean
inductive ObstructionRank
| local      -- delta = 0
| ilm        -- delta = 1
| transcend  -- delta ≠ 0, 1
deriving DecidableEq
```

Then the rank function:

```lean
def obstructionRank (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)] :
  ObstructionRank :=
  if h0 : E.delta φ = 0 then
    ObstructionRank.local
  else if h1 : E.delta φ = 1 then
    ObstructionRank.ilm
  else
    ObstructionRank.transcend
```

And the specification lemma:

```lean
lemma obstructionRank_spec
    (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)] :
  (obstructionRank E φ = ObstructionRank.local ∧ E.delta φ = 0)
  ∨ (obstructionRank E φ = ObstructionRank.ilm ∧ E.delta φ = 1)
  ∨ (obstructionRank E φ = ObstructionRank.transcend
      ∧ E.delta φ ≠ 0 ∧ E.delta φ ≠ 1)
```

This lemma says exactly that:

* `obstructionRank E φ` adds **no new information** to `E.delta φ`,
* it simply **classifies** the value of `delta` according to the trichotomy.

The obstruction rank is therefore a **discrete summary** of the continuous invariant `delta`.

---

### 14. Step 5 – Classification of numerical codes

The rank is then applied to **families of sentences** that code numerical objects.

Typical forms:

* `Code` : type of numerical codes,
* `Cut : ℚ → Code → Sentence`  (rational cuts),
* `Bit : ℕ → ℕ → Code → Sentence` (dyadic bits).

We define:

```lean
cutRank E Cut x q :=
  obstructionRank E (Cut q x)

bitRank E Bit x n a :=
  obstructionRank E (Bit n a x)
```

And properties such as:

```lean
codeIsCutLocal E Cut x :=
  ∀ q, cutRank E Cut x q = ObstructionRank.local

codeHasTranscendentBits E Bit x :=
  ∃ n a, bitRank E Bit x n a = ObstructionRank.transcend
```

These are:

* purely **derived** notions,
* built on `RefSystem`, `delta`, `obstructionRank`,
* and the lemmas already proved in `Rank.lean`.

In this way, for a code `x : Code`, we can express properties such as:

* “all rational cuts of `x` are local” (`codeIsCutLocal`),
* “`x` has at least one dyadic bit of transcend rank” (`codeHasTranscendentBits`).

In particular, in `LogicDissoc/Omega.lean` (§15), we are interested in codes `x` for which **all** cuts are of rank `ilm` and **all** dyadic bits are of rank `transcend`.

---

### 15. Ω-type codes (Omega.lean)

The definitions of `cutRank` and `bitRank` allow us to classify *every* code
`x : Code` in terms of obstruction (local, `ilm`, transcend). To capture
abstractly a Chaitin-Ω-type code, we do not add a global constant
`Omega : Code` nor axioms in `Rank.lean`.

Instead, the file

```text
LogicDissoc/Omega.lean
```

introduces a parameterized specification:

```lean
namespace LogicDissoc.Omega

structure Spec
    {Model Sentence Code : Type _}
    (E   : RefSystem Model Sentence)
    (Cut : ℚ → Code → Sentence)
    (Bit : ℕ → ℕ → Code → Sentence)
    (x   : Code) : Prop :=
  (cuts_are_ilm :
     ∀ q : ℚ,
       E.delta (Cut q x) ≠ 0 ∧ E.delta (Cut q x) = 1)
  (bits_are_transcend :
     ∀ n a : ℕ,
       E.delta (Bit n a x) ≠ 0 ∧ E.delta (Bit n a x) ≠ 1)
```

In other words, `Spec E Cut Bit x` says that the code `x` is obstructionally
of Ω-type:

* all its rational cuts `Cut q x` are of rank `ilm`,
* all its dyadic bits `Bit n a x` are of rank `transcend`,

in the sense of `ObstructionRank` defined in `Rank.lean`.

From this specification, `Omega.lean` proves that, for every `x` and every proof
`hΩ : Spec E Cut Bit x`, we have:

```lean
open LogicDissoc.Omega

lemma omega_cutRank_is_ilm
    (hΩ : Spec E Cut Bit x)
    [∀ q, Decidable (E.delta (Cut q x) = 0)]
    [∀ q, Decidable (E.delta (Cut q x) = 1)] :
  ∀ q : ℚ,
    cutRank E Cut x q = ObstructionRank.ilm

lemma omega_bitRank_is_transcend
    (hΩ : Spec E Cut Bit x)
    [∀ n a, Decidable (E.delta (Bit n a x) = 0)]
    [∀ n a, Decidable (E.delta (Bit n a x) = 1)] :
  ∀ n a : ℕ,
    bitRank E Bit x n a = ObstructionRank.transcend
```

These lemmas only exploit the structure of `Spec` and the general lemmas in
`Rank.lean` (`obstructionRank_ilm_of_delta_eq_one`,
`obstructionRank_transcend_of_delta_ne`). They add no axiom: `Spec` is a purely
propositional property of a code `x`, expressed in the language of `RefSystem`.

The file `Rank.lean` thus remains purely general (it does not mention Ω);
all the “Chaitin-type” logic is isolated in `Omega.lean`, at the level
of `Prop`, without `noncomputable` or additional global constants.

The future connection with **halting** (via `Rev.lean`) will consist, as a third
step, in exhibiting concrete codes `x` satisfying `Spec E Cut Bit x`
from a Chaitin-Ω-type construction. This step will be done in a separate file
(for example `OmegaViaHalting.lean`), reusing the abstract halting theory
developed in `Rev.lean`.

---

### 16. Step 6 – Synthesis of the internal layer

In summary:

1. A **concrete model** is built with `delta` and proofs of its behavior (locality / non-locality).
2. These properties are encapsulated in an abstraction `RefSystem`, preserving the guarantee of existence.
3. A **trichotomy** for `delta` is proved.
4. A finite type `ObstructionRank` is defined to re-encode this trichotomy.
5. Rank-based definitions are then introduced for families of sentences (cuts, bits, etc.), solely from these building blocks.
6. Optionally, finer specifications such as `Omega.Spec` are isolated to describe Ω-type codes, without modifying `Rank.lean` or adding axioms.

Conclusion:

* the obstruction rank is **proved**, not postulated,
* it is derived from `delta` inside `RefSystem`,
* `RefSystem` itself is justified by an explicit **prior construction**,
* Ω-type constructions are formulated as properties (`Spec`) on top of this layer, not as additional non-computable global constants.

---

## 17. License

This project is distributed under the **GNU Affero General Public License version 3.0 only (AGPL-3.0-only)**.

Any modified or derived version made accessible to third parties, including via an online service, must be distributed under the same license, together with the corresponding source code.

For more details:
[https://www.gnu.org/licenses/agpl-3.0.html](https://www.gnu.org/licenses/agpl-3.0.html)
