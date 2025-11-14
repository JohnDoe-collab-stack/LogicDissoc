# LogicDissoc: Semantic Obstruction and Quantified Incompleteness

This document explains the conceptual architecture of **LogicDissoc**:

1. A general Gödel-style **obstruction index** `A*_Godel` that measures how much a finite extension `S` of a reference theory `Γ_ref` deforms its class of models.
2. An internal **non-locality measure** `delta` packaged in a `RefSystem`, and a derived finite **obstruction rank** `ObstructionRank` that discretizes the behaviour of `delta`.

The goal is to help a reader understand *what is going on and why*, not to give an API or installation guide.

---

## 0. High-level picture

We fix a **reference system**:

```text
(Sentence, Model, Sat, Γ_ref)
````

and look at finite extensions `Γ_ref ∪ S`. The core semantic notion is:

* The extension is **conservative** if it does not change the class of admissible models:

  ```text
  ModE(Γ_ref ∪ S) = ModE(Γ_ref).
  ```

The library attaches to each finite batch `S` a real number

```text
A*_Godel(S) ∈ ℝ
```

such that:

```text
A*_Godel(S) = 0   ⇔   Γ_ref ∪ S is conservative
A*_Godel(S) > 0   ⇔   Γ_ref ∪ S is non-conservative.
```

Moreover, the 0 / >0 verdict does **not** depend on the choice of a certain linear functional; only the numerical scale changes.

Internally, for some frameworks, this obstruction is refined further via a semantic measure

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

which re-encodes the behaviour of `delta` and is then used to classify numerical codes (e.g. cuts and bits).

---

## 1. Foundational viewpoint: reference systems, not absolute foundations

LogicDissoc starts from a simple stance:

* There is no global, all-encompassing “final” theory where everything is decided.
* In practice, we always reason **relative to a reference system**:

  * a background theory (PA, ZFC, a type theory, a piece of QFT, …),
  * a class of admissible models,
  * and an internal notion of truth.

In the library, such a reference system is represented by:

```text
(Sentence, Model, Sat, Γ_ref)
```

* `Γ_ref` is not “all of mathematics”, but a **local reference frame**.
* Finite batches `S` of sentences are **extensions** of this frame.

The central question is:

> What happens semantically to `ModE(Γ_ref)` when we pass to `ModE(Γ_ref ∪ S)`?

From this point of view:

* **Incompleteness is normal**: as soon as `S` really changes the reference system, the extension is non-conservative.
* The index `A*_Godel` is not there to fix incompleteness, but to **measure the obstruction** to conservativity.

---

## Part I – The Gödel-style obstruction index

This part describes the abstract mechanism that builds `A*_Godel`.

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

For a finite `S ⊆ Sentence` (code: `Battery Sentence = Finset Sentence`), the extension is **conservative** if:

```text
ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

This is written:

```text
Cons_S(S) :⇔ ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

All later constructions refer only to `ModE` and `Cons_S`.

---

### 3. Cone of legitimate obstructions (geometric layer)

Fix a finite set `B` of obstruction types.

**Counters.** A counter profile is:

```text
c : B → ℕ
```

i.e. `c ∈ ℕ^B` (code: `GenCounters B`).

**Legitimate obstructions.** A legitimate obstruction on `B` is a map:

```text
F : (B → ℕ) → ℝ
```

such that (as in `ObstructionGen` and `Legit`):

1. **Linearity over ℕ.** There exist `α_b > 0` with

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

This gives a **positive cone** of linear forms on `ℕ^B`:

* changing `L` is a renormalization,
* it does **not** change the geometry of the 0 / >0 frontier.

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

In words:

* The **zero profile** (all coordinates 0) is equivalent to **semantic conservativity**.

Given:

* a semantic framework `S`,
* a legitimate obstruction `L`,
* an admissible `Count`,

define the general index:

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

We now encode **where** non-conservativity happens using Gödel directions.

A **Gödel direction** for framework `S` and alphabet `B` is a predicate:

```text
P : B → Model → Prop
```

such that:

1. **Local decidability.** For all finite `S` and all `b ∈ B`, the statement

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

So Gödel directions are **semantic channels** along which model loss must show up.

From `P`, define the **canonical Gödel counting**:

```text
Count^Godel(S)(b) :=
  1 if ∃ m,
       m ∈ ModE(Γ_ref),
       m ∉ ModE(Γ_ref ∪ S),
       P b m;
  0 otherwise.
```

In Lean: `GodelDirection.CountFromGodel`.

**Admissibility.** One proves:

```text
Count^Godel : Battery Sentence → (B → ℕ)
```

satisfies:

```text
∀ S, (∀ b, Count^Godel(S)(b) = 0)   ⇔   Cons_S(S),
```

i.e. `Count^Godel` is an admissible counting protocol (instance `CountSpec`).

Given a legitimate obstruction `L` and Gödel direction `P`, the **Gödel index** is:

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

2. **Positive boundary**

   ```text
   A*_Godel(S) > 0   ⇔   ¬Cons_S(S).
   ```

3. **Independence of `L`**

   For any two legitimate obstructions `L1`, `L2`:

   ```text
   A*_{Godel}(S; L1) = 0  ⇔  A*_{Godel}(S; L2) = 0
   A*_{Godel}(S; L1) > 0 ⇔  A*_{Godel}(S; L2) > 0
   ```

So:

* The qualitative verdict “0 vs >0” is **independent** of the choice of `L` in the cone.
* Only the numerical scale changes.

In Lean this corresponds to:

* `metaGodel_frontier_zero`,
* `metaGodel_frontier_pos`,
* and lemmas on `LegitObstruction` (`linear_repr`, `zero_iff_all_zero`, `F_nonneg`).

---

### 7. Conceptual hierarchy (summary of Part I)

The abstract mechanism has four layers:

1. **Level 0 – Model theory.**
   `ModE`, `Cons_S` for a framework `S`.

2. **Level 1 – Obstruction cone.**
   Positive linear functionals `L : (B → ℕ) → ℝ` with trivial kernel.

3. **Level 2 – Gödel directions.**
   `P : B → Model → Prop` with decidability and separation, giving canonical `Count^Godel`.

4. **Level 3 – A* index.**
   For each `(S,B,P,L)`, the index

   ```text
   S ↦ A*_Godel(S)
   ```

   detects exactly the conservative extensions (`=0`) and non-conservative ones (`>0`), and provides a numerical measure of obstruction strength.

---

### 8. Finite example: graphs with non-trivial δ (`GraphToy`)

The file:

```text
LogicDissoc/GraphToy.lean
```

implements a fully explicit finite instance:

* `Model  := Graph3` (undirected graphs on 3 labeled vertices),

* `Sentence := GraphSentence` with atoms like `conn`, `tri`, `¬conn`, `¬tri`,

* a concrete `RefSystem`:

  ```lean
  E_graph : RefSystem Graph3 GraphSentence
  ```

  with `delta : Sentence → ℝ` such that:

  * `delta(top) = 0` for the unique everywhere-true local sentence,
  * for every non-local sentence `φ`, `1 ≤ delta φ < 2`,
  * distinct non-local formulas (e.g. `conn`, `¬conn`, `tri`, `¬tri`) get distinct real values.

* a finite type of Gödel directions `GraphDir` with `GraphGodelDirection`,

* a canonical obstruction `GraphDeltaObstruction` built from `delta`,

* a specialized index:

  ```lean
  noncomputable def graphAstar (S : GraphBattery) : ℝ := ...
  ```

`GraphToy` illustrates:

* the **local / non-local** dichotomy via `delta`,
* the **granularity** of `delta` on non-local formulas,
* detection of non-conservativity via Gödel directions,
* the 0 / >0 meta-theorem in a finite, fully proved Lean setting.

---

## Part II – Internal justification of `RefSystem` and obstruction rank

This part explains how the internal layer

* `RefSystem`,
* `delta : Sentence → ℝ`,
* `ObstructionRank`

is *constructed* and why it introduces no extra axioms.

### 9. Guiding idea

The main idea is:

1. Start from a **concrete system** with models, sentences, satisfaction, closure, and a function `delta`.
2. Prove in this concrete system the key properties of `delta` (locality, non-locality, band `[1,2)`, etc.).
3. Abstract these data into a generic structure `RefSystem`.
4. From there, define a finite type `ObstructionRank` that only **recodes** information already contained in `delta`.

Nothing is postulated for free:

* the rank is not assumed; it is *derived* from a trichotomy of `delta`.

---

### 10. Step 1 – Concrete construction of `delta`

In a concrete file (e.g. `DeltaConstruction.lean` / `BasicSemantics.lean`), we have:

* a type `Model`,
* a type `Sentence`,
* a relation `Sat : Model → Sentence → Prop`,
* a closure operator `CloE : Set Sentence → Set Sentence` (theory closure),
* a function

  ```lean
  delta : Sentence → ℝ
  ```

  constructed explicitly (e.g. on a finite universe, or from a canonical measure).

On this concrete system, one proves (by construction, not by axiom):

* `delta_eq_zero_iff_mem_closure`:

  ```text
  delta φ = 0   ⇔   φ ∈ CloE ∅.
  ```

* `nonmem_closure_iff_delta_band`:

  ```text
  φ ∉ CloE ∅   ⇔   1 ≤ delta φ ∧ delta φ < 2.
  ```

Define:

```lean
isLocal    φ := φ ∈ CloE ∅
isNonlocal φ := ¬ isLocal φ
```

Then prove:

* `isLocal φ     ⇔ delta φ = 0`,
* `isNonlocal φ  ⇔ 1 ≤ delta φ ∧ delta φ < 2`.

At this stage:

* `delta = 0` **exactly** characterizes local sentences,
* the band `[1,2)` characterizes controlled non-local sentences,
* and this entire package is fully **concrete** and exhibited in Lean.

---

### 11. Step 2 – Abstraction as `RefSystem`

Once the concrete construction is in place, we abstract it into:

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

* `delta_eq_zero_iff_mem_closure` and `nonlocal_iff_delta_band` are **theorems** from Step 1, now recorded as fields.
* `RefSystem` is **known to be inhabited** (non-empty) because of the explicit concrete construction.

At the abstract level, define:

```lean
def isLocal    (E : RefSystem Model Sentence) (φ : Sentence) :=
  φ ∈ E.CloE ∅

def isNonlocal (E : RefSystem Model Sentence) (φ : Sentence) :=
  ¬ isLocal E φ
```

Using the structure fields, prove:

* `isLocal_iff_delta_zero`:

  ```text
  E.isLocal φ   ⇔   E.delta φ = 0.
  ```

* `isNonlocal_iff_delta_band`:

  ```text
  E.isNonlocal φ   ⇔   1 ≤ E.delta φ ∧ E.delta φ < 2.
  ```

So `RefSystem` is not a bag of axioms; it is an abstraction of an explicitly constructed instance.

---

### 12. Step 3 – Trichotomy of `delta` (justifying the rank)

From any `RefSystem E`, we already know:

* `φ` local ⇒ `E.delta φ = 0`,
* `φ` non-local ⇒ `1 ≤ E.delta φ < 2`.

We now refine this using classical logic (LEM) for reals:

* either `E.delta φ = 1`,
* or `E.delta φ ≠ 1`.

Combining both, we prove a lemma `delta_trichotomy`:

> For every sentence `φ`, exactly one of the three cases holds:
>
> 1. `E.delta φ = 0`
> 2. `E.delta φ = 1`
> 3. `E.delta φ ≠ 0` and `E.delta φ ≠ 1`.

This is a **pure theorem** based on:

* the concrete properties of `delta` encoded in `RefSystem`,
* classical logic in Lean.

We are not postulating a rank here; we are proving a **three-way decomposition** of the real value `E.delta φ`.

---

### 13. Step 4 – Definition of `ObstructionRank` (TriRank)

Given the trichotomy, it is natural to define a finite type:

```lean
inductive ObstructionRank
| local      -- delta = 0
| ilm        -- delta = 1
| transcend  -- delta ≠ 0, 1
deriving DecidableEq
```

Define the rank function:

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

Then prove the specification lemma:

```lean
lemma obstructionRank_spec
    (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)] :
  (obstructionRank E φ = ObstructionRank.local ∧ E.delta φ = 0)
  ∨ (obstructionRank E φ = ObstructionRank.ilm ∧ E.delta φ = 1)
  ∨ (obstructionRank E φ = ObstructionRank.transcend
      ∧ E.delta φ ≠ 0 ∧ E.delta φ ≠ 1)
```

This states precisely:

* `obstructionRank E φ` introduces **no new information** beyond `E.delta φ`,
* it simply classifies `E.delta φ` into the three cases given by `delta_trichotomy`.

So the obstruction rank is a **discrete summary** of the continuous invariant `delta`.

---

### 14. Step 5 – Classification of numerical codes

The rank is then used to classify **families of sentences** that encode numerical objects.

Typical shapes:

* `Cut : ℚ → Code → Sentence`  (cuts),
* `Bit : ℕ → ℕ → Code → Sentence`  (bits).

Define:

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
* and the previously established lemmas.

---

### 15. Step 6 – Synthesis of the internal layer

Putting everything together:

1. A **concrete model** is built, with `delta` and proofs of its locality / non-locality behaviour.
2. An abstract `RefSystem` bundles these properties, preserving the guarantee of existence.
3. A **trichotomy** of `delta` is proved inside `RefSystem`.
4. A finite type `ObstructionRank` is defined, recoding this trichotomy.
5. Rank-based definitions are given for families of sentences (cuts, bits, …), relying only on these bricks.

Conclusion:

* The obstruction rank is **proved**, not assumed.
* It is derived from `delta` inside `RefSystem`.
* And `RefSystem` itself is justified by an **explicit construction** upstream.

---

## 16. License

This project is licensed under the **GNU Affero General Public License version 3.0 only (AGPL-3.0-only)**.

Any modified or derived version made accessible to third parties, including via online services, must be provided under the same license, with corresponding source code.

For details, see:
[https://www.gnu.org/licenses/agpl-3.0.html](https://www.gnu.org/licenses/agpl-3.0.html)
