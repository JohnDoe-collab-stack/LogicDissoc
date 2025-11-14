# LogicDissoc: Semantic Obstruction and Quantified Incompleteness

### TL;DR

This library builds a general “Gödel-style” obstruction index \(A^*\) on top of:

- a **semantic framework** (models, satisfaction, conservativity),
- a **cone of positive linear obstructions** on \(\mathbb{N}^B\),
- **Gödel directions** detecting which models are lost when extending a theory.

For any admissible setup (PA, ZF/ZFC, QFT, etc.), the induced index A*_Godel(S) satisfies:

- A*_Godel(S) = 0 iff the extension Gamma_ref ∪ S is conservative,
- A*_Godel(S) > 0 iff the extension is semantically non-conservative.


with the **0 / >0 verdict independent** of the particular obstruction functional, and the **numeric value** quantifying the “strength” of the obstruction / incompleteness.

A fully worked finite example is in  
`LogicDissoc/GraphToy.lean` (graphs on 3 vertices, non-trivial δ distinguishing formulas like `conn`, `¬conn`, `tri`, and a concrete \(A^*\)).

---

## 1. Basic semantic framework

**Definition 1 (Semantic framework).**  
A semantic framework consists of:

- `Sentence` : a set of formulas,
- `Model`    : a set of models,
- `Sat : Model → Sentence → Prop` : a satisfaction relation,
- `Γ_ref : Set Sentence`          : a reference theory.

For a theory `Γ ⊆ Sentence`, define its class of models by

```text
ModE(Γ) := { M ∈ Model | for all φ in Γ, Sat M φ }.
````

For a finite batch `S ⊆ Sentence` (in the code: `Battery Sentence = Finset Sentence`), the extension of `Γ_ref` by `S` is **conservative** if

```text
ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

Write this property as

```text
Cons_S(S) :⇔ ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

All subsequent constructions are phrased purely in terms of `ModE` and `Cons_S`.

---

## 2. Cone of legitimate obstructions (geometric layer)

Fix a finite set `B` of obstruction types.

**Definition 2 (Counters).**
A counter profile is a function

```text
c : B → ℕ
```

i.e. an element of (\mathbb{N}^B) (in the code: `GenCounters B`).

**Definition 3 (Legitimate obstruction).**
A legitimate obstruction on `B` is a map

```text
F : (B → ℕ) → ℝ
```

satisfying (as in `ObstructionGen` and `Legit`):

1. **Linearity over ℕ.** There exist coefficients `α_b > 0` such that

   ```text
   F(c) = sum over b in B of (α_b * c(b)).
   ```

2. **Non-negativity.** For every profile `c`,

   ```text
   F(c) ≥ 0.
   ```

3. **Trivial kernel.** One has

   ```text
   F(c) = 0   ⇔   for all b, c(b) = 0.
   ```

In the code, such objects are packaged as `LegitObstruction B`, with the functional denoted `L.O.F`.

This defines a **positive cone of linear functionals** on (\mathbb{N}^B): changing `L` amounts to a renormalization, not a change of 0/>0 geometry.

---

## 3. Admissible counting scheme

Everything remains purely semantic: counting is defined via model classes and conservativity.

**Definition 4 (Admissible counting protocol).**
A counting protocol for the framework `S` is a map

```text
Count : { finite batches S ⊆ Sentence } → (B → ℕ).
```

The protocol `Count` is **admissible** (class `CountSpec`) if

```text
for all S,  (for all b, Count(S)(b) = 0)   ⇔   Cons_S(S).
```

In words: the **zero profile** (all components zero) is equivalent to **semantic conservativity**.

**Definition 5 (General A* index).**
Given a semantic framework `S`, a legitimate obstruction `L`, and an admissible `Count`, define

```text
A*_{S,L,Count}(S) := F(Count(S)) ∈ ℝ,
```

where `F = L.O.F`.

In the code:

```lean
AstarGen (Sat := Sat) (Γ_ref := Γ_ref)
         (L := L) (Count := Count) S
```

---

## 4. Gödel directions (dynamic layer)

The “dynamic” part enters through semantic directions that detect which models are lost when extending the theory.

**Definition 6 (Gödel direction).**
A Gödel direction for a framework `S` and an alphabet `B` is a predicate

```text
P : B → Model → Prop
```

such that:

1. **Local decidability.** For every finite batch `S` and every `b ∈ B`, the following statement is decidable:

   ```text
   there exists m such that
     m ∈ ModE(Γ_ref),
     m ∉ ModE(Γ_ref ∪ S),
     and P b m holds.
   ```

   (Field `dec` in `GodelDirection`.)

2. **Separation.** For every finite batch `S`,

   ```text
   not Cons_S(S)
   implies
   there exist b and m such that
     m ∈ ModE(Γ_ref),
     m ∉ ModE(Γ_ref ∪ S),
     and P b m holds.
   ```

   (Field `separating`.)

These directions are semantic “channels” along which non-conservativity must manifest.

Based on `P`, one defines a canonical counting scheme.

**Definition 7 (Gödel counting).**
The counting protocol induced by `P` is

```text
Count^Godel(S)(b) :=
  1 if there exists m with
      m ∈ ModE(Γ_ref),
      m ∉ ModE(Γ_ref ∪ S),
      and P b m;
  0 otherwise.
```

In the code: `GodelDirection.CountFromGodel`.

**Proposition 7 (Admissibility of Gödel counting).**
For every framework `S` and every Gödel direction `P`, the protocol

```text
Count^Godel : Battery Sentence → (B → ℕ)
```

satisfies the admissibility condition (Definition 4):

```text
for all S,  (for all b, Count^Godel(S)(b) = 0)   ⇔   Cons_S(S).
```

This is exactly the `CountSpec` instance proved for `CountFromGodel`.

Consequently, one can specialize the index.

**Definition 8 (A*_Godel index).**
For a legitimate obstruction `L` and a Gödel direction `P`, define

```text
A*_Godel(S) := F(Count^Godel(S)).
```

In the code: `Astar_Godel`.

---

## 5. Meta-theorem: quantitative alignment of incompleteness

**Theorem 9 (Quantitative alignment of incompleteness).**
Let

* a semantic framework `S = (Sentence, Model, Sat, Γ_ref)`,
* a finite set `B`,
* a legitimate obstruction `L` on `B`,
* a Gödel direction `P` for `S` and `B`.

Then for every finite batch `S` of sentences:

1. **Zero boundary**

   ```text
   A*_Godel(S) = 0   ⇔   Cons_S(S).
   ```

   The index is zero exactly on conservative extensions of `Γ_ref`.

2. **Strictly positive boundary**

   ```text
   A*_Godel(S) > 0   ⇔   not Cons_S(S).
   ```

   Every non-conservative extension is detected and strictly separated from 0 by (A^*_{\mathrm{Gödel}}).

3. **Independence from the choice of L**

   If `L1` and `L2` are two legitimate obstructions on the same `B`, then for all `S`:

   ```text
   A*_{Godel}(S; L1) = 0  ⇔  A*_{Godel}(S; L2) = 0,
   A*_{Godel}(S; L1) > 0 ⇔  A*_{Godel}(S; L2) > 0.
   ```

   The qualitative verdict “0 / > 0” does not depend on which linear functional is chosen in the cone of legitimate obstructions. Only the **numerical value** changes (renormalization of the obstruction).

In the Lean code, this corresponds to:

* `metaGodel_frontier_zero` and `metaGodel_frontier_pos` (section `MetaGodel`),
* the `CountSpec` instance for `GodelDirection.CountFromGodel`,
* and the basic lemmas on `LegitObstruction` (`linear_repr`, `zero_iff_all_zero`, `F_nonneg`).

---

## 6. Conceptual hierarchy

The conceptual structure can be summarized as a four-level hierarchy:

1. **Level 0 – Model theory (semantic structure).**
   Framework `S`: definitions of `ModE`, `Cons_S`, conservativity, independent of any specific syntax or proof system.

2. **Level 1 – Obstruction cone (geometry on (\mathbb{N}^B)).**
   Legitimate obstructions `L`: positive linear functionals on (\mathbb{N}^B) with trivial kernel. This is the geometric layer (a positive cone of “obstruction forms”).

3. **Level 2 – Gödel directions (semantic dynamics).**
   Directions `P`: predicates on models that detect which parts of `ModE(Γ_ref)` disappear when adding `S`.
   The canonical counting `Count^Godel` turns these semantic events into profiles in `B → ℕ`.

4. **Level 3 – Index and semantic quantification of incompleteness.**
   For every combination `(S, B, P, L)` satisfying the axioms, the index

   ```text
   S ↦ A*_Godel(S)
   ```

   provides:

   * an invariant qualitative verdict: `0` if and only if the extension is conservative, `> 0` otherwise;
   * a real-valued quantitative measure of “obstruction size” along the chosen directions.

This is formulated entirely at the level of **model theory** (classes of models, conservativity) and **linear structure** on (\mathbb{N}^B), without committing to any particular syntax or proof calculus.

---

## 7. Example: finite graphs with a non-trivial δ (GraphToy)

The file

```text
LogicDissoc/GraphToy.lean
```

implements a complete finite example:

* `Model  := Graph3` (undirected graphs on 3 labeled vertices),
* `Sentence := GraphSentence` with atoms like `conn`, `tri`, `¬conn`, `¬tri`,
* a concrete `RefSystem` `E_graph` with a non-trivial
  `delta : Sentence → ℝ` such that

  * `delta(top) = 0` for the unique “everywhere true” local sentence,
  * for every **non-local** sentence `φ`, one has `1 ≤ delta φ` and `delta φ < 2`,
  * in the toy instance, different non-local formulas receive distinct weights
    (e.g. `conn`, `¬conn`, `tri`, `¬tri` get different real values),
* a finite type of Gödel directions `GraphDir` and a `GraphGodelDirection`,
* the canonical obstruction `GraphDeltaObstruction` built from `delta`,
* and finally a specialized index

  ```lean
  noncomputable def graphAstar (S : GraphBattery) : ℝ := ...
  ```

This example shows explicitly:

* the **local / non-local** dichotomy via `delta` (local sentences have `delta = 0`, non-local ones lie in the band `1 ≤ δ < 2`),
* **granularity of δ** on non-local sentences: different formulas get different non-locality weights,
* detection of non-conservativity via Gödel directions,
* and the general 0 / >0 meta-theorem in a finite, fully proved Lean model.

---

## 12. License

This project is licensed under the **GNU Affero General Public License version 3.0 only (AGPL-3.0-only)**.

Any modified or derived version made accessible to third parties, including via online services, must be provided under the same license, with corresponding source code.

For details, see: [https://www.gnu.org/licenses/agpl-3.0.html](https://www.gnu.org/licenses/agpl-3.0.html)

