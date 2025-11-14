import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import LogicDissoc.BasicSemantics

namespace LogicDissoc

universe u v


/--
Reference system in the SLE sense:

* `Model`    : type of models,
* `Sentence` : type of formulas,
* `Sat`      : satisfaction relation,
* `delta`    : real-valued "Δ_ref",

with axioms (DR0), (DR1) and semantic invariance.

NOTE: This is an axiomatic structure. For a concrete construction
in the finite/decidable case, see DeltaConstruction.lean which
shows that RefSystem can be explicitly built from BasicSemantics
by counting model proportions.
-/
structure RefSystem (Model : Type u) (Sentence : Type v) where
  Sat   : Model → Sentence → Prop
  delta : Sentence → ℝ
  /-- (DR0) : `delta φ = 0` iff `φ` belongs to `CloE(∅)`. -/
  DR0   :
    ∀ φ : Sentence,
      delta φ = 0 ↔
        φ ∈ ThE (Sat := Sat) (ModE (Sat := Sat) (∅ : Set Sentence))
  /-- (DR1) : if `φ` is non-local, then `delta φ ∈ [1,2)`. -/
  DR1   :
    ∀ {φ : Sentence},
      φ ∉ ThE (Sat := Sat) (ModE (Sat := Sat) (∅ : Set Sentence)) →
        1 ≤ delta φ ∧ delta φ < 2
  /-- Semantic invariance: `delta` depends only on the truth class of `φ`. -/
  delta_semantic_invariance :
    ∀ {φ ψ : Sentence},
      (∀ M : Model, Sat M φ ↔ Sat M ψ) →
      delta φ = delta ψ

namespace RefSystem

variable {Model : Type u} {Sentence : Type v}
variable (E : RefSystem Model Sentence)

open Set

/-- Closure `CloE Γ := ThE (ModE Γ)` associated with `E`. -/
def CloE (Γ : Set Sentence) : Set Sentence :=
  ThE (Sat := E.Sat) (ModE (Sat := E.Sat) Γ)

/-- “Rank 0” (local) sentences: membership in `CloE ∅`. -/
def isLocal (φ : Sentence) : Prop :=
  φ ∈ E.CloE (∅ : Set Sentence)

/-- “Rank 1” (non-local) sentences: not in `CloE ∅`. -/
def isNonlocal (φ : Sentence) : Prop :=
  ¬ E.isLocal φ

/-- Direct rewriting of (DR0) via `CloE`. -/
lemma delta_eq_zero_iff_mem_closure (φ : Sentence) :
  E.delta φ = 0 ↔ φ ∈ E.CloE (∅ : Set Sentence) := by
  -- DR0 : delta φ = 0 ↔ φ ∈ ThE (ModE ∅)
  have h := E.DR0 φ
  simpa [RefSystem.CloE] using h

lemma mem_closure_iff_delta_eq_zero (φ : Sentence) :
  φ ∈ E.CloE (∅ : Set Sentence) ↔ E.delta φ = 0 :=
  (E.delta_eq_zero_iff_mem_closure φ).symm

/--
“Rank 1” alignment at the level of the closure:

`φ ∉ CloE ∅`  ↔  `delta φ ∈ [1,2)`.
-/
lemma nonmem_closure_iff_delta_band (φ : Sentence) :
  φ ∉ E.CloE (∅ : Set Sentence) ↔ 1 ≤ E.delta φ ∧ E.delta φ < 2 := by
  constructor
  · intro hnot
    -- Rewrite the hypothesis into the form required by DR1.
    have h' :
        φ ∉ ThE (Sat := E.Sat) (ModE (Sat := E.Sat) (∅ : Set Sentence)) := by
      simpa [RefSystem.CloE] using hnot
    exact E.DR1 (φ := φ) h'
  · intro hband hmem
    -- If `φ ∈ CloE ∅`, then `delta φ = 0` by DR0, contradicting `1 ≤ delta φ`.
    have hδ0 : E.delta φ = 0 :=
      (E.delta_eq_zero_iff_mem_closure φ).mpr hmem
    have h1le0 : (1 : ℝ) ≤ 0 := by
      simpa [hδ0] using hband.left
    have h0lt1 : (0 : ℝ) < 1 := zero_lt_one
    have hnot : ¬ (0 : ℝ) < 1 := not_lt_of_ge h1le0
    exact hnot h0lt1

/--
“Rank 1” alignment formulated with `isLocal` / `isNonlocal`:

`isNonlocal φ`  ↔  `delta φ ∈ [1,2)`.
-/
lemma nonlocal_iff_delta_band (φ : Sentence) :
  E.isNonlocal φ ↔ 1 ≤ E.delta φ ∧ E.delta φ < 2 := by
  unfold RefSystem.isNonlocal RefSystem.isLocal
  exact E.nonmem_closure_iff_delta_band φ

end RefSystem

end LogicDissoc
