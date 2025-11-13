import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import LogicDissoc.BasicSemantics

namespace LogicDissoc

universe u v

/--
Système de référence au sens SLE :

* `Model`    : type des modèles,
* `Sentence` : type des formules,
* `Sat`      : relation de satisfaction,
* `delta`    : « Δ_ref » à valeurs réelles,

avec les axiomes (DR0), (DR1) et une invariance sémantique.
-/
structure RefSystem (Model : Type u) (Sentence : Type v) where
  Sat   : Model → Sentence → Prop
  delta : Sentence → ℝ
  /-- (DR0) : `delta φ = 0` ssi `φ` appartient à `CloE(∅)`. -/
  DR0   :
    ∀ φ : Sentence,
      delta φ = 0 ↔
        φ ∈ ThE (Sat := Sat) (ModE (Sat := Sat) (∅ : Set Sentence))
  /-- (DR1) : si `φ` n'est pas locale, alors `delta φ ∈ [1,2)`. -/
  DR1   :
    ∀ {φ : Sentence},
      φ ∉ ThE (Sat := Sat) (ModE (Sat := Sat) (∅ : Set Sentence)) →
        1 ≤ delta φ ∧ delta φ < 2
  /-- Invariance sémantique : `delta` ne dépend que de la classe de vérité de `φ`. -/
  delta_semantic_invariance :
    ∀ {φ ψ : Sentence},
      (∀ M : Model, Sat M φ ↔ Sat M ψ) →
      delta φ = delta ψ

namespace RefSystem

variable {Model : Type u} {Sentence : Type v}
variable (E : RefSystem Model Sentence)

open Set

/-- Clôture `CloE Γ := ThE (ModE Γ)` associée à `E`. -/
def CloE (Γ : Set Sentence) : Set Sentence :=
  ThE (Sat := E.Sat) (ModE (Sat := E.Sat) Γ)

/-- Phrases « rang 0 » (locales) : appartenir à `CloE ∅`. -/
def isLocal (φ : Sentence) : Prop :=
  φ ∈ E.CloE (∅ : Set Sentence)

/-- Phrases « rang 1 » (non locales) : ne pas être dans `CloE ∅`. -/
def isNonlocal (φ : Sentence) : Prop :=
  ¬ E.isLocal φ

/-- Réécriture directe de (DR0) via `CloE`. -/
lemma delta_eq_zero_iff_mem_closure (φ : Sentence) :
  E.delta φ = 0 ↔ φ ∈ E.CloE (∅ : Set Sentence) := by
  -- DR0 : delta φ = 0 ↔ φ ∈ ThE (ModE ∅)
  have h := E.DR0 φ
  simpa [RefSystem.CloE] using h

lemma mem_closure_iff_delta_eq_zero (φ : Sentence) :
  φ ∈ E.CloE (∅ : Set Sentence) ↔ E.delta φ = 0 :=
  (E.delta_eq_zero_iff_mem_closure φ).symm

/--
Alignement « rang 1 » au niveau de la clôture :

`φ ∉ CloE ∅`  ↔  `delta φ ∈ [1,2)`.
-/
lemma nonmem_closure_iff_delta_band (φ : Sentence) :
  φ ∉ E.CloE (∅ : Set Sentence) ↔ 1 ≤ E.delta φ ∧ E.delta φ < 2 := by
  constructor
  · intro hnot
    -- On réécrit l'hypothèse dans la forme attendue par DR1.
    have h' :
        φ ∉ ThE (Sat := E.Sat) (ModE (Sat := E.Sat) (∅ : Set Sentence)) := by
      simpa [RefSystem.CloE] using hnot
    exact E.DR1 (φ := φ) h'
  · intro hband hmem
    -- Si `φ ∈ CloE ∅`, alors `delta φ = 0` par DR0, contradiction avec `1 ≤ delta φ`.
    have hδ0 : E.delta φ = 0 :=
      (E.delta_eq_zero_iff_mem_closure φ).mpr hmem
    have h1le0 : (1 : ℝ) ≤ 0 := by
      simpa [hδ0] using hband.left
    have h0lt1 : (0 : ℝ) < 1 := zero_lt_one
    have hnot : ¬ (0 : ℝ) < 1 := not_lt_of_ge h1le0
    exact hnot h0lt1

/--
Alignement « rang 1 » formulé avec `isLocal` / `isNonlocal` :

`isNonlocal φ`  ↔  `delta φ ∈ [1,2)`.
-/
lemma nonlocal_iff_delta_band (φ : Sentence) :
  E.isNonlocal φ ↔ 1 ≤ E.delta φ ∧ E.delta φ < 2 := by
  unfold RefSystem.isNonlocal RefSystem.isLocal
  exact E.nonmem_closure_iff_delta_band φ

end RefSystem

end LogicDissoc
