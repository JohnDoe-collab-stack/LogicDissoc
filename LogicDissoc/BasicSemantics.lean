import Mathlib.Data.Set.Basic

universe u v

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)

/-- Classe des modèles de Γ.
-/
def ModE (Γ : Set Sentence) : Set Model :=
  { M |
∀ φ ∈ Γ, Sat M φ }

/-- Théorie vraie dans tous les modèles de K. -/
def ThE (K : Set Model) : Set Sentence :=
  { φ |
∀ M ∈ K, Sat M φ }

namespace LogicDissoc

open Set

variable {Sat}

/-- Lemme Galois : extension conservative.
-/
lemma mod_conservative_iff_subset_ThE
    (Γ Δ : Set Sentence) :
    ModE Sat (Γ ∪ Δ) = ModE Sat Γ ↔ Δ ⊆ ThE Sat (ModE Sat Γ) := by
  constructor
  · intro h_eq φ hφ M hM
    have hM' : M ∈ ModE Sat (Γ ∪ Δ) := by
      simpa [h_eq] using hM
    exact hM' φ (Or.inr hφ)
  · intro h_sub
    apply Subset.antisymm
    · intro M hM φ hφΓ
      exact hM φ (Or.inl hφΓ)
    · intro M hM φ hφUnion
      cases hφUnion with
      | inl hφΓ =>
          exact hM φ hφΓ
      | inr hφΔ =>
          have hφIn : φ ∈ ThE Sat (ModE Sat Γ) := h_sub hφΔ
          exact hφIn M hM

/-- Classe K = ModE(Γ_TD).
-/
def K (Sat : Model → Sentence → Prop) (Γ_TD : Set Sentence) : Set Model :=
  ModE Sat Γ_TD

end LogicDissoc
