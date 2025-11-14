import Mathlib.Data.Set.Basic

universe u v

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)

/-- Class of models of Γ. -/
def ModE (Γ : Set Sentence) : Set Model :=
  { M |
∀ φ ∈ Γ, Sat M φ }

/-- Theory true in all models of `K`. -/
def ThE (K : Set Model) : Set Sentence :=
  { φ |
∀ M ∈ K, Sat M φ }

/-- Semantic closure operator: CloE(Γ) = ThE(ModE(Γ)). -/
def CloE (Γ : Set Sentence) : Set Sentence :=
  ThE Sat (ModE Sat Γ)

namespace LogicDissoc

open Set

variable {Sat}

/-- Galois lemma: conservative extension. -/
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

/-- Idempotence of closure. -/
lemma CloE_idempotent (Γ : Set Sentence) :
  CloE Sat (CloE Sat Γ) = CloE Sat Γ := by
  unfold CloE ThE ModE
  ext φ
  simp only [Set.mem_setOf_eq]
  constructor
  · -- (→) Si φ ∈ CloE(CloE(Γ)), montrer φ ∈ CloE(Γ)
    intro h M hM
    -- h : ∀ M, (∀ ψ ∈ CloE Sat Γ, Sat M ψ) → Sat M φ
    -- hM : ∀ χ ∈ Γ, Sat M χ
    -- Goal: Sat M φ
    apply h
    intro ψ hψ
    -- hψ : ψ ∈ CloE Sat Γ, i.e., ∀ N, (∀ χ ∈ Γ, Sat N χ) → Sat N ψ
    -- Goal: Sat M ψ
    exact hψ M hM
  · -- (←) Si φ ∈ CloE(Γ), montrer φ ∈ CloE(CloE(Γ))
    intro h M hM
    -- h : ∀ M, (∀ χ ∈ Γ, Sat M χ) → Sat M φ
    -- hM : ∀ ψ ∈ CloE Sat Γ, Sat M ψ
    -- Goal: Sat M φ
    apply h
    intro χ hχ
    -- hχ : χ ∈ Γ
    -- Goal: Sat M χ
    -- On utilise l'extensivité: Γ ⊆ CloE Sat Γ
    have hχ_clo : χ ∈ CloE Sat Γ := by
      unfold CloE ThE ModE
      simp only [Set.mem_setOf_eq]
      intro N hN
      exact hN χ hχ
    exact hM χ hχ_clo

/-- Extensivity of closure. -/
lemma subset_CloE (Γ : Set Sentence) :
  Γ ⊆ CloE Sat Γ := by
  intro φ hφ
  unfold CloE ThE ModE
  simp only [Set.mem_setOf_eq]
  intro M hM
  exact hM φ hφ

/-- Monotonicity of closure. -/
lemma CloE_mono {Γ Δ : Set Sentence} (h : Γ ⊆ Δ) :
  CloE Sat Γ ⊆ CloE Sat Δ := by
  intro φ hφ
  unfold CloE ThE ModE at *
  simp only [Set.mem_setOf_eq] at *
  intro M hM
  apply hφ
  intro ψ hψ
  exact hM ψ (h hψ)

/-- Class `K = ModE(Γ_TD)`. -/
def K (Sat : Model → Sentence → Prop) (Γ_TD : Set Sentence) : Set Model :=
  ModE Sat Γ_TD

end LogicDissoc
