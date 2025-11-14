import LogicDissoc.BasicSemantics
import LogicDissoc.RefSystem
import LogicDissoc.Rev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith



namespace LogicDissoc

universe u v

section FiniteConstruction

variable {Model : Type u} {Sentence : Type v}
variable [Fintype Model]
variable (Sat : Model → Sentence → Prop)
variable [∀ M φ, Decidable (Sat M φ)]
/--
Proportion of models satisfying φ among all models.
This is the key metric that becomes the interior of [1,2).
-/
def modelProportion (φ : Sentence) : ℚ :=
  let total := (Finset.univ : Finset Model).card
  let satisfying := (Finset.univ.filter (fun M => Sat M φ)).card
  ↑satisfying / ↑total

/--
Construction of delta for finite decidable models.
For local formulas: delta = 0
For non-local formulas: delta = 1 + proportion
-/
def constructDelta (φ : Sentence) : ℝ :=
  if _ : ∀ M : Model, Sat M φ then
    0
  else
    1 + (modelProportion Sat φ : ℝ)

/-- DR0 is satisfied by construction. -/
theorem constructDelta_satisfies_DR0 (φ : Sentence) :
  constructDelta Sat φ = 0 ↔
    φ ∈ ThE Sat (ModE Sat (∅ : Set Sentence)) := by
  unfold constructDelta ThE ModE
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, forall_const]
  constructor
  · intro heq
    by_cases h : ∀ M : Model, Sat M φ
    · exact h
    · simp [h] at heq
      exfalso
      have hp : (0 : ℝ) ≤ (modelProportion Sat φ : ℝ) := by
        apply Rat.cast_nonneg.mpr
        simp [modelProportion]
        apply div_nonneg <;> exact Nat.cast_nonneg _
      linarith
  · intro h
    simp [h]

/-- DR1 is satisfied: non-local formulas have a delta in [1,2). -/
theorem constructDelta_satisfies_DR1 {φ : Sentence}
    (h_nonlocal : φ ∉ ThE Sat (ModE Sat (∅ : Set Sentence))) :
  1 ≤ constructDelta Sat φ ∧ constructDelta Sat φ < 2 := by
  unfold constructDelta ThE ModE at *
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, forall_const,
               not_forall] at h_nonlocal
  obtain ⟨M, hM⟩ := h_nonlocal
  have h : ¬ ∀ M : Model, Sat M φ := by
    intro hall
    exact hM (hall M)
  simp [h]
  constructor
  · have hp0 : (0 : ℝ) ≤ (modelProportion Sat φ : ℝ) := by
      apply Rat.cast_nonneg.mpr
      unfold modelProportion
      simp
      apply div_nonneg <;> exact Nat.cast_nonneg _
    have := add_le_add_left hp0 1
    simpa using this
  · have hpQ : modelProportion Sat φ < 1 := by
      have hpQ' :
        (↑((Finset.univ.filter fun M : Model => Sat M φ).card) /
         ↑((Finset.univ : Finset Model).card) : ℚ) < 1 := by
        set num : ℕ :=
          (Finset.univ.filter fun M : Model => Sat M φ).card with hnum
        set den : ℕ :=
          (Finset.univ : Finset Model).card with hden
        have hle :
            num ≤ den := by
          have hle' :
              (Finset.univ.filter fun M : Model => Sat M φ).card ≤
                (Finset.univ : Finset Model).card :=
            Finset.card_filter_le _ _
          simpa [hnum, hden] using hle'
        have hltNat : num < den := by
          apply Nat.lt_of_le_of_ne hle
          intro heq

          have h_eq_univ : (Finset.univ.filter fun M => Sat M φ) = Finset.univ := by
            apply Finset.eq_of_subset_of_card_le
            · exact Finset.filter_subset _ _
            · exact Nat.le_of_eq heq.symm

          have hallsat : ∀ M' : Model, Sat M' φ := by
            intro M'
            have : M' ∈ Finset.univ.filter (fun M => Sat M φ) := by
              rw [h_eq_univ]
              exact Finset.mem_univ M'
            exact (Finset.mem_filter.mp this).2

          exact h hallsat
        have hltQ : (num : ℚ) < (den : ℚ) := by
          exact_mod_cast hltNat
        have hden_pos_nat : 0 < den := by
          have : 0 < (Finset.univ : Finset Model).card :=
            Finset.card_pos.mpr ⟨M, Finset.mem_univ M⟩
          simpa [hden] using this
        have hden_pos : (0 : ℚ) < (den : ℚ) := by
          exact_mod_cast hden_pos_nat
        have hdiv :
            (num : ℚ) / (den : ℚ) < (den : ℚ) / (den : ℚ) :=
          div_lt_div_of_pos_right hltQ hden_pos
        have hden_ne : (den : ℚ) ≠ 0 := ne_of_gt hden_pos
        have hdiv' : (num : ℚ) / (den : ℚ) < 1 := by
          simpa [hden_ne] using hdiv
        have : (↑num / ↑den : ℚ) < 1 := by
          simpa using hdiv'
        simpa [hnum, hden] using this
      simpa [modelProportion] using hpQ'
    have hp : (modelProportion Sat φ : ℝ) < 1 := by
      exact_mod_cast hpQ
    have := add_lt_add_left hp 1
    simpa [one_add_one_eq_two, add_comm, add_left_comm, add_assoc] using this



/-- Semantic invariance is satisfied. -/
theorem constructDelta_semantic_invariance [DecidableEq Model] {φ ψ : Sentence}
    (h_equiv : ∀ M : Model, Sat M φ ↔ Sat M ψ) :
  constructDelta Sat φ = constructDelta Sat ψ := by
  unfold constructDelta

  have h_cond_equiv : (∀ M : Model, Sat M φ) ↔ (∀ M : Model, Sat M ψ) := by
    constructor
    · intro h_all_phi M
      exact (h_equiv M).mp (h_all_phi M)
    · intro h_all_psi M
      exact (h_equiv M).mpr (h_all_psi M)

  have h_prop_equiv : modelProportion Sat φ = modelProportion Sat ψ := by
    unfold modelProportion

    have h_filter_eq : (Finset.univ.filter fun M => Sat M φ) =
                       (Finset.univ.filter fun M => Sat M ψ) := by
      ext M
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_equiv M
    rw [h_filter_eq]

  by_cases hφ : (∀ M : Model, Sat M φ)

  · have hψ := h_cond_equiv.mp hφ
    simp [hφ, hψ]

  · have hψ : ¬(∀ M : Model, Sat M ψ) := mt h_cond_equiv.mpr hφ
    simp [hφ, hψ]
    rw [h_prop_equiv]


/--
Explicit construction of a RefSystem from finite decidable structure.
This proves that RefSystem is not just an axiom system but can be
explicitly constructed from BasicSemantics in the finite case.
-/
def finiteDeltaRefSystem [DecidableEq Model] : RefSystem Model Sentence :=
{
  Sat := Sat
  delta := constructDelta Sat
  DR0 := constructDelta_satisfies_DR0 Sat
  DR1 := constructDelta_satisfies_DR1 Sat
  delta_semantic_invariance := constructDelta_semantic_invariance Sat
}

end FiniteConstruction

end LogicDissoc
