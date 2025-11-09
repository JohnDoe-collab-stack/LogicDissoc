import Mathlib.Data.Real.Basic
import LogicDissoc.AstarConcrete

namespace LogicDissoc

structure Counters where
  vp : ℕ
  vk : ℕ
  vE : ℕ

structure ObstructionAxioms where
  F   : Counters → ℝ
  fp  : ℕ → ℝ
  fk  : ℕ → ℝ
  fE  : ℕ → ℝ
  hF  : ∀ c, F c = fp c.vp + fk c.vk + fE c.vE
  fp0 : fp 0 = 0
  fk0 : fk 0 = 0
  fE0 : fE 0 = 0
  fp_pos : ∀ {n}, 0 < n → 0 < fp n
  fk_pos : ∀ {n}, 0 < n → 0 < fk n
  fE_pos : ∀ {n}, 0 < n → 0 < fE n
  fp_add : ∀ m n, fp (m + n) = fp m + fp n
  fk_add : ∀ m n, fk (m + n) = fk m + fk n
  fE_add : ∀ m n, fE (m + n) = fE m + fE n

namespace ObstructionAxioms

variable (O : ObstructionAxioms)

lemma fp_linear : ∀ n, O.fp n = (n : ℝ) * O.fp 1 := by
  intro n
  induction n with
  | zero =>
      simp [O.fp0]
  | succ n ih =>
      have h := O.fp_add n 1
      have h' : O.fp (Nat.succ n) = O.fp n + O.fp 1 := by
        simpa [Nat.succ_eq_add_one] using h
      calc
        O.fp (Nat.succ n)
            = O.fp n + O.fp 1 := h'
        _ = (n : ℝ) * O.fp 1 + O.fp 1 := by
              simp [ih]
        _ = ((Nat.succ n : ℕ) : ℝ) * O.fp 1 := by
              simp [Nat.succ_eq_add_one, add_mul, one_mul, add_comm]

lemma fk_linear : ∀ n, O.fk n = (n : ℝ) * O.fk 1 := by
  intro n
  induction n with
  | zero =>
      simp [O.fk0]
  | succ n ih =>
      have h := O.fk_add n 1
      have h' : O.fk (Nat.succ n) = O.fk n + O.fk 1 := by
        simpa [Nat.succ_eq_add_one] using h
      calc
        O.fk (Nat.succ n)
            = O.fk n + O.fk 1 := h'
        _ = (n : ℝ) * O.fk 1 + O.fk 1 := by
              simp [ih]
        _ = ((Nat.succ n : ℕ) : ℝ) * O.fk 1 := by
              simp [Nat.succ_eq_add_one, add_mul, one_mul, add_comm]

lemma fE_linear : ∀ n, O.fE n = (n : ℝ) * O.fE 1 := by
  intro n
  induction n with
  | zero =>
      simp [O.fE0]
  | succ n ih =>
      have h := O.fE_add n 1
      have h' : O.fE (Nat.succ n) = O.fE n + O.fE 1 := by
        simpa [Nat.succ_eq_add_one] using h
      calc
        O.fE (Nat.succ n)
            = O.fE n + O.fE 1 := h'
        _ = (n : ℝ) * O.fE 1 + O.fE 1 := by
              simp [ih]
        _ = ((Nat.succ n : ℕ) : ℝ) * O.fE 1 := by
              simp [Nat.succ_eq_add_one, add_mul, one_mul, add_comm]

theorem canonical :
  ∃ α β γ,
    0 < α ∧ 0 < β ∧ 0 < γ ∧
    ∀ c : Counters,
      O.F c =
        (c.vp : ℝ) * α +
        (c.vk : ℝ) * β +
        (c.vE : ℝ) * γ := by
  let α := O.fp 1
  let β := O.fk 1
  let γ := O.fE 1
  have hα : 0 < α := by
    have h1 : 0 < (1 : ℕ) := Nat.succ_pos 0
    simpa [α] using O.fp_pos (n := 1) h1
  have hβ : 0 < β := by
    have h1 : 0 < (1 : ℕ) := Nat.succ_pos 0
    simpa [β] using O.fk_pos (n := 1) h1
  have hγ : 0 < γ := by
    have h1 : 0 < (1 : ℕ) := Nat.succ_pos 0
    simpa [γ] using O.fE_pos (n := 1) h1
  refine ⟨α, β, γ, hα, hβ, hγ, ?_⟩
  intro c
  have hF := O.hF c
  have hfp := O.fp_linear c.vp
  have hfk := O.fk_linear c.vk
  have hfE := O.fE_linear c.vE
  simp [hF, hfp, hfk, hfE, α, β, γ]

lemma canonical_coeffs_unique
  {α β γ α' β' γ' : ℝ}
  (h :
    ∀ c : Counters,
      O.F c =
        (c.vp : ℝ) * α +
        (c.vk : ℝ) * β +
        (c.vE : ℝ) * γ)
  (h' :
    ∀ c : Counters,
      O.F c =
        (c.vp : ℝ) * α' +
        (c.vk : ℝ) * β' +
        (c.vE : ℝ) * γ') :
  α = α' ∧ β = β' ∧ γ = γ' := by
  have h_eq :
    ∀ c : Counters,
      (c.vp : ℝ) * α +
      (c.vk : ℝ) * β +
      (c.vE : ℝ) * γ =
      (c.vp : ℝ) * α' +
      (c.vk : ℝ) * β' +
      (c.vE : ℝ) * γ' := by
    intro c
    have h1 := h c
    have h2 := h' c
    exact h1.symm.trans h2
  have hα_eq := h_eq { vp := 1, vk := 0, vE := 0 }
  have hβ_eq := h_eq { vp := 0, vk := 1, vE := 0 }
  have hγ_eq := h_eq { vp := 0, vk := 0, vE := 1 }
  have hα : α = α' := by
    simpa [one_mul, zero_mul, add_zero, zero_add] using hα_eq
  have hβ : β = β' := by
    simpa [one_mul, zero_mul, add_zero, zero_add] using hβ_eq
  have hγ : γ = γ' := by
    simpa [one_mul, zero_mul, add_zero, zero_add] using hγ_eq
  exact ⟨hα, hβ, hγ⟩

lemma zero_iff_zero_counts
  (O : LogicDissoc.ObstructionAxioms) :
  ∀ c : LogicDissoc.Counters,
    O.F c = 0 ↔
      c.vp = 0 ∧ c.vk = 0 ∧ c.vE = 0 := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hF⟩ := O.canonical
  intro c
  constructor
  · intro h0
    have hsum :
      (c.vp : ℝ) * α +
      (c.vk : ℝ) * β +
      (c.vE : ℝ) * γ = 0 := by
      simpa [hF c] using h0
    have hvp_nonneg : 0 ≤ (c.vp : ℝ) := by
      exact_mod_cast (Nat.zero_le c.vp)
    have hvk_nonneg : 0 ≤ (c.vk : ℝ) := by
      exact_mod_cast (Nat.zero_le c.vk)
    have hvE_nonneg : 0 ≤ (c.vE : ℝ) := by
      exact_mod_cast (Nat.zero_le c.vE)
    have ha : 0 ≤ (c.vp : ℝ) * α :=
      mul_nonneg hvp_nonneg (le_of_lt hα)
    have hb : 0 ≤ (c.vk : ℝ) * β :=
      mul_nonneg hvk_nonneg (le_of_lt hβ)
    have hc : 0 ≤ (c.vE : ℝ) * γ :=
      mul_nonneg hvE_nonneg (le_of_lt hγ)
    have hsplit :=
      LogicDissoc.three_nonneg_sum_eq_zero_iff ha hb hc hsum
    rcases hsplit with ⟨hvp, hvk, hvE⟩
    have hvp0 : c.vp = 0 := by
      have := mul_eq_zero.mp hvp
      cases this with
      | inl hvp_real =>
          exact (Nat.cast_eq_zero).1 hvp_real
      | inr hα0 =>
          exact (False.elim ((ne_of_gt hα) hα0))
    have hvk0 : c.vk = 0 := by
      have := mul_eq_zero.mp hvk
      cases this with
      | inl hvk_real =>
          exact (Nat.cast_eq_zero).1 hvk_real
      | inr hβ0 =>
          exact (False.elim ((ne_of_gt hβ) hβ0))
    have hvE0 : c.vE = 0 := by
      have := mul_eq_zero.mp hvE
      cases this with
      | inl hvE_real =>
          exact (Nat.cast_eq_zero).1 hvE_real
      | inr hγ0 =>
          exact (False.elim ((ne_of_gt hγ) hγ0))
    exact ⟨hvp0, hvk0, hvE0⟩
  · rintro ⟨hvp0, hvk0, hvE0⟩
    have hFc := hF c
    simp [hFc, hvp0, hvk0, hvE0]

end ObstructionAxioms

end LogicDissoc
