import Mathlib.Data.Real.Basic
import LogicDissoc.BasicSemantics

universe u v

variable {Sentence : Type u} {Model : Type v}

namespace LogicDissoc

open Set

variable {Sat}

/-- Décomposition de Σ_R en trois blocs (identifiants ASCII seulement).
-/
structure SigmaDecomp where
  sigmaAll : Set Sentence
  sigmaP   : Set Sentence
  sigmaK   : Set Sentence
  sigmaE   : Set Sentence
  hUnion   : sigmaAll = sigmaP ∪ sigmaK ∪ sigmaE

/-- Indicateurs logiques pour Σ_R (ASCII: p, k, e).
-/
structure Indicators (Sat : Model → Sentence → Prop) (Γ_TD : Set Sentence) (sd : SigmaDecomp) where
  p : ℝ
  k : ℝ
  e : ℝ
  hp1 :
    p = 1 ↔ sd.sigmaP ⊆ ThE Sat (K Sat Γ_TD)
  hk1 :
    k = 1 ↔ sd.sigmaK ⊆ ThE Sat (K Sat Γ_TD)
  he0 :
    e = 0 ↔ sd.sigmaE ⊆ ThE Sat (K Sat Γ_TD)
  hp_nonneg : 0 ≤ 1 - p
  hk_nonneg : 0 ≤ 1 - k
  he_nonneg : 0 ≤ e

/-- Indice A*(R).
-/
def Astar (Sat : Model → Sentence → Prop) (Γ_TD : Set Sentence)
    (sd : SigmaDecomp) (I : Indicators Sat Γ_TD sd) (α β γ : ℝ) : ℝ :=
  α * (1 - I.p) + β * (1 - I.k) + γ * I.e

/-- Somme de deux termes ≥ 0 vaut 0 ⇒ chaque terme = 0. -/
lemma two_nonneg_sum_eq_zero_iff
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) :
    a = 0 ∧ b = 0 := by
  have h_eq : a = -b := by
    have := congrArg (fun x => x - b) h
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  have h_le0 : a ≤ 0 := by
    have hnb : -b ≤ 0 := neg_nonpos_of_nonneg hb
    simpa [h_eq] using hnb
  have ha0 : a = 0 := le_antisymm h_le0 ha
  have hb0 : b = 0 := by
    have := congrArg (fun x => x - a) h
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg, ha0] using this
  exact And.intro ha0 hb0

/-- Somme de trois termes ≥ 0 vaut 0 ⇒ chaque terme = 0. -/
lemma three_nonneg_sum_eq_zero_iff
    {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hab_eq : a + b = -c := by
    have := congrArg (fun x => x + (-c)) h
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hab_ge : 0 ≤ a + b := add_nonneg ha hb
  have hab_le : a + b ≤ 0 := by
    have hnb : -c ≤ 0 := neg_nonpos_of_nonneg hc
    simpa [hab_eq] using hnb
  have hab0 : a + b = 0 := le_antisymm hab_le hab_ge
  have hab_split := two_nonneg_sum_eq_zero_iff ha hb hab0
  rcases hab_split with ⟨ha0, hb0⟩
  have hc0 : c = 0 := by
    have := congrArg (fun x => x - (a + b)) h
    simpa [add_comm, add_left_comm, add_assoc, ha0, hb0, sub_eq_add_neg] using this
  exact And.intro ha0 (And.intro hb0 hc0)

/-- Théorème central : Astar(R) = 0 ⇔ extension conservative.
-/
theorem central_theorem
    (Sat : Model → Sentence → Prop)
    (Γ_TD : Set Sentence)
    (sd : SigmaDecomp)
    (I : Indicators Sat Γ_TD sd)
    {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    Astar Sat Γ_TD sd I α β γ = 0
      ↔ ModE Sat (Γ_TD ∪ sd.sigmaAll) = ModE Sat Γ_TD := by
  set KTD := K Sat Γ_TD with hKTD
  constructor
  · intro hA
    have hsum :
        α * (1 - I.p) + β * (1 - I.k) + γ * I.e = 0 := hA
    have ha : 0 ≤ α * (1 - I.p) :=
      mul_nonneg (le_of_lt hα) I.hp_nonneg
    have hb : 0 ≤ β * (1 - I.k) :=
      mul_nonneg (le_of_lt hβ) I.hk_nonneg
    have hc : 0 ≤ γ * I.e :=
      mul_nonneg (le_of_lt hγ) I.he_nonneg
    have hzero := three_nonneg_sum_eq_zero_iff ha hb hc hsum
    rcases hzero with ⟨hαterm0, hβterm0, hγterm0⟩
    have hp_eq : 1 - I.p = 0 := by
      have h_or := mul_eq_zero.mp hαterm0
      cases h_or with
      | inl hα0 =>
          exact False.elim ((ne_of_gt hα) hα0)
      | inr h1p0 =>
          exact h1p0
    have hk_eq : 1 - I.k = 0 := by
      have h_or := mul_eq_zero.mp hβterm0
      cases h_or with
      | inl hβ0 =>
          exact False.elim ((ne_of_gt hβ) hβ0)
      | inr h1k0 =>
          exact h1k0
    have he_eq : I.e = 0 := by
      have h_or := mul_eq_zero.mp hγterm0
      cases h_or with
      | inl hγ0 =>
          exact False.elim ((ne_of_gt hγ) hγ0)
      | inr hE0 =>
          exact hE0
    have hp1_val : I.p = 1 := by
      have h := congrArg (fun x => x + I.p) hp_eq
      have : 1 = I.p := by
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using h
      exact this.symm
    have hk1_val : I.k = 1 := by
      have h := congrArg (fun x => x + I.k) hk_eq
      have : 1 = I.k := by
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using h
      exact this.symm
    have hSigmaP : sd.sigmaP ⊆ ThE Sat KTD :=
      (I.hp1).mp hp1_val
    have hSigmaK : sd.sigmaK ⊆ ThE Sat KTD :=
      (I.hk1).mp hk1_val
    have hSigmaE : sd.sigmaE ⊆ ThE Sat KTD :=
      (I.he0).mp he_eq
    have hSigmaAll : sd.sigmaAll ⊆ ThE Sat KTD := by
      intro φ hφ
      have : φ ∈ sd.sigmaP ∪ sd.sigmaK ∪ sd.sigmaE := by
        simpa [sd.hUnion] using hφ
      cases this with
      | inl hφPK =>
          cases hφPK with
          | inl hφP => exact hSigmaP hφP
          | inr hφK => exact hSigmaK hφK
      | inr hφE =>
          exact hSigmaE hφE
    have hiff := mod_conservative_iff_subset_ThE (Sat := Sat) Γ_TD sd.sigmaAll
    exact hiff.mpr hSigmaAll
  · intro hModEq
    have hSigmaAll :=
      (mod_conservative_iff_subset_ThE (Sat := Sat) Γ_TD sd.sigmaAll).1 hModEq
    have hSigmaP : sd.sigmaP ⊆ ThE Sat (K Sat Γ_TD) := by
      intro φ hφ
      apply hSigmaAll
      have : φ ∈ sd.sigmaP ∪ sd.sigmaK ∪ sd.sigmaE := Or.inl (Or.inl hφ)
      simpa [sd.hUnion] using this
    have hSigmaK : sd.sigmaK ⊆ ThE Sat (K Sat Γ_TD) := by
      intro φ hφ
      apply hSigmaAll
      have : φ ∈ sd.sigmaP ∪ sd.sigmaK ∪ sd.sigmaE := Or.inl (Or.inr hφ)
      simpa [sd.hUnion] using this
    have hSigmaE : sd.sigmaE ⊆ ThE Sat (K Sat Γ_TD) := by
      intro φ hφ
      apply hSigmaAll
      have : φ ∈ sd.sigmaP ∪ sd.sigmaK ∪ sd.sigmaE := Or.inr hφ
      simpa [sd.hUnion] using this
    have hp1_val : I.p = 1 := (I.hp1).2 hSigmaP
    have hk1_val : I.k = 1 := (I.hk1).2 hSigmaK
    have he0_val : I.e = 0 := (I.he0).2 hSigmaE
    simp [Astar, hp1_val, hk1_val, he0_val]

section CanonicalIndicators

open Classical

variable (Sat : Model → Sentence → Prop) (Γ_TD : Set Sentence)

/-- Construction d'un témoin `Indicators` canonique pour un `SigmaDecomp` donné.
-/
theorem existsIndicators (sd : SigmaDecomp) :
  ∃ _ : Indicators Sat Γ_TD sd, True := by
  classical
  let p0 : ℝ :=
    if h : sd.sigmaP ⊆ ThE Sat (K Sat Γ_TD) then 1 else 0
  let k0 : ℝ :=
    if h : sd.sigmaK ⊆ ThE Sat (K Sat Γ_TD) then 1 else 0
  let e0 : ℝ :=
    if h : sd.sigmaE ⊆ ThE Sat (K Sat Γ_TD) then 0 else 1
  refine ⟨
    { p := p0,
      k := k0,
      e := e0,
      hp1 := ?hp1,
      hk1 := ?hk1,
      he0 := ?he0,
      hp_nonneg := ?hp_nonneg,
      hk_nonneg := ?hk_nonneg,
      he_nonneg := ?he_nonneg },
    trivial⟩
  · unfold p0
    by_cases h' : sd.sigmaP ⊆ ThE Sat (K Sat Γ_TD)
    · simp [h']
    · simp [h']
  · unfold k0
    by_cases h' : sd.sigmaK ⊆ ThE Sat (K Sat Γ_TD)
    · simp [h']
    · simp [h']
  · unfold e0
    by_cases h' : sd.sigmaE ⊆ ThE Sat (K Sat Γ_TD)
    · simp [h']
    · simp [h']
  · unfold p0
    by_cases h' : sd.sigmaP ⊆ ThE Sat (K Sat Γ_TD)
    · simp [h']
    · simp [h']
  · unfold k0
    by_cases h' : sd.sigmaK ⊆ ThE Sat (K Sat Γ_TD)
    · simp [h']
    · simp [h']
  · unfold e0
    by_cases h' : sd.sigmaE ⊆ ThE Sat (K Sat Γ_TD)
    · simp [h']
    · simp [h']

end CanonicalIndicators

end LogicDissoc
