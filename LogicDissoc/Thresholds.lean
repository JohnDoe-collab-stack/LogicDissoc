import LogicDissoc.Frequencies
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finprod

namespace LogicDissoc

open scoped BigOperators
open Finset

/--
Taux critique μ* (SP) comme infimum calculable.
Soit `S : Finset ℚ` l'ensemble fini des valeurs possibles de `e_hat`
(provenant des raffinements compatibles, sur une sous-batterie avec `p_hat = 1`, `k_hat = 1`).
On pose `Bad = { e ∈ S | Ahat α β γ 1 1 e ≤ 0 }`.
Définition:
- si `Bad` est vide, alors `muCrit = 0`,
- sinon `muCrit = max Bad`.
Alors:
1. pour tout `e ∈ S`, si `e > muCrit` alors `Ahat α β γ 1 1 e > 0`,
2. pour tout `μ ∈ [0,1]` tel que `∀ e ∈ S, e ≥ μ → Ahat α β γ 1 1 e > 0`,
   on a `muCrit ≤ μ`.
Donc `muCrit` est l'infimum (au sens exact) des seuils admissibles dans `[0,1]`.
-/
def muCrit (α β γ : ℚ) (S : Finset ℚ) : ℚ :=
  let Bad := S.filter (fun e => Ahat α β γ 1 1 e ≤ 0)
  if h : Bad.Nonempty then Bad.max' h else 0


/-- Ensemble des `p_hat` "mauvais" pour l'axe p :
ceux pour lesquels `Ahat α β γ p_hat 1 0 ≤ 0`.
-/
def pBad (α β γ : ℚ) (S_P : Finset ℚ) : Finset ℚ :=
  S_P.filter (fun p => Ahat α β γ p 1 0 ≤ 0)

/-- Ensemble des `k_hat` "mauvais" pour l'axe k :
ceux pour lesquels `Ahat α β γ 1 k_hat 0 ≤ 0`.
-/
def kBad (α β γ : ℚ) (S_K : Finset ℚ) : Finset ℚ :=
  S_K.filter (fun k => Ahat α β γ 1 k 0 ≤ 0)

/-- Seuil critique p (déficit sur `1 - p_hat`), calculable.
-/
def pCrit (α β γ : ℚ) (S_P : Finset ℚ) : ℚ :=
  let B := pBad α β γ S_P
  if h : B.Nonempty then
    (B.image (fun p => 1 - p)).max'
      (by
        rcases h with ⟨p, hp⟩
        exact ⟨1 - p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩)
  else 0

/-- Seuil critique k (déficit sur `1 - k_hat`), calculable.
-/
def kCrit (α β γ : ℚ) (S_K : Finset ℚ) : ℚ :=
  let B := kBad α β γ S_K
  if h : B.Nonempty then
    (B.image (fun k => 1 - k)).max'
      (by
        rcases h with ⟨k, hk⟩
        exact ⟨1 - k, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩)
  else 0

/-- Taux critique global, entièrement calculable.
-/
def tauCrit (α β γ : ℚ)
    (S_P S_K S_E : Finset ℚ) : ℚ :=
  let τP := pCrit α β γ S_P
  let τK := kCrit α β γ S_K
  let τE := muCrit α β γ S_E
  min τP (min τK τE)

/--
Propriété "au-dessus de μ*" :

On suppose seulement que `S ⊆ [0,1]` (borne naturelle des fréquences).
Alors pour tout `e ∈ S`, si `e > muCrit` alors `Ahat α β γ 1 1 e > 0`.
-/
lemma muCrit_above
    {α β γ : ℚ} {S : Finset ℚ}
    (_ : ∀ e ∈ S, 0 ≤ e ∧ e ≤ 1) :
  ∀ e ∈ S, e > muCrit α β γ S →
    Ahat α β γ 1 1 e > 0 := by
  classical
  intro e heS he_gt
  let Bad := S.filter (fun x => Ahat α β γ 1 1 x ≤ 0)
  by_cases hBad : Bad.Nonempty
  ·
    have hμ :
      muCrit α β γ S = Bad.max' hBad := by
      simp [muCrit, Bad, hBad]
    by_contra hApos
    have hAle : Ahat α β γ 1 1 e ≤ 0 := le_of_not_gt hApos
    have hmemBad : e ∈ Bad := by
      have : e ∈ S ∧ Ahat α β γ 1 1 e ≤ 0 := ⟨heS, hAle⟩
      simpa [Bad] using this
    have h_le_max : e ≤ Bad.max' hBad :=
      Finset.le_max' Bad e hmemBad
    have h_le_muCrit : e ≤ muCrit α β γ S := by
      simpa [hμ] using h_le_max
    exact not_le_of_gt he_gt h_le_muCrit
  ·
    have hμ : muCrit α β γ S = 0 := by
      simp [muCrit, Bad, hBad]
    by_contra hApos
    have hAle : Ahat α β γ 1 1 e ≤ 0 := le_of_not_gt hApos
    have hmemBad : e ∈ Bad := by
      have : e ∈ S ∧ Ahat α β γ 1 1 e ≤ 0 := ⟨heS, hAle⟩
      simpa [Bad] using this
    have : Bad.Nonempty := ⟨e, hmemBad⟩
    exact hBad this

/--
Minimalité (caractère d'infimum) de μ*.
Hypothèses:
- `S ⊆ [0,1]` (fréquences possibles),
- `μ ∈ [0,1]`,
- pour tout `e ∈ S`, si `e ≥ μ` alors `Ahat α β γ 1 1 e > 0`.
Conclusion:
- `muCrit α β γ S ≤ μ`.
-/
lemma muCrit_le_of_good_threshold
    {α β γ : ℚ} {S : Finset ℚ}
    (_ : ∀ e ∈ S, 0 ≤ e ∧ e ≤ 1)
    {μ : ℚ}
    (hμ01 : 0 ≤ μ ∧ μ ≤ 1)
    (hμgood :
      ∀ e ∈ S, e ≥ μ → Ahat α β γ 1 1 e > 0) :
  muCrit α β γ S ≤ μ := by
  classical
  let Bad := S.filter (fun x => Ahat α β γ 1 1 x ≤ 0)
  by_cases hBad : Bad.Nonempty
  ·
    have hμCrit :
        muCrit α β γ S = Bad.max' hBad := by
      simp [muCrit, Bad, hBad]
    by_contra hnot
    have hgt : muCrit α β γ S > μ := lt_of_not_ge hnot
    have hgt_max : Bad.max' hBad > μ := by
      simpa [hμCrit] using hgt
    have hge_max : Bad.max' hBad ≥ μ := le_of_lt hgt_max
    have hmax_mem : Bad.max' hBad ∈ Bad :=
      Finset.max'_mem _ _
    rcases Finset.mem_filter.mp hmax_mem with
      ⟨h_in_S, hAle⟩
    have hApos :=
      hμgood _ h_in_S hge_max
    have hAnonpos :
        ¬ Ahat α β γ 1 1 (Bad.max' hBad) > 0 :=
      not_lt_of_ge hAle
    exact hAnonpos hApos
  ·
    have hμCrit : muCrit α β γ S = 0 := by
      simp [muCrit, Bad, hBad]
    have h0 : 0 ≤ μ := hμ01.left
    simpa [hμCrit] using h0

/--
Seuil "bon" pour la sous-batterie SP :

`goodThreshold α β γ S μ` signifie :

- `0 ≤ μ ≤ 1`, et
- pour tout `e ∈ S`, si `e ≥ μ` alors `Ahat α β γ 1 1 e > 0`.
-/
def goodThreshold (α β γ : ℚ) (S : Finset ℚ) (μ : ℚ) : Prop :=
  0 ≤ μ ∧ μ ≤ 1 ∧
    ∀ e ∈ S, e ≥ μ → Ahat α β γ 1 1 e > 0

/--
`muCrit` est toujours ≥ 0 dès que `S ⊆ [0,1]`.
-/
lemma muCrit_nonneg
    {α β γ : ℚ} {S : Finset ℚ}
    (hS01 : ∀ e ∈ S, 0 ≤ e ∧ e ≤ 1) :
  0 ≤ muCrit α β γ S := by
  classical
  let Bad := S.filter (fun x => Ahat α β γ 1 1 x ≤ 0)
  by_cases hBad : Bad.Nonempty
  ·
    have hμ : muCrit α β γ S = Bad.max' hBad := by
      simp [muCrit, Bad, hBad]
    have hmem : Bad.max' hBad ∈ Bad := Finset.max'_mem _ _
    rcases Finset.mem_filter.mp hmem with ⟨hS, _hA⟩
    have h0 : 0 ≤ (Bad.max' hBad) := (hS01 _ hS).1
    simpa [hμ] using h0
  ·
    have hμ : muCrit α β γ S = 0 := by
      simp [muCrit, Bad, hBad]
    simp [hμ]

/--
Caractérisation "infimum discret" de `muCrit`.
-/
theorem muCrit_inf_characterization
    {α β γ : ℚ} {S : Finset ℚ}
    (hS01 : ∀ e ∈ S, 0 ≤ e ∧ e ≤ 1) :
  (∀ μ, goodThreshold α β γ S μ → muCrit α β γ S ≤ μ)
  ∧ (∀ μ, muCrit α β γ S < μ → μ ≤ 1 → goodThreshold α β γ S μ) := by
  classical
  constructor
  ·
    intro μ hμ
    refine muCrit_le_of_good_threshold
      (α := α) (β := β) (γ := γ) (S := S)
      hS01
      ?hμ01
      ?hμgood
    · exact ⟨hμ.1, hμ.2.1⟩
    · intro e heS he_ge
      exact hμ.2.2 e heS he_ge
  ·
    intro μ hgt hμ1
    have hμ0 : 0 ≤ μ := by
      have hμCrit0 :=
        muCrit_nonneg (α := α) (β := β) (γ := γ) (S := S) hS01
      exact le_trans hμCrit0 (le_of_lt hgt)
    refine ⟨hμ0, hμ1, ?_⟩
    intro e heS he_ge
    have hgt' : muCrit α β γ S < e :=
      lt_of_lt_of_le hgt he_ge
    exact muCrit_above (α := α) (β := β) (γ := γ) (S := S)
      hS01 e heS hgt'

lemma pCrit_above
    {α β γ : ℚ} {S_P : Finset ℚ}
    (_ : ∀ p ∈ S_P, 0 ≤ p ∧ p ≤ 1) :
  ∀ p ∈ S_P, 1 - p > pCrit α β γ S_P →
    Ahat α β γ p 1 0 > 0 := by
  classical
  intro p hp hgt
  unfold pCrit at hgt
  set B := pBad α β γ S_P with hBdef
  by_cases hB : B.Nonempty
  ·
    have hcrit :
        (if h : B.Nonempty then
          (B.image (fun p => 1 - p)).max'
            (by
              rcases h with ⟨p0, hp0⟩
              exact ⟨1 - p0, mem_image.mpr ⟨p0, hp0, rfl⟩⟩)
        else 0)
        =
        (B.image (fun p => 1 - p)).max'
          (by
            rcases hB with ⟨p0, hp0⟩
            exact ⟨1 - p0, mem_image.mpr ⟨p0, hp0, rfl⟩⟩) := by
      simp [hB]
    have hgt' :
      1 - p >
        (B.image (fun p => 1 - p)).max'
          (by
            rcases hB with ⟨p0, hp0⟩
            exact ⟨1 - p0, mem_image.mpr ⟨p0, hp0, rfl⟩⟩) := by
      rwa [hcrit] at hgt
    by_contra hpos
    have hA : Ahat α β γ p 1 0 ≤ 0 := le_of_not_gt hpos
    have hmemB : p ∈ B := by
      have : p ∈ S_P ∧ Ahat α β γ p 1 0 ≤ 0 := ⟨hp, hA⟩
      simpa [hBdef, pBad] using this
    have hmemImg : 1 - p ∈ B.image (fun p => 1 - p) :=
      mem_image.mpr ⟨p, hmemB, rfl⟩
    have hle :
      1 - p ≤ (B.image (fun p => 1 - p)).max' _ :=
      le_max' _ _ hmemImg
    exact not_le_of_gt hgt' hle
  ·
    have hcrit :
        (if h : B.Nonempty then
          (B.image (fun p => 1 - p)).max'
            (by
              rcases h with ⟨p0, hp0⟩
              exact ⟨1 - p0, mem_image.mpr ⟨p0, hp0, rfl⟩⟩)
        else 0) = (0 : ℚ) := by
      simp [hB]
    have hgt0 : 1 - p > 0 := by
      rwa [hcrit] at hgt
    by_contra hpos
    have hA : Ahat α β γ p 1 0 ≤ 0 := le_of_not_gt hpos
    have hmemB : p ∈ B := by
      have : p ∈ S_P ∧ Ahat α β γ p 1 0 ≤ 0 := ⟨hp, hA⟩
      simpa [hBdef, pBad] using this
    exact hB ⟨p, hmemB⟩

lemma kCrit_above
    {α β γ : ℚ} {S_K : Finset ℚ}
    (_ : ∀ k ∈ S_K, 0 ≤ k ∧ k ≤ 1) :
  ∀ k ∈ S_K, 1 - k > kCrit α β γ S_K →
    Ahat α β γ 1 k 0 > 0 := by
  classical
  intro k hk hgt
  unfold kCrit at hgt
  set B := kBad α β γ S_K with hBdef
  by_cases hB : B.Nonempty
  ·
    have hcrit :
        (if h : B.Nonempty then
          (B.image (fun k => 1 - k)).max'
            (by
              rcases h with ⟨k0, hk0⟩
              exact ⟨1 - k0, mem_image.mpr ⟨k0, hk0, rfl⟩⟩)
        else 0)
        =
        (B.image (fun k => 1 - k)).max'
          (by
            rcases hB with ⟨k0, hk0⟩
            exact ⟨1 - k0, mem_image.mpr ⟨k0, hk0, rfl⟩⟩) := by
      simp [hB]
    have hgt' :
      1 - k >
        (B.image (fun k => 1 - k)).max'
          (by
            rcases hB with ⟨k0, hk0⟩
            exact ⟨1 - k0, mem_image.mpr ⟨k0, hk0, rfl⟩⟩) := by
      rwa [hcrit] at hgt
    by_contra hpos
    have hA : Ahat α β γ 1 k 0 ≤ 0 := le_of_not_gt hpos
    have hmemB : k ∈ B := by
      have : k ∈ S_K ∧ Ahat α β γ 1 k 0 ≤ 0 := ⟨hk, hA⟩
      simpa [hBdef, kBad] using this
    have hmemImg : 1 - k ∈ B.image (fun k => 1 - k) :=
      mem_image.mpr ⟨k, hmemB, rfl⟩
    have hle :
      1 - k ≤ (B.image (fun k => 1 - k)).max' _ :=
      le_max' _ _ hmemImg
    exact not_le_of_gt hgt' hle
  ·
    have hcrit :
        (if h : B.Nonempty then
          (B.image (fun k => 1 - k)).max'
            (by
              rcases h with ⟨k0, hk0⟩
              exact ⟨1 - k0, mem_image.mpr ⟨k0, hk0, rfl⟩⟩)
        else 0) = (0 : ℚ) := by
      simp [hB]
    have hgt0 : 1 - k > 0 := by
      rwa [hcrit] at hgt
    by_contra hpos
    have hA : Ahat α β γ 1 k 0 ≤ 0 := le_of_not_gt hpos
    have hmemB : k ∈ B := by
      have : k ∈ S_K ∧ Ahat α β γ 1 k 0 ≤ 0 := ⟨hk, hA⟩
      simpa [hBdef, kBad] using this
    exact hB ⟨k, hmemB⟩

/-- Taux critique global fort (OR) : max des trois seuils.
-/
def tauCritMax (α β γ : ℚ)
    (S_P S_K S_E : Finset ℚ) : ℚ :=
  max (pCrit α β γ S_P)
      (max (kCrit α β γ S_K) (muCrit α β γ S_E))

lemma Ahat_split_p
    (α β γ p k e : ℚ) :
    Ahat α β γ p k e =
      Ahat α β γ p 1 0 + (β * (1 - k) + γ * e) := by
  unfold Ahat
  simp [add_left_comm, add_comm]

lemma Ahat_split_k
    (α β γ p k e : ℚ) :
    Ahat α β γ p k e =
      Ahat α β γ 1 k 0 + (α * (1 - p) + γ * e) := by
  unfold Ahat
  simp [add_assoc, add_comm]

lemma Ahat_split_e
    (α β γ p k e : ℚ) :
    Ahat α β γ p k e =
      Ahat α β γ 1 1 e + (α * (1 - p) + β * (1 - k)) := by
  unfold Ahat
  simp [add_comm]

lemma tauCritMax_forces_pos
    {α β γ : ℚ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    {S_P S_K S_E : Finset ℚ}
    (hS_P : ∀ p ∈ S_P, 0 ≤ p ∧ p ≤ 1)
    (hS_K : ∀ k ∈ S_K, 0 ≤ k ∧ k ≤ 1)
    (hS_E : ∀ e ∈ S_E, 0 ≤ e ∧ e ≤ 1)
    {p_hat k_hat e_hat : ℚ}
    (hp : p_hat ∈ S_P)
    (hk : k_hat ∈ S_K)
    (he : e_hat ∈ S_E)
    (h_exceed :
        (1 - p_hat) > tauCritMax α β γ S_P S_K S_E ∨
        (1 - k_hat) > tauCritMax α β γ S_P S_K S_E ∨
        e_hat > tauCritMax α β γ S_P S_K S_E) :
    Ahat α β γ p_hat k_hat e_hat > 0 := by
  classical
  have hp01 := hS_P _ hp
  have hk01 := hS_K _ hk
  have he01 := hS_E _ he
  have h1p_nonneg : 0 ≤ 1 - p_hat := sub_nonneg.mpr hp01.2
  have h1k_nonneg : 0 ≤ 1 - k_hat := sub_nonneg.mpr hk01.2
  have he_nonneg  : 0 ≤ e_hat      := he01.1

  let τP := pCrit α β γ S_P
  let τK := kCrit α β γ S_K
  let τE := muCrit α β γ S_E
  have hτ :
      tauCritMax α β γ S_P S_K S_E =
      max τP (max τK τE) := rfl

  rcases h_exceed with hP | hrest
  · have h1 : max τP (max τK τE) < 1 - p_hat := by
      simpa [hτ] using hP
    have hge : τP ≤ max τP (max τK τE) := le_max_left _ _
    have hP' : 1 - p_hat > τP := by
      exact lt_of_le_of_lt hge h1
    have hA_p :
      Ahat α β γ p_hat 1 0 > 0 :=
      pCrit_above (α := α) (β := β) (γ := γ)
        (S_P := S_P) hS_P p_hat hp hP'
    have h_extra_nonneg :
      0 ≤ β * (1 - k_hat) + γ * e_hat :=
      add_nonneg
        (mul_nonneg (le_of_lt hβ) h1k_nonneg)
        (mul_nonneg (le_of_lt hγ) he_nonneg)
    have hdecomp :=
      Ahat_split_p α β γ p_hat k_hat e_hat
    have hpos :=
      add_pos_of_pos_of_nonneg hA_p h_extra_nonneg
    simpa [hdecomp] using hpos

  · rcases hrest with hK | hE
    · have h1 : max τP (max τK τE) < 1 - k_hat := by
        simpa [hτ] using hK
      have hA : max τP (max τK τE) ≥ max τK τE :=
        le_max_right _ _
      have hB : max τK τE ≥ τK :=
        le_max_left _ _
      have hge : τK ≤ max τP (max τK τE) :=
        le_trans hB hA
      have hK' : 1 - k_hat > τK := by
        exact lt_of_le_of_lt hge h1
      have hA_k :
        Ahat α β γ 1 k_hat 0 > 0 :=
        kCrit_above (α := α) (β := β) (γ := γ)
          (S_K := S_K) hS_K k_hat hk hK'
      have h_extra_nonneg :
        0 ≤ α * (1 - p_hat) + γ * e_hat :=
        add_nonneg
          (mul_nonneg (le_of_lt hα) h1p_nonneg)
          (mul_nonneg (le_of_lt hγ) he_nonneg)
      have hdecomp :=
        Ahat_split_k α β γ p_hat k_hat e_hat
      have hpos :=
        add_pos_of_pos_of_nonneg hA_k h_extra_nonneg
      simpa [hdecomp] using hpos

    · have h1 : max τP (max τK τE) < e_hat := by
        simpa [hτ] using hE
      have hA : max τP (max τK τE) ≥ max τK τE :=
        le_max_right _ _
      have hB : max τK τE ≥ τE :=
        le_max_right _ _
      have hge : τE ≤ max τP (max τK τE) :=
        le_trans hB hA
      have hE' : e_hat > τE := by
        exact lt_of_le_of_lt hge h1
      have hA_e :
        Ahat α β γ 1 1 e_hat > 0 :=
        muCrit_above (α := α) (β := β) (γ := γ)
          (S := S_E) hS_E e_hat he hE'
      have h_extra_nonneg :
        0 ≤ α * (1 - p_hat) + β * (1 - k_hat) :=
        add_nonneg
          (mul_nonneg (le_of_lt hα) h1p_nonneg)
          (mul_nonneg (le_of_lt hβ) h1k_nonneg)
      have hdecomp :=
        Ahat_split_e α β γ p_hat k_hat e_hat
      have hpos :=
        add_pos_of_pos_of_nonneg hA_e h_extra_nonneg
      simpa [hdecomp] using hpos

end LogicDissoc
