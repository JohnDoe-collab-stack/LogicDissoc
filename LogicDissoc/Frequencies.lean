import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finprod

namespace LogicDissoc

open scoped BigOperators
open Finset

/--
Fréquence de succès (valeurs `true`) sur un type fini.
Totale et calculable:
- si `Fintype.card ι = 0` alors `0`,
- sinon (# {i | v i = true}) / (#ι) dans ℚ.
-/
def freqTrue {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → Bool) : ℚ :=
  if _ : Fintype.card ι = 0 then 0
  else ((univ.filter (fun i => v i = true)).card : ℚ) / (Fintype.card ι : ℚ)

/-- Fréquence d’échec correspondante.
-/
def freqFalse {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → Bool) : ℚ :=
  1 - freqTrue v

/-- Formule explicite de `freqTrue` quand la batterie est non vide.
-/
lemma freqTrue_eq_of_nonempty
    {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : ι → Bool) :
  freqTrue v =
    ((univ.filter (fun i => v i = true)).card : ℚ) / (Fintype.card ι : ℚ) := by
  unfold freqTrue
  have hpos : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hne : Fintype.card ι ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hpos
  simp [hne]

lemma freqTrue_nonneg
    {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : ι → Bool) :
  0 ≤ freqTrue v := by
  have hpos_nat : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hpos : (0 : ℚ) < (Fintype.card ι : ℚ) := by
    exact_mod_cast hpos_nat
  have hnum :
      0 ≤ ((univ.filter (fun i => v i = true)).card : ℚ) := by
    exact_mod_cast (Nat.zero_le _)
  have h := div_nonneg hnum (le_of_lt hpos)
  simpa [freqTrue_eq_of_nonempty (v := v)] using h

lemma freqTrue_le_one
    {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : ι → Bool) :
  freqTrue v ≤ 1 := by
  have hpos_nat : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hpos : (0 : ℚ) < (Fintype.card ι : ℚ) := by
    exact_mod_cast hpos_nat
  have hden_ne : (Fintype.card ι : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos_nat)

  have hle_nat :
      (univ.filter (fun i => v i = true)).card
        ≤ (univ : Finset ι).card := by
    simpa using
      (Finset.card_filter_le
        (s := (univ : Finset ι))
        (p := fun i => v i = true))

  have hle :
      ((univ.filter (fun i => v i = true)).card : ℚ)
        ≤ (Fintype.card ι : ℚ) := by
    simpa [Finset.card_univ] using
      (show
        ((univ.filter (fun i => v i = true)).card : ℚ)
          ≤ ((univ : Finset ι).card : ℚ) from
        by exact_mod_cast hle_nat)

  have hinv_pos : (0 : ℚ) < 1 / (Fintype.card ι : ℚ) := by
    have := inv_pos.mpr hpos
    simpa [one_div] using this
  have hinv_nonneg : 0 ≤ 1 / (Fintype.card ι : ℚ) :=
    le_of_lt hinv_pos

  have hbound_mul :
      ((univ.filter (fun i => v i = true)).card : ℚ)
        * (1 / (Fintype.card ι : ℚ))
      ≤ (Fintype.card ι : ℚ) * (1 / (Fintype.card ι : ℚ)) :=
    mul_le_mul_of_nonneg_right hle hinv_nonneg

  have hbound :
      ((univ.filter (fun i => v i = true)).card : ℚ) /
        (Fintype.card ι : ℚ)
      ≤ 1 := by
    simpa [div_eq_mul_inv, one_div, hden_ne] using hbound_mul

  have hf := freqTrue_eq_of_nonempty (v := v)
  simpa [hf] using hbound


lemma freqFalse_nonneg
    {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : ι → Bool) :
  0 ≤ freqFalse v := by
  unfold freqFalse
  have h1 := freqTrue_le_one (v := v)
  exact sub_nonneg.mpr h1


lemma freqFalse_le_one
    {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : ι → Bool) :
  freqFalse v ≤ 1 := by
  unfold freqFalse
  have h0 := freqTrue_nonneg (v := v)
  have hneg : -(freqTrue v) ≤ 0 := neg_nonpos.mpr h0
  have h := add_le_add_left hneg 1
  simpa [sub_eq_add_neg] using h


/-- Version empirique de A⋆ en fonction des fréquences.
-/
def Ahat (α β γ p_hat k_hat e_hat : ℚ) : ℚ :=
  α * (1 - p_hat) + β * (1 - k_hat) + γ * e_hat

end LogicDissoc
