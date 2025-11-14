import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import LogicDissoc.Frequencies

namespace LogicDissoc

open scoped BigOperators
open Finset

universe u v

/-
  Small utility building block: frequency of the constant `true`.
  We prove it here so that we can use it in any system of finite contexts.
-/
lemma freqTrue_const_true
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
  freqTrue (fun _ : ι => true) = 1 := by
  classical
  -- Explicit formula for freqTrue on a nonempty type
  have h := freqTrue_eq_of_nonempty (v := fun _ : ι => true)
  -- The filtering by the predicate `v i = true` is simply the whole `univ`
  have hfilter :
    ((univ.filter (fun i : ι => (fun _ : ι => true) i = true)).card : ℚ)
      = (Fintype.card ι : ℚ) := by
    have hset :
      (univ.filter (fun i : ι => (fun _ : ι => true) i = true))
        = (univ : Finset ι) := by
      -- Every element passes the filter
      ext i
      simp
    simp [Finset.card_univ]
  -- Denominator is nonzero since the type is nonempty
  have hpos_nat : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hpos : (0 : ℚ) < (Fintype.card ι : ℚ) := by
    exact_mod_cast hpos_nat
  have hne : (Fintype.card ι : ℚ) ≠ 0 := ne_of_gt hpos
  -- Conclusion: (#ι)/#ι = 1
  calc
    freqTrue (fun _ : ι => true)
        = ((univ.filter (fun i : ι => (fun _ : ι => true) i = true)).card : ℚ) /
          (Fintype.card ι : ℚ) := h
    _ = (Fintype.card ι : ℚ) / (Fintype.card ι : ℚ) := by
      simpa [hfilter]
    _ = 1 := by
      exact div_self hne


/--
Abstract system of SLE contexts:
- `Context` : type of contexts Γ,
- `Lext Γ` : finite type of associated linear extensions.
We also require decidable equality on each `Lext Γ` in order to count.
-/
structure LinExtSystem where
  Context : Type u
  Lext    : Context → Type v
  fintypeLext      : ∀ Γ : Context, Fintype (Lext Γ)
  decidableEqLext  : ∀ Γ : Context, DecidableEq (Lext Γ)

attribute [instance] LinExtSystem.fintypeLext
attribute [instance] LinExtSystem.decidableEqLext

namespace LinExtSystem

variable {S : LinExtSystem}

/-- Abbreviation for the type of linear extensions of a context Γ. -/
abbrev L (Γ : S.Context) := S.Lext Γ

/--
Canonical measure Q{Γ} seen as an expectation operator
on Boolean observables `Φ : L(Γ) → Bool`:
we simply use `freqTrue` from `Frequencies.lean`.
-/
def Q_expectation (Γ : S.Context) (Φ : L Γ → Bool) : ℚ :=
  freqTrue (v := Φ)

/-- In particular, the expectation of the constant `True` is 1 if `L Γ` is nonempty. -/
lemma Q_expectation_top (Γ : S.Context) [Nonempty (L Γ)] :
  Q_expectation (S := S) Γ (fun _ => true) = 1 := by
  -- This is exactly `freqTrue_const_true` applied to `ι := L Γ`.
  simpa [Q_expectation] using
    (freqTrue_const_true (ι := L Γ))

/--
Uniform point mass Q{Γ}(lex) on `L Γ`.
For nonempty contexts, the sum of the masses is 1.
-/
def Q_pointMass (Γ : S.Context) (_ : L Γ) : ℚ :=
  1 / (Fintype.card (L Γ) : ℚ)

/-- The sum of the point masses is 1 as soon as `L Γ` is nonempty. -/
lemma Q_pointMass_sum (Γ : S.Context) [Nonempty (L Γ)] :
  ∑ lex : L Γ, Q_pointMass (S := S) Γ lex = 1 := by
  classical
  -- Unfold the definition: sum of a constant
  have h1 :
      ∑ lex : L Γ, Q_pointMass (S := S) Γ lex
        = ∑ _ : L Γ, (1 / (Fintype.card (L Γ) : ℚ)) := by
    simp [Q_pointMass]
  -- Sum of a constant over a finite type = card • constant
  have h2 :
      ∑ _ : L Γ, (1 / (Fintype.card (L Γ) : ℚ))
        = (Fintype.card (L Γ)) • (1 / (Fintype.card (L Γ) : ℚ)) := by
    -- `∑ x : L Γ,` is by definition the sum over `Finset.univ`
    simpa using
      (Finset.sum_const
        (a := (1 / (Fintype.card (L Γ) : ℚ)))
        (s := (Finset.univ : Finset (L Γ))))
  -- Denominator strictly positive (nonempty type)
  have hpos_nat : 0 < Fintype.card (L Γ) :=
    Fintype.card_pos_iff.mpr ‹Nonempty (L Γ)›
  have hpos : (0 : ℚ) < (Fintype.card (L Γ) : ℚ) := by
    exact_mod_cast hpos_nat
  have hne : (Fintype.card (L Γ) : ℚ) ≠ 0 := ne_of_gt hpos
  -- We move from `•` to multiplication in ℚ
  have h3 :
      (Fintype.card (L Γ)) • (1 / (Fintype.card (L Γ) : ℚ))
        = (Fintype.card (L Γ) : ℚ) * (1 / (Fintype.card (L Γ) : ℚ)) := by
    -- In a ring, `n • r = (n : ℚ) * r`
    simp [nsmul_eq_mul]
  -- And finally (#Γ) * (1/#Γ) = 1
  have h4 :
      (Fintype.card (L Γ) : ℚ) * (1 / (Fintype.card (L Γ) : ℚ)) = 1 := by
    -- `a * (1/a) = 1`, via `div_self`
    simpa [one_div, div_eq_mul_inv] using
      (div_self (a := (Fintype.card (L Γ) : ℚ)) hne)
  calc
    ∑ lex : L Γ, Q_pointMass (S := S) Γ lex
        = ∑ _ : L Γ, (1 / (Fintype.card (L Γ) : ℚ)) := h1
    _ = (Fintype.card (L Γ)) • (1 / (Fintype.card (L Γ) : ℚ)) := h2
    _ = (Fintype.card (L Γ) : ℚ) * (1 / (Fintype.card (L Γ) : ℚ)) := h3
    _ = 1 := h4

end LinExtSystem

end LogicDissoc
