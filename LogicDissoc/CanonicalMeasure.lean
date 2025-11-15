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
  have hne : (Fintype.card ι : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty ι›).ne'
  simp [freqTrue_eq_of_nonempty, Finset.card_univ]


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
  have hne : (Fintype.card (L Γ) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty (L Γ)›).ne'
  simp [Q_pointMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
end LinExtSystem

end LogicDissoc
