import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import LogicDissoc.Frequencies

namespace LogicDissoc

open scoped BigOperators
open Finset

universe u v

/-
  Petite brique utilitaire : fréquence de la constante `true`.
  On la prouve ici pour pouvoir s’en servir dans tout système de contextes finis.
-/
lemma freqTrue_const_true
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
  freqTrue (fun _ : ι => true) = 1 := by
  classical
  -- Formule explicite de freqTrue sur un type non vide
  have h := freqTrue_eq_of_nonempty (v := fun _ : ι => true)
  -- La filtration par le prédicat `v i = true` est simplement tout `univ`
  have hfilter :
    ((univ.filter (fun i : ι => (fun _ : ι => true) i = true)).card : ℚ)
      = (Fintype.card ι : ℚ) := by
    have hset :
      (univ.filter (fun i : ι => (fun _ : ι => true) i = true))
        = (univ : Finset ι) := by
      -- Tout élément passe le filtre
      ext i
      simp
    simp [Finset.card_univ]
  -- Denominateur non nul puisque le type est non vide
  have hpos_nat : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hpos : (0 : ℚ) < (Fintype.card ι : ℚ) := by
    exact_mod_cast hpos_nat
  have hne : (Fintype.card ι : ℚ) ≠ 0 := ne_of_gt hpos
  -- Conclusion : (#ι)/#ι = 1
  calc
    freqTrue (fun _ : ι => true)
        = ((univ.filter (fun i : ι => (fun _ : ι => true) i = true)).card : ℚ) /
          (Fintype.card ι : ℚ) := h
    _ = (Fintype.card ι : ℚ) / (Fintype.card ι : ℚ) := by
      simpa [hfilter]
    _ = 1 := by
      exact div_self hne


/--
Système abstrait de contextes SLE:
- `Context` : type des contextes Γ,
- `Lext Γ` : type fini des extensions linéaires associées.
On exige aussi une égalité décidable sur chaque `Lext Γ`, pour pouvoir compter.
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

/-- Abréviation pour le type des extensions linéaires d’un contexte Γ. -/
abbrev L (Γ : S.Context) := S.Lext Γ

/--
Mesure canonique Q{Γ} vue comme opérateur d'espérance
sur des observables booléennes `Φ : L(Γ) → Bool`:
on utilise simplement `freqTrue` de `Frequencies.lean`.
-/
def Q_expectation (Γ : S.Context) (Φ : L Γ → Bool) : ℚ :=
  freqTrue (v := Φ)

/-- En particulier, l'espérance de la constante `True` vaut 1 si `L Γ` est non vide. -/
lemma Q_expectation_top (Γ : S.Context) [Nonempty (L Γ)] :
  Q_expectation (S := S) Γ (fun _ => true) = 1 := by
  -- C’est exactement `freqTrue_const_true` appliqué à `ι := L Γ`.
  simpa [Q_expectation] using
    (freqTrue_const_true (ι := L Γ))

/--
Masse ponctuelle uniforme Q{Γ}(lex) sur `L Γ`.
Pour les contextes non vides, la somme des masses vaut 1.
-/
def Q_pointMass (Γ : S.Context) (_ : L Γ) : ℚ :=
  1 / (Fintype.card (L Γ) : ℚ)

/-- La somme des masses ponctuelles vaut 1 dès que `L Γ` est non vide. -/
lemma Q_pointMass_sum (Γ : S.Context) [Nonempty (L Γ)] :
  ∑ lex : L Γ, Q_pointMass (S := S) Γ lex = 1 := by
  classical
  -- Déplier la définition : somme d’une constante
  have h1 :
      ∑ lex : L Γ, Q_pointMass (S := S) Γ lex
        = ∑ _ : L Γ, (1 / (Fintype.card (L Γ) : ℚ)) := by
    simp [Q_pointMass]
  -- Somme d’une constante sur un type fini = card • constante
  have h2 :
      ∑ _ : L Γ, (1 / (Fintype.card (L Γ) : ℚ))
        = (Fintype.card (L Γ)) • (1 / (Fintype.card (L Γ) : ℚ)) := by
    -- `∑ x : L Γ,` est par définition la somme sur `Finset.univ`
    simpa using
      (Finset.sum_const
        (a := (1 / (Fintype.card (L Γ) : ℚ)))
        (s := (Finset.univ : Finset (L Γ))))
  -- Denominateur strictement positif (type non vide)
  have hpos_nat : 0 < Fintype.card (L Γ) :=
    Fintype.card_pos_iff.mpr ‹Nonempty (L Γ)›
  have hpos : (0 : ℚ) < (Fintype.card (L Γ) : ℚ) := by
    exact_mod_cast hpos_nat
  have hne : (Fintype.card (L Γ) : ℚ) ≠ 0 := ne_of_gt hpos
  -- On passe de `•` à la multiplication dans ℚ
  have h3 :
      (Fintype.card (L Γ)) • (1 / (Fintype.card (L Γ) : ℚ))
        = (Fintype.card (L Γ) : ℚ) * (1 / (Fintype.card (L Γ) : ℚ)) := by
    -- Dans un anneau, `n • r = (n : ℚ) * r`
    simp [nsmul_eq_mul]
  -- Et finalement (#Γ) * (1/#Γ) = 1
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
