import Mathlib.Data.Finset.Basic
import LogicDissoc.BasicSemantics
import LogicDissoc.ObstructionGen
import LogicDissoc.Legit

namespace LogicDissoc

open Finset

section

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)

variable {B : Type*} [Fintype B] [DecidableEq B]

variable (Γ_ref : Set Sentence)

/-- Batteries finies de formules. -/
abbrev Battery (Sentence : Type*) := Finset Sentence

/-- Extension conservative de `Γ_ref` par une batterie finie `S`.
-/
def conservativeExt (S : Battery Sentence) : Prop :=
  ModE Sat (Γ_ref ∪ (↑S : Set Sentence)) = ModE Sat Γ_ref

variable (Count : Battery Sentence → GenCounters B)

/--
Axiome de correction du protocole de comptage :

Le profil nul (toutes composantes à 0) est équivalent
à la conservativité sémantique de l'extension.
-/
class CountSpec : Prop where
  sound :
    ∀ S : Battery Sentence,
      (∀ b, (Count S).v b = 0) ↔
        conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S

variable (L : LegitObstruction B)

/-- Indice général associé à `L` et au protocole `Count`.
-/
def AstarGen (S : Battery Sentence) : ℝ :=
  L.O.F (Count S)

/--
Théorème Meta-Gödel (frontière conservative) :

Pour toute batterie finie `S`, sous `CountSpec` :

`AstarGen L Count S = 0`
iff
`ModE(Γ_ref ∪ S) = ModE(Γ_ref)`.
Autrement dit, toute fonctionnelle légitime découpe
exactement la même frontière conservative / non-conservative.
-/
theorem metaGodel_frontier_zero
    [CountSpec (Sat := Sat) (Γ_ref := Γ_ref) (Count := Count)]
    (S : Battery Sentence) :
  AstarGen (Count := Count) (L := L) S = 0
    ↔ conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S := by
  unfold AstarGen
  have h0 :=
    LegitObstruction.zero_iff_all_zero (L := L) (c := Count S)
  have h1 :=
    CountSpec.sound (Sat := Sat) (Γ_ref := Γ_ref) (Count := Count) S
  exact h0.trans h1


/--
Version "non-zéro" :

Sous les mêmes hypothèses,

`AstarGen L Count S ≠ 0`
iff
`ModE(Γ_ref ∪ S) ≠ ModE(Γ_ref)`.

Le verdict 0 / non-0 est donc invariant par le choix
de la fonction d'obstruction légitime dans le cône linéaire positif.
-/
theorem metaGodel_frontier_nonzero
    [CountSpec (Sat := Sat) (Γ_ref := Γ_ref) (Count := Count)]
    (S : Battery Sentence) :
  AstarGen (Count := Count) (L := L) S ≠ 0
    ↔ ¬ conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S := by
  have h :=
    metaGodel_frontier_zero
      (Sat := Sat) (Γ_ref := Γ_ref)
      (Count := Count) (L := L) S
  constructor
  · intro hne hcons
    exact hne (h.mpr hcons)
  · intro hnot hEq0
    exact hnot (h.mp hEq0)

/-- `AstarGen` est toujours ≥ 0 pour une obstruction légitime.
-/
lemma AstarGen_nonneg (S : Battery Sentence) :
  0 ≤ AstarGen (Count := Count) (L := L) S := by
  unfold AstarGen
  exact LegitObstruction.F_nonneg (L := L) (c := Count S)

/-- Version forte du méta-théorème :
`AstarGen > 0` ssi l’extension n’est pas conservative.
-/
theorem metaGodel_frontier_pos
  [CountSpec (Sat := Sat) (Γ_ref := Γ_ref) (Count := Count)]
  (S : Battery Sentence) :
  0 < AstarGen (Count := Count) (L := L) S
    ↔ ¬ conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S := by
  have h_nonneg :
    0 ≤ AstarGen (Count := Count) (L := L) S :=
    AstarGen_nonneg (Count := Count) (L := L) S
  have h_ne :
    AstarGen (Count := Count) (L := L) S ≠ 0
      ↔ ¬ conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S :=
    metaGodel_frontier_nonzero
      (Sat := Sat) (Γ_ref := Γ_ref)
      (Count := Count) (L := L) S
  constructor
  · intro hpos
    exact h_ne.mp (ne_of_gt hpos)
  · intro hnot
    have hne := h_ne.mpr hnot
    exact lt_of_le_of_ne h_nonneg hne.symm

end

end LogicDissoc