import LogicDissoc.RefSystem
import LogicDissoc.ObstructionGen
import LogicDissoc.Legit
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace LogicDissoc

open scoped BigOperators
open Finset

universe u v w

namespace RefSystem

variable {Model : Type u} {Sentence : Type v}
variable (E : RefSystem Model Sentence)
variable {B : Type w} [Fintype B] [DecidableEq B]

/--
Axiomes d'une obstruction canonique construite à partir d'un système
de référence `E` et d'une batterie de tests non locaux `probe : B → Sentence`.

Intuition : chaque type `b` est pondéré par `δ (probe b)`, et l'obstruction
d'un profil `c` est la somme des contributions `(c.v b) * δ (probe b)`.
-/
def deltaObstructionAxioms
    (probe : B → Sentence)
    (h_nonlocal : ∀ b, E.isNonlocal (probe b)) :
    ObstructionAxiomsGen B :=
{ F := fun c =>
    ∑ b ∈ (Finset.univ : Finset B),
      (c.v b : ℝ) * E.delta (probe b),
  f := fun b n => (n : ℝ) * E.delta (probe b),
  hF := by
    -- Par définition, F c est déjà la somme de `f b (c.v b)` sur `univ`.
    intro c
    classical
    rfl,
  f0 := by
    intro b
    -- f b 0 = 0 * δ(probe b) = 0
    simp,
  f_pos := by
    intro b n hn
    -- On utilise le fait que `probe b` est non locale pour obtenir δ > 0
    have hband :
        1 ≤ E.delta (probe b) ∧ E.delta (probe b) < 2 :=
      (E.nonlocal_iff_delta_band (probe b)).1 (h_nonlocal b)
    have hδ_pos : 0 < E.delta (probe b) := by
      have h1_pos : (0 : ℝ) < 1 := zero_lt_one
      exact lt_of_lt_of_le h1_pos hband.left
    -- et `0 < n` ⇒ `0 < (n : ℝ)`
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    -- donc le produit est strictement positif
    have := mul_pos hnR hδ_pos
    simpa using this,
  f_add := by
    intro b m n
    -- f b (m + n) = (m + n) * δ = m*δ + n*δ = f b m + f b n
    simp [Nat.cast_add, add_mul] }

/--
Obstruction légitime canonique associée à `E` et à une batterie
de tests non locaux `probe : B → Sentence`.
-/
def deltaObstruction
    (probe : B → Sentence)
    (h_nonlocal : ∀ b, E.isNonlocal (probe b)) :
    LegitObstruction B :=
  ⟨E.deltaObstructionAxioms probe h_nonlocal⟩

/--
Forme explicite de l'obstruction canonique : pour tout profil `c`,
`F c = ∑_b (c.v b) * δ (probe b)`.
-/
lemma deltaObstruction_F
    (probe : B → Sentence)
    (h_nonlocal : ∀ b, E.isNonlocal (probe b))
    (c : GenCounters B) :
  (E.deltaObstruction probe h_nonlocal).O.F c =
    ∑ b ∈ (Finset.univ : Finset B),
      (c.v b : ℝ) * E.delta (probe b) := by
  -- C'est par définition même de `deltaObstructionAxioms.F`.
  rfl

end RefSystem

end LogicDissoc
