import LogicDissoc.ObstructionGen
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace LogicDissoc

open scoped BigOperators
open Finset

/--
Une fonction d'obstruction "légitime" sur `B` :
exactement une instance des axiomes abstraits `ObstructionAxiomsGen`.
Interprétation :
- toute mesure d'obstruction admissible au sens structurel vit dans ce schéma.
- les lemmes ci-dessous rendent explicite que cette classe est un cône linéaire positif.
- A⋆ est une instanciation particulière (choix de coefficients) de ce cône.
- la liberté sur les coefficients est une renormalisation, pas une autre géométrie.
-/
structure LegitObstruction (B : Type*) [Fintype B] [DecidableEq B] where
  O : ObstructionAxiomsGen B

namespace LegitObstruction

variable {B : Type*} [Fintype B] [DecidableEq B]

/--
Représentation linéaire canonique :

Toute fonction d'obstruction légitime est une forme linéaire positive
sur les compteurs `GenCounters B`.
Plus précisément, il existe `α : B → ℝ` avec `α b > 0` tel que
`F c = ∑_{b ∈ univ} (c.v b) * α b` pour tout profil `c`.
-/
theorem linear_repr (L : LegitObstruction B) :
  ∃ α : B → ℝ,
    (∀ b, 0 < α b) ∧
    ∀ c : GenCounters B,
      L.O.F c =
        ∑ b ∈ (Finset.univ : Finset B),
          (c.v b : ℝ) * α b := by
  refine ⟨(fun b => L.O.α b), ?_, ?_⟩
  · intro b
    exact L.O.α_pos b
  · intro c
    simpa using L.O.canonical c

/--
Noyau exact :

Pour une fonction d'obstruction légitime, l'annulation est équivalente
à l'absence totale d'obstruction :

`F c = 0` ssi `c.v b = 0` pour tout `b`.
-/
theorem zero_iff_all_zero (L : LegitObstruction B) (c : GenCounters B) :
  L.O.F c = 0 ↔ ∀ b, c.v b = 0 := by
  simpa using (ObstructionAxiomsGen.zero_iff_all_zero (O := L.O) (c := c))

/-- Toute fonction d'obstruction légitime est ≥ 0 sur tout profil.
-/
lemma F_nonneg (L : LegitObstruction B) (c : GenCounters B) :
  0 ≤ L.O.F c := by
  classical
  obtain ⟨α, hα_pos, hF⟩ := L.linear_repr
  have hterm_nonneg :
      ∀ b ∈ (Finset.univ : Finset B),
        0 ≤ (c.v b : ℝ) * α b := by
    intro b hb
    have hcv : 0 ≤ (c.v b : ℝ) := by
      exact_mod_cast Nat.zero_le (c.v b)
    exact mul_nonneg hcv (le_of_lt (hα_pos b))
  have hsum_nonneg :
      0 ≤ ∑ b ∈ (Finset.univ : Finset B),
              (c.v b : ℝ) * α b :=
    Finset.sum_nonneg (by
      intro b hb
      exact hterm_nonneg b hb)
  simpa [hF c] using hsum_nonneg

end LegitObstruction

end LogicDissoc
