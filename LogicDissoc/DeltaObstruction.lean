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
Axioms of a canonical obstruction built from a reference system `E`
and a family of non-local tests `probe : B → Sentence`.

Intuition: each type `b` is weighted by `δ (probe b)`, and the obstruction
of a profile `c` is the sum of the contributions `(c.v b) * δ (probe b)`.
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
    -- By definition, F c is already the sum of `f b (c.v b)` over `univ`.
    intro c
    classical
    rfl,
  f0 := by
    intro b
    -- f b 0 = 0 * δ(probe b) = 0
    simp,
  f_pos := by
    intro b n hn
    -- We use that `probe b` is non-local to get δ > 0
    have hband :
        1 ≤ E.delta (probe b) ∧ E.delta (probe b) < 2 :=
      (E.nonlocal_iff_delta_band (probe b)).1 (h_nonlocal b)
    have hδ_pos : 0 < E.delta (probe b) := by
      have h1_pos : (0 : ℝ) < 1 := zero_lt_one
      exact lt_of_lt_of_le h1_pos hband.left
    -- and `0 < n` ⇒ `0 < (n : ℝ)`
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    -- hence the product is strictly positive
    have := mul_pos hnR hδ_pos
    simpa using this,
  f_add := by
    intro b m n
    -- f b (m + n) = (m + n) * δ = m*δ + n*δ = f b m + f b n
    simp [Nat.cast_add, add_mul] }

/--
Canonical legitimate obstruction associated with `E` and a family
of non-local tests `probe : B → Sentence`.
-/
def deltaObstruction
    (probe : B → Sentence)
    (h_nonlocal : ∀ b, E.isNonlocal (probe b)) :
    LegitObstruction B :=
  ⟨E.deltaObstructionAxioms probe h_nonlocal⟩

/--
Explicit form of the canonical obstruction: for every profile `c`,
`F c = ∑_b (c.v b) * δ (probe b)`.
-/
lemma deltaObstruction_F
    (probe : B → Sentence)
    (h_nonlocal : ∀ b, E.isNonlocal (probe b))
    (c : GenCounters B) :
  (E.deltaObstruction probe h_nonlocal).O.F c =
    ∑ b ∈ (Finset.univ : Finset B),
      (c.v b : ℝ) * E.delta (probe b) := by
  -- This is exactly by definition of `deltaObstructionAxioms.F`.
  rfl

end RefSystem

end LogicDissoc
