import LogicDissoc.ObstructionGen
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace LogicDissoc

open scoped BigOperators
open Finset

/--
A "legitimate" obstruction function on `B`:
exactly an instance of the abstract axioms `ObstructionAxiomsGen`.

Interpretation:
- every structurally admissible obstruction measure lives in this scheme;
- the lemmas below make explicit that this class is a positive linear cone;
- A⋆ is a particular instantiation (choice of coefficients) of this cone;
- the freedom on the coefficients is a renormalization, not a different geometry.
-/
structure LegitObstruction (B : Type*) [Fintype B] [DecidableEq B] where
  O : ObstructionAxiomsGen B

namespace LegitObstruction

variable {B : Type*} [Fintype B] [DecidableEq B]

/--
Canonical linear representation:

Every legitimate obstruction function is a positive linear form
on the counters `GenCounters B`.

More precisely, there exists `α : B → ℝ` with `α b > 0` such that
`F c = ∑_{b ∈ univ} (c.v b) * α b` for every profile `c`.
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
Exact kernel:

For a legitimate obstruction function, vanishing is equivalent
to the complete absence of obstruction:

`F c = 0` iff `c.v b = 0` for every `b`.
-/
theorem zero_iff_all_zero (L : LegitObstruction B) (c : GenCounters B) :
  L.O.F c = 0 ↔ ∀ b, c.v b = 0 := by
  simpa using (ObstructionAxiomsGen.zero_iff_all_zero (O := L.O) (c := c))

/-- Every legitimate obstruction function is ≥ 0 on every profile. -/
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
