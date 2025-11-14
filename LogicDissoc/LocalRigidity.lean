/-
LogicDissoc/LocalRigidity.lean

Local rigidity of discrete–continuous obstructions.

This file exposes, in a minimal abstract interface, the pattern proved in:
ObstructionGen, Legit.

Given:
- a local semantic system with a counting protocol `Count`
  satisfying `CountSpec : Count(S) = 0 ↔ S` is conservative,
- a legitimate obstruction `L : LegitObstruction B`
  (backed by `ObstructionAxiomsGen`),

the induced score

  score(S) := L.O.F ⟨Count(S)⟩

satisfies

  score(S) = 0    ↔    S is conservative
  score(S) ≠ 0    ↔    S is non-conservative

This is the discrete–continuous bridge used conceptually
for CH, AC, Gödel-dynamic directions, etc.
-/

import LogicDissoc.ObstructionGen
import LogicDissoc.Legit

namespace LogicDissoc

open scoped BigOperators

/-- Local semantic + counting system for the rigidity interface. -/
structure LocalBridgeSystem where
  Sentence : Type _
  Model : Type _
  Sat : Model → Sentence → Prop
  Γref : Set Sentence
  -- Set of models of a theory.
  Mod : Set Sentence → Set Model
  -- Semantic conservativity of a finite batch `S` over `Γref`.
  conservative : Finset Sentence → Prop
  -- Finite set of "types" / "directions" used for counting.
  B : Type _
  [fintypeB : Fintype B]
  [decB : DecidableEq B]
  -- Counting protocol on finite batches.
  Count : Finset Sentence → (B → ℕ)
  -- Specification: Count(S) = 0 iff the extension is conservative.
  CountSpec :
    ∀ S, Count S = (fun _ => 0) ↔ conservative S

attribute [instance] LocalBridgeSystem.fintypeB LocalBridgeSystem.decB

namespace LocalBridgeSystem

variable (LS : LocalBridgeSystem)

/-- Zero counting profile on `B`. -/
@[simp] def zeroProfile : LS.B → ℕ := fun _ => 0

/-- Semantic non-conservativity. -/
def nonConservative (S : Finset LS.Sentence) : Prop :=
  ¬ LS.conservative S

end LocalBridgeSystem

namespace LocalRigidity

variable (LS : LocalBridgeSystem)
variable (L : LegitObstruction LS.B)

/-- Score of a finite batch `S` induced by the legitimate obstruction `L`. -/
def score (S : Finset LS.Sentence) : ℝ :=
  L.O.F ⟨LS.Count S⟩

/--
Local rigidity: the score is zero exactly on conservative extensions.
-/
lemma score_eq_zero_iff_conservative (S : Finset LS.Sentence) :
    score LS L S = 0 ↔ LS.conservative S := by
  classical
  unfold score
  constructor
  · intro h
    -- From F(c) = 0, use zero_iff_all_zero.
    have hcoords :
        ∀ b, (⟨LS.Count S⟩ : GenCounters LS.B).v b = 0 :=
      (LegitObstruction.zero_iff_all_zero (L := L)
        (c := ⟨LS.Count S⟩)).mp h
    -- Count S is pointwise zero.
    have hcount : LS.Count S = (fun _ => 0) := by
      funext b
      simpa using hcoords b
    -- Apply the specification.
    exact (LS.CountSpec S).mp hcount
  · intro hcons
    -- If S is conservative, Count S = 0, so all coordinates are zero,
    -- hence F(c) = 0.
    have hcount : LS.Count S = (fun _ => 0) :=
      (LS.CountSpec S).mpr hcons
    have hcoords :
        ∀ b, (⟨LS.Count S⟩ : GenCounters LS.B).v b = 0 := by
      intro b
      have := congrArg (fun f => f b) hcount
      simpa using this
    exact
      (LegitObstruction.zero_iff_all_zero (L := L)
        (c := ⟨LS.Count S⟩)).2 hcoords

/--
Equivalent strict form: the score is nonzero exactly on non-conservative extensions.
-/
lemma score_ne_zero_iff_nonConservative (S : Finset LS.Sentence) :
    score LS L S ≠ 0 ↔ LS.nonConservative S := by
  classical
  unfold LocalBridgeSystem.nonConservative
  constructor
  · intro h hcons
    -- direction 1: (score ≠ 0) → (¬ conservative)
    -- contradiction if we assume conservative
    have hz :
        score LS L S = 0 :=
      (score_eq_zero_iff_conservative (LS := LS) (L := L) S).2 hcons
    exact h hz
  · intro h hz
    -- direction 2: (¬ conservative) → (score ≠ 0)
    -- contradiction if we assume score = 0
    have hcons :
        LS.conservative S :=
      (score_eq_zero_iff_conservative (LS := LS) (L := L) S).1 hz
    exact h hcons


end LocalRigidity

end LogicDissoc
