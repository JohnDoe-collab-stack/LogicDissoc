/-
  LogicDissoc/DynamicRank.lean

  Dynamic ranks on traces / LocalReading (Rev layer),
  and abstract correspondence with ObstructionRank (RefSystem + delta).

  This file does not build a concrete instance of DynamicRefinement:
  it provides the general definitions and bridge lemmas,
  parameterized by a DynamicRefinement structure.
-/

import LogicDissoc.RefSystem
import LogicDissoc.Rank
import LogicDissoc.Rev

namespace LogicDissoc
namespace DynamicRank

--------------------------------------------------------------
-- 1. Dynamic side: traces and dynamic ranks
--------------------------------------------------------------

-- We reuse `Trace` and `LocalReading` defined in `LogicDissoc.Rev`.

-- Canonical verdict on a trace: "did the event occur at least once?"
def verdictTrace (T : Trace) : Prop :=
  ∃ n, T n

-- Dynamic rank 0 for a trace:
-- the verdict only depends on a bounded finite prefix of the trace.
def rank0Trace (T : Trace) : Prop :=
  ∃ N : ℕ,
    ∀ U : Trace,
      (∀ n, n < N → T n = U n) →
        verdictTrace T ↔ verdictTrace U

/-- Dynamic ILM (minimal version):
the verdict of the trace is invariant under replacement of the trace.

In a concrete setting, this definition could be refined
to reflect a "one-sided tail dependence". Here we take the
strongest form: the verdict does not depend on any detail of the trace. -/
def ilmTrace (T : Trace) : Prop :=
  ∀ U : Trace, verdictTrace T ↔ verdictTrace U

-- Dynamic transcendence for a trace:
-- the trace is neither rank 0 nor ILM.
def transcendTrace (T : Trace) : Prop :=
  ¬ rank0Trace T ∧ ¬ ilmTrace T

variable {Context Sentence : Type _}

/-- Dynamic rank 0 for a sentence φ in a context Γ:
the trace `LR Γ φ` has rank0Trace. -/
def rank0Dyn (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) : Prop :=
  rank0Trace (LR Γ φ)

/-- Dynamic ILM for a sentence φ in a context Γ. -/
def ilmDyn (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) : Prop :=
  ilmTrace (LR Γ φ)

/-- Dynamic transcendence for a sentence φ in a context Γ. -/
def transcendDyn (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) : Prop :=
  transcendTrace (LR Γ φ)

--------------------------------------------------------------
-- 2. Bridge to RefSystem: DynamicRefinement
--------------------------------------------------------------

open LogicDissoc

variable {Model : Type _}

/-- Relates a dynamic semantics (LR) to a `RefSystem` (E),
    by postulating the correspondence between dynamic rank and `delta`.

    This structure encodes the "bridge" between
    the dynamic layer (traces, `LocalReading`) and the `RefSystem` layer
    (`delta`, `ObstructionRank`). -/
structure DynamicRefinement where
  (E  : RefSystem Model Sentence)
  (LR : LocalReading Context Sentence)

  -- 1. Dynamic rank 0 ↔ delta = 0
  (rank0_iff_delta_zero :
    ∀ (Γ : Context) (φ : Sentence),
      rank0Dyn LR Γ φ ↔ E.delta φ = 0)

  -- 2. Dynamic ILM ↔ delta = 1
  (ilm_iff_delta_one :
    ∀ (Γ : Context) (φ : Sentence),
      ilmDyn LR Γ φ ↔ E.delta φ = 1)

  -- 3. Dynamic transcendence ↔ delta ≠ 0 and ≠ 1
  (transcend_iff_delta_ne :
    ∀ (Γ : Context) (φ : Sentence),
      transcendDyn LR Γ φ ↔ (E.delta φ ≠ 0 ∧ E.delta φ ≠ 1))

namespace DynamicRefinement

variable (R : DynamicRefinement (Context := Context) (Model := Model) (Sentence := Sentence))

-- Shorthand: underlying `RefSystem`.
abbrev E' : RefSystem Model Sentence := R.E

-- Shorthand: underlying `LocalReading`.
abbrev LR' : LocalReading Context Sentence := R.LR

/-- Correspondence: dynamic local rank ↔ `ObstructionRank.local`. -/
lemma rank0Dyn_iff_obstructionRank_local
    [∀ φ : Sentence, Decidable ((R.E').delta φ = 0)]
    [∀ φ : Sentence, Decidable ((R.E').delta φ = 1)]
    (Γ : Context) (φ : Sentence) :
  rank0Dyn R.LR' Γ φ ↔
    obstructionRank R.E' φ = ObstructionRank.local := by
  -- equivalence rank0Dyn ↔ delta = 0
  have hδ0 : rank0Dyn R.LR' Γ φ ↔ (R.E').delta φ = 0 :=
    R.rank0_iff_delta_zero Γ φ
  -- trichotomy on (obstructionRank, delta)
  have htri := obstructionRank_spec (E := R.E') (φ := φ)
  constructor
  · -- (→) rank0Dyn ⇒ local rank
    intro h
    have hδ : (R.E').delta φ = 0 := (hδ0.mp h)
    -- inspect the three possible cases
    rcases htri with hlocal | hrest
    · -- case (local ∧ delta = 0)
      exact hlocal.1
    · rcases hrest with hilm | htrans
      · -- case (ilm ∧ delta = 1): contradicts delta = 0
        -- `simp` rewrites using `hδ` and closes `False` from `0 = 1`
        have : False := by simpa [hδ] using hilm.2
        exact this.elim
      · -- case (transcend ∧ delta ≠ 0 ∧ delta ≠ 1): contradicts delta = 0
        exact (htrans.2.1 hδ).elim
  · -- (←) local rank ⇒ rank0Dyn
    intro hRank
    -- first, derive delta = 0 from the trichotomy
    have hδ : (R.E').delta φ = 0 := by
      rcases htri with hlocal | hrest
      · -- case (local ∧ delta = 0)
        exact hlocal.2
      · rcases hrest with hilm | htrans
        · -- case (ilm ∧ delta = 1) impossible if rank = local
          have hEq : ObstructionRank.local = ObstructionRank.ilm := by
            simpa [hRank] using hilm.1
          cases hEq
        · -- case (transcend ∧ …) impossible if rank = local
          have hEq : ObstructionRank.local = ObstructionRank.transcend := by
            simpa [hRank] using htrans.1
          cases hEq
    -- then go back via rank0_iff_delta_zero
    exact (hδ0.mpr hδ)


/-- Correspondence: dynamic ILM ↔ `ObstructionRank.ilm`. -/
lemma ilmDyn_iff_obstructionRank_ilm
    [∀ φ : Sentence, Decidable ((R.E').delta φ = 0)]
    [∀ φ : Sentence, Decidable ((R.E').delta φ = 1)]
    (Γ : Context) (φ : Sentence) :
  ilmDyn R.LR' Γ φ ↔
    obstructionRank R.E' φ = ObstructionRank.ilm := by
  -- 1. Dynamic correspondence: ILM ↔ delta = 1
  have hδ1 : ilmDyn R.LR' Γ φ ↔ (R.E').delta φ = 1 :=
    R.ilm_iff_delta_one Γ φ
  -- 2. Trichotomy on (obstructionRank, delta)
  have htri := obstructionRank_spec (E := R.E') (φ := φ)
  constructor
  · -- (→) ilmDyn ⇒ ilm rank
    intro h
    have hδ : (R.E').delta φ = 1 := hδ1.mp h
    rcases htri with hlocal | hrest
    · -- case (local ∧ delta = 0): impossible if delta = 1
      have hδ0 : (R.E').delta φ = 0 := hlocal.2
      have h01 : (0 : ℝ) = 1 := by
        -- 0 = delta from hδ0.symm, then delta = 1 from hδ
        calc
          (0 : ℝ) = (R.E').delta φ := hδ0.symm
          _ = 1 := hδ
      have hne : (0 : ℝ) ≠ 1 := by simp
      exact (hne h01).elim
    · rcases hrest with hilm | htrans
      · -- case (ilm ∧ delta = 1): exactly what we want
        exact hilm.1
      · -- case (transcend ∧ delta ≠ 0 ∧ delta ≠ 1): impossible if delta = 1
        have hne1 : (R.E').delta φ ≠ 1 := htrans.2.2
        exact (hne1 hδ).elim
  · -- (←) ilm rank ⇒ ilmDyn
    intro hRank
    -- first, show delta φ = 1
    have hδ : (R.E').delta φ = 1 := by
      rcases htri with hlocal | hrest
      · -- case (local ∧ delta = 0): impossible if rank = ilm
        have h1 : obstructionRank R.E' φ = ObstructionRank.local := hlocal.1
        -- from h1 and hRank, we get local = ilm, contradiction
        have hEq : ObstructionRank.local = ObstructionRank.ilm :=
          Eq.trans h1.symm hRank
        cases hEq
      · rcases hrest with hilm | htrans
        · -- case (ilm ∧ delta = 1): consistent with hRank
          exact hilm.2
        · -- case (transcend ∧ …): impossible if rank = ilm
          have h1 : obstructionRank R.E' φ = ObstructionRank.transcend := htrans.1
          have hEq : ObstructionRank.transcend = ObstructionRank.ilm :=
            Eq.trans h1.symm hRank
          cases hEq
    -- then go back via ilm_iff_delta_one
    exact hδ1.mpr hδ


/-- Correspondence: dynamic transcendence ↔ `ObstructionRank.transcend`. -/
lemma transcendDyn_iff_obstructionRank_transcend
    [∀ φ : Sentence, Decidable ((R.E').delta φ = 0)]
    [∀ φ : Sentence, Decidable ((R.E').delta φ = 1)]
    (Γ : Context) (φ : Sentence) :
  transcendDyn R.LR' Γ φ ↔
    obstructionRank R.E' φ = ObstructionRank.transcend := by
  -- 1. Dynamic correspondence: transcendDyn ↔ (delta ≠ 0 ∧ delta ≠ 1)
  have hδne : transcendDyn R.LR' Γ φ ↔
      ((R.E').delta φ ≠ 0 ∧ (R.E').delta φ ≠ 1) :=
    R.transcend_iff_delta_ne Γ φ
  -- 2. Trichotomy on (obstructionRank, delta)
  have htri := obstructionRank_spec (E := R.E') (φ := φ)
  constructor
  · -- (→) transcendDyn ⇒ transcend rank
    intro h
    have hne : (R.E').delta φ ≠ 0 ∧ (R.E').delta φ ≠ 1 := hδne.mp h
    rcases htri with hlocal | hrest
    · -- case (local ∧ delta = 0): impossible since delta ≠ 0
      have hδ0 : (R.E').delta φ = 0 := hlocal.2
      exact (hne.1 hδ0).elim
    · rcases hrest with hilm | htrans
      · -- case (ilm ∧ delta = 1): impossible since delta ≠ 1
        have hδ1 : (R.E').delta φ = 1 := hilm.2
        exact (hne.2 hδ1).elim
      · -- case (transcend ∧ delta ≠ 0 ∧ delta ≠ 1): exactly what we want
        exact htrans.1
  · -- (←) transcend rank ⇒ transcendDyn
    intro hRank
    -- retrieve delta ≠ 0 and ≠ 1 from the trichotomy
    have hne : (R.E').delta φ ≠ 0 ∧ (R.E').delta φ ≠ 1 := by
      rcases htri with hlocal | hrest
      · -- case (local ∧ delta = 0): impossible if rank = transcend
        have hEq : ObstructionRank.local = ObstructionRank.transcend := by
          -- obstructionRank R.E' φ = local and = transcend
          -- gives an equality of constructors
          simpa [hlocal.1] using hRank.symm
        cases hEq
      · rcases hrest with hilm | htrans
        · -- case (ilm ∧ delta = 1): impossible if rank = transcend
          have hEq : ObstructionRank.ilm = ObstructionRank.transcend := by
            simpa [hilm.1] using hRank.symm
          cases hEq
        · -- case (transcend ∧ delta ≠ 0 ∧ delta ≠ 1): consistent with hRank
          exact And.intro htrans.2.1 htrans.2.2
    -- and go back via the dynamic specification R.transcend_iff_delta_ne
    exact hδne.mpr hne

end DynamicRefinement

end DynamicRank
end LogicDissoc
