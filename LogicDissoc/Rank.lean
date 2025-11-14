import Mathlib.Data.Real.Basic
import LogicDissoc.RefSystem

namespace LogicDissoc

universe u v w

/-!
  TriRank

  Justification of the obstruction rank from the existing building blocks
  of `RefSystem`, then definition of a finite type `ObstructionRank`
  which only re-encodes the information already present in `delta`.
-/

/- --------------------------------------------------------------
   1. Justification from `delta` and the lemmas of `RefSystem`
   -------------------------------------------------------------- -/

section Justification

variable {Model : Type u} {Sentence : Type v}
variable (E : RefSystem Model Sentence)

/-- In `RefSystem`, locality is exactly characterized by `delta = 0`. -/
lemma isLocal_iff_delta_zero (φ : Sentence) :
  E.isLocal φ ↔ E.delta φ = 0 := by
  -- We start from the lemma provided by RefSystem:
  --   E.delta_eq_zero_iff_mem_closure φ :
  --     E.delta φ = 0 ↔ φ ∈ E.CloE ∅
  -- and from the definition of `isLocal`:
  --   E.isLocal φ := φ ∈ E.CloE ∅.
  have h := E.delta_eq_zero_iff_mem_closure φ
  -- h : E.delta φ = 0 ↔ φ ∈ E.CloE ∅
  -- We rewrite `isLocal` in terms of `CloE ∅`.
  -- Depending on the exact definition in your `RefSystem`, adapt the
  -- name used below (here we assume `isLocal` is defined by
  -- `φ ∈ E.CloE ∅`).
  -- The formal idea is the same: `isLocal` is just this membership.
  -- We want: isLocal φ ↔ delta φ = 0,
  -- so we replace φ ∈ CloE ∅ with isLocal φ.
  -- This line assumes that
  --   E.isLocal φ = (φ ∈ E.CloE ∅)
  -- is a transparent definition.
  simpa [RefSystem.isLocal] using h.symm

-- Non-locality is exactly characterized by the band `[1, 2)` of `delta`.
lemma isNonlocal_iff_delta_band (φ : Sentence) :
  E.isNonlocal φ ↔ 1 ≤ E.delta φ ∧ E.delta φ < 2 := by
  -- Here we use directly the lemma provided by RefSystem:
  --   E.nonlocal_iff_delta_band φ :
  --     E.isNonlocal φ ↔ 1 ≤ E.delta φ ∧ E.delta φ < 2
  simpa using E.nonlocal_iff_delta_band φ

-- Basic partition: for every sentence, `delta` is either `0` or in `[1, 2)`.
lemma delta_partition (φ : Sentence) :
  E.delta φ = 0 ∨ (1 ≤ E.delta φ ∧ E.delta φ < 2) := by
  classical
  -- Case split on locality (defined in RefSystem)
  by_cases hloc : E.isLocal φ
  · -- local
    left
    -- isLocal ↔ delta = 0
    exact (isLocal_iff_delta_zero (E := E) φ).1 hloc
  · -- non-local
    right
    -- By definition, isNonlocal is the complement of isLocal
    have hnon : E.isNonlocal φ := by
      -- Adjust if the exact definition of `isNonlocal` differs,
      -- but typically: isNonlocal φ := ¬ isLocal φ
      simp [RefSystem.isNonlocal, hloc]  -- (definition of isNonlocal)
    -- nonlocal ↔ 1 ≤ delta < 2
    exact (isNonlocal_iff_delta_band (E := E) φ).1 hnon

-- Refinement: for every sentence, we have exactly one of the three disjoint cases:

-- * `delta = 0`  (local),
-- * `delta = 1`  (minimally non-local),
-- * `delta ≠ 0` and `delta ≠ 1` (transcendent non-local).

-- It is this trichotomy that motivates introducing `ObstructionRank`.

lemma delta_trichotomy (φ : Sentence) :
  E.delta φ = 0 ∨ E.delta φ = 1 ∨ (E.delta φ ≠ 0 ∧ E.delta φ ≠ 1) := by
  classical
  -- LEM on equality to 0 and to 1.
  by_cases h0 : E.delta φ = 0
  · exact Or.inl h0
  · have : E.delta φ ≠ 0 := h0
    -- either delta = 1 or delta ≠ 1
    by_cases h1 : E.delta φ = 1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨this, h1⟩)

end Justification

/- ----------------------------------------------------------------
   2. Type `ObstructionRank` and derived function `obstructionRank`
   ---------------------------------------------------------------- -/

-- Three basic obstruction ranks for sentences, defined from `delta`.
inductive ObstructionRank
| local      -- delta = 0
| ilm        -- delta = 1
| transcend  -- delta ≠ 0,1
deriving DecidableEq

namespace ObstructionRank

-- Convenience predicates on ranks.
def isLocal : ObstructionRank → Prop
| .local      => True
| _           => False

def isIlm : ObstructionRank → Prop
| .ilm        => True
| _           => False

def isTranscend : ObstructionRank → Prop
| .transcend  => True
| _           => False

end ObstructionRank

-- ### Rank of a sentence for a fixed reference system

section SentenceRank

variable {Model : Type u} {Sentence : Type v}

/-- Obstruction rank of a sentence `φ` in a reference system `E`. -/
def obstructionRank (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)] :
  ObstructionRank :=
  if _ : E.delta φ = 0 then
    ObstructionRank.local
  else if _ : E.delta φ = 1 then
    ObstructionRank.ilm
  else
    ObstructionRank.transcend

/-- If `delta φ = 0`, the rank is local. -/
lemma obstructionRank_local_of_delta_eq_zero
    (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)]
    (h0 : E.delta φ = 0) :
  obstructionRank E φ = ObstructionRank.local := by
  unfold obstructionRank
  simp [h0]

/-- If `delta φ = 1` and `delta φ ≠ 0`, the rank is `ilm`. -/
lemma obstructionRank_ilm_of_delta_eq_one
    (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)]
    (_ : E.delta φ ≠ 0) (h1 : E.delta φ = 1) :
  obstructionRank E φ = ObstructionRank.ilm := by
  unfold obstructionRank
  simp [h1]

/-- If `delta φ ≠ 0` and `delta φ ≠ 1`, the rank is transcend. -/
lemma obstructionRank_transcend_of_delta_ne
    (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)]
    (h0 : E.delta φ ≠ 0) (h1 : E.delta φ ≠ 1) :
  obstructionRank E φ = ObstructionRank.transcend := by
  unfold obstructionRank
  simp [h0, h1]

-- Complete specification: we re-encode exactly the trichotomy of `delta`
-- into `ObstructionRank`.
lemma obstructionRank_spec
    (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)] :
  (obstructionRank E φ = ObstructionRank.local ∧ E.delta φ = 0)
  ∨ (obstructionRank E φ = ObstructionRank.ilm ∧ E.delta φ = 1)
  ∨ (obstructionRank E φ = ObstructionRank.transcend
      ∧ E.delta φ ≠ 0 ∧ E.delta φ ≠ 1) := by
  classical
  -- We use the trichotomy of `delta` proven above.
  have htri := delta_trichotomy (E := E) φ
  rcases htri with h0 | h1 | hrest
  · -- delta = 0
    left
    refine ⟨?_, h0⟩
    exact obstructionRank_local_of_delta_eq_zero (E := E) (φ := φ) h0
  · -- delta = 1
    right
    left
    refine ⟨?_, h1⟩
    -- here we only know delta = 1; we deduce that delta ≠ 0
    have h0 : E.delta φ ≠ 0 := by
      intro h
      rw [h] at h1
      exact one_ne_zero h1.symm
    exact obstructionRank_ilm_of_delta_eq_one (E := E) (φ := φ) h0 h1
  · -- delta ≠ 0 and delta ≠ 1
    right
    right
    rcases hrest with ⟨h0, h1⟩
    refine ⟨?_, h0, h1⟩
    exact obstructionRank_transcend_of_delta_ne (E := E) (φ := φ) h0 h1

end SentenceRank

/- --------------------------------------------------------------
   3. Abstract obstructional classification of “numeric codes”
   -------------------------------------------------------------- -/

/-
We stay completely abstract here:

* `Sentence` and `Model` come from the reference system `E`.
* `Code` is any type of “numeric code”.
* `Cut    : ℚ → Code → Sentence`
* `Bit    : ℕ → ℕ → Code → Sentence`

are simply families of sentences that talk about a code `x : Code`
(rational cuts, dyadic bits, etc.).
-/

section NumericCodes

variable {Model : Type u} {Sentence : Type v} {Code : Type w}

-- Rank of a rational cut sentence `Cut q x` for a fixed reference system.
def cutRank
    (E   : RefSystem Model Sentence)
    (Cut : ℚ → Code → Sentence)
    (x   : Code) (q : ℚ)
    [Decidable (E.delta (Cut q x) = 0)] [Decidable (E.delta (Cut q x) = 1)] :
  ObstructionRank :=
  obstructionRank E (Cut q x)

-- Rank of a dyadic-bit sentence `Bit n a x` for a fixed reference system.
def bitRank
    (E   : RefSystem Model Sentence)
    (Bit : ℕ → ℕ → Code → Sentence)
    (x   : Code) (n a : ℕ)
    [Decidable (E.delta (Bit n a x) = 0)] [Decidable (E.delta (Bit n a x) = 1)] :
  ObstructionRank :=
  obstructionRank E (Bit n a x)

-- All rational cuts of `x` are local (delta = 0).
def codeIsCutLocal
    (E   : RefSystem Model Sentence)
    (Cut : ℚ → Code → Sentence)
    (x   : Code) : Prop :=
  ∀ q : ℚ, cutRank E Cut x q = ObstructionRank.local

-- `x` has at least one dyadic-bit sentence of transcend rank.
def codeHasTranscendentBits
    (E   : RefSystem Model Sentence)
    (Bit : ℕ → ℕ → Code → Sentence)
    (x   : Code) : Prop :=
  ∃ n a : ℕ, bitRank E Bit x n a = ObstructionRank.transcend


end NumericCodes

section OmegaSpecification

variable {Model : Type u} {Sentence : Type v}
variable (E : RefSystem Model Sentence)
variable (Cut : ℚ → Code → Sentence)
variable (Bit : ℕ → ℕ → Code → Sentence)

variable (Omega : Code)

axiom omega_cuts_are_ilm :
  ∀ q : ℚ,
    (E.delta (Cut q Omega) ≠ 0) ∧ (E.delta (Cut q Omega) = 1)

axiom omega_bits_are_transcend :
  ∀ n a : ℕ,
    (E.delta (Bit n a Omega) ≠ 0) ∧ (E.delta (Bit n a Omega) ≠ 1)

lemma omega_cutRank_is_ilm
    [∀ q, Decidable (E.delta (Cut q Omega) = 0)]
    [∀ q, Decidable (E.delta (Cut q Omega) = 1)] :
  ∀ q : ℚ, cutRank E Cut Omega q = ObstructionRank.ilm := by
  intro q
  -- axiomatic data: delta ≠ 0 and delta = 1 for Cut q Omega
  have h := omega_cuts_are_ilm (E := E) (Cut := Cut) (Omega := Omega) q
  -- h.1 : E.delta (Cut q Omega) ≠ 0
  -- h.2 : E.delta (Cut q Omega) = 1
  unfold cutRank
  exact
    obstructionRank_ilm_of_delta_eq_one
      (E := E) (φ := Cut q Omega) h.1 h.2


lemma omega_bitRank_is_transcend
    [∀ n a, Decidable (E.delta (Bit n a Omega) = 0)]
    [∀ n a, Decidable (E.delta (Bit n a Omega) = 1)] :
  ∀ n a : ℕ, bitRank E Bit Omega n a = ObstructionRank.transcend := by
  intro n a
  -- 1. We call the axiom with the arguments of this section
  have h := omega_bits_are_transcend (E := E) (Bit := Bit) (Omega := Omega) n a
  -- h.1 : E.delta (Bit n a Omega) ≠ 0
  -- h.2 : E.delta (Bit n a Omega) ≠ 1

  -- 2. We use the same strategy as for the previous lemma
  unfold bitRank
  exact
    obstructionRank_transcend_of_delta_ne
      (E := E) (φ := Bit n a Omega) h.1 h.2

end OmegaSpecification

end LogicDissoc
