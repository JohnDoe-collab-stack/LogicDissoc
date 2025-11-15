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
  -- From RefSystem:
  --   E.delta_eq_zero_iff_mem_closure φ :
  --     E.delta φ = 0 ↔ φ ∈ E.CloE ∅
  -- and `isLocal φ := φ ∈ E.CloE ∅`.
  have h := E.delta_eq_zero_iff_mem_closure φ
  -- h : E.delta φ = 0 ↔ φ ∈ E.CloE ∅
  simpa [RefSystem.isLocal] using h.symm

/-- Non-locality is exactly characterized by the band `[1, 2)` of `delta`. -/
lemma isNonlocal_iff_delta_band (φ : Sentence) :
  E.isNonlocal φ ↔ 1 ≤ E.delta φ ∧ E.delta φ < 2 := by
  -- Directly the lemma from RefSystem:
  --   E.nonlocal_iff_delta_band φ
  simpa using E.nonlocal_iff_delta_band φ

/-- Basic partition: for every sentence, `delta` is either `0` or in `[1, 2)`. -/
lemma delta_partition (φ : Sentence) :
  E.delta φ = 0 ∨ (1 ≤ E.delta φ ∧ E.delta φ < 2) := by
  classical
  by_cases hloc : E.isLocal φ
  · -- local
    left
    exact (isLocal_iff_delta_zero (E := E) φ).1 hloc
  · -- non-local
    right
    have hnon : E.isNonlocal φ := by
      -- `isNonlocal φ := ¬ isLocal φ` in RefSystem
      simp [RefSystem.isNonlocal, hloc]
    exact (isNonlocal_iff_delta_band (E := E) φ).1 hnon

/-
Refinement: for every sentence, we have exactly one of the three disjoint cases:

* `delta = 0`  (local),
* `delta = 1`  (minimally non-local),
* `delta ≠ 0` and `delta ≠ 1` (transcendent non-local).

It is this trichotomy that motivates introducing `ObstructionRank`.
-/
lemma delta_trichotomy (φ : Sentence) :
  E.delta φ = 0 ∨ E.delta φ = 1 ∨ (E.delta φ ≠ 0 ∧ E.delta φ ≠ 1) := by
  classical
  by_cases h0 : E.delta φ = 0
  · exact Or.inl h0
  · have h0' : E.delta φ ≠ 0 := h0
    by_cases h1 : E.delta φ = 1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨h0', h1⟩)

end Justification


/- ----------------------------------------------------------------
   2. Type `ObstructionRank` and derived function `obstructionRank`
   ---------------------------------------------------------------- -/

/-- Three basic obstruction ranks for sentences, defined from `delta`. -/
inductive ObstructionRank
| local      -- delta = 0
| ilm        -- delta = 1
| transcend  -- delta ≠ 0,1
deriving DecidableEq

namespace ObstructionRank

/-- Convenience predicate: rank is local. -/
def isLocal : ObstructionRank → Prop
| .local      => True
| _           => False

/-- Convenience predicate: rank is `ilm`. -/
def isIlm : ObstructionRank → Prop
| .ilm        => True
| _           => False

/-- Convenience predicate: rank is `transcend`. -/
def isTranscend : ObstructionRank → Prop
| .transcend  => True
| _           => False

end ObstructionRank


/-! ### Rank of a sentence for a fixed reference system -/
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

/--
Complete specification: we re-encode exactly the trichotomy of `delta`
into `ObstructionRank`.
-/
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

/-- Rank of a rational cut sentence `Cut q x` for a fixed reference system. -/
def cutRank
    (E   : RefSystem Model Sentence)
    (Cut : ℚ → Code → Sentence)
    (x   : Code) (q : ℚ)
    [Decidable (E.delta (Cut q x) = 0)] [Decidable (E.delta (Cut q x) = 1)] :
  ObstructionRank :=
  obstructionRank E (Cut q x)

/-- Rank of a dyadic-bit sentence `Bit n a x` for a fixed reference system. -/
def bitRank
    (E   : RefSystem Model Sentence)
    (Bit : ℕ → ℕ → Code → Sentence)
    (x   : Code) (n a : ℕ)
    [Decidable (E.delta (Bit n a x) = 0)] [Decidable (E.delta (Bit n a x) = 1)] :
  ObstructionRank :=
  obstructionRank E (Bit n a x)

/-- All rational cuts of `x` are local (delta = 0). -/
def codeIsCutLocal
    (E   : RefSystem Model Sentence)
    (Cut : ℚ → Code → Sentence)
    (x   : Code) : Prop :=
  ∀ q : ℚ, cutRank E Cut x q = ObstructionRank.local

/-- `x` has at least one dyadic-bit sentence of transcend rank. -/
def codeHasTranscendentBits
    (E   : RefSystem Model Sentence)
    (Bit : ℕ → ℕ → Code → Sentence)
    (x   : Code) : Prop :=
  ∃ n a : ℕ, bitRank E Bit x n a = ObstructionRank.transcend

end NumericCodes


/-!
### Halting, reverse halting (`Rev`) et rang obstructionnel

Ce fichier se situe au-dessus de deux briques plus élémentaires :

* `RefSystem` : un système de référence sémantique avec
  `delta : Sentence → ℝ` et le rang fini `ObstructionRank`
  (local / ilm / transcend).
* `Rev` (`LogicDissoc/Rev.lean`) : une théorie abstraite des traces
  temporelles et de la "révision de queue" (`Rev`) qui caractérise
  le halting.

Dans `Rev.lean`, pour une trace `T : Trace := ℕ → Prop`, on a deux
points de vue sur le même phénomène :

* halting direct :
  `Halts T :≡ ∃ n, T n`  (il existe un temps où `T` vaut) ;

* reverse halting :
  `Rev Q T :≡ Q.pi (up T)` pour un `QueueProjector Q`.

Le lemme `Rev_iff_Halts` formalise :

  `Rev Q T ↔ Halts T`

pour tout `Q`. Autrement dit, toute révision de queue satisfaisant les
axiomes de `QueueProjector` coïncide extensionnellement avec le
prédicat de halting direct `∃ n, T n`.

Pour une lecture locale

  `LR : Context → Sentence' → Trace`

(on garde ici un type `Sentence'` abstrait, potentiellement différent
du `Sentence` de `RefSystem`), on définit :

* `Prov LR Γ φ :≡ ∃ n, LR Γ φ n`
  (point de vue dynamique : il y a un temps où la procédure de preuve
   voit `φ` à partir de `Γ`) ;

* `verdict LR Γ φ :≡ Rev0 (LR Γ φ)`
  (point de vue stabilisé : la révision de la trace conclut "oui").

Le lemme `verdict_iff_HaltsLR` formalise :

  `verdict LR Γ φ ↔ HaltsLR LR Γ φ`.

Ce fichier `Rank` fournit la couche `delta` / `ObstructionRank` /
`cutRank` / `bitRank`, c’est-à-dire une classification obstructionnelle
abstraite des phrases du langage de `RefSystem`.

La spécification obstructionnelle d’un code de type "Ω de Chaitin" est
désormais isolée dans `LogicDissoc/Omega.lean`, via la structure

  `Omega.Spec E Cut Bit x`,

sans axiomes globaux et sans constante `Omega` non calculable.
-/

end LogicDissoc
