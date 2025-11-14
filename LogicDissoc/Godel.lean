import Mathlib.Data.Finset.Basic
import LogicDissoc.BasicSemantics
import LogicDissoc.ObstructionGen
import LogicDissoc.Legit
import LogicDissoc.Rev
import LogicDissoc.RefSystem
import LogicDissoc.DeltaObstruction

namespace LogicDissoc

universe u v

open Finset

/-- Finite batteries of formulas. -/
abbrev Battery (Sentence : Type*) := Finset Sentence

-- ============================================================================
-- PART 1: MetaGodel
-- ============================================================================

section MetaGodel

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)
variable {B : Type*} [Fintype B] [DecidableEq B]
variable (Γ_ref : Set Sentence)

/-- Conservative extension of `Γ_ref` by a finite battery `S`. -/
def conservativeExt (S : Battery Sentence) : Prop :=
  ModE Sat (Γ_ref ∪ (↑S : Set Sentence)) = ModE Sat Γ_ref

variable (Count : Battery Sentence → GenCounters B)

/--
Soundness axiom for the counting protocol:

The zero profile (all components equal to 0) is equivalent to
semantic conservativity of the extension.
-/
class CountSpec : Prop where
  sound :
    ∀ S : Battery Sentence,
      (∀ b, (Count S).v b = 0) ↔
        conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S

variable (L : LegitObstruction B)

/-- General index associated to `L` and the protocol `Count`. -/
def AstarGen (S : Battery Sentence) : ℝ :=
  L.O.F (Count S)

/--
Meta-Gödel theorem (conservative boundary):

For every finite battery `S`, under `CountSpec` we have

`AstarGen L Count S = 0`
iff
`ModE(Γ_ref ∪ S) = ModE(Γ_ref)`.

In other words, every legitimate functional induces
exactly the same conservative / non-conservative boundary.
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
“Non-zero” version:

Under the same assumptions,

`AstarGen L Count S ≠ 0`
iff
`ModE(Γ_ref ∪ S) ≠ ModE(Γ_ref)`.

The 0 / non-0 verdict is therefore invariant under the choice
of the legitimate obstruction functional in the positive linear cone.
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

/-- `AstarGen` is always ≥ 0 for a legitimate obstruction. -/
lemma AstarGen_nonneg (S : Battery Sentence) :
  0 ≤ AstarGen (Count := Count) (L := L) S := by
  unfold AstarGen
  exact LegitObstruction.F_nonneg (L := L) (c := Count S)

/--
Strong version of the meta-theorem:
`AstarGen > 0` iff the extension is not conservative.
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

end MetaGodel

-- ============================================================================
-- PART 2: GodelDynamic
-- ============================================================================

/-
Gödel-style instantiation layer on top of MetaGodel.

Given:
- a base theory Γ_ref,
- a family of semantic "directions" detecting non-conservativity,

we define a counting protocol CountFromGodel and show it satisfies CountSpec.
Then MetaGodel applies: any legitimate obstruction yields the same 0/>0
boundary for these Gödel-style directions.
-/

section GodelDynamic

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)
variable (Γ_ref : Set Sentence)
variable {B : Type*} [Fintype B] [DecidableEq B]

/--
`GodelDirection Sat Γ_ref B` packages semantic "directions"
along which non-conservativity must be witnessed.

Parameters:

* `P b m` : predicate saying that model `m` realizes direction `b`.
* `dec`   : for every finite battery `S` and direction `b`, we have a
            decidable test for the existence of a witness model eliminated
            by `Γ_ref ∪ S` along direction `b`.
* `separating` : any non-conservative extension is detected by at least
                 one direction `b` via some model `m`.
-/
structure GodelDirection
  (Sat : Model → Sentence → Prop)
  (Γ_ref : Set Sentence)
  (B : Type*) [Fintype B] [DecidableEq B] where
  P :
    B → Model → Prop
  dec :
    ∀ (S : Battery Sentence) (b : B),
      Decidable
        (∃ m,
          m ∈ ModE Sat Γ_ref ∧
          ¬ m ∈ ModE Sat (Γ_ref ∪ (↑S : Set Sentence)) ∧
          P b m)
  separating :
    ∀ {S : Battery Sentence},
      ¬ conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S →
      ∃ b m,
        m ∈ ModE Sat Γ_ref ∧
        ¬ m ∈ ModE Sat (Γ_ref ∪ (↑S : Set Sentence)) ∧
        P b m

namespace GodelDirection

/--
Counting protocol induced by a `GodelDirection`.

`CountFromGodel GD S` sets component `b` to 1 iff `dec S b`
witnesses the existence of a model of `Γ_ref` with property `P b`
that is eliminated by `Γ_ref ∪ S`. Otherwise it is 0.
-/
def CountFromGodel
    (GD : GodelDirection Sat Γ_ref B)
    (S : Battery Sentence) : GenCounters B :=
{ v := fun b =>
    match GD.dec S b with
    | isTrue _  => 1
    | isFalse _ => 0 }

/--
`CountFromGodel` satisfies `CountSpec`:

- If all components are zero, the extension must be conservative:
  otherwise `GD.separating` would produce a witness, contradicting
  the corresponding zero.
- If the extension is conservative, no such witness exists, so all
  components must be zero.
-/
instance
    (GD : GodelDirection Sat Γ_ref B) :
  CountSpec (Sat := Sat) (Γ_ref := Γ_ref)
    (Count := GD.CountFromGodel (Sat := Sat) (Γ_ref := Γ_ref)) :=
by
  constructor
  intro S
  constructor
  · -- (∀ b, (CountFromGodel GD S).v b = 0) → conservative extension
    intro hZero
    by_contra hNotCons
    obtain ⟨b, m, hm_ref, hm_not, hP⟩ :=
      GD.separating (Sat := Sat) (Γ_ref := Γ_ref) (S := S) hNotCons
    have hWitness :
      ∃ m,
        m ∈ ModE Sat Γ_ref ∧
        ¬ m ∈ ModE Sat (Γ_ref ∪ (↑S : Set Sentence)) ∧
        GD.P b m :=
      ⟨m, hm_ref, hm_not, hP⟩
    have hb := hZero b
    -- Inspect the decision for (S, b)
    cases hDec : GD.dec S b with
    | isTrue _ =>
        -- dec says: witness exists, so v b = 1
        have hv :
          (GD.CountFromGodel (Sat := Sat) (Γ_ref := Γ_ref) S).v b = 1 := by
          simp [CountFromGodel, hDec]
        -- but hZero says v b = 0
        have hv0 :
          (GD.CountFromGodel (Sat := Sat) (Γ_ref := Γ_ref) S).v b = 0 := hb
        rw [hv] at hv0
        exact one_ne_zero hv0
    | isFalse h =>
        -- dec says: no witness, contradiction with hWitness
        exact h hWitness
  · -- conservative extension → (∀ b, (CountFromGodel GD S).v b = 0)
    intro hCons b
    -- equality of model classes
    have hEq :
      ModE Sat (Γ_ref ∪ (↑S : Set Sentence)) = ModE Sat Γ_ref := by
      simpa [conservativeExt] using hCons
    -- hence no witness for this b
    have hNo :
      ¬ ∃ m,
          m ∈ ModE Sat Γ_ref ∧
          ¬ m ∈ ModE Sat (Γ_ref ∪ (↑S : Set Sentence)) ∧
          GD.P b m :=
    by
      intro h
      rcases h with ⟨m, hm_ref, hm_not, hP⟩
      have hm_ext :
        m ∈ ModE Sat (Γ_ref ∪ (↑S : Set Sentence)) := by
        simpa [hEq] using hm_ref
      exact hm_not hm_ext
    -- inspect dec S b
    cases hDec : GD.dec S b with
    | isTrue h =>
        -- dec gives a witness, contradicting hNo
        exact (hNo h).elim
    | isFalse _ =>
        -- no witness: v b = 0
        simp [CountFromGodel, hDec]

end GodelDirection

/-
Gödel-style obstruction index associated with:
- a legitimate obstruction `L`,
- a `GodelDirection Sat Γ_ref B` instance `GD`,
- the induced counting protocol `CountFromGodel`.
-/
variable (L : LegitObstruction B)

def Astar_Godel
    (GD : GodelDirection Sat Γ_ref B)
    (S : Battery Sentence) : ℝ :=
  AstarGen
    (Count :=
      GodelDirection.CountFromGodel (Sat := Sat) (Γ_ref := Γ_ref) (B := B) GD)
    (L := L) S

/--
Gödel-style meta-theorem (zero boundary):

For any `GD` and legitimate `L`, the induced `Astar_Godel` is zero
exactly on conservative extensions of `Γ_ref`.
-/
theorem Astar_Godel_zero_iff_conservative
    (GD : GodelDirection Sat Γ_ref B)
    (S : Battery Sentence) :
  Astar_Godel (Sat := Sat) (Γ_ref := Γ_ref) (L := L) GD S = 0
    ↔ conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S :=
by
  unfold Astar_Godel
  simpa using
    metaGodel_frontier_zero
      (Sat := Sat) (Γ_ref := Γ_ref)
      (Count :=
        GodelDirection.CountFromGodel
          (Sat := Sat) (Γ_ref := Γ_ref) (B := B) GD)
      (L := L) S

/--
Gödel-style meta-theorem (strictly positive boundary):

For any `GD` and legitimate `L`, the induced `Astar_Godel` is
strictly positive exactly when the extension is non-conservative.
-/
theorem Astar_Godel_pos_iff_nonconservative
    (GD : GodelDirection Sat Γ_ref B)
    (S : Battery Sentence) :
  0 < Astar_Godel (Sat := Sat) (Γ_ref := Γ_ref) (L := L) GD S
    ↔ ¬ conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S :=
by
  unfold Astar_Godel
  simpa using
    metaGodel_frontier_pos
      (Sat := Sat) (Γ_ref := Γ_ref)
      (Count :=
        GodelDirection.CountFromGodel
          (Sat := Sat) (Γ_ref := Γ_ref) (B := B) GD)
      (L := L) S

-- ----------------------------------------------------------------------------
-- Incompleteness
-- ----------------------------------------------------------------------------

section Incompleteness

variable {Sentence : Type u} {Model : Type v}
variable {Sat : Model → Sentence → Prop}
variable {Γ_ref : Set Sentence}
variable {B : Type*} [Fintype B] [DecidableEq B]

/--
Abstract Gödel-style incompleteness scenario in this framework:

- `GD` : semantic directions over `(Sat, Γ_ref, B)` (as in `GodelDirection`);
- `L`  : legitimate obstruction on profiles of type `B`;
- `S`  : finite batch of axioms;
- `nonCons` : the extension by `S` is semantically non-conservative over `Γ_ref`.

This packages exactly the shape of an "incompleteness witness"
as used by the general MetaGodel + GodelDynamic machinery.
-/
structure GodelIncompleteness where
  GD : GodelDirection Sat Γ_ref B
  L  : LegitObstruction B
  S  : Battery Sentence
  nonCons :
    ¬ conservativeExt (Sat := Sat) (Γ_ref := Γ_ref) S

/--
Dynamic quantification lemma:

In any `GodelIncompleteness` scenario, the canonical index
`Astar_Godel` associated with `(GD, L)` is strictly positive
on the witnessing batch `S`.

Equivalently: every such incompleteness witness is detected
and quantitatively separated by the 0 / > 0 boundary.
-/
theorem godelIncompleteness_quantified
    (I : GodelIncompleteness
      (Sat := Sat) (Γ_ref := Γ_ref) (B := B)) :
  0 < Astar_Godel
        (Sat := Sat) (Γ_ref := Γ_ref)
        (L := I.L) I.GD I.S :=
by
  -- From the meta-theorem already proved:
  -- 0 < Astar_Godel ↔ non-conservativity of the extension.
  have h :=
    Astar_Godel_pos_iff_nonconservative
      (Sat := Sat) (Γ_ref := Γ_ref)
      (L := I.L) I.GD I.S
  exact h.mpr I.nonCons

end Incompleteness

-- ============================================================================
-- PART 3: Integration with RefSystem / deltaObstruction
-- ============================================================================

section DeltaRefGodel

variable {Sentence : Type u} {Model : Type v}
variable (E : RefSystem Model Sentence)
variable (Γ_ref : Set Sentence)
variable {B : Type*} [Fintype B] [DecidableEq B]

/--
Canonical Gödel index induced by Δ_ref.

We fix:
* a reference system `E`,
* a base theory `Γ_ref`,
* a finite type of directions `B`,
* a family of tests `probe : B → Sentence` such that each `probe b`
  is non-local for `E`.

We then obtain a canonical legitimate obstruction
`E.deltaObstruction probe h_nonlocal`, which we plug into `Astar_Godel`.
-/
def Astar_Godel_delta
    (probe : B → Sentence)
    (h_nonlocal : ∀ b, E.isNonlocal (probe b))
    (GD : GodelDirection E.Sat Γ_ref B)
    (S : Battery Sentence) : ℝ :=
  Astar_Godel
    (Sat := E.Sat)
    (Γ_ref := Γ_ref)
    (B := B)
    (L := E.deltaObstruction probe h_nonlocal)
    GD S

/--
Specialized version of `Astar_Godel_pos_iff_nonconservative`
for the canonical obstruction coming from Δ_ref.

For every finite battery `S` and Gödel direction `GD` we have:

`0 < Astar_Godel_delta E Γ_ref probe h_nonlocal GD S`
iff
`Γ_ref ∪ S` is semantically non-conservative over `Γ_ref`.
-/
theorem Astar_Godel_delta_pos_iff_nonconservative
    (probe : B → Sentence)
    (h_nonlocal : ∀ b, E.isNonlocal (probe b))
    (GD : GodelDirection E.Sat Γ_ref B)
    (S : Battery Sentence) :
  0 < Astar_Godel_delta
        (E := E) (Γ_ref := Γ_ref)
        (B := B) probe h_nonlocal GD S
    ↔ ¬ conservativeExt (Sat := E.Sat) (Γ_ref := Γ_ref) S :=
by
  -- Unfold our abbreviation and reuse the general theorem.
  unfold Astar_Godel_delta
  simpa using
    (Astar_Godel_pos_iff_nonconservative
      (Sat := E.Sat)
      (Γ_ref := Γ_ref)
      (B := B)
      (L := E.deltaObstruction probe h_nonlocal)
      (GD := GD)
      (S := S))

end DeltaRefGodel



end GodelDynamic


section DeltaRefDiagonal



variable {Model : Type u} {Sentence : Type v} {Context : Type w}

variable (E : RefSystem Model Sentence)
variable (LR : LocalReading Context Sentence)
variable (Γ_ref : Context)

open RefSystem

/--
Truth in the reference system `E`: `φ` is true in all models
of the reference system.
-/
def refTruth (φ : Sentence) : Prop :=
  ∀ M : Model, E.Sat M φ

/--
Meta-predicate associated with Δ_ref and internal non-provability
with respect to `Γ_ref`.
-/
def DeltaMetaPred (φ : Sentence) : Prop :=
  1 ≤ E.delta φ ∧ ¬ Prov LR Γ_ref φ

/--
Gödel-style fixed-point scenario for Δ_ref (abstract Thm 8.3 version).

We package the existence of a formula `G` such that

  `refTruth E G ↔ (1 ≤ δ(G) ∧ ¬ Prov_{Γ_ref}(G))`.

We do not attempt to construct `G` here: this structure is exactly what
a Gödel-style diagonalization provides (which requires a full syntactic
formalization). We take it as a given / structured hypothesis.
-/
structure DeltaRefFixedPoint where
  G     : Sentence
  fixed :
    refTruth (E := E) G ↔
      DeltaMetaPred (E := E) (LR := LR) Γ_ref G

namespace DeltaRefFixedPoint

variable {E LR Γ_ref}
variable (fp : DeltaRefFixedPoint (E := E) (LR := LR) (Γ_ref := Γ_ref))

/--
If `G` satisfies the fixed-point scheme and the meta condition
(δ≥1, non-provability) holds, then `G` is true in the reference
system `E`.
-/
lemma truth_of_meta :
  DeltaMetaPred (E := E) (LR := LR) Γ_ref fp.G →
  refTruth (E := E) fp.G :=
(fp.fixed).mpr

/--
Conversely: if `G` is true in the reference system `E`, then it satisfies
the meta condition (δ≥1, non-provability).
-/
lemma meta_of_truth :
  refTruth (E := E) fp.G →
  DeltaMetaPred (E := E) (LR := LR) Γ_ref fp.G :=
(fp.fixed).mp

/--
In particular, if `G` is true in `E`, then `G` is not provable
from `Γ_ref` in the sense of the local reading `LR`.
-/
lemma notProv_of_truth :
  refTruth (E := E) fp.G → ¬ Prov LR Γ_ref fp.G := by
  intro htruth
  have h := fp.meta_of_truth (E := E) (LR := LR) (Γ_ref := Γ_ref) htruth
  exact h.right

/--
Still assuming `G` is true in `E`, we obtain `δ(G) ≥ 1`: `G` is
necessarily non-local (in the Δ_ref sense).
-/
lemma delta_ge_one_of_truth :
  refTruth (E := E) fp.G → 1 ≤ E.delta fp.G := by
  intro htruth
  have h := fp.meta_of_truth (E := E) (LR := LR) (Γ_ref := Γ_ref) htruth
  exact h.left

end DeltaRefFixedPoint

end DeltaRefDiagonal


end LogicDissoc
