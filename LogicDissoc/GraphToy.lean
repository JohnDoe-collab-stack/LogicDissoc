import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import LogicDissoc.BasicSemantics
import LogicDissoc.RefSystem
import LogicDissoc.DeltaObstruction
import LogicDissoc.Godel
import Mathlib.Tactic


namespace LogicDissoc.Examples

/-! # Toy example: graphs on 3 vertices

Concrete instantiation of the LogicDissoc framework on:
- a finite world of graphs `Graph3`,
- a few sentences `GraphSentence`,
- a toy `RefSystem`,
- a toy `GodelDirection`,
- and the canonical obstruction Δ_ref via `deltaObstruction`.

This toy illustrates:
- The local/non-local dichotomy via delta
- **Granularity in [1,2)**: different formulas have different weights
- Detection of non-conservativity via GodelDirection
- The meta-theorem: universal 0/>0 boundary

## Note on `noncomputable`

The function `graphDelta` and the structures depending on it are marked `noncomputable`
because they use division on ℝ (type Real), which is not computable in Lean.

**This is acceptable** for a pedagogical toy because:
1. Delta values are **conceptual** (a measure of non-locality)
2. **Decisions** (GodelDirection.dec, sat, etc.) remain computable
3. **Proofs** remain constructive (no `classical` in the tactics)
4. We are demonstrating the framework, not an effective algorithm

In a "production" implementation, one could:
- Use ℚ (rationals) instead of ℝ
- Or keep delta abstract (axiomatic) without numerical values
-/

open LogicDissoc

-- ============================================================
-- 1. Models and sentences
-- ============================================================

/-- Simple undirected graph on 3 vertices {1,2,3}. -/
structure Graph3 where
  e12 : Bool
  e13 : Bool
  e23 : Bool
deriving DecidableEq, Repr

/-- Atomic sentences of the toy example. -/
inductive GraphSentence
  | top     -- ⊤
  | conn    -- Conn
  | tri     -- Tri
  | notConn -- ¬Conn
  | notTri  -- ¬Tri
deriving DecidableEq, Repr

open GraphSentence

namespace Graph3

/-- Connectivity (toy definition): at least 2 "chained" edges. -/
def isConnected (g : Graph3) : Bool :=
  (g.e12 && g.e13) || (g.e12 && g.e23) || (g.e13 && g.e23)

/-- Complete triangle. -/
def hasTriangle (g : Graph3) : Bool :=
  g.e12 && g.e13 && g.e23

/-- Some useful graphs for the proofs. -/
def g0 : Graph3 :=
  { e12 := false, e13 := false, e23 := false }

def g4 : Graph3 :=
  { e12 := true, e13 := true, e23 := false }

def g7 : Graph3 :=
  { e12 := true, e13 := true, e23 := true }

end Graph3

open Graph3

/-- Satisfaction of sentences by a graph. -/
def sat (g : Graph3) : GraphSentence → Prop
  | top     => True
  | conn    => g.isConnected = true
  | tri     => g.hasTriangle = true
  | notConn => g.isConnected = false
  | notTri  => g.hasTriangle = false

-- ============================================================
-- 2. RefSystem on graphs
-- ============================================================

/-- Toy δ: 0 for ⊤, values in [1,2) for the others.

    The distinct values illustrate that different formulas
    have different "non-locality weights":
    - conn : 1.3 (connectivity structure)
    - notConn : 1.4 (negation of connectivity, slightly different weight)
    - tri : 1.7 (strong global structure - complete triangle)
    - notTri : 1.2 (weak property)
-/
noncomputable def graphDelta (φ : GraphSentence) : ℝ :=
  match φ with
  | GraphSentence.top     => 0
  | GraphSentence.conn    => 13/10  -- 1.3
  | GraphSentence.notConn => 14/10  -- 1.4
  | GraphSentence.tri     => 17/10  -- 1.7
  | GraphSentence.notTri  => 12/10  -- 1.2



/-- Toy reference system on `Graph3`. -/
noncomputable def GraphRefSystem : RefSystem Graph3 GraphSentence :=
{ Sat   := fun g φ => sat g φ,
  delta := graphDelta,
  -- (DR0) : δ φ = 0 ↔ φ ∈ ThE(ModE ∅)
  DR0 := by
    intro φ
    -- We use that ModE(sat, ∅) = the set of all graphs,
    -- and ThE on this set = "φ is true in all graphs".
    have hThE :
      ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) =
        { ψ : GraphSentence | ∀ g : Graph3, sat g ψ } := by
      ext ψ
      simp [ThE, ModE]
    cases φ with
    | top =>
        -- δ(top) = 0 and ⊤ is true everywhere
        constructor
        · intro _
          -- top ∈ ThE(ModE ∅)
          have h : top ∈ { ψ : GraphSentence | ∀ g : Graph3, sat g ψ } := by
            -- ⊤ is true in all graphs
            simp [sat]
          simpa [hThE] using h
        · intro _
          simp [graphDelta]

    | conn =>
        constructor
        · intro hδ
          -- δ(conn) ≠ 0, so the assumption is impossible
          have : graphDelta conn ≠ 0 := by
            norm_num [graphDelta]
          exact (this hδ).elim
        · intro hmem
          -- Unfold membership in ThE(ModE ∅) via hThE
          have hAll : ∀ g : Graph3, sat g conn := by
            have hIn :
              conn ∈ ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) :=
              hmem
            have : conn ∈ { ψ : GraphSentence | ∀ g, sat g ψ } := by
              simpa [hThE] using hIn
            exact this
          -- But g0 is not connected: contradiction
          have hNot : ¬ sat Graph3.g0 conn := by
            simp [sat, Graph3.isConnected, Graph3.g0]
          have : False := hNot (hAll _)
          exact this.elim

    | tri =>
        constructor
        · intro hδ
          have : graphDelta tri ≠ 0 := by
            norm_num [graphDelta]
          exact (this hδ).elim
        · intro hmem
          have hAll : ∀ g : Graph3, sat g tri := by
            have hIn :
              tri ∈ ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) :=
              hmem
            have : tri ∈ { ψ : GraphSentence | ∀ g, sat g ψ } := by
              simpa [hThE] using hIn
            exact this
          -- g0 has no triangle: contradiction
          have hNot : ¬ sat Graph3.g0 tri := by
            simp [sat, Graph3.hasTriangle, Graph3.g0]
          have : False := hNot (hAll _)
          exact this.elim

    | notConn =>
        constructor
        · intro hδ
          have : graphDelta notConn ≠ 0 := by
            norm_num [graphDelta]
          exact (this hδ).elim
        · intro hmem
          have hAll : ∀ g : Graph3, sat g notConn := by
            have hIn :
              notConn ∈ ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) :=
              hmem
            have : notConn ∈ { ψ : GraphSentence | ∀ g, sat g ψ } := by
              simpa [hThE] using hIn
            exact this
          -- g4 is connected, so notConn is false
          have hNot : ¬ sat Graph3.g4 notConn := by
            simp [sat, Graph3.isConnected, Graph3.g4]
          have : False := hNot (hAll _)
          exact this.elim

    | notTri =>
        constructor
        · intro hδ
          have : graphDelta notTri ≠ 0 := by
            norm_num [graphDelta]
          exact (this hδ).elim
        · intro hmem
          have hAll : ∀ g : Graph3, sat g notTri := by
            have hIn :
              notTri ∈ ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) :=
              hmem
            have : notTri ∈ { ψ : GraphSentence | ∀ g, sat g ψ } := by
              simpa [hThE] using hIn
            exact this
          -- g7 has a triangle, so notTri is false
          have hNot : ¬ sat Graph3.g7 notTri := by
            simp [sat, Graph3.hasTriangle, Graph3.g7]
          have : False := hNot (hAll _)
          exact this.elim

  -- (DR1) : non-local φ → δ(φ) ∈ [1,2)
  DR1 := by
    intro φ hNotLocal
    -- "Local" = φ ∈ ThE(ModE ∅) = true everywhere.
    -- We have seen that only top is true everywhere.
    have hThE :
      ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) =
        { ψ : GraphSentence | ∀ g : Graph3, sat g ψ } := by
      ext ψ
      simp [ThE, ModE]
    -- Show that φ ≠ top
    have hφ_ne_top : φ ≠ top := by
      intro hEq
      subst hEq
      -- top is in ThE(ModE ∅), contradiction
      have : top ∈ ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) := by
        simp [hThE, sat]
      exact hNotLocal this
    cases φ with
    | top =>
        exact (hφ_ne_top rfl).elim
    | conn =>
        constructor
        · -- 1 ≤ 13/10
          unfold graphDelta
          norm_num
        · -- 13/10 < 2
          unfold graphDelta
          norm_num
    | tri =>
        constructor
        · -- 1 ≤ 17/10
          unfold graphDelta
          norm_num
        · -- 17/10 < 2
          unfold graphDelta
          norm_num
    | notConn =>
        constructor
        · -- 1 ≤ 14/10
          unfold graphDelta
          norm_num
        · -- 14/10 < 2
          unfold graphDelta
          norm_num
    | notTri =>
        constructor
        · -- 1 ≤ 12/10
          unfold graphDelta
          norm_num
        · -- 12/10 < 2
          unfold graphDelta
          norm_num,


  -- Semantic invariance: two equivalent sentences have the same δ
  -- CRITICAL: With differentiated values, we force the real proofs
  delta_semantic_invariance := by
    intro φ ψ hEquiv
    -- Strategy: case analysis on (φ, ψ)
    -- - Diagonal: rfl
    -- - Off-diagonal: exfalso via a counterexample
    cases φ <;> cases ψ

    -- ===== Row top =====
    · -- (top, top)
      rfl
    · -- (top, conn): distinguished by g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.isConnected, Graph3.g0] at h
    · -- (top, tri): distinguished by g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.hasTriangle, Graph3.g0] at h
    · -- (top, notConn): distinguished by g4
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.g4] at h
    · -- (top, notTri): distinguished by g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.hasTriangle, Graph3.g7] at h

    -- ===== Row conn =====
    · -- (conn, top): distinguished by g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.isConnected, Graph3.g0] at h
    · -- (conn, conn)
      rfl
    · -- (conn, tri): distinguished by g4 (conn but not tri)
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g4] at h
    · -- (conn, notConn): distinguished by g0 (or g4)
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.isConnected, Graph3.g0] at h
    · -- (conn, notTri): distinguished by g7 (conn and tri, hence not notTri)
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g7] at h

    -- ===== Row tri =====
    · -- (tri, top): distinguished by g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.hasTriangle, Graph3.g0] at h
    · -- (tri, conn): distinguished by g4
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g4] at h
    · -- (tri, tri)
      rfl
    · -- (tri, notConn): distinguished by g7 (tri and conn)
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g7] at h
    · -- (tri, notTri): distinguished by g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.hasTriangle, Graph3.g7] at h

    -- ===== Row notConn =====
    · -- (notConn, top): distinguished by g4
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.g4] at h
    · -- (notConn, conn): distinguished by g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.isConnected, Graph3.g0] at h
    · -- (notConn, tri): distinguished by g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g7] at h
    · -- (notConn, notConn)
      rfl
    · -- (notConn, notTri): distinguished by g4 (conn + notTri ≠ notConn + notTri)
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g4] at h

    -- ===== Row notTri =====
    · -- (notTri, top): distinguished by g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.hasTriangle, Graph3.g7] at h
    · -- (notTri, conn): distinguished by g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g7] at h
    · -- (notTri, tri): distinguished by g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.hasTriangle, Graph3.g7] at h
    · -- (notTri, notConn): distinguished by g4
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g4] at h
    · -- (notTri, notTri)
      rfl
}

notation "E_graph" => GraphRefSystem

-- ============================================================
-- 3. Gödel directions on graphs
-- ============================================================

/-- Semantic directions of the toy example. -/
inductive GraphDir
  | conn
  | nonconn
  | tri
deriving DecidableEq, Repr

/-- Explicit finset of directions. -/
def allGraphDir : Finset GraphDir :=
  { GraphDir.conn, GraphDir.nonconn, GraphDir.tri }

/-- Finite instance for `GraphDir`. -/
instance : Fintype GraphDir where
  elems := allGraphDir
  complete := by
    intro x
    cases x <;> simp [allGraphDir]


open GraphDir

/-- Probe: formula tested by each direction. -/
def graphProbe : GraphDir → GraphSentence
  | GraphDir.conn    => GraphSentence.conn
  | GraphDir.nonconn => GraphSentence.notConn
  | GraphDir.tri     => GraphSentence.tri

/-- Predicate of realization of a direction by a graph. -/
def graphDirPred : GraphDir → Graph3 → Prop
  | GraphDir.conn,    g => sat g GraphSentence.conn
  | GraphDir.nonconn, g => sat g GraphSentence.notConn
  | GraphDir.tri,     g => sat g GraphSentence.tri


open RefSystem



/-- All formulas `probe b` are non-local in `GraphRefSystem`. -/
lemma graphProbe_nonlocal :
  ∀ b : GraphDir, GraphRefSystem.isNonlocal (graphProbe b) := by
  intro b
  have h := GraphRefSystem.nonlocal_iff_delta_band (graphProbe b)
  rw [h]
  cases b
  · -- conn: 1 ≤ 13/10 < 2
    unfold graphProbe GraphRefSystem graphDelta
    constructor <;> norm_num
  · -- nonconn: 1 ≤ 14/10 < 2
    unfold graphProbe GraphRefSystem graphDelta
    constructor <;> norm_num
  · -- tri: 1 ≤ 17/10 < 2
    unfold graphProbe GraphRefSystem graphDelta
    constructor <;> norm_num


open LogicDissoc.GodelDirection

/-- Fintype instance for Graph3. -/
instance : Fintype Graph3 where
  elems := {
    { e12 := false, e13 := false, e23 := false },
    { e12 := true,  e13 := false, e23 := false },
    { e12 := false, e13 := true,  e23 := false },
    { e12 := false, e13 := false, e23 := true },
    { e12 := true,  e13 := true,  e23 := false },
    { e12 := true,  e13 := false, e23 := true },
    { e12 := false, e13 := true,  e23 := true },
    { e12 := true,  e13 := true,  e23 := true }
  }
  complete := by
    intro ⟨e12, e13, e23⟩
    cases e12 <;> cases e13 <;> cases e23 <;> decide

instance (g : Graph3) (φ : GraphSentence) : Decidable (sat g φ) := by
  cases φ <;> unfold sat <;> infer_instance

instance (b : GraphDir) (g : Graph3) : Decidable (graphDirPred b g) := by
  cases b <;> unfold graphDirPred <;> infer_instance

/-- Toy GodelDirection for graphs. -/
def GraphGodelDirection :
  GodelDirection sat (∅ : Set GraphSentence) GraphDir :=
{ P := graphDirPred,
  dec := fun S b =>
    decidable_of_iff
      (∃ m : Graph3, (∃ φ ∈ S, ¬sat m φ) ∧ graphDirPred b m)
      (by
        simp only [ModE, Set.mem_setOf_eq, Set.empty_union]
        constructor
        · intro ⟨m, h1, h2⟩
          use m
          constructor
          · simp
          · constructor
            · intro hall
              obtain ⟨φ, hφS, hnsat⟩ := h1
              exact hnsat (hall φ hφS)
            · exact h2
        · intro ⟨m, _, hnot, hpred⟩
          use m
          constructor
          · push_neg at hnot
            exact hnot
          · exact hpred),
  separating := by
    intro S hNotCons
    have hneq :
      ModE sat ((∅ : Set GraphSentence) ∪ (↑S : Set GraphSentence)) ≠
      ModE sat (∅ : Set GraphSentence) := by
      intro hEq
      have hCons :
        LogicDissoc.conservativeExt
          (Sat := sat) (Γ_ref := (∅ : Set GraphSentence)) S := by
        simpa [LogicDissoc.conservativeExt] using hEq
      exact hNotCons hCons

    have hsubset :
      ModE sat ((∅ : Set GraphSentence) ∪ (↑S : Set GraphSentence)) ⊆
      ModE sat (∅ : Set GraphSentence) := by
      intro m hm
      simp [ModE] at hm ⊢

    have hExists :
      ∃ m,
        m ∈ ModE sat (∅ : Set GraphSentence) ∧
        ¬ m ∈ ModE sat ((∅ : Set GraphSentence) ∪ (↑S : Set GraphSentence)) := by
      by_contra h
      have hsubset' :
        ModE sat (∅ : Set GraphSentence) ⊆
        ModE sat ((∅ : Set GraphSentence) ∪ (↑S : Set GraphSentence)) := by
        intro m hm
        by_contra hm'
        apply h
        exact ⟨m, hm, hm'⟩
      have hEq :
        ModE sat ((∅ : Set GraphSentence) ∪ (↑S : Set GraphSentence)) =
        ModE sat (∅ : Set GraphSentence) :=
        Set.Subset.antisymm hsubset hsubset'
      exact hneq hEq

    rcases hExists with ⟨m, hm_ref, hm_not⟩

    by_cases hconn : sat m .conn
    · refine ⟨GraphDir.conn, m, hm_ref, hm_not, ?_⟩
      simp [graphDirPred, hconn]
    · have hnonconn : sat m .notConn := by
        simp [sat] at hconn ⊢
        cases h : m.isConnected
        · rfl
        · simp [h] at hconn
      refine ⟨GraphDir.nonconn, m, hm_ref, hm_not, ?_⟩
      simp [graphDirPred, hnonconn] }


-- ============================================================
-- 4. Canonical obstruction Δ and index A*
-- ============================================================

open RefSystem

/-- Canonical δ obstruction for the graph toy model. -/
noncomputable def GraphDeltaObstruction : LegitObstruction GraphDir :=
  RefSystem.deltaObstruction
    (E := E_graph)
    (B := GraphDir)
    graphProbe
    graphProbe_nonlocal

/-- Abbreviation: battery of sentences on graphs. -/
abbrev GraphBattery := Battery GraphSentence

/-- Gödel A* index, specialized to the graph reference system.

    With the differentiated delta values, we obtain:
    - Extension by {¬conn}: A* ≈ 1·1.3 + contributions from other directions
    - Extension by {tri}: A* different depending on which directions are eliminated
    - This illustrates the **quantification of incompleteness**
-/
noncomputable def graphAstar (S : GraphBattery) : ℝ :=
  Astar_Godel_delta
    (E := E_graph)
    (Γ_ref := (∅ : Set GraphSentence))
    (B := GraphDir)
    graphProbe
    graphProbe_nonlocal
    GraphGodelDirection
    S

/-!
## Pedagogical summary

This toy example demonstrates the full framework with **granularity in [1,2)**:

### Delta values:
- top : 0 (local)
- conn : 1.3 (connectivity)
- notConn : 1.4 (negation of connectivity)
- tri : 1.7 (triangle - strong globality)
- notTri : 1.2 (negation of triangle - weak globality)

### Observations:
1. The different values show that some formulas are "more global" than others
2. The Astar obstruction weights the eliminated directions by their delta weight
3. Extension {tri} will have a stronger weight than {notTri} in the obstruction
4. The 0/>0 theorem remains universal: only the binary verdict matters for conservativity
5. But the **numerical value** of Astar encodes the "strength" of non-conservativity

### Key points:
- ✓ Pedagogical granularity in [1,2)
- ✓ All cases of delta_semantic_invariance proved cleanly
- ✓ Complete illustration of the LogicDissoc framework
-/

end LogicDissoc.Examples
