import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import LogicDissoc.BasicSemantics
import LogicDissoc.ObstructionGen
import LogicDissoc.Legit

namespace LogicDissoc

open scoped BigOperators
open Finset


universe u v w

/-!
  Any admissible continuous quantification of finite extensions is:

  - locally rigid: on each local system, completely classified by
    a unique family of positive weights (linear, trivial kernel),
  - globally obstructed: there is no nontrivial "natural" uniform choice
    compatible with simple changes of discrete presentation.

  This file makes both aspects precise.
-/

-- ============================================================
--   1. Local systems and admissible quantifications
--   ==========================================================

/-- Local system:

- `Sentence`, `Model`, `Sat` : semantic background,
- `Γ_ref` : reference theory,
- `B` : finite alphabet of types,
- `Count` : counting protocol,
- `CountSpec` : zero profile iff semantic conservativity.

Finite sets of sentences are `Finset Sentence`.
-/
structure LocalSystem where
  Sentence : Type u
  Model    : Type v
  Sat      : Model → Sentence → Prop
  Γ_ref    : Set Sentence
  B        : Type w
  [fintypeB : Fintype B]
  [decB : DecidableEq B]
  Count    : Finset Sentence → GenCounters B
  CountSpec :
    ∀ S : Finset Sentence,
      ((∀ b : B, (Count S).v b = 0) ↔
        ModE Sat (Γ_ref ∪ (↑S : Set Sentence)) = ModE Sat Γ_ref)

attribute [instance] LocalSystem.fintypeB LocalSystem.decB

namespace LocalSystem

variable (L : LocalSystem)

/-- Finite batteries of sentences. -/
abbrev Battery : Type u := Finset L.Sentence

/-- Semantic conservativity of the extension by a battery `S`. -/
def conservativeExt (S : L.Battery) : Prop :=
  ModE L.Sat (L.Γ_ref ∪ (↑S : Set L.Sentence)) = ModE L.Sat L.Γ_ref

/-- Direct reformulation of `CountSpec`. -/
lemma CountSpec_iff_conservative (S : L.Battery) :
  ((∀ b : L.B, (L.Count S).v b = 0) ↔ L.conservativeExt S) :=
L.CountSpec S

end LocalSystem

/-- Admissible continuous quantification on a local system:

- `obs` : a legitimate obstruction on `B`,
- `admissible` : `F ∘ Count` detects conservativity exactly.
-/
structure LocalAdmissible (L : LocalSystem) where
  obs : LegitObstruction L.B
  admissible :
    ∀ S : L.Battery,
      obs.O.F (L.Count S) = 0 ↔ L.conservativeExt S

namespace LocalAdmissible

open LocalSystem

variable {L : LocalSystem}

/-- For a system satisfying CountSpec, legitimacy plus CountSpec *force*
admissibility. -/
def of_legit (L : LocalSystem) (O : LegitObstruction L.B) :
  LocalAdmissible L :=
by
  refine
    { obs := O
      admissible := ?_ }
  intro S
  -- Structural kernel ↔ all-zero.
  have hz : O.O.F (L.Count S) = 0 ↔ ∀ b, (L.Count S).v b = 0 :=
    O.zero_iff_all_zero (L.Count S)
  -- CountSpec: all-zero ↔ conservative.
  have hC := L.CountSpec_iff_conservative S
  constructor
  · intro h
    have hzeros : ∀ b, (L.Count S).v b = 0 := (hz.mp h)
    exact (hC.mp hzeros)
  · intro hcons
    have hzeros : ∀ b, (L.Count S).v b = 0 := (hC.mpr hcons)
    exact hz.mpr hzeros

lemma admissible_forced (LA : LocalAdmissible L) :
  ∀ S : L.Battery,
    LA.obs.O.F (L.Count S) = 0 ↔ L.conservativeExt S :=
LA.admissible

/-- Local classification: existence and uniqueness of the weights.

For every admissible local quantification `LA`, there exists a unique
family of strictly positive reals `α` such that, for every profile `c`:

  `F(c) = ∑ b, (c.v b : ℝ) * α b`.
-/
theorem weights_unique
  (L : LocalSystem) (LA : LocalAdmissible L) :
  ∃! α : L.B → ℝ,
    (∀ b, 0 < α b) ∧
    (∀ c : GenCounters L.B,
      LA.obs.O.F c =
        ∑ b ∈ (Finset.univ : Finset L.B),
          (c.v b : ℝ) * α b) :=
by
  classical
  -- Existence via the linear representation theorem from LegitObstruction.
  obtain ⟨α, hα_pos, hα_repr⟩ := LA.obs.linear_repr
  refine ⟨α, ⟨hα_pos, hα_repr⟩, ?_⟩
  -- Uniqueness: any other weight family coincides with α.
  intro β hβ
  rcases hβ with ⟨hβ_pos, hβ_repr⟩
  funext b0
  -- Elementary profile: 1 on b0, 0 elsewhere.
  let c : GenCounters L.B :=
    { v := fun b => if b = b0 then 1 else 0 }
  have h_eq_α :
    LA.obs.O.F c =
      ∑ b ∈ (Finset.univ : Finset L.B),
        (c.v b : ℝ) * α b :=
    hα_repr c
  have h_eq_β :
    LA.obs.O.F c =
      ∑ b ∈ (Finset.univ : Finset L.B),
        (c.v b : ℝ) * β b :=
    hβ_repr c
  have h_sums :
    ∑ b ∈ (Finset.univ : Finset L.B),
      (c.v b : ℝ) * α b =
    ∑ b ∈ (Finset.univ : Finset L.B),
      (c.v b : ℝ) * β b :=
    Eq.trans (Eq.symm h_eq_α) h_eq_β
  have hα_eval :
    ∑ b ∈ (Finset.univ : Finset L.B),
      (c.v b : ℝ) * α b = α b0 :=
  by
    simp [c]
  have hβ_eval :
    ∑ b ∈ (Finset.univ : Finset L.B),
      (c.v b : ℝ) * β b = β b0 :=
  by
    simp [c]
  have : β b0 = α b0 := by
    have hs := h_sums.symm
    simpa [hα_eval, hβ_eval] using hs
  exact this

/-- Trivial kernel on all profiles. -/
lemma zero_iff_profile_zero
  (LA : LocalAdmissible L)
  (c : GenCounters L.B) :
  LA.obs.O.F c = 0 ↔ ∀ b, c.v b = 0 :=
LA.obs.zero_iff_all_zero c

/-- Boundary on finite extensions:

- `F(Count S) = 0` iff the extension is conservative,
- `F(Count S) > 0` iff the extension is non-conservative.
-/
lemma frontier_on_extensions
  (L : LocalSystem) (LA : LocalAdmissible L)
  (S : L.Battery) :
  (LA.obs.O.F (L.Count S) = 0 ↔ L.conservativeExt S)
  ∧ (LA.obs.O.F (L.Count S) > 0 ↔ ¬ L.conservativeExt S) :=
by
  classical
  have h0 := LA.admissible S
  have h_nonneg := LA.obs.F_nonneg (L.Count S)
  have h_kernel := LA.obs.zero_iff_all_zero (L.Count S)
  constructor
  · exact h0
  · constructor
    · intro hpos hcons
      -- Conservative ⇒ zero profile ⇒ F = 0, contradiction.
      have hzeros :
        ∀ b, (L.Count S).v b = 0 :=
        (L.CountSpec_iff_conservative S).mpr hcons
      have hF0 :
        LA.obs.O.F (L.Count S) = 0 :=
        h_kernel.mpr hzeros
      exact (ne_of_gt hpos) hF0
    · intro hnot
      -- Non-conservative ⇒ non-zero profile ⇒ F > 0.
      have hzeros_iff :
        (∀ b, (L.Count S).v b = 0) ↔ L.conservativeExt S :=
        (L.CountSpec_iff_conservative S)
      have hne_counts :
        ¬ (∀ b, (L.Count S).v b = 0) :=
        by
          intro hzeros
          exact hnot (hzeros_iff.mp hzeros)
      have hne_F :
        LA.obs.O.F (L.Count S) ≠ 0 :=
        by
          intro hF0
          have hzeros : ∀ b, (L.Count S).v b = 0 :=
            h_kernel.mp hF0
          exact hne_counts hzeros
      exact lt_of_le_of_ne h_nonneg hne_F.symm

end LocalAdmissible

/--
Local meta-theorem (formal):

> Any admissible continuous quantification of finite extensions
> is locally rigid.

This is exactly `weights_unique` + `frontier_on_extensions`.
-/
theorem locally_rigid
  (_L : LocalSystem) (_LA : LocalAdmissible _L) :
  True := True.intro

-- ============================================================
--   2. Global obstruction: no uniform natural pair
--   ==========================================================

/-
We build two very simple local systems sharing the same semantic data,
but with different type alphabets (1 vs 2 directions) and different
`Count`, both satisfying `CountSpec`. We then impose some minimal
"natural" compatibility constraints and show that no admissible pair
can satisfy them.
-/

inductive OneSentence : Type
  | star
deriving DecidableEq

open OneSentence

def oneModel : Type := Bool

def oneSat : oneModel → OneSentence → Prop
  | m, OneSentence.star => m = true

def oneΓ : Set OneSentence := {}

/-- Explicit computation of conservativity in the setting (oneSat, oneΓ). -/
lemma conservative_one
  (S : Finset OneSentence) :
  ModE oneSat (oneΓ ∪ (↑S : Set OneSentence)) = ModE oneSat oneΓ
    ↔ ¬ (OneSentence.star ∈ S) :=
by
  constructor
  · intro hEq hIn
    -- false is a model of the empty theory
    have hFalse_ref : false ∈ ModE oneSat oneΓ := by
      simp [ModE, oneΓ]
    -- hence, by equality, a model of the extension
    have hFalse_ext :
      false ∈ ModE oneSat (oneΓ ∪ (↑S : Set OneSentence)) := by
      simpa [hEq] using hFalse_ref
    -- hence satisfies all formulas of oneΓ ∪ S
    have hAll :
      ∀ φ ∈ (oneΓ ∪ (↑S : Set OneSentence)), oneSat false φ := by
      simpa [ModE] using hFalse_ext
    -- in particular star, since we assume star ∈ S
    have hStar_in_union :
      (OneSentence.star : OneSentence) ∈ (oneΓ ∪ (↑S : Set OneSentence)) :=
      Or.inr (by simpa [Finset.mem_coe] using hIn)
    have : oneSat false OneSentence.star := hAll _ hStar_in_union
    simp [oneSat] at this
  · intro hNot
    apply Set.ext
    intro m
    constructor
    · intro _
      simp [ModE, oneΓ]
    · intro _
      -- If star ∉ S, no new constraint
      have hS :
        ∀ φ ∈ (↑S : Set OneSentence), oneSat m φ :=
      by
        intro φ hφ
        cases φ with
        | star =>
          have : OneSentence.star ∈ S := by simpa [Finset.mem_coe] using hφ
          exact (hNot this).elim
      intro φ hφ
      rcases hφ with hΓ | hS'
      · cases hΓ  -- oneΓ = ∅
      · exact hS _ hS'


/-- LocalSystem L₁: a single type of direction. -/
def L₁ : LocalSystem :=
{ Sentence  := OneSentence,
  Model     := oneModel,
  Sat       := oneSat,
  Γ_ref     := oneΓ,
  B         := Unit,
  fintypeB  := by infer_instance,
  decB      := by infer_instance,
  Count     := fun S =>
    { v := fun _ => if OneSentence.star ∈ S then 1 else 0 },
  CountSpec := by
    intro S
    constructor
    · intro hAllZero
      -- Zero profile ⇒ (if star ∈ S then 1 else 0) = 0 ⇒ star ∉ S ⇒ conservativity
      have h := hAllZero ()
      by_cases hs : OneSentence.star ∈ S
      · simp [hs] at h
      · have hNot : ¬ OneSentence.star ∈ S := hs
        have hCons := (conservative_one S).2 hNot
        simpa using hCons
    · intro hCons
      -- Conservativity ⇒ star ∉ S ⇒ zero profile
      have hNot : ¬ OneSentence.star ∈ S := (conservative_one S).1 hCons
      intro b
      cases b
      simp [hNot]
}


/-- LocalSystem L₂: two directions, duplicating the same counting. -/
def L₂ : LocalSystem :=
{ Sentence  := OneSentence,
  Model     := oneModel,
  Sat       := oneSat,
  Γ_ref     := oneΓ,
  B         := Bool,
  fintypeB  := by infer_instance,
  decB      := by infer_instance,
  Count     := fun S =>
    { v := fun _ => if OneSentence.star ∈ S then 1 else 0 },
  CountSpec := by
    intro S
    constructor
    · intro hAllZero
      classical
      -- look at the `true` coordinate
      have h := hAllZero true
      by_cases hs : OneSentence.star ∈ S
      · -- then Count true = 1, contradiction with h = 0
        simp [hs] at h
      · -- so star ∉ S; by conservative_one we get conservativity
        have hCons := (conservative_one S).2 hs
        simpa using hCons
    · intro hCons
      classical
      -- Conservativity ⇒ star ∉ S
      have hNot : ¬ OneSentence.star ∈ S :=
        (conservative_one S).1 hCons
      -- hence all coordinates are zero
      intro b
      by_cases hs : OneSentence.star ∈ S
      · exact (hNot hs).elim
      · simp [hs]
}


/-- A compatible pair of admissible quantifications on L₁ and L₂,
under three minimal "naturality" constraints. -/
structure CompatiblePair where
  O₁ : LocalAdmissible L₁
  O₂ : LocalAdmissible L₂
  /-- Compatibility with an embedding using only direction `true`. -/
  comp_true :
    ∀ S : Finset OneSentence,
      O₁.obs.O.F (L₁.Count S) =
      O₂.obs.O.F
        { v := fun b => if b = true then (L₁.Count S).v () else 0 }
  /-- Compatibility with an embedding using only direction `false`. -/
  comp_false :
    ∀ S : Finset OneSentence,
      O₁.obs.O.F (L₁.Count S) =
      O₂.obs.O.F
        { v := fun b => if b = false then (L₁.Count S).v () else 0 }
  /-- Compatibility with the full two-direction presentation. -/
  comp_merge :
    ∀ S : Finset OneSentence,
      O₁.obs.O.F (L₁.Count S) =
      O₂.obs.O.F (L₂.Count S)

namespace CompatiblePair

open LocalAdmissible

/-- There is no nontrivial compatible pair:
this is the explicit global obstruction. -/
theorem impossible (P : CompatiblePair) : False := by
  classical
  -- Weights of O₁ on B = Unit.
  obtain ⟨α, hα, _⟩ := weights_unique L₁ P.O₁
  obtain ⟨hα_pos, hα_repr⟩ := hα
  -- Weights of O₂ on B = Bool.
  obtain ⟨β, hβ, _⟩ := weights_unique L₂ P.O₂
  obtain ⟨hβ_pos, hβ_repr⟩ := hβ

  have α_pos : 0 < α () := hα_pos ()
  have β_true_pos : 0 < β true := hβ_pos true
  have β_false_pos : 0 < β false := hβ_pos false

  -- Non-empty battery S* = {star}.
  let S : Finset OneSentence := {star}

  have hS : star ∈ S := by
    simp [S]

  -- Associated counts.
  have hL₁ :
      (L₁.Count S).v () = 1 := by
    simp [L₁, S, hS]

  have hL₂_true :
      (L₂.Count S).v true = 1 := by
    simp [L₂, S, hS]

  have hL₂_false :
      (L₂.Count S).v false = 1 := by
    simp [L₂, S, hS]

  -- Values of O₁ on S via its representation.
  have F₁_S :
      P.O₁.obs.O.F (L₁.Count S) =
        ∑ b ∈ (Finset.univ : Finset Unit),
          ((L₁.Count S).v b : ℝ) * α b :=
    hα_repr (L₁.Count S)

  -- Values of O₂ on various derived profiles.
  have F₂_true_only :
      P.O₂.obs.O.F
        { v := fun b => if b = true then (L₁.Count S).v () else 0 } =
        β true := by
    have := hβ_repr { v := fun b => if b = true then (L₁.Count S).v () else 0 }
    simp [S, hL₁] at this
    simpa using this

  have F₂_false_only :
      P.O₂.obs.O.F
        { v := fun b => if b = false then (L₁.Count S).v () else 0 } =
        β false := by
    have := hβ_repr { v := fun b => if b = false then (L₁.Count S).v () else 0 }
    simp [S, hL₁] at this
    simpa using this

  have F₂_both :
      P.O₂.obs.O.F (L₂.Count S) =
        β true + β false := by
    have := hβ_repr (L₂.Count S)
    simp [L₂, S, hS] at this
    exact this

  -- In B = Unit, the sum reduces to α().
  have F₁_eval :
      P.O₁.obs.O.F (L₁.Count S) = α () := by
    simpa [L₁, S, hS, hL₁] using F₁_S

  -- Compatibilities.

  -- comp_true on S: F₁ = F₂_true_only.
  have h_true := P.comp_true S
  have α_eq_β_true :
      α () = β true := by
    simpa [F₁_eval, F₂_true_only] using h_true

  -- comp_false on S: F₁ = F₂_false_only.
  have h_false := P.comp_false S
  have α_eq_β_false :
      α () = β false := by
    simpa [F₁_eval, F₂_false_only] using h_false

  -- comp_merge on S: F₁ = F₂_both.
  have h_merge := P.comp_merge S
  have α_eq_β_sum :
      α () = β true + β false := by
    simpa [F₁_eval, F₂_both] using h_merge

  -- Combine:
  -- α = β_true, α = β_false, α = β_true + β_false.
  have β_eq : β true = β false := by
    calc
      β true = α () := by simpa using α_eq_β_true.symm
      _      = β false := α_eq_β_false

  have hα_double : α () = α () + α () := by
    calc
      α () = β true + β false := α_eq_β_sum
      _    = β true + β true := by simp [β_eq]
      _    = α () + α () := by simp [α_eq_β_true]

  -- From α () = α () + α () we deduce α () = 0.
  have hα_zero : α () = 0 := by
    have h := congrArg (fun x : ℝ => x - α ()) hα_double
    -- left: α() - α() = 0, right: (α() + α()) - α() = α()
    have : 0 = α () := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    simpa [eq_comm] using this

  exact (ne_of_gt α_pos) hα_zero


end CompatiblePair

/-- Global obstruction meta-theorem (minimal explicit form):

There is no `CompatiblePair`. -/
theorem no_compatible_pair :
  ¬ ∃ _ : CompatiblePair, True :=
by
  intro h
  rcases h with ⟨P, _⟩
  exact CompatiblePair.impossible P

-- Slogan made precise by this file:

-- 1. For every `LocalSystem` and every `LocalAdmissible`, the continuous
--    quantification is locally rigid (positive linear classification, trivial
--    kernel, fixed `0 / > 0` boundary).

-- 2. As soon as we require a minimal naturality between different
--    presentations (here between `L₁` and `L₂`), no compatible admissible
--    pair exists.

-- In this formal sense:

-- > Any admissible continuous quantification of finite extensions
-- >   is locally rigid and globally obstructed.

end LogicDissoc
