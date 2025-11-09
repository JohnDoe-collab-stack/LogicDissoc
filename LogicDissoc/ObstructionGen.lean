import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finprod

namespace LogicDissoc

open scoped BigOperators
open Finset

/-- Vecteur de compteurs générique sur un ensemble de types d'obstruction `B`.
-/
structure GenCounters (B : Type*) where
  v : B → ℕ

/--
Axiomes abstraits pour une fonction d'obstruction sur `ℕ^B`.
On somme toujours sur `Finset.univ`, donc on exige `[Fintype B] [DecidableEq B]`.
-/
structure ObstructionAxiomsGen (B : Type*) [Fintype B] [DecidableEq B] where
  F   : GenCounters B → ℝ
  f   : B → ℕ → ℝ
  hF  : ∀ c, F c = ∑ b ∈ (Finset.univ : Finset B), f b (c.v b)
  f0    : ∀ b, f b 0 = 0
  f_pos : ∀ b {n}, 0 < n → 0 < f b n
  f_add : ∀ b m n, f b (m + n) = f b m + f b n

namespace ObstructionAxiomsGen

variable {B : Type*} [Fintype B] [DecidableEq B]
variable (O : ObstructionAxiomsGen B)

/-- Additivité + f(0)=0 ⇒ linéarité sur ℕ pour chaque type.
-/
lemma f_linear (b : B) : ∀ n, O.f b n = (n : ℝ) * O.f b 1 := by
  intro n
  induction n with
  | zero =>
      simp [O.f0]
  | succ n ih =>
      have h := O.f_add b n 1
      have h' : O.f b (Nat.succ n) = O.f b n + O.f b 1 := by
        simpa [Nat.succ_eq_add_one] using h
      calc
        O.f b (Nat.succ n)
            = O.f b n + O.f b 1 := h'
        _ = (n : ℝ) * O.f b 1 + O.f b 1 := by simp [ih]
        _ = ((Nat.succ n : ℕ) : ℝ) * O.f b 1 := by
              simp [Nat.succ_eq_add_one, add_mul, one_mul, add_comm]

/-- Coefficient α_b associé à chaque type b.
-/
def α (b : B) : ℝ := O.f b 1

lemma α_pos (b : B) : 0 < O.α b := by
  have h1 : 0 < (1 : ℕ) := Nat.succ_pos 0
  simpa [α] using O.f_pos b h1

/-- Forme linéaire canonique : `F(c) = ∑ b (c.v b) * α_b`.
-/
lemma canonical (c : GenCounters B) :
  O.F c = ∑ b ∈ (Finset.univ : Finset B), (c.v b : ℝ) * O.α b := by
  classical
  have hF := O.hF c
  have hlin : ∀ b, O.f b (c.v b) = (c.v b : ℝ) * O.α b := by
    intro b
    have := O.f_linear b (c.v b)
    simpa [α] using this
  simpa [hlin] using hF

/--
Si `f b ≥ 0` pour tout `b` et `∑_{b ∈ univ} f b = 0`,
alors `f b = 0` pour tout `b`.
-/
lemma all_terms_zero_of_sum_zero
  (f : B → ℝ)
  (h_nonneg : ∀ b, 0 ≤ f b)
  (h_sum : ∑ b ∈ (Finset.univ : Finset B), f b = 0) :
  ∀ b, f b = 0 := by
  classical
  intro b0
  by_contra hb0
  have hb0pos : 0 < f b0 :=
    lt_of_le_of_ne (h_nonneg b0) (Ne.symm hb0)

  let s : Finset B := Finset.univ
  have hb0mem : b0 ∈ s := by simp [s]

  have hdecomp :
      ∑ b ∈ s, f b =
        (∑ b ∈ s.erase b0, f b) + f b0 := by
    have h := Finset.sum_erase_add (s := s) (f := f) (a := b0) hb0mem
    exact h.symm

  have hrest_nonneg :
      0 ≤ ∑ b ∈ s.erase b0, f b := by
    refine Finset.induction ?_ ?_ (s := s.erase b0)
    · simp
    · intro a t ha_notin ih
      have hfa : 0 ≤ f a := h_nonneg a
      have ht : 0 ≤ ∑ x ∈ t, f x := ih
      have : 0 ≤ f a + ∑ x ∈ t, f x := add_nonneg hfa ht
      simpa [Finset.sum_insert ha_notin] using this

  have hpos_total :
      0 < (∑ b ∈ s.erase b0, f b) + f b0 :=
    lt_of_lt_of_le hb0pos (le_add_of_nonneg_left hrest_nonneg)

  have hsum' :
      (∑ b ∈ s.erase b0, f b) + f b0 = 0 := by
    exact hdecomp ▸ h_sum

  have ne : 0 ≠ (∑ b ∈ s.erase b0, f b) + f b0 := ne_of_lt hpos_total
  exact ne hsum'.symm



/--
Critère zéro général :
`O.F c = 0` ssi tous les compteurs `c.v b` sont nuls.
-/
lemma zero_iff_all_zero (c : GenCounters B) :
  O.F c = 0 ↔ (∀ b, c.v b = 0) := by
  classical
  constructor
  · intro h0
    have hF := O.canonical c
    have hsum :
        ∑ b ∈ (Finset.univ : Finset B),
          (c.v b : ℝ) * O.α b = 0 := by
      simpa [hF] using h0
    have h_nonneg : ∀ b,
        0 ≤ (c.v b : ℝ) * O.α b := by
      intro b
      exact mul_nonneg
        (by exact_mod_cast Nat.zero_le (c.v b))
        (le_of_lt (O.α_pos b))
    have h_each :=
      all_terms_zero_of_sum_zero
        (B := B)
        (f := fun b => (c.v b : ℝ) * O.α b)
        h_nonneg
        hsum
    intro b
    specialize h_each b
    have hmul := mul_eq_zero.mp h_each
    cases hmul with
    | inl hv =>
        exact (Nat.cast_eq_zero).1 hv
    | inr hα0 =>
        exact (False.elim ((ne_of_gt (O.α_pos b)) hα0))
  · intro h_all
    have hF := O.canonical c
    simp [hF, h_all]

variable {B : Type*} [Fintype B]

/-- Mesure totale d'un profil d'obstruction : somme des multiplicités.
-/
def mu (c : GenCounters B) [DecidableEq B] : ℕ :=
  ∑ b ∈ (Finset.univ : Finset B), c.v b

/--
Induction forte sur les profils `GenCounters B` via la mesure `mu`.
Si `P` vaut pour tout profil de mesure nulle,
et si pour tout profil `c` la validité de `P` pour tous les profils
de mesure strictement plus petite entraîne `P c`,
alors `P` vaut pour tout profil.
-/
lemma induction_on_mu
  [DecidableEq B]
  {P : GenCounters B → Prop}
  (h_base :
    ∀ c : GenCounters B, mu c = 0 → P c)
  (h_step :
    ∀ c : GenCounters B,
      (∀ c' : GenCounters B, mu c' < mu c → P c') →
      P c) :
  ∀ c : GenCounters B, P c := by
  classical
  have main :
    ∀ n : ℕ, ∀ c : GenCounters B, mu c = n → P c :=
  by
    intro n
    refine
      Nat.strongRecOn n
        (motive := fun n => ∀ c : GenCounters B, mu c = n → P c)
        ?step
    intro n ih c hc
    by_cases hn : n = 0
    · subst hn
      exact h_base c hc
    · apply h_step c
      intro c' hlt
      have : mu c' < n := by
        simpa [hc] using hlt
      exact ih (mu c') this c' rfl
  intro c
  exact main (mu c) c rfl

end ObstructionAxiomsGen


/-- Verdict logique "aucune obstruction" extrait d'un profil de compteurs.
-/
def sp_ok {B} [Fintype B] [DecidableEq B]
    (O : ObstructionAxiomsGen B) (c : GenCounters B) : Prop :=
  O.F c = 0

lemma sp_ok_iff_all_zero {B} [Fintype B] [DecidableEq B]
    (O : ObstructionAxiomsGen B) (c : GenCounters B) :
  sp_ok O c ↔ (∀ b, c.v b = 0) := by
  simpa [sp_ok] using
    (ObstructionAxiomsGen.zero_iff_all_zero (O := O) c)


section DiscreteBattery

variable {B Test : Type*} [Fintype B] [DecidableEq B] [Fintype Test]

variable (J : Test → GenCounters B)
variable (O : ObstructionAxiomsGen B)

/-- Profil global = somme des compteurs sur tous les tests.
-/
def globalCounters : GenCounters B :=
  { v := fun b =>
      ∑ t ∈ (Finset.univ : Finset Test), (J t).v b }

lemma global_sp_ok_iff_all_tests_ok :
  (sp_ok O (globalCounters J)) ↔
    (∀ t, sp_ok O (J t)) := by
  classical
  constructor
  · intro hF0 t
    have h_all_zero := (O.zero_iff_all_zero (globalCounters J)).1 hF0
    have : ∀ b, (J t).v b = 0 := by
      intro b
      have hglob := h_all_zero b
      unfold globalCounters at hglob
      simp only at hglob
      have hsum :
          ∑ t ∈ (Finset.univ : Finset Test), (J t).v b = 0 := by
        simpa using hglob
      have : (J t).v b = 0 := by
        have h_nonneg :
            ∀ t ∈ (Finset.univ : Finset Test),
              0 ≤ (J t).v b := by
          intro t _; exact Nat.zero_le _
        have := Finset.sum_eq_zero_iff_of_nonneg h_nonneg
        have h_all := this.mp hsum
        have ht_mem : t ∈ (Finset.univ : Finset Test) := by simp
        exact h_all t ht_mem
      exact this
    have hFJ :=
      (O.zero_iff_all_zero (J t)).2 this
    exact hFJ
  · intro h_all
    have : ∀ t, O.F (J t) = 0 := h_all
    have hJ0 : ∀ t b, (J t).v b = 0 := by
      intro t b
      have hF := this t
      have := (O.zero_iff_all_zero (J t)).1 hF
      exact this b
    have hglob0 : ∀ b, (globalCounters J).v b = 0 := by
      intro b
      unfold globalCounters
      simp [hJ0]
    exact (O.zero_iff_all_zero (globalCounters J)).2 hglob0

end DiscreteBattery

end LogicDissoc
