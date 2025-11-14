-- LogicDissoc/Rev.lean
import Mathlib.Data.Nat.Basic

namespace LogicDissoc

/-! ### Traces and temporal closure -/

/-- A temporal trace: at each time `n`, a proposition may hold. -/
abbrev Trace := ℕ → Prop

/-- Temporal closure: `(up T) n` means “there exists `k ≤ n` with `T k`”. -/
def up (T : Trace) : Trace :=
  fun n => ∃ k ≤ n, T k

lemma up_mono (T : Trace) :
  ∀ {n m : ℕ}, n ≤ m → up T n → up T m := by
  intro n m hnm h
  rcases h with ⟨k, hk_le_n, hk_T⟩
  exact ⟨k, Nat.le_trans hk_le_n hnm, hk_T⟩

lemma exists_up_iff (T : Trace) :
  (∃ n, up T n) ↔ ∃ n, T n := by
  constructor
  · rintro ⟨n, hn⟩
    rcases hn with ⟨k, hk_le_n, hk_T⟩
    exact ⟨k, hk_T⟩
  · rintro ⟨k, hk_T⟩
    refine ⟨k, ?_⟩
    exact ⟨k, le_rfl, hk_T⟩

lemma exists_up_tail_eq (T U : Trace)
    (hTail : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (up T n ↔ up U n)) :
  (∃ n : ℕ, up T n) ↔ ∃ n : ℕ, up U n := by
  rcases hTail with ⟨N, hN⟩
  constructor
  · rintro ⟨n0, hn0⟩
    let m := Nat.max n0 N
    have h_le_m : n0 ≤ m := Nat.le_max_left _ _
    have hUpTm : up T m := up_mono T h_le_m hn0
    have hN_le_m : N ≤ m := Nat.le_max_right _ _
    have hEquiv : up T m ↔ up U m := hN m hN_le_m
    have hUpUm : up U m := hEquiv.mp hUpTm
    exact ⟨m, hUpUm⟩
  · rintro ⟨n0, hn0⟩
    let m := Nat.max n0 N
    have h_le_m : n0 ≤ m := Nat.le_max_left _ _
    have hUpUm : up U m := up_mono U h_le_m hn0
    have hN_le_m : N ≤ m := Nat.le_max_right _ _
    have hEquiv : up T m ↔ up U m := hN m hN_le_m
    have hUpTm : up T m := hEquiv.mpr hUpUm
    exact ⟨m, hUpTm⟩


/-! ### Tail projectors and revision -/

/--
Abstract tail projector acting on traces after `up`:

* `Q1` : `pi (up T)` detects whether `T` ever holds at some time.
* `Q2` : `pi (up T)` is invariant under tail equivalence of `up T`.
-/
structure QueueProjector where
  pi : Trace → Prop
  Q1 : ∀ T : Trace, pi (up T) ↔ ∃ n : ℕ, T n
  Q2 :
    ∀ {T U : Trace},
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → (up T n ↔ up U n)) →
        (pi (up T) ↔ pi (up U))


/-- Canonical projector: `pi S := ∃ n, S n`. -/
def canonicalQueueProjector : QueueProjector where
  pi S := ∃ n : ℕ, S n
  Q1 T := by
    -- `pi (up T) = ∃ n, up T n` iff `∃ n, T n`
    simpa using exists_up_iff T
  Q2 {T U} hTail := by
    -- `pi (up T) = ∃ n, up T n`, similarly for `U`,
    -- and `exists_up_tail_eq` gives the equivalence.
    simpa using exists_up_tail_eq T U hTail

/-- Revision operator `Rev := pi ∘ up`. -/
def Rev (Q : QueueProjector) (T : Trace) : Prop :=
  Q.pi (up T)

/-- Concrete revision via the canonical projector. -/
def Rev0 (T : Trace) : Prop :=
  Rev canonicalQueueProjector T

/-! ### Local reading, provability, verdict -/

universe u v

/--
Abstract local reading: to each pair `(Γ, φ)` it assigns a temporal trace.
-/
abbrev LocalReading (Context : Type v) (Sentence : Type u) :=
  Context → Sentence → Trace

/-- Provability: there exists a time at which the reading of `φ` under `Γ` holds. -/
def Prov {Context : Type v} {Sentence : Type u}
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) : Prop :=
  ∃ n : ℕ, LR Γ φ n

/-- Stabilized verdict via `Rev0`. -/
def verdict {Context : Type v} {Sentence : Type u}
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) : Prop :=
  Rev0 (LR Γ φ)

/--
Equivalence between stabilized verdict and provability:

the stabilized verdict for `(Γ, φ)` is true iff `φ` is provable from `Γ`
in the sense of the local reading `LR`.
-/
lemma verdict_iff_Prov
    {Context : Type v} {Sentence : Type u}
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) :
  verdict LR Γ φ ↔ Prov LR Γ φ := by
  unfold verdict Rev0 Rev Prov
  -- goal: `canonicalQueueProjector.pi (up (LR Γ φ)) ↔ ∃ n, LR Γ φ n`
  simpa using (canonicalQueueProjector.Q1 (LR Γ φ))


/-! ### Robustness with respect to the queue projector -/

/-- For any queue projector `Q`, `Rev Q T` is equivalent to `∃ n, T n`. -/
lemma Rev_iff_exists (Q : QueueProjector) (T : Trace) :
  Rev Q T ↔ ∃ n, T n := by
  unfold Rev
  simpa using Q.Q1 T

/-- Verdict associated with an arbitrary `QueueProjector` `Q`. -/
def verdictQ {Context : Type v} {Sentence : Type u}
    (Q : QueueProjector)
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) : Prop :=
  Rev Q (LR Γ φ)

/-- For every `Q`, the stabilized verdict coincides with `Prov`. -/
lemma verdictQ_iff_Prov
    {Context : Type v} {Sentence : Type u}
    (Q : QueueProjector)
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) :
  verdictQ Q LR Γ φ ↔ Prov LR Γ φ := by
  unfold verdictQ Prov
  -- `Rev Q (LR Γ φ) ↔ ∃ n, LR Γ φ n`
  simpa using (Rev_iff_exists Q (LR Γ φ))

end LogicDissoc


/-! ### Direct halting and its relation to `Rev` -/

namespace LogicDissoc

/-- Direct halting predicate on traces: `Halts T` iff `T` holds at some time. -/
def Halts (T : Trace) : Prop := ∃ n : ℕ, T n

lemma Halts_iff_exists (T : Trace) :
  Halts T ↔ ∃ n, T n := Iff.rfl

/-- For any queue projector `Q`, `Rev Q` coincides extensionally with `Halts`. -/
lemma Rev_iff_Halts (Q : QueueProjector) (T : Trace) :
  Rev Q T ↔ Halts T := by
  -- `Rev Q T ↔ ∃ n, T n` by `Rev_iff_exists`,
  -- and `Halts T ↔ ∃ n, T n` by definition.
  simpa [Halts] using Rev_iff_exists Q T

/-- Extensional equality: `Rev Q` *is* the direct halting predicate `Halts`. -/
lemma Rev_eq_Halts (Q : QueueProjector) :
  Rev Q = Halts := by
  funext T
  apply propext
  exact Rev_iff_Halts Q T

/-- In particular, the canonical revision `Rev0` is also just `Halts`. -/
lemma Rev0_iff_Halts (T : Trace) :
  Rev0 T ↔ Halts T := by
  -- `Rev0 T = Rev canonicalQueueProjector T`
  simpa [Rev0, Halts] using Rev_iff_exists canonicalQueueProjector T

lemma Rev0_eq_Halts :
  Rev0 = Halts := Rev_eq_Halts canonicalQueueProjector

end LogicDissoc


/-! ### Direct halting for a local reading -/

namespace LogicDissoc

universe u v

/-- Direct halting for a local reading: the trace `LR Γ φ` ever holds. -/
def HaltsLR {Context : Type v} {Sentence : Type u}
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) : Prop :=
  ∃ n : ℕ, LR Γ φ n

lemma HaltsLR_iff_Prov
    {Context : Type v} {Sentence : Type u}
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) :
  HaltsLR LR Γ φ ↔ Prov LR Γ φ := Iff.rfl

/-- `verdict` is the reverse-halting version of `HaltsLR`, and they coincide. -/
lemma verdict_iff_HaltsLR
    {Context : Type v} {Sentence : Type u}
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) :
  verdict LR Γ φ ↔ HaltsLR LR Γ φ := by
  -- `verdict ↔ Prov` (déjà prouvé), et `Prov = HaltsLR` par déf.
  simpa [HaltsLR_iff_Prov] using verdict_iff_Prov LR Γ φ

/-- Pour un projecteur arbitraire `Q`, même résultat. -/
lemma verdictQ_iff_HaltsLR
    {Context : Type v} {Sentence : Type u}
    (Q : QueueProjector)
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) :
  verdictQ Q LR Γ φ ↔ HaltsLR LR Γ φ := by
  -- `verdictQ ↔ Prov` (déjà prouvé), et `Prov = HaltsLR` par déf.
  simpa [HaltsLR_iff_Prov] using verdictQ_iff_Prov Q LR Γ φ


end LogicDissoc
