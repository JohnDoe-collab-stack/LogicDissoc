-- LogicDissoc/Rev.lean
import Mathlib.Data.Nat.Basic

namespace LogicDissoc

/-! ### Traces, Up -/

/-- Une trace temporelle : à chaque instant `n`, une proposition peut valoir. -/
abbrev Trace := ℕ → Prop

/-- Clôture temporelle : `(up T) n` signifie « il y a eu un `k ≤ n` avec `T k`. » -/
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


/-! ### Projecteurs de queue et révision -/

/--
Projecteur de queue abstrait (à la SLE), agissant sur les traces après `up` :

* `Q1` : `pi (up T)` détecte si `T` est vrai à un instant quelconque.
* `Q2` : invariance de `pi (up T)` par égalité de queue de `up T`.
-/
structure QueueProjector where
  pi : Trace → Prop
  Q1 : ∀ T : Trace, pi (up T) ↔ ∃ n : ℕ, T n
  Q2 :
    ∀ {T U : Trace},
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → (up T n ↔ up U n)) →
        (pi (up T) ↔ pi (up U))


/-- Projecteur canonique : `pi S := ∃ n, S n`. -/
def canonicalQueueProjector : QueueProjector where
  pi S := ∃ n : ℕ, S n
  Q1 T := by
    -- pi (up T) = ∃ n, up T n ↔ ∃ n, T n
    simpa using exists_up_iff T
  Q2 {T U} hTail := by
    -- pi (up T) = ∃ n, up T n, idem pour U,
    -- et `exists_up_tail_eq` donne l'équivalence.
    simpa using exists_up_tail_eq T U hTail

/-- Opérateur de révision `Rev := pi ∘ up`. -/
def Rev (Q : QueueProjector) (T : Trace) : Prop :=
  Q.pi (up T)

/-- Révision concrète via le projecteur canonique. -/
def Rev0 (T : Trace) : Prop :=
  Rev canonicalQueueProjector T

/-! ### Lecture locale, provabilité, verdict -/

universe u v

/--
Lecture locale abstraite : à chaque `(Γ, φ)` associe une trace temporelle.
-/
abbrev LocalReading (Context : Type v) (Sentence : Type u) :=
  Context → Sentence → Trace

/-- Provabilité : il existe un temps où la lecture de `φ` sous `Γ` est vraie. -/
def Prov {Context : Type v} {Sentence : Type u}
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) : Prop :=
  ∃ n : ℕ, LR Γ φ n

/-- Verdict stabilisé via `Rev0`. -/
def verdict {Context : Type v} {Sentence : Type u}
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) : Prop :=
  Rev0 (LR Γ φ)

/--
Équivalence « à la SLE » :
le verdict stabilisé pour `(Γ, φ)` vaut vrai ssi `φ` est « prouvable » depuis `Γ`
au sens de la lecture locale `LR`.
-/
lemma verdict_iff_Prov
    {Context : Type v} {Sentence : Type u}
    (LR : LocalReading Context Sentence)
    (Γ : Context) (φ : Sentence) :
  verdict LR Γ φ ↔ Prov LR Γ φ := by
  unfold verdict Rev0 Rev Prov
  -- but : canonicalQueueProjector.pi (up (LR Γ φ)) ↔ ∃ n, LR Γ φ n
  simpa using (canonicalQueueProjector.Q1 (LR Γ φ))

end LogicDissoc
