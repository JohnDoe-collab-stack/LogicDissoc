import Mathlib.Data.Set.Basic
import LogicDissoc.BasicSemantics

universe u v

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)

/-- Typeclass "class of models" for `Γ`.
    Provides a carrier `carrier : Set Model` characterized by equivalence with `ModE`. -/
class ModelClass (Sat : Model → Sentence → Prop) (Γ : Set Sentence) where
  carrier : Set Model
  mem_iff : ∀ {M : Model}, M ∈ carrier ↔ ∀ φ ∈ Γ, Sat M φ

namespace ModelClass

variable {Sat}

/-- Coercion to `Set Model`. -/
instance instCoe (Sat : Model → Sentence → Prop) (Γ : Set Sentence) :
  CoeTC (ModelClass (Sat := Sat) Γ) (Set Model) :=
  ⟨fun MC => MC.carrier⟩

/-- Readable shorthand. -/
notation "Models" =>
  (fun (Sat : _ → _ → Prop) (Γ : Set _)
    [ModelClass (Sat := Sat) Γ] =>
      (ModelClass.carrier (Sat := Sat) (Γ := Γ)))

@[simp] lemma mem_models_iff {Γ : Set Sentence} [MC : ModelClass (Sat := Sat) Γ]
    {M : Model} : M ∈ (Models Sat Γ) ↔ ∀ φ ∈ Γ, Sat M φ := MC.mem_iff

/-- Canonical instance: `carrier = ModE`. -/
instance (priority := 100) instModelClassDefault
    (Sat : Model → Sentence → Prop) (Γ : Set Sentence) :
    ModelClass (Sat := Sat) Γ where
  carrier := ModE Sat Γ
  mem_iff := by intro M; rfl

@[simp] lemma Models_eq_ModE (Γ : Set Sentence) :
  (Models Sat Γ) = ModE Sat Γ := rfl

end ModelClass

namespace LogicDissoc

open Set
variable {Sat}

/-- "Class of models" version of conservativity. -/
lemma conservative_iff_subset_ThE_models (Γ Δ : Set Sentence) :
  (Models Sat (Γ ∪ Δ)) = (Models Sat Γ) ↔ Δ ⊆ ThE Sat (Models Sat Γ) := by
  simpa [ModelClass.Models_eq_ModE (Sat := Sat) Γ] using
    (mod_conservative_iff_subset_ThE (Sat := Sat) Γ Δ)

end LogicDissoc
