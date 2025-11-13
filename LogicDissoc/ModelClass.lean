import Mathlib.Data.Set.Basic
import LogicDissoc.BasicSemantics

universe u v

variable {Sentence : Type u} {Model : Type v}
variable (Sat : Model → Sentence → Prop)

/-- Typeclasse « classe de modèles » pour `Γ`.
    Fournit un porteur `carrier : Set Model` caractérisé par l'équivalence avec `ModE`. -/
class ModelClass (Sat : Model → Sentence → Prop) (Γ : Set Sentence) where
  carrier : Set Model
  mem_iff : ∀ {M : Model}, M ∈ carrier ↔ ∀ φ ∈ Γ, Sat M φ

namespace ModelClass

variable {Sat}

/-- Coercion vers `Set Model`. -/
instance instCoe (Sat : Model → Sentence → Prop) (Γ : Set Sentence) :
  CoeTC (ModelClass (Sat := Sat) Γ) (Set Model) :=
  ⟨fun MC => MC.carrier⟩

/-- Raccourci lisible. -/
notation "Models" =>
  (fun (Sat : _ → _ → Prop) (Γ : Set _)
    [ModelClass (Sat := Sat) Γ] =>
      (ModelClass.carrier (Sat := Sat) (Γ := Γ)))

@[simp] lemma mem_models_iff {Γ : Set Sentence} [MC : ModelClass (Sat := Sat) Γ]
    {M : Model} : M ∈ (Models Sat Γ) ↔ ∀ φ ∈ Γ, Sat M φ := MC.mem_iff

/-- Instance canonique : `carrier = ModE`. -/
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

/-- Version « classe de modèles » de la conservativité. -/
lemma conservative_iff_subset_ThE_models (Γ Δ : Set Sentence) :
  (Models Sat (Γ ∪ Δ)) = (Models Sat Γ) ↔ Δ ⊆ ThE Sat (Models Sat Γ) := by
  simpa [ModelClass.Models_eq_ModE (Sat := Sat) Γ] using
    (mod_conservative_iff_subset_ThE (Sat := Sat) Γ Δ)

end LogicDissoc
