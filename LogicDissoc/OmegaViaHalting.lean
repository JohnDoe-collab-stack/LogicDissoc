/-
  LogicDissoc/OmegaViaHalting.lean

  Rôle de ce fichier :
  - donner une lecture probabiliste abstraite via `LinExtSystem` + `Q_expectation`,
  - définir un schéma de halting dynamique (traces),
  - introduire un code Ω abstrait et sa spécification obstructionnelle `Omega.Spec`,
  - en déduire les résultats sur les rangs des coupes/bits (ILM / transcend).

  Rien ici ne construit Ω concrètement : on isole la couche "Spec + rangs"
  et la couche "probabiliste sur les linéarisations".
-/

import LogicDissoc.BasicSemantics
import LogicDissoc.RefSystem
import LogicDissoc.Rank
import LogicDissoc.Rev
import LogicDissoc.DynamicRank
import LogicDissoc.Omega
import LogicDissoc.CanonicalMeasure

namespace LogicDissoc
namespace OmegaViaHalting

------------------------------------------------------------
-- 1. Couche probabiliste : `LinExtSystem` + Q_expectation
------------------------------------------------------------

-- Probabilité abstraite sur les linéarisations d’un système `S`.
section Probabilities

variable (S : LinExtSystem)

/-- Probabilité d’un observable booléen `Φ` sur `L Γ`, définie via `Q_expectation`. -/
def P_on_Lext (Γ : S.Context) (Φ : LinExtSystem.L (S := S) Γ → Bool) : ℚ :=
  LinExtSystem.Q_expectation (S := S) Γ Φ

/-- Pour tout contexte non vide, la probabilité de `true` est 1. -/
lemma P_on_Lext_true (Γ : S.Context)
    [Nonempty (LinExtSystem.L (S := S) Γ)] :
  P_on_Lext S Γ (fun _ => true) = 1 := by
  -- C’est exactement le lemme `Q_expectation_top` de CanonicalMeasure.
  simpa [P_on_Lext] using
    (LinExtSystem.Q_expectation_top (S := S) Γ)

end Probabilities


------------------------------------------------------------
-- 2. Couche halting dynamique (abstraite, sur les traces)
------------------------------------------------------------

-- Type de programmes (abstrait).
variable (Prog : Type _) [DecidableEq Prog]

-- Types sous-jacents du RefSystem (arithmétique, par ex.).
variable {Model Sentence : Type _}

-- Système de référence (arithmétique ou autre).
variable (E : RefSystem Model Sentence)

-- Type de codes numériques (indices, descriptions, programmes…).
variable (Code : Type _)

-- Coupes rationnelles : "x est strictement au-dessus de q" encodé en phrase.
variable (Cut : ℚ → Code → Sentence)

-- Bits dyadiques : "au rang n, le paquet de bits vaut a" encodé en phrase.
variable (Bit : ℕ → ℕ → Code → Sentence)

/-- Trace de halting abstraite d’un programme `e`.

    Dans une instance concrète, `haltingTrace e n` exprimerait :
    "à l’étape n, on a découvert que `e` s’arrête". -/
def haltingTrace (_ : Prog) : Trace :=
  fun _n => False   -- placeholder : à instancier dans un modèle de halting concret

/-- "`e` s’arrête" comme événement dynamique (existence d’un temps de halting). -/
def halts (e : Prog) : Prop :=
  ∃ n, haltingTrace Prog e n

/-- "`e` diverge" comme négation de l’événement de halting. -/
def diverges (e : Prog) : Prop :=
  ¬ halts Prog e


------------------------------------------------------------
-- 3. Ω abstrait et spécification obstructionnelle (Omega.Spec)
------------------------------------------------------------

-- Un code abstrait de type Ω.

--    Dans un développement ultérieur, ce `Ω` serait construit à partir
--    d’une probabilité de halting (à la Chaitin). Ici on ne fige
--    que son comportement obstructionnel via `delta`.
variable (Ω : Code)

/-- Comportement de `delta` sur les coupes de Ω :
    chaque coupe rationnelle est ILM (`delta = 1`, donc ≠ 0). -/
axiom Omega_cuts_behave :
  ∀ q : ℚ,
    E.delta (Cut q Ω) ≠ 0 ∧ E.delta (Cut q Ω) = 1

/-- Comportement de `delta` sur les bits de Ω :
    chaque phrase "bit dyadique" est obstructionnellement transcendante :
    `delta ≠ 0` et `delta ≠ 1`. -/
axiom Omega_bits_behave :
  ∀ n a : ℕ,
    E.delta (Bit n a Ω) ≠ 0 ∧ E.delta (Bit n a Ω) ≠ 1

/-- Ω satisfait la spécification obstructionnelle `Omega.Spec`. -/
def OmegaSpec : Omega.Spec (E := E) (Cut := Cut) (Bit := Bit) (x := Ω) :=
{ cuts_are_ilm      := fun q => Omega_cuts_behave E Code Cut Ω q,
  bits_are_transcend := fun n a => Omega_bits_behave E Code Bit Ω n a }



------------------------------------------------------------
-- 4. Conséquences sur les rangs d’obstruction de Ω
------------------------------------------------------------


theorem Omega_ranks_behave
    [∀ q : ℚ, Decidable (E.delta (Cut q Ω) = 0)]
    [∀ q : ℚ, Decidable (E.delta (Cut q Ω) = 1)]
    [∀ n a : ℕ, Decidable (E.delta (Bit n a Ω) = 0)]
    [∀ n a : ℕ, Decidable (E.delta (Bit n a Ω) = 1)] :
  (∀ q : ℚ, cutRank E Cut Ω q = ObstructionRank.ilm) ∧
  (∀ n a : ℕ, bitRank E Bit Ω n a = ObstructionRank.transcend) :=
let hΩ : Omega.Spec (E := E) (Cut := Cut) (Bit := Bit) (x := Ω) :=
{ cuts_are_ilm       := fun q => Omega_cuts_behave E Code Cut Ω q,
  bits_are_transcend := fun n a => Omega_bits_behave E Code Bit Ω n a }
⟨
  Omega.Spec.omega_cutRank_is_ilm hΩ,
  Omega.Spec.omega_bitRank_is_transcend hΩ
⟩

/-- Pour un code de type Ω, toutes les coupes rationnelles ont rang `ilm`. -/
theorem Omega_cuts_rank_ilm
    [∀ q : ℚ, Decidable (E.delta (Cut q Ω) = 0)]
    [∀ q : ℚ, Decidable (E.delta (Cut q Ω) = 1)]
    [∀ n a : ℕ, Decidable (E.delta (Bit n a Ω) = 0)]
    [∀ n a : ℕ, Decidable (E.delta (Bit n a Ω) = 1)] :
  ∀ q : ℚ,
    cutRank E Cut Ω q = ObstructionRank.ilm :=
  (Omega_ranks_behave (E := E) (Code := Code) (Cut := Cut) (Bit := Bit) (Ω := Ω)).1

/-- Pour un code de type Ω, tous les éléments dyadiques ont rang `transcend`. -/
theorem Omega_bits_rank_transcend
    [∀ q : ℚ, Decidable (E.delta (Cut q Ω) = 0)]
    [∀ q : ℚ, Decidable (E.delta (Cut q Ω) = 1)]
    [∀ n a : ℕ, Decidable (E.delta (Bit n a Ω) = 0)]
    [∀ n a : ℕ, Decidable (E.delta (Bit n a Ω) = 1)] :
  ∀ n a : ℕ,
    bitRank E Bit Ω n a = ObstructionRank.transcend :=
  (Omega_ranks_behave (E := E) (Code := Code) (Cut := Cut) (Bit := Bit) (Ω := Ω)).2


end OmegaViaHalting
end LogicDissoc
