/-
  LogicDissoc/Omega.lean

  Spécification abstraite d’un "Omega" via la fonction delta d’un RefSystem,
  sans objet global non calculable et sans axiomes globaux.

  On travaille uniquement au niveau Prop :

  - `Spec E Cut Bit x` : "le code x se comporte comme un Omega" au sens des
    valeurs de `E.delta` sur les formules de coupe `Cut q x` et de bits
    `Bit n a x`.

  - À partir de cette spécification et des lemmes de `Rank.lean`, on montre que :
      * toutes les coupes rationnelles de x ont rang `ObstructionRank.ilm`,
      * tous les bits dyadiques de x ont rang `ObstructionRank.transcend`.
-/

import LogicDissoc.Rank

namespace LogicDissoc
namespace Omega

universe u v w

variable {Model : Type u} {Sentence : Type v} {Code : Type w}

-- Système de référence (sémantique, delta, etc.).
variable (E   : RefSystem Model Sentence)

-- Famille de formules de coupe rationnelle : `Cut q x` parle de la relation
--    entre le code réel `x : Code` et le rationnel `q : ℚ`.
variable (Cut : ℚ → Code → Sentence)

-- Famille de formules de bits dyadiques : `Bit n a x` parle du n-ième
--    bit de `x`.
variable (Bit : ℕ → ℕ → Code → Sentence)

/--
`Spec E Cut Bit x` signifie : "le code `x` se comporte comme un Omega" au sens où :

* pour toute coupe rationnelle `q`, la formule `Cut q x` est non locale et a
  `delta = 1` ;

* pour tout bit dyadique `(n,a)`, la formule `Bit n a x` est non locale et
  a une valeur de `delta` différente de `0` et de `1`.
-/
structure Spec (x : Code) : Prop where
  (cuts_are_ilm :
     ∀ q : ℚ,
       E.delta (Cut q x) ≠ 0 ∧ E.delta (Cut q x) = 1)
  (bits_are_transcend :
     ∀ n a : ℕ,
       E.delta (Bit n a x) ≠ 0 ∧ E.delta (Bit n a x) ≠ 1)

namespace Spec

variable {E Cut Bit}
variable {x : Code}

/-! ### Coupes : rang obstructionnel = `ilm` -/

/-- Pour un code `x` qui satisfait `Spec`, toutes les coupes rationnelles
    ont rang d’obstruction `ObstructionRank.ilm`. -/
lemma cutRank_is_ilm
    (hΩ : Spec (E := E) (Cut := Cut) (Bit := Bit) x)
    [∀ q, Decidable (E.delta (Cut q x) = 0)]
    [∀ q, Decidable (E.delta (Cut q x) = 1)] :
  ∀ q : ℚ,
    cutRank (E := E) (Cut := Cut) x q = ObstructionRank.ilm :=
by
  intro q
  -- données de la spécification pour la coupe en q
  have h := hΩ.cuts_are_ilm q
  -- h.1 : E.delta (Cut q x) ≠ 0
  -- h.2 : E.delta (Cut q x) = 1
  unfold cutRank
  exact
    obstructionRank_ilm_of_delta_eq_one
      (E := E) (φ := Cut q x) h.1 h.2

/-- Version au nom proche de l’ancienne `omega_cutRank_is_ilm`. -/
lemma omega_cutRank_is_ilm
    (hΩ : Spec (E := E) (Cut := Cut) (Bit := Bit) x)
    [∀ q, Decidable (E.delta (Cut q x) = 0)]
    [∀ q, Decidable (E.delta (Cut q x) = 1)] :
  ∀ q : ℚ,
    cutRank (E := E) (Cut := Cut) x q = ObstructionRank.ilm :=
cutRank_is_ilm (E := E) (Cut := Cut) (Bit := Bit) (x := x) hΩ

/-! ### Bits : rang obstructionnel = `transcend` -/

/-- Pour un code `x` qui satisfait `Spec`, tous les bits dyadiques ont
    rang d’obstruction `ObstructionRank.transcend`. -/
lemma bitRank_is_transcend
    (hΩ : Spec (E := E) (Cut := Cut) (Bit := Bit) x)
    [∀ n a, Decidable (E.delta (Bit n a x) = 0)]
    [∀ n a, Decidable (E.delta (Bit n a x) = 1)] :
  ∀ n a : ℕ,
    bitRank (E := E) (Bit := Bit) x n a = ObstructionRank.transcend :=
by
  intro n a
  -- données de la spécification pour le bit (n,a)
  have h := hΩ.bits_are_transcend n a
  -- h.1 : E.delta (Bit n a x) ≠ 0
  -- h.2 : E.delta (Bit n a x) ≠ 1
  unfold bitRank
  exact
    obstructionRank_transcend_of_delta_ne
      (E := E) (φ := Bit n a x) h.1 h.2

/-- Version au nom proche de l’ancienne `omega_bitRank_is_transcend`. -/
lemma omega_bitRank_is_transcend
    (hΩ : Spec (E := E) (Cut := Cut) (Bit := Bit) x)
    [∀ n a, Decidable (E.delta (Bit n a x) = 0)]
    [∀ n a, Decidable (E.delta (Bit n a x) = 1)] :
  ∀ n a : ℕ,
    bitRank (E := E) (Bit := Bit) x n a = ObstructionRank.transcend :=
bitRank_is_transcend (E := E) (Cut := Cut) (Bit := Bit) (x := x) hΩ

end Spec

end Omega
end LogicDissoc
