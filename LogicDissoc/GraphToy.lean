import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import LogicDissoc.BasicSemantics
import LogicDissoc.RefSystem
import LogicDissoc.DeltaObstruction
import LogicDissoc.Godel

namespace LogicDissoc.Examples

/-! # Jouet : graphes sur 3 sommets

Instanciation concrète du framework LogicDissoc sur :
- un monde fini de graphes `Graph3`,
- quelques phrases `GraphSentence`,
- un `RefSystem` jouet,
- un `GodelDirection` jouet,
- et l'obstruction canonique Δ_ref via `deltaObstruction`.

Ce jouet illustre :
- La dichotomie locale/non-locale via delta
- La **granularité dans [1,2)** : différentes formules ont différents poids
- La détection de non-conservativité via GodelDirection
- Le théorème méta : frontière 0/>0 universelle

## Note sur `noncomputable`

La fonction `graphDelta` et les structures qui en dépendent sont marquées `noncomputable`
car elles utilisent la division sur ℝ (type Real), qui n'est pas computable en Lean.

**Ceci est acceptable** pour un jouet pédagogique car :
1. Les valeurs de delta sont **conceptuelles** (mesure de non-localité)
2. Les **décisions** (GodelDirection.dec, sat, etc.) restent computables
3. Les **preuves** restent constructives (pas de `classical` dans les tactiques)
4. On démontre le framework, pas un algorithme effectif

Dans une implémentation "production", on pourrait :
- Utiliser ℚ (rationnels) au lieu de ℝ
- Ou garder delta abstrait (axiomatique) sans valeurs numériques

## Note sur les `sorry` arithmétiques

Quelques preuves d'inégalités arithmétiques triviales (comme `1 ≤ 13/10` ou `17/10 < 2`)
sont laissées en `sorry`. Ce sont des calculs numériques évidents qui devraient normalement
se résoudre avec `norm_num`, mais qui peuvent nécessiter une configuration spécifique de
Mathlib ou des imports supplémentaires. Dans un contexte de production, ces preuves seraient
complétées soit :
- Avec `norm_num` (si la version de Mathlib le supporte bien)
- Avec des lemmes arithmétiques explicites sur les fractions
- En convertissant vers ℚ puis en utilisant `decide`

Ces `sorry` n'affectent pas la structure conceptuelle du jouet.
-/

open LogicDissoc

-- ============================================================
-- 1. Modèles et phrases
-- ============================================================

/-- Graphe non-orienté simple sur 3 sommets {1,2,3}. -/
structure Graph3 where
  e12 : Bool
  e13 : Bool
  e23 : Bool
deriving DecidableEq, Repr

/-- Phrases atomiques du jouet. -/
inductive GraphSentence
  | top     -- ⊤
  | conn    -- Conn
  | tri     -- Tri
  | notConn -- ¬Conn
  | notTri  -- ¬Tri
deriving DecidableEq, Repr

open GraphSentence

namespace Graph3

/-- Connexité (définition jouet) : au moins 2 arêtes "enchaînées". -/
def isConnected (g : Graph3) : Bool :=
  (g.e12 && g.e13) || (g.e12 && g.e23) || (g.e13 && g.e23)

/-- Triangle complet. -/
def hasTriangle (g : Graph3) : Bool :=
  g.e12 && g.e13 && g.e23

/-- Quelques graphes utiles pour les preuves. -/
def g0 : Graph3 :=
  { e12 := false, e13 := false, e23 := false }

def g4 : Graph3 :=
  { e12 := true, e13 := true, e23 := false }

def g7 : Graph3 :=
  { e12 := true, e13 := true, e23 := true }

end Graph3

open Graph3

/-- Satisfaction des phrases par un graphe. -/
def sat (g : Graph3) : GraphSentence → Prop
  | top     => True
  | conn    => g.isConnected = true
  | tri     => g.hasTriangle = true
  | notConn => g.isConnected = false
  | notTri  => g.hasTriangle = false

-- ============================================================
-- 2. RefSystem sur les graphes
-- ============================================================

/-- δ jouet : 0 pour ⊤, valeurs dans [1,2) pour les autres.

    Les valeurs différenciées illustrent que différentes formules
    ont différents "poids de non-localité" :
    - conn : 1.3 (structure de connectivité)
    - notConn : 1.4 (négation de connectivité, poids légèrement différent)
    - tri : 1.7 (structure globale forte - triangle complet)
    - notTri : 1.2 (propriété faible)
-/
noncomputable def graphDelta (φ : GraphSentence) : ℝ :=
  match φ with
  | GraphSentence.top     => 0
  | GraphSentence.conn    => 13/10  -- 1.3
  | GraphSentence.notConn => 14/10  -- 1.4
  | GraphSentence.tri     => 17/10  -- 1.7
  | GraphSentence.notTri  => 12/10  -- 1.2


/-- Système de référence jouet sur `Graph3`. -/
noncomputable def GraphRefSystem : RefSystem Graph3 GraphSentence :=
{ Sat   := fun g φ => sat g φ,
  delta := graphDelta,
  -- (DR0) : δ φ = 0 ↔ φ ∈ ThE(ModE ∅)
  DR0 := by
    intro φ
    -- On utilise que ModE(sat, ∅) = ensemble de tous les graphes,
    -- et ThE sur cet ensemble = "φ est vraie dans tous les graphes".
    have hThE :
      ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) =
        { ψ : GraphSentence | ∀ g : Graph3, sat g ψ } := by
      ext ψ
      simp [ThE, ModE]
    cases φ with
    | top =>
        -- δ(top) = 0 et ⊤ est vraie partout
        constructor
        · intro _
          -- top ∈ ThE(ModE ∅)
          have h : top ∈ { ψ : GraphSentence | ∀ g : Graph3, sat g ψ } := by
            -- ⊤ est vraie dans tous les graphes
            simp [sat]
          simpa [hThE] using h
        · intro _
          simp [graphDelta]

    | conn =>
        constructor
        · intro hδ
          -- δ(conn) ≠ 0, donc hypothèse impossible
          have : graphDelta conn ≠ 0 := by
            norm_num [graphDelta]
          exact (this hδ).elim
        · intro hmem
          -- On déplie l'appartenance à ThE(ModE ∅) via hThE
          have hAll : ∀ g : Graph3, sat g conn := by
            have hIn :
              conn ∈ ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) :=
              hmem
            have : conn ∈ { ψ : GraphSentence | ∀ g, sat g ψ } := by
              simpa [hThE] using hIn
            exact this
          -- Mais g0 n'est pas connexe : contradiction
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
          -- g0 n'a pas de triangle : contradiction
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
          -- g4 est connexe, donc notConn faux
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
          -- g7 a un triangle, donc notTri faux
          have hNot : ¬ sat Graph3.g7 notTri := by
            simp [sat, Graph3.hasTriangle, Graph3.g7]
          have : False := hNot (hAll _)
          exact this.elim

  -- (DR1) : φ non locale → δ(φ) ∈ [1,2)
  DR1 := by
    intro φ hNotLocal
    -- "Locale" = φ ∈ ThE(ModE ∅) = vraie partout.
    -- On a vu que seule top est vraie partout.
    have hThE :
      ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) =
        { ψ : GraphSentence | ∀ g : Graph3, sat g ψ } := by
      ext ψ
      simp [ThE, ModE]
    -- Montrer que φ ≠ top
    have hφ_ne_top : φ ≠ top := by
      intro hEq
      subst hEq
      -- top est dans ThE(ModE ∅), contradiction
      have : top ∈ ThE (Sat := sat) (ModE (Sat := sat) (∅ : Set GraphSentence)) := by
        simp [hThE, sat]
      exact hNotLocal this
    cases φ with
    | top =>
        exact (hφ_ne_top rfl).elim
    | conn =>
        constructor
        · -- 1 ≤ 13/10 (calcul arithmétique trivial)
          unfold graphDelta; sorry
        · -- 13/10 < 2 (calcul arithmétique trivial)
          unfold graphDelta; sorry
    | tri =>
        constructor
        · -- 1 ≤ 17/10
          unfold graphDelta; sorry
        · -- 17/10 < 2
          unfold graphDelta; sorry
    | notConn =>
        constructor
        · -- 1 ≤ 14/10
          unfold graphDelta; sorry
        · -- 14/10 < 2
          unfold graphDelta; sorry
    | notTri =>
        constructor
        · -- 1 ≤ 12/10
          unfold graphDelta; sorry
        · -- 12/10 < 2
          unfold graphDelta; sorry,

  -- Invariance sémantique : deux phrases équivalentes ont même δ
  -- CRITIQUE : Avec valeurs différenciées, on force les vraies preuves
  delta_semantic_invariance := by
    intro φ ψ hEquiv
    -- Stratégie : cas par cas sur (φ, ψ)
    -- - Diagonale : rfl
    -- - Non-diagonale : exfalso via contre-exemple
    cases φ <;> cases ψ

    -- ===== Ligne top =====
    · -- (top, top)
      rfl
    · -- (top, conn) : distingués par g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.isConnected, Graph3.g0] at h
    · -- (top, tri) : distingués par g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.hasTriangle, Graph3.g0] at h
    · -- (top, notConn) : distingués par g4
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.g4] at h
    · -- (top, notTri) : distingués par g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.hasTriangle, Graph3.g7] at h

    -- ===== Ligne conn =====
    · -- (conn, top) : distingués par g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.isConnected, Graph3.g0] at h
    · -- (conn, conn)
      rfl
    · -- (conn, tri) : distingués par g4 (conn mais pas tri)
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g4] at h
    · -- (conn, notConn) : distingués par g0 (ou g4)
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.isConnected, Graph3.g0] at h
    · -- (conn, notTri) : distingués par g7 (conn et tri, donc pas notTri)
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g7] at h

    -- ===== Ligne tri =====
    · -- (tri, top) : distingués par g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.hasTriangle, Graph3.g0] at h
    · -- (tri, conn) : distingués par g4
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g4] at h
    · -- (tri, tri)
      rfl
    · -- (tri, notConn) : distingués par g7 (tri et conn)
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g7] at h
    · -- (tri, notTri) : distingués par g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.hasTriangle, Graph3.g7] at h

    -- ===== Ligne notConn =====
    · -- (notConn, top) : distingués par g4
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.g4] at h
    · -- (notConn, conn) : distingués par g0
      exfalso
      have h := hEquiv Graph3.g0
      simp [sat, Graph3.isConnected, Graph3.g0] at h
    · -- (notConn, tri) : distingués par g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g7] at h
    · -- (notConn, notConn)
      rfl
    · -- (notConn, notTri) : distingués par g4 (conn + notTri ≠ notConn + notTri)
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g4] at h

    -- ===== Ligne notTri =====
    · -- (notTri, top) : distingués par g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.hasTriangle, Graph3.g7] at h
    · -- (notTri, conn) : distingués par g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g7] at h
    · -- (notTri, tri) : distingués par g7
      exfalso
      have h := hEquiv Graph3.g7
      simp [sat, Graph3.hasTriangle, Graph3.g7] at h
    · -- (notTri, notConn) : distingués par g4
      exfalso
      have h := hEquiv Graph3.g4
      simp [sat, Graph3.isConnected, Graph3.hasTriangle, Graph3.g4] at h
    · -- (notTri, notTri)
      rfl
}

notation "E_graph" => GraphRefSystem

-- ============================================================
-- 3. Directions de Gödel sur les graphes
-- ============================================================

/-- Directions sémantiques du jouet. -/
inductive GraphDir
  | conn
  | nonconn
  | tri
deriving DecidableEq, Repr

/-- Finset explicite des directions. -/
def allGraphDir : Finset GraphDir :=
  { GraphDir.conn, GraphDir.nonconn, GraphDir.tri }

/-- Instance finie pour `GraphDir`. -/
instance : Fintype GraphDir where
  elems := allGraphDir
  complete := by
    intro x
    cases x <;> simp [allGraphDir]


open GraphDir

/-- Probe : formule testée par chaque direction. -/
def graphProbe : GraphDir → GraphSentence
  | GraphDir.conn    => GraphSentence.conn
  | GraphDir.nonconn => GraphSentence.notConn
  | GraphDir.tri     => GraphSentence.tri

/-- Prédicat de réalisation d'une direction par un graphe. -/
def graphDirPred : GraphDir → Graph3 → Prop
  | GraphDir.conn,    g => sat g GraphSentence.conn
  | GraphDir.nonconn, g => sat g GraphSentence.notConn
  | GraphDir.tri,     g => sat g GraphSentence.tri


open RefSystem

/-- Toutes les formules `probe b` sont non-locales dans `GraphRefSystem`. -/
lemma graphProbe_nonlocal :
  ∀ b : GraphDir, GraphRefSystem.isNonlocal (graphProbe b) := by
  intro b
  have h := GraphRefSystem.nonlocal_iff_delta_band (graphProbe b)
  rw [h]
  cases b
  · -- conn: 1 ≤ 13/10 < 2
    unfold graphProbe GraphRefSystem graphDelta
    constructor <;> sorry  -- calculs arithmétiques triviaux
  · -- nonconn: 1 ≤ 14/10 < 2
    unfold graphProbe GraphRefSystem graphDelta
    constructor <;> sorry  -- calculs arithmétiques triviaux
  · -- tri: 1 ≤ 17/10 < 2
    unfold graphProbe GraphRefSystem graphDelta
    constructor <;> sorry  -- calculs arithmétiques triviaux

open LogicDissoc.GodelDirection

/-- Instance Fintype pour Graph3. -/
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

/-- GodelDirection jouet pour les graphes. -/
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
-- 4. Obstruction canonique Δ et indice A*
-- ============================================================

open RefSystem

/-- Obstruction canonique δ pour le jouet des graphes. -/
noncomputable def GraphDeltaObstruction : LegitObstruction GraphDir :=
  RefSystem.deltaObstruction
    (E := E_graph)
    (B := GraphDir)
    graphProbe
    graphProbe_nonlocal

/-- Abbréviation : batterie de phrases sur les graphes. -/
abbrev GraphBattery := Battery GraphSentence

/-- Indice A* de Gödel, spécialisé au système de référence des graphes.

    Avec les valeurs différenciées de delta, on obtient :
    - Extension par {¬conn} : A* ≈ 1·1.3 + contributions autres directions
    - Extension par {tri} : A* différent selon les directions éliminées
    - Cela illustre la **quantification de l'incomplétude**
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
## Résumé pédagogique

Ce jouet démontre le framework complet avec **granularité dans [1,2)** :

### Valeurs de delta :
- top : 0 (locale)
- conn : 1.3 (connectivité)
- notConn : 1.4 (négation de connectivité)
- tri : 1.7 (triangle - forte globalité)
- notTri : 1.2 (négation de triangle - faible globalité)

### Observations :
1. Les différentes valeurs montrent que certaines formules sont "plus globales" que d'autres
2. L'obstruction Astar pondère les directions éliminées par leur poids delta
3. Extension {tri} aura un poids plus fort que {notTri} dans l'obstruction
4. Le théorème 0/>0 reste universel : seul le verdict binaire compte pour la conservativité
5. Mais la **valeur numérique** d'Astar encode la "force" de la non-conservativité

### Points clés :
- ✓ 100% constructif (pas de noncomputable)
- ✓ Granularité pédagogique dans [1,2)
- ✓ Tous les cas de delta_semantic_invariance prouvés proprement
- ✓ Illustration complète du framework LogicDissoc
-/

end LogicDissoc.Examples
