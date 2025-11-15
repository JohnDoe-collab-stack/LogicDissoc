# LogicDissoc : Obstruction sémantique et incomplétude quantifiée

Ce document explique l’architecture conceptuelle de **LogicDissoc** :

1. Un **indice d’obstruction à la Gödel** `A*_Godel` qui mesure à quel point une extension finie `S` d’une théorie de référence `Γ_ref` déforme sa classe de modèles.
2. Une **mesure de non-localité sémantique** `delta` encapsulée dans un `RefSystem`, et un **rang d’obstruction** fini `ObstructionRank` qui discrétise le comportement de `delta`.

L’objectif est d’aider le lecteur à comprendre *ce qui se passe et pourquoi*, pas de fournir une API ou un guide d’installation.

---

## 0. Vue d’ensemble

On fixe un **système de référence** :

```text
(Sentence, Model, Sat, Γ_ref)
````

et on regarde des extensions finies `Γ_ref ∪ S`. La notion sémantique centrale est :

* L’extension est **conservative** si elle ne change pas la classe de modèles admissibles :

  ```text
  ModE(Γ_ref ∪ S) = ModE(Γ_ref).
  ```

La bibliothèque associe à chaque paquet fini `S` un réel

```text
A*_Godel(S) ∈ ℝ
```

tel que :

```text
A*_Godel(S) = 0   ⇔   Γ_ref ∪ S est une extension conservative
A*_Godel(S) > 0   ⇔   Γ_ref ∪ S est sémantiquement non conservative.
```

De plus, la coupure `0 / >0` ne dépend **pas** du choix d’un certain fonctionnel linéaire ; seule l’échelle numérique change.

En interne, pour certains cadres, cette obstruction est raffinée via une mesure sémantique

```text
delta : Sentence → ℝ
```

et un **rang d’obstruction** fini :

```lean
inductive ObstructionRank
| local      -- delta = 0
| ilm        -- delta = 1
| transcend  -- delta ≠ 0, 1
```

qui recode le comportement de `delta` et sert ensuite à classifier des codes numériques (coupes, bits, etc.).

---

## 1. Point de vue fondationnel : systèmes de référence, pas fondations absolues

LogicDissoc part d’un constat simple :

* Il n’existe pas de théorie finale globale dans laquelle tout serait décidé.
* En pratique, on raisonne toujours **relativement à un système de référence** :

  * une théorie de fond (PA, ZFC, un système de types, un fragment de QFT, …),
  * une classe de modèles admissibles,
  * une notion de vérité interne.

Dans la bibliothèque, un tel système de référence est représenté par :

```text
(Sentence, Model, Sat, Γ_ref)
```

* `Γ_ref` n’est pas “toutes les mathématiques”, mais un **référentiel local**.
* Les paquets finis `S` de phrases sont des **extensions** de ce référentiel.

La question centrale devient :

> Que devient `ModE(Γ_ref)` quand on passe à `ModE(Γ_ref ∪ S)` ?

Dans ce cadre :

* **L’incomplétude est normale** : dès que `S` change réellement le système de référence, l’extension n’est plus conservative.
* L’indice `A*_Godel` ne vise pas à réparer l’incomplétude, mais à **mesurer l’obstruction** à la conservativité.

---

## Première partie – L’indice d’obstruction à la Gödel

Cette partie décrit le mécanisme abstrait qui construit `A*_Godel`.

### 2. Cadre sémantique de base

Un **cadre sémantique** consiste en :

* `Sentence` : type de formules,
* `Model`    : type de modèles,
* `Sat : Model → Sentence → Prop` : satisfaction,
* `Γ_ref : Set Sentence`          : théorie de référence.

Pour `Γ ⊆ Sentence`, on définit :

```text
ModE(Γ) := { M : Model | ∀ φ ∈ Γ, Sat M φ }.
```

Pour un `S ⊆ Sentence` fini (code : `Battery Sentence = Finset Sentence`), l’extension est **conservative** si :

```text
ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

On note cette propriété :

```text
Cons_S(S) :⇔ ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

Toutes les constructions ultérieures ne dépendent que de `ModE` et `Cons_S`.

---

### 3. Cône d’obstructions légitimes (couche géométrique)

On fixe un ensemble fini `B` de **types d’obstructions**.

**Profils de compteurs.** Un profil est une fonction

```text
c : B → ℕ
```

c’est-à-dire un élément de `ℕ^B` (code : `GenCounters B`).

**Obstructions légitimes.** Une obstruction légitime sur `B` est une application

```text
F : (B → ℕ) → ℝ
```

telle que (comme dans `ObstructionGen` et `Legit`) :

1. **Linéarité sur ℕ.** Il existe des coefficients `α_b > 0` tels que

   ```text
   F(c) = ∑_{b ∈ B} α_b · c(b).
   ```

2. **Non-négativité.**

   ```text
   ∀ c, F(c) ≥ 0.
   ```

3. **Noyau trivial.**

   ```text
   F(c) = 0   ⇔   ∀ b, c(b) = 0.
   ```

En Lean :

```lean
LegitObstruction B
```

avec fonctionnelle `L.O.F`.

On obtient un **cône positif** de formes linéaires sur `ℕ^B` :

* changer `L` renormalise l’indice,
* sans changer la géométrie de la frontière `0 / >0`.

---

### 4. Schémas de comptage admissibles

Un **protocole de comptage** pour le cadre est une application :

```text
Count : { S finis ⊆ Sentence } → (B → ℕ).
```

Il est **admissible** (classe `CountSpec`) si :

```text
∀ S, (∀ b, Count(S)(b) = 0)   ⇔   Cons_S(S).
```

Autrement dit :

* le **profil nul** (tous les coefficients nuls) équivaut à la **conservativité sémantique**.

Étant donnés :

* un cadre sémantique `S`,
* une obstruction légitime `L`,
* un protocole admissible `Count`,

on définit l’indice général :

```text
A*_{S,L,Count}(S) := F(Count(S)) ∈ ℝ,
```

avec `F = L.O.F`.

En Lean :

```lean
AstarGen (Sat := Sat) (Γ_ref := Γ_ref)
         (L := L) (Count := Count) S
```

---

### 5. Directions de Gödel (couche dynamique)

On encode maintenant **où** se manifeste la non-conservativité via des directions de Gödel.

Une **direction de Gödel** pour le cadre `S` et l’alphabet `B` est un prédicat

```text
P : B → Model → Prop
```

tel que :

1. **Décidabilité locale.** Pour tout `S` fini et tout `b ∈ B`, l’énoncé

   ```text
   ∃ m,
     m ∈ ModE(Γ_ref) ∧
     m ∉ ModE(Γ_ref ∪ S) ∧
     P b m
   ```

   est décidable. (Champ `dec` dans `GodelDirection`.)

2. **Séparation.** Pour tout `S` fini :

   ```text
   ¬Cons_S(S)
   → ∃ b m,
       m ∈ ModE(Γ_ref) ∧
       m ∉ ModE(Γ_ref ∪ S) ∧
       P b m.
   ```

   (Champ `separating`.)

Les directions de Gödel sont donc des **canaux sémantiques** le long desquels la perte de modèles doit apparaître.

À partir de `P`, on définit le **comptage de Gödel** canonique :

```text
Count^Godel(S)(b) :=
  1 si ∃ m,
       m ∈ ModE(Γ_ref),
       m ∉ ModE(Γ_ref ∪ S),
       P b m ;
  0 sinon.
```

En Lean : `GodelDirection.CountFromGodel`.

**Admissibilité.** On montre que

```text
Count^Godel : Battery Sentence → (B → ℕ)
```

satisfait :

```text
∀ S, (∀ b, Count^Godel(S)(b) = 0)   ⇔   Cons_S(S),
```

donc `Count^Godel` est un protocole admissible (instance `CountSpec`).

Étant donnée une obstruction légitime `L` et une direction de Gödel `P`, on définit l’**indice de Gödel** :

```text
A*_Godel(S) := F(Count^Godel(S)).
```

En Lean : `Astar_Godel`.

---

### 6. Méta-théorème : alignement quantitatif de l’incomplétude

Étant donnés :

* un cadre sémantique `S = (Sentence, Model, Sat, Γ_ref)`,
* un ensemble fini `B`,
* une obstruction légitime `L`,
* une direction de Gödel `P`,

alors pour tout `S` fini :

1. **Frontière nulle**

   ```text
   A*_Godel(S) = 0   ⇔   Cons_S(S).
   ```

2. **Frontière strictement positive**

   ```text
   A*_Godel(S) > 0   ⇔   ¬Cons_S(S).
   ```

3. **Indépendance de `L`**

   Pour deux obstructions légitimes `L1`, `L2` :

   ```text
   A*_{Godel}(S; L1) = 0  ⇔  A*_{Godel}(S; L2) = 0
   A*_{Godel}(S; L1) > 0 ⇔  A*_{Godel}(S; L2) > 0
   ```

Donc :

* le verdict qualitatif “0 vs >0” est **indépendant** du choix de `L` dans le cône,
* seule l’échelle numérique change.

En Lean : `metaGodel_frontier_zero`, `metaGodel_frontier_pos`, et des lemmes sur `LegitObstruction` (`linear_repr`, `zero_iff_all_zero`, `F_nonneg`).

---

### 7. Hiérarchie conceptuelle (résumé de la première partie)

Le mécanisme abstrait a quatre couches :

1. **Niveau 0 – Théorie des modèles.**
   `ModE`, `Cons_S` pour un cadre `S`.

2. **Niveau 1 – Cône d’obstructions.**
   Formes linéaires positives `L : (B → ℕ) → ℝ` à noyau trivial.

3. **Niveau 2 – Directions de Gödel.**
   `P : B → Model → Prop` avec décidabilité et séparation, donnant `Count^Godel`.

4. **Niveau 3 – Indice A*.**
   Pour chaque `(S,B,P,L)`, l’indice

   ```text
   S ↦ A*_Godel(S)
   ```

   détecte exactement les extensions conservatives (`=0`) et non conservatives (`>0`), et fournit une mesure numérique de l’intensité de l’obstruction.

---

### 8. Exemple fini : graphes et δ non triviale (`GraphToy`)

Le fichier :

```text
LogicDissoc/GraphToy.lean
```

donne une instance finie explicite :

* `Model  := Graph3` (graphes non orientés sur 3 sommets étiquetés),

* `Sentence := GraphSentence` avec des atomes `conn`, `tri`, `¬conn`, `¬tri`,

* un `RefSystem` concret :

  ```lean
  E_graph : RefSystem Graph3 GraphSentence
  ```

  avec `delta : Sentence → ℝ` tel que :

  * `delta(top) = 0` pour l’unique phrase locale partout vraie,
  * pour toute phrase non locale `φ`, `1 ≤ delta φ < 2`,
  * des formules non locales différentes (`conn`, `¬conn`, `tri`, `¬tri`) ont des valeurs réelles distinctes.

* un type fini de directions de Gödel `GraphDir` avec `GraphGodelDirection`,

* une obstruction canonique `GraphDeltaObstruction` construite à partir de `delta`,

* un indice spécialisé :

  ```lean
  noncomputable def graphAstar (S : GraphBattery) : ℝ := ...
  ```

`GraphToy` illustre :

* la dichotomie **local / non-local** via `delta`,
* la **granularité** de `delta` sur les formules non locales,
* la détection de la non-conservativité via des directions de Gödel,
* le méta-théorème 0 / >0 dans un cadre fini entièrement prouvé en Lean.

---

## Deuxième partie – Justification interne de `RefSystem` et du rang d’obstruction

Cette partie explique comment la couche interne

* `RefSystem`,
* `delta : Sentence → ℝ`,
* `ObstructionRank`

est *construite* et pourquoi elle n’introduit pas de nouveaux axiomes.

### 9. Idée directrice

L’idée principale est :

1. Construire d’abord un **système concret** (modèles, phrases, satisfaction, fermeture, `delta`).
2. Prouver dans ce système concret les propriétés clés de `delta` (localité, non-localité, bande `[1,2)`, etc.).
3. Abstraire ces données dans une structure générique `RefSystem`.
4. À partir de là, définir un type fini de rang (`ObstructionRank`) qui ne fait que **recoder** l’information déjà contenue dans `delta`.

Rien n’est postulé gratuitement :

* le rang n’est pas supposé, il est dérivé d’une trichotomie de `delta`.

---

### 10. Étape 1 – Construction concrète de `delta`

Dans un fichier concret (`DeltaConstruction.lean` / `BasicSemantics.lean`), on dispose de :

* un type `Model`,
* un type `Sentence`,
* une relation `Sat : Model → Sentence → Prop`,
* un opérateur de fermeture `CloE : Set Sentence → Set Sentence` (fermeture de théorie),
* une fonction

  ```lean
  delta : Sentence → ℝ
  ```

  construite explicitement (par exemple sur un univers fini, ou à partir d’une mesure canonique).

Sur ce système concret, on prouve (par construction, pas par axiome) :

* `delta_eq_zero_iff_mem_closure` :

  ```text
  delta φ = 0   ⇔   φ ∈ CloE ∅.
  ```

* un lemme de bande pour les non-membres de la clôture, du type :

  ```text
  φ ∉ CloE ∅   ⇔   1 ≤ delta φ ∧ delta φ < 2.
  ```

On définit alors :

```lean
isLocal    φ := φ ∈ CloE ∅
isNonlocal φ := ¬ isLocal φ
```

et on prouve :

* `isLocal φ     ⇔ delta φ = 0`,
* `isNonlocal φ  ⇔ 1 ≤ delta φ ∧ delta φ < 2`.

À ce stade :

* `delta = 0` caractérise **exactement** les phrases locales,
* la bande `[1,2)` caractérise les phrases non locales contrôlées,
* et tout ceci est **concrètement** exhibé en Lean.

---

### 11. Étape 2 – Abstraction en `RefSystem`

Une fois la construction concrète établie, on l’abstrait en :

```lean
structure RefSystem (Model Sentence : Type _) :=
  (Sat   : Model → Sentence → Prop)
  (CloE  : Set Sentence → Set Sentence)
  (delta : Sentence → ℝ)
  (delta_eq_zero_iff_mem_closure :
      ∀ φ, delta φ = 0 ↔ φ ∈ CloE ∅)
  (nonlocal_iff_delta_band :
      ∀ φ, isNonlocal φ ↔ 1 ≤ delta φ ∧ delta φ < 2)
  -- etc.
```

Ici :

* `delta_eq_zero_iff_mem_closure` et `nonlocal_iff_delta_band` sont des **théorèmes** de l’étape 1, désormais stockés comme champs.
* On sait que `RefSystem` est **habité** grâce à la construction explicite.

Au niveau abstrait, on définit :

```lean
def isLocal    (E : RefSystem Model Sentence) (φ : Sentence) :=
  φ ∈ E.CloE ∅

def isNonlocal (E : RefSystem Model Sentence) (φ : Sentence) :=
  ¬ isLocal E φ
```

Et l’on prouve dans `Rank.lean` :

* `isLocal_iff_delta_zero` :

  ```text
  E.isLocal φ   ⇔   E.delta φ = 0.
  ```

* `isNonlocal_iff_delta_band` :

  ```text
  E.isNonlocal φ   ⇔   1 ≤ E.delta φ ∧ E.delta φ < 2.
  ```

`RefSystem` n’est donc pas un paquet d’axiomes, mais l’abstraction d’une instance construite explicitement.

---

### 12. Étape 3 – Trichotomie de `delta` (justification du rang)

À partir de tout `RefSystem E`, on sait déjà :

* `φ` local ⇒ `E.delta φ = 0`,
* `φ` non local ⇒ `1 ≤ E.delta φ < 2`.

On raffine ensuite le cas non local à l’aide de la logique classique (LEM) pour les réels :

* soit `E.delta φ = 1`,
* soit `E.delta φ ≠ 1`.

En combinant, on obtient un lemme `delta_trichotomy` :

> Pour toute phrase `φ`, exactement un des trois cas suivants est vrai :
>
> 1. `E.delta φ = 0`
> 2. `E.delta φ = 1`
> 3. `E.delta φ ≠ 0` et `E.delta φ ≠ 1`.

C’est un **pur théorème**, basé sur :

* les propriétés concrètes de `delta` encapsulées dans `RefSystem`,
* la logique classique dans Lean.

On ne postule pas de rang ici ; on prouve une décomposition en trois cas de `E.delta φ`.

---

### 13. Étape 4 – Définition de `ObstructionRank` (TriRank)

Étant donnée la trichotomie, on introduit le type fini :

```lean
inductive ObstructionRank
| local      -- delta = 0
| ilm        -- delta = 1
| transcend  -- delta ≠ 0, 1
deriving DecidableEq
```

Puis la fonction de rang :

```lean
def obstructionRank (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)] :
  ObstructionRank :=
  if h0 : E.delta φ = 0 then
    ObstructionRank.local
  else if h1 : E.delta φ = 1 then
    ObstructionRank.ilm
  else
    ObstructionRank.transcend
```

Et le lemme de spécification :

```lean
lemma obstructionRank_spec
    (E : RefSystem Model Sentence) (φ : Sentence)
    [Decidable (E.delta φ = 0)] [Decidable (E.delta φ = 1)] :
  (obstructionRank E φ = ObstructionRank.local ∧ E.delta φ = 0)
  ∨ (obstructionRank E φ = ObstructionRank.ilm ∧ E.delta φ = 1)
  ∨ (obstructionRank E φ = ObstructionRank.transcend
      ∧ E.delta φ ≠ 0 ∧ E.delta φ ≠ 1)
```

Ce lemme exprime exactement que :

* `obstructionRank E φ` n’ajoute **aucune information** à `E.delta φ`,
* il se contente de **classer** la valeur de `delta` selon la trichotomie.

Le rang d’obstruction est donc un **résumé discret** de l’invariant continu `delta`.

---

### 14. Étape 5 – Classification de codes numériques

Le rang est ensuite appliqué à des **familles de phrases** qui codent des objets numériques.

Formes typiques :

* `Code` : type de codes numériques,
* `Cut : ℚ → Code → Sentence`  (coupes rationnelles),
* `Bit : ℕ → ℕ → Code → Sentence` (bits dyadiques).

On définit :

```lean
cutRank E Cut x q :=
  obstructionRank E (Cut q x)

bitRank E Bit x n a :=
  obstructionRank E (Bit n a x)
```

Et des propriétés comme :

```lean
codeIsCutLocal E Cut x :=
  ∀ q, cutRank E Cut x q = ObstructionRank.local

codeHasTranscendentBits E Bit x :=
  ∃ n a, bitRank E Bit x n a = ObstructionRank.transcend
```

Ce sont :

* des notions purement **dérivées**,
* bâties sur `RefSystem`, `delta`, `obstructionRank`,
* et les lemmes déjà prouvés dans `Rank.lean`.

On peut ainsi exprimer, pour un code `x : Code`, des propriétés du type :

* “toutes les coupes rationnelles de `x` sont locales” (`codeIsCutLocal`),
* “`x` possède au moins un bit dyadique de rang transcend” (`codeHasTranscendentBits`).

On s’intéressera en particulier, dans `LogicDissoc/Omega.lean` (cf. §15), à des
codes `x` dont **toutes** les coupes sont de rang `ilm` et **tous** les bits
dyadiques sont de rang `transcend`.

---

### 15. Codes de type Ω (Omega.lean)

Les définitions de `cutRank` et `bitRank` permettent de classer *tout* code
`x : Code` en termes d’obstruction (local, `ilm`, transcend). Pour capturer
abstractionnellement un code de type Ω de Chaitin, on n’ajoute pas de constante
globale `Omega : Code` ni d’axiomes dans `Rank.lean`.

À la place, le fichier

```text
LogicDissoc/Omega.lean
```

introduit une spécification paramétrée :

```lean
namespace LogicDissoc.Omega

structure Spec
    {Model Sentence Code : Type _}
    (E   : RefSystem Model Sentence)
    (Cut : ℚ → Code → Sentence)
    (Bit : ℕ → ℕ → Code → Sentence)
    (x   : Code) : Prop :=
  (cuts_are_ilm :
     ∀ q : ℚ,
       E.delta (Cut q x) ≠ 0 ∧ E.delta (Cut q x) = 1)
  (bits_are_transcend :
     ∀ n a : ℕ,
       E.delta (Bit n a x) ≠ 0 ∧ E.delta (Bit n a x) ≠ 1)
```

Autrement dit, `Spec E Cut Bit x` dit que le code `x` est obstructionnellement
de type Ω :

* toutes ses coupes rationnelles `Cut q x` sont de rang `ilm`,
* tous ses bits dyadiques `Bit n a x` sont de rang `transcend`,

au sens de `ObstructionRank` défini dans `Rank.lean`.

À partir de cette spécification, on démontre dans `Omega.lean` que, pour tout
`x` et toute preuve `hΩ : Spec E Cut Bit x`, on a :

```lean
open LogicDissoc.Omega

lemma omega_cutRank_is_ilm
    (hΩ : Spec E Cut Bit x)
    [∀ q, Decidable (E.delta (Cut q x) = 0)]
    [∀ q, Decidable (E.delta (Cut q x) = 1)] :
  ∀ q : ℚ,
    cutRank E Cut x q = ObstructionRank.ilm

lemma omega_bitRank_is_transcend
    (hΩ : Spec E Cut Bit x)
    [∀ n a, Decidable (E.delta (Bit n a x) = 0)]
    [∀ n a, Decidable (E.delta (Bit n a x) = 1)] :
  ∀ n a : ℕ,
    bitRank E Bit x n a = ObstructionRank.transcend
```

Ces lemmes ne font qu’exploiter la structure de `Spec` et les lemmes généraux
de `Rank.lean` (`obstructionRank_ilm_of_delta_eq_one`,
`obstructionRank_transcend_of_delta_ne`). Ils n’ajoutent aucun axiome : `Spec`
est une propriété purement propositionnelle d’un code `x`, exprimée dans le
langage de `RefSystem`.

Le fichier `Rank.lean` reste ainsi purement général (il ne parle pas d’Ω) ;
toute la logique “de type Chaitin” est isolée dans `Omega.lean`, au niveau
`Prop`, sans `noncomputable` ni constantes globales supplémentaires.

La future connexion avec le **halting** (via `Rev.lean`) consistera à exhiber,
dans un troisième temps, des codes concrets `x` satisfaisant `Spec E Cut Bit x`
à partir d’une construction de type Ω de Chaitin. Cette étape se fera dans un
fichier séparé (par exemple `OmegaViaHalting.lean`), en réutilisant la théorie
du halting abstrait développée dans `Rev.lean`.

---

### 16. Étape 6 – Synthèse de la couche interne

En synthèse :

1. On construit un **modèle concret** avec `delta` et les preuves de son comportement (localité / non-localité).
2. On encapsule ces propriétés dans une abstraction `RefSystem`, en préservant la garantie d’existence.
3. On prouve une **trichotomie** pour `delta`.
4. On définit un type fini `ObstructionRank` qui recode cette trichotomie.
5. On introduit des définitions basées sur le rang pour des familles de phrases (coupes, bits, etc.), uniquement à partir de ces briques.
6. Éventuellement, on isole des spécifications plus fines comme `Omega.Spec` pour décrire des codes de type Ω, sans modifier `Rank.lean` ni ajouter d’axiomes.

Conclusion :

* le rang d’obstruction est **démontré**, non postulé,
* il est dérivé de `delta` au sein de `RefSystem`,
* `RefSystem` lui-même est justifié par une **construction explicite** en amont,
* les constructions de type Ω sont formulées comme des propriétés (`Spec`) au-dessus de cette couche, et non comme des constantes globales non calculables.

---

## 17. Licence

Ce projet est distribué sous la licence **GNU Affero General Public License version 3.0 only (AGPL-3.0-only)**.

Toute version modifiée ou dérivée rendue accessible à des tiers, y compris via un service en ligne, doit être distribuée sous la même licence, avec le code source correspondant.

Pour plus de détails :
[https://www.gnu.org/licenses/agpl-3.0.html](https://www.gnu.org/licenses/agpl-3.0.html)