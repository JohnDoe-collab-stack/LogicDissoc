## 1. Cadre sémantique de base

**Définition 1 (Cadre sémantique).**
Un cadre sémantique est un quadruplet

* `Sentence` : ensemble de formules,
* `Model` : ensemble de modèles,
* `Sat : Model → Sentence → Prop` : relation de satisfaction,
* `Γ_ref : Set Sentence` : théorie de référence.

On définit la classe de modèles d’une théorie `Γ ⊆ Sentence` par :

```text
ModE(Γ) := { M ∈ Model | ∀ φ ∈ Γ, Sat M φ }.
```

Pour une batterie finie `S ⊆ Sentence` (dans le code : `Battery Sentence = Finset Sentence`), on dit que l’extension par `S` est conservative si :

```text
ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

On note cette propriété :

```text
Cons_S(S) :⇔ ModE(Γ_ref ∪ S) = ModE(Γ_ref).
```

---

## 2. Cône d’obstructions légitimes (couche géométrique)

On fixe un ensemble fini `B` de types d’obstruction.

**Définition 2 (Compteurs).**
Un profil de compteurs est une fonction

```text
c : B → ℕ
```

c’est-à-dire un élément de `ℕ^B` (dans le code : `GenCounters B`).

**Définition 3 (Obstruction légitime).**
Une obstruction légitime sur `B` est la donnée d’une application

```text
F : (B → ℕ) → ℝ
```

satisfaisant (comme dans `ObstructionGen` et `Legit`) :

1. Linéarité sur ℕ : il existe des coefficients `α_b > 0` tels que

   ```text
   F(c) = ∑_{b ∈ B} α_b * c(b).
   ```

2. Non-négativité : pour tout profil `c`,

   ```text
   F(c) ≥ 0.
   ```

3. Noyau trivial : on a

   ```text
   F(c) = 0   ⇔   ∀ b, c(b) = 0.
   ```

Dans le code, un tel objet est encapsulé dans `LegitObstruction B`, avec `L.O.F = F`.

---

## 3. Schéma de comptage admissible

Tout reste purement sémantique (tout passe par `ModE` et `Cons_S`).

**Définition 4 (Protocole de comptage admissible).**
Un protocole de comptage pour le cadre `S` est une application

```text
Count : { batteries finies S ⊆ Sentence } → (B → ℕ).
```

On dit que `Count` est admissible (classe `CountSpec`) si

```text
∀ S,  (∀ b, Count(S)(b) = 0)   ⇔   Cons_S(S).
```

Autrement dit, le profil nul (toutes composantes à 0) est exactement équivalent à la conservativité sémantique.

**Définition 5 (Indice général A*).**
Donnés un cadre `S`, une obstruction légitime `L` et un `Count` admissible, on définit

```text
A*_{S,L,Count}(S) := F(Count(S)) ∈ ℝ,
```

où `F = L.O.F`.

Dans le code : `AstarGen (Sat := Sat) (Γ_ref := Γ_ref) (L := L) (Count := Count) S`.

---

## 4. Directions de Gödel (couche dynamique)

La dynamique intervient à travers des directions sémantiques qui détectent les pertes de modèles quand on enrichit la théorie.

**Définition 6 (Direction de Gödel).**
Une direction de Gödel pour un cadre `S` et un alphabet `B` est la donnée d’un prédicat

```text
P : B → Model → Prop
```

tel que :

1. **Décidabilité locale** : pour toute batterie finie `S` et tout `b ∈ B`, l’assertion suivante est décidable :

   ```text
   ∃ m,
     m ∈ ModE(Γ_ref)
     ∧ m ∉ ModE(Γ_ref ∪ S)
     ∧ P b m.
   ```

   (Champ `dec` dans `GodelDirection`.)

2. **Séparation** : pour toute batterie finie `S`,

   ```text
   ¬ Cons_S(S)
   ⇒
   ∃ b m,
     m ∈ ModE(Γ_ref)
     ∧ m ∉ ModE(Γ_ref ∪ S)
     ∧ P b m.
   ```

   (Champ `separating`.)

À partir de `P`, on définit un comptage canonique.

**Définition 7 (Comptage de Gödel).**
Le protocole de comptage induit par `P` est défini par

```text
Count^Godel(S)(b) :=
  1 si ∃ m, m ∈ ModE(Γ_ref), m ∉ ModE(Γ_ref ∪ S), P b m ;
  0 sinon.
```

Dans le code : `GodelDirection.CountFromGodel`.

**Proposition 7 (Admissibilité du comptage de Gödel).**
Pour tout cadre `S` et toute direction de Gödel `P`, le protocole

```text
Count^Godel : Battery Sentence → (B → ℕ)
```

satisfait la condition d’admissibilité (Définition 4) :

```text
∀ S,  (∀ b, Count^Godel(S)(b) = 0)   ⇔   Cons_S(S).
```

C’est exactement ce qui est démontré par l’instance `CountSpec` pour `CountFromGodel`.

On peut alors spécialiser l’indice.

**Définition 8 (Indice A*_Godel).**
Pour une obstruction légitime `L` et une direction de Gödel `P`, on pose

```text
A*_Godel(S) := F(Count^Godel(S)).
```

Dans le code : `Astar_Godel`.

---

## 5. Méta-théorème d’alignement quantitatif de l’incomplétude

**Théorème 9 (Alignement quantitatif de l’incomplétude).**
Soit un cadre sémantique `S = (Sentence, Model, Sat, Γ_ref)`, un ensemble fini `B`, une obstruction légitime `L` sur `B`, et une direction de Gödel `P` pour `S` et `B`. Alors, pour toute batterie finie `S` de formules :

1. **Frontière zéro**

   ```text
   A*_Godel(S) = 0   ⇔   Cons_S(S).
   ```

   L’indice est nul exactement sur les extensions conservatives de `Γ_ref`.

2. **Frontière strictement positive**

   ```text
   A*_Godel(S) > 0   ⇔   ¬ Cons_S(S).
   ```

   Toute extension non conservative est détectée et strictement séparée de 0 par `A*_Godel`.

3. **Indépendance vis-à-vis du choix de L**

   Si `L1` et `L2` sont deux obstructions légitimes sur le même `B`, alors pour tout `S` :

   ```text
   A*_{Godel}(S; L1) = 0  ⇔  A*_{Godel}(S; L2) = 0,
   A*_{Godel}(S; L1) > 0 ⇔  A*_{Godel}(S; L2) > 0.
   ```

   Le verdict « 0 / > 0 » ne dépend pas du choix du fonctionnel linéaire dans le cône des obstructions légitimes.

Dans le code, ces faits correspondent à :

* `metaGodel_frontier_zero` et `metaGodel_frontier_pos` (partie `MetaGodel`),
* l’instance `CountSpec` pour `GodelDirection.CountFromGodel`,
* les lemmes standard sur `LegitObstruction` (non-négativité, noyau trivial).

---

## 6. Hiérarchie conceptuelle

L’organisation conceptuelle peut se résumer par quatre niveaux :

1. **Niveau 0 – Théorie des modèles (structure sémantique)**
   Cadre `S` : définitions de `ModE`, `Cons_S`, notion de conservativité, indépendantes de tout langage concret particulier.

2. **Niveau 1 – Cône d’obstructions (géométrie sur ℕ^B)**
   Obstructions légitimes `L` : fonctionnels linéaires positifs sur `ℕ^B`, avec noyau trivial. Il s’agit de la couche géométrique.

3. **Niveau 2 – Directions de Gödel (dynamique sémantique)**
   Directions `P` : choix de prédicats sur les modèles qui détectent quelles parties de `ModE(Γ_ref)` disparaissent sous l’ajout de `S`.
   Le comptage canonique `Count^Godel` convertit ces phénomènes sémantiques en profils `B → ℕ`.

4. **Niveau 3 – Indice et quantification sémantique de l’incomplétude**
   Pour toute combinaison `(S, B, P, L)` satisfaisant les axiomes, l’indice

   ```text
   S ↦ A*_Godel(S)
   ```

   fournit :

   * un verdict qualitatif invariant : `0` si et seulement si l’extension est conservative, `>0` sinon ;
   * une valeur quantitative réelle mesurant la « taille d’obstruction » suivant les directions choisies.

Ce schéma est entièrement formulé au niveau de la théorie des modèles (classes de modèles, conservativité) et des structures linéaires sur `ℕ^B`, sans supposer une syntaxe particulière ni un système de preuve spécifique.


---

## 10. Licence

Ce projet est distribué sous licence **GNU Affero General Public License version 3.0 uniquement (AGPL-3.0-only)**.

Toute version modifiée ou dérivée rendue accessible à des tiers, y compris via un service en ligne, doit être publiée sous la même licence, avec mise à disposition du code source correspondant.

Pour les conditions complètes, se reporter au texte officiel de la licence GNU AGPL v3.0.

https://www.gnu.org/licenses/agpl-3.0.html