# Axiomatic Set Theory

Project link: <https://github.com/claby2/axiomatic-set-theory>

This project seeks to formalize an axiomatic approach to set theory within Lean.
Drawing inspiration from Enderton's *Elements of Set Theory*, it begins with the fundamental axioms and proceeds to formalize selected theorems and exercises presented in the book. While this document provides a brief overview, the project's full details and implementations (including proofs to theorems and exercises) can be found in its source code.

## Overview

The core of the project involves introducing a primitive notion of a set and a membership relation, and then building up the standard axioms of ZFC-like set theory.
The development proceeds through the formalization of sets, elementary constructions, and fundamental operations, eventually leading to the formalization of relations, functions, and the beginnings of natural number construction.

### Basic Definitions

First, a `Set` type is introduced as an axiom, along with a membership predicate `ElementOf`:

```lean
axiom Set : Type

axiom ElementOf : Set -> Set -> Prop
infix:50 " ∈ " => ElementOf
infix:40 " ∉ " => λ x y => ¬ ElementOf x y
```

Using this notion, the usual set-theoretic definitions are introduced:

```lean
def Nonempty (A : Set) : Prop := ∃ (x : Set), x ∈ A
def SubsetOf (x a : Set) : Prop := ∀ (t : Set), t ∈ x → t ∈ a
```

### Axioms

With these fundamental ingredients in place, the axioms of set theory are stated.
These include the axiom of comprehension (sometimes called subset or separation), extensionality, the existence of an empty set, pairing, the power set, and union.
Each axiom is stated as an existential claim that asserts the existence of a set satisfying a given property:

```lean
axiom comprehension (P : Set → Prop) (c : Set) :
∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ P x
axiom extensionality : ∀ (A B : Set), (∀ (x : Set), (x ∈ A ↔ x ∈ B)) → A = B
axiom empty : ∃ (B : Set), ∀ (x : Set), x ∉ B
axiom pairing : ∀ (u v : Set), ∃ (B: Set), ∀ (x : Set), x ∈ B ↔ x = u ∨ x = v
axiom power : ∀ (a : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ⊆ a
axiom union_preliminary : ∀ (a b : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ a ∨ x ∈ b
axiom union : ∀ (A : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ (∃ (b : Set), b ∈ A ∧ x ∈ b)
```

### Constructing Specific Sets

From these axioms, particular sets are constructed using the classical choice operator ([`Classical.choose`](https://leanprover-community.github.io/mathlib4_docs/Init/Classical.html#Classical.choose)).
For example, the empty set is defined as follows:

```lean
noncomputable def Empty : Set := Classical.choose empty
lemma Empty.Spec : ∀ x : Set, x ∉ Empty := Classical.choose_spec empty
notation "∅" => Empty
```

This pattern -- defining a set using `Classical.choose` and then providing a lemma stating its properties -- recurs throughout the project.
For instance, the construction of pairs, singletons, unions, intersections, and power sets follows a similar methodology.
Uniqueness results can then be proven separately when necessary.

### Relations and Functions

Once these basic building blocks are in place, the formalization extends to ordered pairs, products, relations, and functions.
Ordered pairs are defined following Kuratowski's approach as outlined in Enderton:

```lean
noncomputable def OrderedPair (x y : Set) : Set := Pair (Singleton x) (Pair x y)
notation:90 "⟨" x ", " y "⟩" => OrderedPair x y
```

With ordered pairs, we can proceed by defining products and products, along with domains, ranges, and fields of relations.

```lean
noncomputable def Product (A B : Set) : Set := Classical.choose (OrderedPair.product A B)
infix:60 " ⨯ " => Product
def IsRelation (R : Set) : Prop := ∀ w, w ∈ R → ∃ x y, w = ⟨x, y⟩
noncomputable def Relation.Domain (R : Set) : Set :=
  Classical.choose (comprehension (λ x ↦ ∃ (y : Set), ⟨x, y⟩ ∈ R) (⋃⋃R))
noncomputable def Relation.Range (R : Set) : Set :=
  Classical.choose (comprehension (λ y ↦ ∃ (x : Set), ⟨x, y⟩ ∈ R) (⋃⋃R))
noncomputable def Relation.Field (R : Set) : Set := (dom R) ∪ (ran R)
```

A natural extension of relations is formalizing the notions of functions, which are defined as a special kind of relation. From Enderton, to be a function, a set must be a relation that satisfies the property that for each $x$ in the domain of the relation, there exists only one $y$ such that $xFy$.
This is expressed in Lean as follows:

```lean
def IsFunction (F : Set) : Prop :=
  IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟨x, y⟩ ∈ F
```

From here, we can define function operations: inverse, composition, restriction, and image.
Their formalizations are as follows:

```lean
noncomputable def Inverse (F : Set) :=
  Classical.choose (comprehension (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ w = ⟨v, u⟩) ((ran F) ⨯ (dom F)))
postfix:90 "⁻¹" => Inverse
noncomputable def Composition (F G : Set) :=
  Classical.choose (comprehension
    (λ w ↦ ∃ (u v t : Set), ⟨u, t⟩ ∈ G ∧ ⟨t, v⟩ ∈ F ∧ w = ⟨u, v⟩)
    ((dom G) ⨯ (ran F)))
infixr:90 " ∘ " => Composition
noncomputable def Restriction (F : Set) (C : Set) :=
  Classical.choose (comprehension (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ u ∈ C ∧ w = ⟨u, v⟩) F)
infixr:90 " ↾ " => Restriction
noncomputable def Image (F : Set) (C : Set) :=
  ran (Restriction F C)
notation:90 F "⟦" A "⟧" => Image F A
```

As noted in Enderton, this is formalized in a way that applies to all sets, not just sets that are functions.

### Natural Numbers

The final part of the current work involves the beginnings of natural number construction.
Following the standard set-theoretic approach, the successor operation is introduced, and inductive sets are defined.
Natural numbers are then those sets contained in every inductive set.

```lean
noncomputable def Successor (a : Set) : Set := a ∪ Singleton a
postfix:90 "⁺" => Successor
def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A
def Natural (n : Set) : Prop := ∀ (A : Set), Inductive A → n ∈ A
```

## Next Steps

So far, the project has developed the foundational machinery through the first few chapters of Enderton's *Elements of Set Theory*.
Many theorems and exercises still remain to be formalized.
A natural next step is to complete the formalization of the natural numbers, which will require invoking the recursion theorem.
Once natural numbers are fully treated, the path is open to formalizing arithmetic, real numbers, cardinal numbers, and ordinals.
