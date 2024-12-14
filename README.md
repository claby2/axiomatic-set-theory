# Axiomatic Set Theory

This project seeks to embed axiomatic set theory within Lean. Inspired by Enderton's "Elements of Set Theory," this project begins with fundamental axioms and proceeds to formalize the proofs of theorems and exercises presented in the book.

The following serves as a (brief) overview of the formalization of the axioms and theorems in the project.
For the full picture, please refer to the project's source code.

The formalization begins by defining a `Set` as an axiom and what it means to be an "element of" a set (set membership).

```lean
axiom Set : Type

namespace Set
  axiom ElementOf : Set -> Set -> Prop
end
```

Then, the notion of what it means to be `Nonempty` and be a `SubsetOf` another set can be defined in terms of set membership:

```lean
def Nonempty (A : Set) : Prop := ∃ (x : Set), x ∈ A
def SubsetOf (x a : Set) : Prop := ∀ (t : Set), t ∈ x → t ∈ a
```

From this, we can define the axioms of extensionality, comprehension (subset axiom), emptiness, pairing, power, and union.
These axioms largely take on the form of existential claims, where we assert the existence of a set that satisfies a certain property.

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

Using the existence of these sets, we can then define a way to construct instances of these sets.
For example, using the empty set axiom (that is, there exists some set such that no element is a member of it), we can construct the empty set as follows:

```lean
noncomputable def Empty : Set := Classical.choose empty
lemma Empty.Spec : ∀ x : Set, x ∉ Empty := Classical.choose_spec empty
notation "∅" => Empty
```

The above construction features a pattern that is is commonly featured throughout the project.
We first define a `noncomputable` definition that uses choice to construct a set that satisfies the desired property (`Empty`).
Then, an accompanying lemma is defined that asserts the property of the constructed set (e.g. `Empty.Spec`).
This lemma is useful when proving theorems about the constructed set.
Finally, a notation is defined for the constructed set for convenience.

Hence, in a similar manner, we can define and construct notions such as the pair of two sets, the singleton set, the union and intersection of two sets, and the power set among others.

> **A note on uniqueness**: while the above approach does not immediately guarantee the uniqueness of the constructed set, auxiliary lemmas can be defined to assert the uniqueness of the constructed set. This is done when necessary.

With these basic notions in place, we can then proceed to construct ordered pairs and products along with domains, ranges, and fields of relations.

```lean
noncomputable def OrderedPair (x y : Set) : Set := Pair (Singleton x) (Pair x y)
notation:90 "⟨" x ", " y "⟩" => OrderedPair x y
noncomputable def Product (A B : Set) : Set := Classical.choose (OrderedPair.product A B)
infix:60 " ⨯ " => Product
def IsRelation (R : Set) : Prop := ∀ w, w ∈ R → ∃ x y, w = ⟨x, y⟩
noncomputable def Relation.Domain (R : Set) : Set :=
  Classical.choose (comprehension (λ x ↦ ∃ (y : Set), ⟨x, y⟩ ∈ R) (⋃⋃R))
noncomputable def Relation.Range (R : Set) : Set :=
  Classical.choose (comprehension (λ y ↦ ∃ (x : Set), ⟨x, y⟩ ∈ R) (⋃⋃R))
noncomputable def Relation.Field (R : Set) : Set := (dom R) ∪ (ran R)
```

A natural extension of relations is formalizing the notiong of functions, which are defined as a special kind of relation. From Enderton, to be a function, a set must be a relation that satisfies the property that for each x in the domain of the relation, there exists only one y such that xFy.
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

We also start formalizing the notion of natural numbers.
This section starts out by defining what it means to be a "successor" of another set.
That is,

```lean
noncomputable def Successor (a : Set) : Set := a ∪ Singleton a
```

Then, we define the property of being inductive and define a natural number as a set that belongs to every inductive set.

```lean
def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A
def Natural (n : Set) : Prop := ∀ (A : Set), Inductive A → n ∈ A
```

## Next Steps

Thus far, this project only formalizes the first few chapters of Enderton's "Elements of Set Theory."
Even then, there are still some theorems and many exercises that have yet to be formalized.
A natural next direction would be to complete the formalization of the natural numbers (predicated on the formalization of the recursion theorem), which then permits the formalization of arithmetic operations.
Real numbers, cardinal numbers, and ordinals are also interesting directions to explore.
