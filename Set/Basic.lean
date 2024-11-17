import Aesop
import Mathlib.Logic.Basic
import Set.Axioms

namespace Set
  -- Empty set
  noncomputable def Empty : Set :=
    Classical.choose empty
  lemma Empty.Spec : ∀ x : Set, x ∉ Empty :=
    Classical.choose_spec empty
  notation "∅" => Empty

  -- Pair
  noncomputable def Pair (u v : Set) : Set := Classical.choose (pairing u v)

  -- Singleton Set
  noncomputable def Singleton (x : Set) : Set := Classical.choose (pairing x x)
  lemma Singleton.Spec (x : Set) : ∀ y : Set, y ∈ Singleton x ↔ y = x := by
    have h : ∀ y, y ∈ Singleton x ↔ y = x ∨ y = x :=
      Classical.choose_spec (pairing x x)
    aesop

  -- Power
  noncomputable def Power (A : Set) : Set := Classical.choose (power A)
  lemma Power.Spec (A : Set) : ∀ (x : Set), x ∈ Power A ↔ x ⊆ A := Classical.choose_spec (power A)
  prefix:75 "𝒫" => Power

  -- Big Union
  noncomputable def BigUnion (A : Set) : Set := Classical.choose (union A)
  lemma BigUnion.Spec (A : Set) : ∀ x : Set, x ∈ BigUnion A ↔ (∃ (b : Set), b ∈ A ∧ x ∈ b) :=
    Classical.choose_spec (union A)
  prefix:75 "⋃" => BigUnion


  -- Union [Enderton, p. 27]
  noncomputable def Union (A B : Set) : Set := Classical.choose (union (Classical.choose (pairing A B)))
  lemma Union.Spec (A B : Set) : ∀ x : Set, x ∈ Union A B ↔ x ∈ A ∨ x ∈ B := by sorry

  -- Intersection [Enderton, p. 27]
  noncomputable def Intersection (A B : Set) : Set := Classical.choose (comprehension (λ x ↦ x ∈ A ∧ x ∈ B) (Union A B))
  lemma Intersection.Spec (A B : Set) : ∀ x : Set, x ∈ Intersection A B ↔ x ∈ A ∧ x ∈ B := by sorry


  -- Show that two sets are not equal if there exists an element that is in one set but not the other
  lemma not_eq (A B : Set) (x : Set) : (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A) → A ≠ B := by aesop

end Set
