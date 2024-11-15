import Set.Axioms

namespace Set
  -- Empty set
  noncomputable def Empty : Set :=
    Classical.choose empty
  lemma Empty.Spec : ∀ x : Set, x ∉ Set.Empty :=
    Classical.choose_spec empty
  notation "∅" => Set.Empty

  -- Pair
  noncomputable def Pair (u v : Set) : Set := Classical.choose (pairing u v)

  -- Singleton Set
  noncomputable def Singleton (x : Set) : Set := Classical.choose (pairing x x)
  lemma Singleton.Spec (x : Set) : ∀ y : Set, y ∈ Set.Singleton x ↔ y = x := by
    have h : ∀ y, y ∈ Set.Singleton x ↔ y = x ∨ y = x :=
      Classical.choose_spec (pairing x x)
    aesop

  -- Union
  noncomputable def Union (A : Set) : Set := Classical.choose (union A)
  lemma Union.Spec (A : Set) : ∀ x : Set, x ∈ Set.Union A ↔ (∃ (b : Set), b ∈ A ∧ x ∈ b) :=
    Classical.choose_spec (union A)
  prefix:75 "⋃" => Set.Union


  -- Show that two sets are not equal if there exists an element that is in one set but not the other
  lemma not_eq (A B : Set) (x : Set) : (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A) → A ≠ B := by aesop

end Set
