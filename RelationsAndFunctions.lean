import Set.Relations

lemma exists_elem_in_nonempty (A : Set) : A ≠ ∅ → ∃ x, x ∈ A := by
  intro h
  apply by_contradiction
  intro ha
  have h' : ∀ x, ¬ x ∈ A := by
    intro x
    aesop
  have h' : A = Set.Empty := by
    apply Set.extensionality
    intro x
    apply Iff.intro
    aesop
    { intro hx
      exfalso
      exact (Set.Empty.Spec x) hx
    }
  contradiction

/-
[Enderton, Exercise 3.2]
(a) Show that A ⨯ (B ∪ C) = (A ⨯ B) ∪ (A ⨯ C).
(b) Show that if A ⨯ B = A ⨯ C and A ≠ ∅, then B = C.
-/
lemma exercise_3_2 (A B C : Set) :
  A ⨯ (B ∪ C) = (A ⨯ B) ∪ (A ⨯ C) ∧ (A ⨯ B = A ⨯ C ∧ A ≠ ∅ → B = C) := by
  have a : A ⨯ (B ∪ C) = (A ⨯ B) ∪ (A ⨯ C) := by
    apply Set.extensionality
    aesop
  have b : A ⨯ B = A ⨯ C ∧ A ≠ ∅ → B = C := by
    intro ⟨h₁, h₂⟩
    apply Set.extensionality
    intro x
    apply Iff.intro
    { intro hxb
      obtain ⟨a, ha⟩ := exists_elem_in_nonempty A h₂
      let w := ⟨a, x⟩
      have hw : w ∈ A ⨯ B := by
        rw [Set.Product.Spec]
        aesop
      have hw : w ∈ A ⨯ C := by aesop
      rw [Set.Product.Spec] at hw
      obtain ⟨_, hw⟩ := hw
      obtain ⟨x', y', _, ⟨hy', hw'⟩⟩ := hw
      have hxy' : x = y' := by
        rw [Set.OrderedPair.uniqueness] at hw'
        exact hw'.right
      subst hxy'
      exact hy'
    }
    { intro hxc
      obtain ⟨a, ha⟩ := exists_elem_in_nonempty A h₂
      let w := ⟨a, x⟩
      have hw : w ∈ A ⨯ C := by
        rw [Set.Product.Spec]
        aesop
      have hw : w ∈ A ⨯ B := by aesop
      rw [Set.Product.Spec] at hw
      obtain ⟨_, hw⟩ := hw
      obtain ⟨x', y', _, ⟨hy', hw'⟩⟩ := hw
      have hxy' : x = y' := by
        rw [Set.OrderedPair.uniqueness] at hw'
        exact hw'.right
      subst hxy'
      exact hy'
    }
  exact And.intro a b

/-
[Enderton, Exercise 3.7]
Show that if R is a relation, then fld R = ⋃⋃R
-/
lemma exercise_3_7 (A B R : Set) (prop : Set → Set → Prop) : R = Set.Relation A B prop → (fld R) = ⋃⋃R := by
  intro h
  apply Set.extensionality
  intro x
  apply Iff.intro
  { intro hx
    rw [Set.Relation.Field.Spec] at hx
    cases hx with
      | inl hx =>
        rw [Set.Relation.Domain.Spec] at hx
        obtain ⟨y, hy⟩ := hx
        exact (Set.OrderedPair.in_union_union x y R hy).left
      | inr hx =>
        rw [Set.Relation.Range.Spec] at hx
        obtain ⟨y, hy⟩ := hx
        exact (Set.OrderedPair.in_union_union y x R hy).right
  }
  { intro hx
    rw [Set.Relation.Field.Spec, Set.Relation.Domain.Spec, Set.Relation.Range.Spec]
    rw [h] at hx
    rw [Set.BigUnion.Spec] at hx
    obtain ⟨b₁, ⟨hb₂, hb₁⟩⟩ := hx
    rw [Set.BigUnion.Spec] at hb₂
    obtain ⟨b₂, ⟨hb₂, hb₁b₂⟩⟩ := hb₂
    rw [Set.Relation.Spec, Set.Product.Spec] at hb₂
    obtain ⟨⟨_, _, _, _, _, h⟩, _⟩ := hb₂
    rw [Set.OrderedPair] at h
    rw [h] at hb₁b₂
    rw [Set.Pair.Spec] at hb₁b₂
    cases hb₁b₂ with
      | inl h => aesop
      | inr h => aesop
  }
