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
      let w := Set.OrderedPair a x
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
      let w := Set.OrderedPair a x
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
