import Set.Basic

namespace Set
  /-
  [Enderton, Theorem 2A]
  There is no set to which every set belongs.
  -/
  theorem no_universal_set : ¬ ∃ (A : Set), ∀ (x : Set), x ∈ A := by
    intro h
    obtain ⟨A, hA⟩ := h
    have hB : ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ A ∧ x ∉ x := by apply comprehension
    obtain ⟨B, hB⟩ := hB
    have h : B ∈ B ↔ B ∈ A ∧ B ∉ B := by apply hB B
    cases Classical.em (B ∈ B) with
      | inl hBB =>
        have hnBB : B ∉ B := by aesop
        exact hnBB hBB
      | inr hnBB =>
        have hBB : B ∈ B := by aesop
        exact hnBB hBB
  /-
  [Enderton, Theorem 2B]
  For any nonempty set A, there exists a unique set B such that for any x,

    x ∈ B ↔ x belongs to every member of A.

  This theorem permits defining ⋂A to be that unique set B.
  -/
  theorem intersection (A : Set) (h : A.Nonempty) : ∃! (B : Set), ∀ (x : Set), x ∈ B ↔ (∀ (a : Set), a ∈ A → x ∈ a) := by
    obtain ⟨c, hc⟩ := h
    have hB : ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ ∀ (a : Set), a ∈ A ∧ a ≠ c → x ∈ a := by apply comprehension
    obtain ⟨B, hB⟩ := hB
    apply Exists.intro B
    simp
    apply And.intro
    -- Show that it matches the definition
    intro x
    { apply Iff.intro
      { intro hx
        intro a ha
        have h : x ∈ c ∧ ∀ (a : Set), a ∈ A ∧ a ≠ c → x ∈ a := by aesop
        cases Classical.em (a = c) with
          | inl heq => aesop
          | inr hneq => aesop
      }
      aesop
    }
    -- Uniqueness
    { intro B' hB'
      apply extensionality
      intro x'
      apply Iff.intro
      { aesop }
      { intro hBx
        have h : ∀ (a : Set), a ∈ A → x' ∈ a := by
          intro a ha
          have h : x' ∈ c ∨ ∀ (a : Set), a ∈ A ∧ a ≠ c → x' ∈ a := by aesop
          cases Classical.em (a = c) with
            | inl heq => aesop
            | inr hneq => aesop
        aesop
      }
    }

  /-
  [Enderton, p.28]
  Elementary facts of the algebra of sets.
  -/
  -- Union
  lemma Union.comm (A B : Set) : A ∪ B = B ∪ A := by
    apply extensionality
    intro x
    apply Iff.intro
    repeat
    { intro hx
      rw [Union.Spec] at *
      aesop
    }
  lemma Union.assoc (A B C : Set) : A ∪ (B ∪ C) = (A ∪ B) ∪ C := by
    apply extensionality
    intro x
    apply Iff.intro
    repeat
    { intro hx
      simp [Union.Spec] at *
      cases hx with
        | inl hx => aesop
        | inr hx => aesop
    }
  lemma Union.dist (A B C : Set) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
    apply extensionality
    intro x
    apply Iff.intro
    { intro hx
      simp [Intersection.Spec, Union.Spec] at *
      aesop
    }
    { intro hx
      simp [Intersection.Spec, Union.Spec] at *
      aesop
    }

  lemma Union.deMorgan (A B C : Set) : C - (A ∪ B) = (C - A) ∩ (C - B) := by
    apply extensionality
    intro x
    apply Iff.intro
    repeat
    { intro hx
      simp [Difference.Spec, Intersection.Spec, Union.Spec] at *
      aesop
    }
  lemma Union.empty (A : Set) : A ∪ Empty = A := by
    apply extensionality
    intro x
    apply Iff.intro
    {
      intro hx
      rw [Union.Spec] at *
      cases hx with
        | inl hx => exact hx
        | inr hx =>
          exfalso
          apply Empty.Spec x
          exact hx
    }
    {
      intro hx
      rw [Union.Spec]
      apply Or.intro_left
      exact hx
    }
  -- Intersection
  lemma Intersection.comm (A B : Set) : A ∩ B = B ∩ A := by
    apply extensionality
    intro x
    apply Iff.intro
    repeat
    { simp [Intersection.Spec]
      intro hxa hxb
      exact And.intro hxb hxa
    }
  lemma Intersection.assoc (A B C : Set) : A ∩ (B ∩ C) = (A ∩ B) ∩ C := by
    apply extensionality
    intro x
    apply Iff.intro
    simp [Intersection.Spec]
    { intro hxa hxb hxc
      exact And.intro (And.intro hxa hxb) hxc
    }
    { simp [Intersection.Spec]
      intro hxa hxb hxc
      exact And.intro hxa (And.intro hxb hxc)
    }
  lemma Intersection.dist (A B C : Set) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
    apply extensionality
    intro x
    apply Iff.intro
    { intro hx
      simp [Union.Spec, Intersection.Spec] at *
      obtain ⟨hx₁, hx₂⟩ := hx
      cases hx₂ with
        | inl hx₂ =>
          apply Or.intro_left
          exact And.intro hx₁ hx₂
        | inr hx₂ =>
          apply Or.intro_right
          exact And.intro hx₁ hx₂
    }
    { intro hx
      simp [Union.Spec, Intersection.Spec] at *
      cases hx with
        | inl hx =>
          obtain ⟨hx₁, hx₂⟩ := hx
          apply And.intro hx₁
          apply Or.intro_left
          exact hx₂
        | inr hx =>
          obtain ⟨hx₁, hx₂⟩ := hx
          apply And.intro hx₁
          apply Or.intro_right
          exact hx₂
    }
  lemma Intersection.deMorgan (A B C : Set) : C - (A ∩ B) = (C - A) ∪ (C - B) := by sorry
  lemma Intersection.empty (A : Set) : A ∩ Empty = Empty := by sorry
  lemma Intersection.empty' (A C : Set) : A ∩ (C - A) = Empty := by sorry

end Set
