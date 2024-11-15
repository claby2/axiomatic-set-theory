import Set.Basic

namespace Set
  /-
  [Enderton, Theorem 2A]
  There is no set to which every set belongs.
  -/
  theorem no_universal_set : ¬ ∃ (A : Set), ∀ (x : Set), x ∈ A := by
    intro h
    obtain ⟨A, hA⟩ := h
    have hB : ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ A ∧ x ∉ x := by apply Set.comprehension
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
    have hB : ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ ∀ (a : Set), a ∈ A ∧ a ≠ c → x ∈ a := by apply Set.comprehension
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
      apply Set.extensionality
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
end Set
