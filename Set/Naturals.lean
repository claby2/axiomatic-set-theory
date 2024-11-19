import Set.Theorems

namespace Set

  noncomputable def Successor (a : Set) : Set := a ∪ Singleton a
  postfix:90 "⁺" => Successor

  def Inductive (A : Set) : Prop := ∅ ∈ A ∧ ∀ a, a ∈ A → a⁺ ∈ A

  axiom infinity : ∃ (A : Set), Inductive A

  -- A natural number is a set that belongs to every inductive set.
  def Natural (n : Set) : Prop := ∀ (A : Set), Inductive A → n ∈ A

  /-
  [Enderton, Theorem 4A, p. 68]
  There is a set whose members are exactly the natural numbers.
  -/
  theorem natural_numbers_exist : ∃ (ω : Set), ∀ (n : Set), n ∈ ω ↔ Natural n := by
    obtain ⟨A, hA⟩ := infinity
    have hw : ∃ (w : Set), ∀ (x : Set), x ∈ w ↔ x ∈ A ∧ ∀ (A' : Set), A' ≠ A ∧ Inductive A' → x ∈ A' := by apply comprehension
    obtain ⟨w, hw⟩ := hw
    apply Exists.intro w
    intro n
    apply Iff.intro
    { intro hn
      intro a ha
      have h : n ∈ A ∧ ∀ (A' : Set), A' ≠ A ∧ Inductive A' → n ∈ A' := by aesop
      cases Classical.em (a = A) with
        | inl heq => aesop
        | inr hneq => aesop
    }
    { aesop }

  noncomputable def ω := Classical.choose natural_numbers_exist
  @[simp]
  lemma ω.Spec : ∀ n, n ∈ ω ↔ Natural n := by
    have h := Classical.choose_spec natural_numbers_exist
    rw [ω]
    aesop

  /-
  [Enderton, Theorem 4B, p. 69]
  ω is inductive, and is a subset of every other inductive set.
  -/
  theorem ω.inductive : Inductive ω := by
    rw [Inductive]
    apply And.intro
    { rw [ω.Spec, Natural]
      intro A hA
      rw [Inductive] at hA
      exact hA.left
    }
    { intro n hn
      rw [ω.Spec, Natural]
      intro A hA
      obtain ⟨hA₁, hA₂⟩ := hA
      apply hA₂ n
      rw [ω.Spec] at hn
      rw [Natural] at hn
      apply hn
      rw [Inductive]
      exact And.intro hA₁ hA₂
    }
  theorem ω.subset_of_inductive : ∀ (A : Set), Inductive A → ω ⊆ A := by
    intro A hA
    intro n hn
    rw [ω.Spec] at hn
    rw [Natural] at hn
    apply hn
    exact hA

  /-
  [Enderton, Theorem 4C, p. 69]
  Every natural number except 0 is the successor of some natural number.

  Here we are invoking the Induction Principle for ω.
  -/
  theorem ω.exists_successor (n : Set) : n ≠ ∅ → Natural n → ∃ (m : Set), m ∈ ω ∧ n = m⁺ := by
    intro hneqe hnat
    have hT : ∃ (T : Set), ∀ (n : Set), n ∈ T ↔ n ∈ ω ∧ (n = Empty ∨ ∃ (p : Set), p ∈ ω ∧ n = p⁺) := by apply comprehension
    obtain ⟨T, hT⟩ := hT
    have hTn : n ∈ T ↔ n ∈ ω ∧ (n = Empty ∨ ∃ p, p ∈ ω ∧ n = p⁺) := by apply hT n
    have hTinductive : Inductive T := by
      rw [Inductive]
      apply And.intro
      { have he : ∅ ∈ ω := by
          rw [ω.Spec]
          intro A hA
          rw [Inductive] at hA
          exact hA.left
        aesop
      }
      { intro k hk
        rw [hT] at hk
        obtain ⟨hk, h⟩ := hk
        cases h with
          | inl h =>
            rw [h]
            apply (hT (∅⁺)).mpr
            apply And.intro
            { rw [ω.Spec, Natural]
              intro A hA
              rw [Inductive] at hA
              obtain ⟨hA₁, hA₂⟩ := hA
              apply hA₂ ∅
              exact hA₁
            }
            { aesop }
          | inr h =>
            apply (hT (k⁺)).mpr
            apply And.intro
            { rw [ω.Spec, Natural]
              intro A hA
              obtain ⟨hA₁, hA₂⟩ := hA
              apply hA₂ k
              rw [ω.Spec, Natural] at hk
              apply hk A
              rw [Inductive]
              exact And.intro hA₁ hA₂
            }
            { aesop }
      }
    have hnT : n ∈ T := by
      rw [Natural] at hnat
      apply hnat T hTinductive
    rw [hT] at hnT
    obtain ⟨_, h⟩ := hnT
    cases h with
      | inl h => contradiction
      | inr h => exact h


end Set
