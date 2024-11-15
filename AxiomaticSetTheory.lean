import Aesop
import Mathlib.Logic.Basic
import Set.Basic


-- Union of the empty set is the empty set
lemma union_of_empty_set : ⋃ Set.Empty = Set.Empty := by
  apply Set.extensionality
  intro x
  apply Iff.intro
  { intro hx
    have hx' : ∃ (b : Set), b ∈ Set.Empty ∧ x ∈ b := by
      apply (Set.Union.Spec Set.Empty x).mp
      exact hx
    cases hx' with
      | intro b hb =>
        exfalso
        exact (Set.Empty.Spec b) hb.1
  }
  { intro hx
    exfalso
    exact (Set.Empty.Spec x) hx
  }

/-
[Enderton, Exercise 2.2]
Give an example of sets A and B for which ⋃A = ⋃B but A ≠ B
-/
lemma exercise_2_2 : ∃ (A B : Set), ⋃A = ⋃B ∧ A ≠ B := by
  -- A = ∅
  let A : Set := ∅
  -- B = {∅}
  let B : Set := Set.Singleton ∅
  apply Exists.intro A
  apply Exists.intro B
  apply And.intro
  { apply Set.extensionality
    intro x
    apply Iff.intro
    { intro hxa
      have hb := (Set.Union.Spec A x).mp hxa
      cases hb with
        | intro b hb =>
          exfalso
          obtain ⟨hb, _⟩ := hb
          have hb' : b ∉ A := by
            apply Set.Empty.Spec
          exact hb' hb
    }
    { intro hxb
      have ha := (Set.Union.Spec B x).mp hxb
      obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := ha
      have ha : a = Set.Empty := by
        apply (Set.Singleton.Spec ∅ a).mp
        exact ha₁
      rw [ha] at ha₂
      exfalso
      have ha' : x ∉ ∅ := by
        apply Set.Empty.Spec x
      exact ha' ha₂
    }
  }
  { intro h
    have hneq : A ≠ B := by
      apply A.not_eq B ∅
      simp
      apply Or.inr
      apply And.intro
      { apply (Set.Singleton.Spec ∅ ∅).mpr
        rfl
      }
      { apply Set.Empty.Spec }
    exact hneq h
  }

-- The empty set is unique
lemma empty_set_unique (e₁ e₂ : Set) :
  (∀ x, ¬ x ∈ e₁) → (∀ x, ¬ x ∈ e₂) → e₁ = e₂ := by
  intro h₁ h₂
  apply Set.extensionality
  intro x
  apply Iff.intro
  { intro hx
    have hx' : ¬ (x ∈ e₁) := h₁ x
    exfalso
    exact hx' hx
  }
  { intro hx
    have hx' : ¬ (x ∈ e₂) := h₂ x
    exfalso
    exact hx' hx
  }

