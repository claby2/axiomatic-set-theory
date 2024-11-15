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
        exact (Set.Empty.Spec b) hb.left
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

/-
[Enderton, Exercise 2.3]
Show that every member of a set A is a subset of ⋃A.
-/
lemma exercise_2_3 (A : Set): ∀ (x : Set), x ∈ A → x ⊆ ⋃A := by
  intro x hx
  intro y hy
  apply (Set.Union.Spec A y).mpr
  apply Exists.intro x
  apply And.intro
  { exact hx }
  { exact hy }

/-
[Enderton, Exercise 2.4]
Show that if A ⊆ B, then ⋃A ⊆ ⋃B
-/
lemma exercise_2_4 (A B : Set) : A ⊆ B → ⋃A ⊆ ⋃B := by
  intro hsub
  intro a ha
  have ha' : (∃ (a' : Set), a' ∈ A ∧ a ∈ a') := by apply (Set.Union.Spec A a).mp ha
  obtain ⟨a', ha'⟩ := ha'
  apply (Set.Union.Spec B a).mpr
  apply Exists.intro a'
  apply And.intro
  { apply hsub
    apply ha'.left
  }
  { exact ha'.right }

/-
[Enderton, Exercise 2.6]
(a) Show that for any set A, ⋃𝒫A = A.
(b) Show that A ⊆ 𝒫⋃A.
-/
lemma exercise_2_6 (A : Set) : ⋃𝒫 A = A ∧ A ⊆ 𝒫⋃ A := by
  -- Part (a)
  have a : ⋃(A.Power) = A := by
    apply Set.extensionality
    intro x
    apply Iff.intro
    { intro h
      have hb : ∃ (b : Set), b ∈ 𝒫 A ∧ x ∈ b := by apply (Set.Union.Spec (𝒫 A) x).mp h
      obtain ⟨b, ⟨hb, hxb⟩⟩ := hb
      have hbsub : b ⊆ A := by apply (Set.Power.Spec A b).mp hb
      apply hbsub
      exact hxb
    }
    { intro h
      have hb : (∃ (b : Set), b ∈ 𝒫 A ∧ x ∈ b) := by
        let xsingleton := Set.Singleton x
        apply Exists.intro xsingleton
        apply And.intro
        { have hxs : xsingleton ⊆ A := by
            intro x' hxs
            have hxeq : x' = x := by
              apply (Set.Singleton.Spec x x').mp hxs
            rw [←hxeq] at h
            exact h
          apply (Set.Power.Spec A xsingleton).mpr hxs
        }
        { apply (Set.Singleton.Spec x x).mpr
          rfl
        }
      exact (Set.Union.Spec (𝒫 A) x).mpr hb
    }
  -- Part (b)
  have b : A ⊆ (⋃A).Power := by
    intro a ha
    apply (Set.Power.Spec (⋃A) a).mpr
    intro a' ha'
    apply (Set.Union.Spec A a').mpr
    apply Exists.intro a
    exact And.intro ha ha'
  exact And.intro a b

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

