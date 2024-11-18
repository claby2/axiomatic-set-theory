import Set.Theorems

-- BigUnion of the empty set is the empty set
lemma union_of_empty_set : ⋃ Set.Empty = Set.Empty := by
  apply Set.extensionality
  intro x
  apply Iff.intro
  { intro hx
    have hx' : ∃ (b : Set), b ∈ Set.Empty ∧ x ∈ b := by
      apply (Set.BigUnion.Spec Set.Empty x).mp
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
      have hb := (Set.BigUnion.Spec A x).mp hxa
      cases hb with
        | intro b hb =>
          exfalso
          obtain ⟨hb, _⟩ := hb
          have hb' : b ∉ A := by
            apply Set.Empty.Spec
          exact hb' hb
    }
    { intro hxb
      have ha := (Set.BigUnion.Spec B x).mp hxb
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
  apply (Set.BigUnion.Spec A y).mpr
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
  have ha' : (∃ (a' : Set), a' ∈ A ∧ a ∈ a') := by apply (Set.BigUnion.Spec A a).mp ha
  obtain ⟨a', ha'⟩ := ha'
  apply (Set.BigUnion.Spec B a).mpr
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
      have hb : ∃ (b : Set), b ∈ 𝒫 A ∧ x ∈ b := by apply (Set.BigUnion.Spec (𝒫 A) x).mp h
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
      exact (Set.BigUnion.Spec (𝒫 A) x).mpr hb
    }
  -- Part (b)
  have b : A ⊆ (⋃A).Power := by
    intro a ha
    apply (Set.Power.Spec (⋃A) a).mpr
    intro a' ha'
    apply (Set.BigUnion.Spec A a').mpr
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

/-
[Enderton, Exercise 2.11]
Show that for any sets A and B,
(a) A = (A ∩ B) ∪ (A - B), and
(b) A = (A ∪ B) - (B - A).
-/
lemma exercise_2_11 (A B : Set) :
  A = (A ∩ B) ∪ (A - B) ∧ A = (A ∪ B) - (B - A) := by
  -- Proving A = (A ∩ B) ∪ (A - B)
  have a : A = (A ∩ B) ∪ (A - B) := by
    apply Set.extensionality
    intro x
    apply Iff.intro
    { intro h
      rw [Set.Union.comm, Set.Union.dist]
      have h1 : (A - B) ∪ A = A := by
        apply Set.extensionality
        intro y
        apply Iff.intro
        { intro hy
          rw [Set.Union.Spec] at hy
          cases hy with
            | inl hy =>
              rw [Set.Difference.Spec] at hy
              exact hy.left
            | inr hy => exact hy
        }
        { intro hy
          rw [Set.Union.Spec]
          apply Or.intro_right
          exact hy
        }
      have h2 : (A - B) ∪ B = A ∪ B := by
        apply Set.extensionality
        intro x
        apply Iff.intro
        { intro hx
          rw [Set.Union.Spec] at *
          cases hx with
            | inl hx =>
              rw [Set.Difference.Spec] at hx
              apply Or.intro_left
              exact hx.left
            | inr hx =>
              apply Or.intro_right
              exact hx
        }
        { intro hx
          rw [Set.Union.Spec] at *
          cases hx with
            | inl hx =>
              cases Classical.em (x ∈ B) with
                | inl hx' =>
                  apply Or.intro_right
                  exact hx'
                | inr hx' =>
                  apply Or.intro_left
                  rw [Set.Difference.Spec]
                  apply And.intro hx hx'
            | inr hx =>
              apply Or.intro_right
              exact hx
        }
      rw [h1, h2]
      have h3 : A ∩ (A ∪ B) = A := by
        apply Set.extensionality
        intro x
        apply Iff.intro
        { intro hx
          rw [Set.Intersection.Spec] at hx
          exact hx.left
        }
        { intro hx
          rw [Set.Intersection.Spec]
          apply And.intro hx
          rw [Set.Union.Spec]
          apply Or.intro_left
          exact hx
        }
      rw [h3]
      exact h
    }
    { intro h
      rw [Set.Union.Spec, Set.Intersection.Spec] at h
      cases h with
        | inl h => exact h.left
        | inr h =>
          rw [Set.Difference.Spec] at h
          exact h.left
    }
  -- Proving A = (A ∪ B) - (B - A).
  have b : A = (A ∪ B) - (B - A) := by
    apply Set.extensionality
    intro x
    apply Iff.intro
    { intro hx
      rw [Set.Difference.Spec]
      apply And.intro
      { rw [Set.Union.Spec]
        apply Or.intro_left
        exact hx
      }
      { simp [Set.Difference.Spec]
        intro _
        exact hx
      }
    }
    { intro hx
      simp [Set.Difference.Spec, Set.Union.Spec] at hx
      cases hx.left with
        | inl hx' => exact hx'
        | inr hx' =>
          apply hx.right
          exact hx'
    }
  exact And.intro a b
