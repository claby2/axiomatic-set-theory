import Aesop
import Mathlib.Logic.Basic

-- Declare the constants
axiom Set : Type
axiom ElementOf : Set → Set → Prop

infix:50 " ∈ " => ElementOf
infix:40 " ∉ " => λ x y => ¬ ElementOf x y


def SubsetOf (x a : Set) : Prop := ∀ (t : Set), t ∈ x → t ∈ a
infix:50 " ⊆ " => SubsetOf

/-
Roughly from [Enderton, p. 21, Subset Axioms]
-/
axiom comprehension (P : Set → Prop) (c : Set) :
  ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ P x

axiom extensionality : ∀ (A B : Set), (∀ (x : Set), (x ∈ A ↔ x ∈ B)) → A = B

axiom empty : ∃ (B : Set), ∀ (x : Set), x ∉ B
noncomputable def Set.Empty : Set :=
  Classical.choose empty
lemma Set.Empty.Spec : ∀ x : Set, x ∉ Set.Empty :=
  Classical.choose_spec empty
notation "∅" => Set.Empty


axiom pairing : ∀ (u v : Set), ∃ (B: Set), ∀ (x : Set), x ∈ B ↔ x = u ∨ x = v
noncomputable def Set.Pair (u v : Set) : Set := Classical.choose (pairing u v)

noncomputable def Set.Singleton (x : Set) : Set := Classical.choose (pairing x x)
lemma Set.Singleton.Spec (x : Set) : ∀ y : Set, y ∈ Set.Singleton x ↔ y = x := by
  have h : ∀ y, y ∈ Set.Singleton x ↔ y = x ∨ y = x :=
    Classical.choose_spec (pairing x x)
  aesop

axiom power : ∀ (a : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ⊆ a

axiom union_preliminary : ∀ (a b : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ a ∨ x ∈ b

axiom union : ∀ (A : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ (∃ (b : Set), b ∈ A ∧ x ∈ b)
noncomputable def Set.Union (A : Set) : Set := Classical.choose (union A)
lemma Set.Union.Spec (A : Set) : ∀ x : Set, x ∈ Set.Union A ↔ (∃ (b : Set), b ∈ A ∧ x ∈ b) :=
  Classical.choose_spec (union A)

prefix:75 "⋃" => Set.Union

def Set.Nonempty (A : Set) : Prop := ∃ (x : Set), x ∈ A

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

lemma set_not_equal (A B : Set) (x : Set) : (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A) → A ≠ B := by aesop

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
  { apply extensionality
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
      apply set_not_equal A B ∅
      simp
      apply Or.inr
      apply And.intro
      { apply (Set.Singleton.Spec ∅ ∅).mpr
        rfl
      }
      { apply Set.Empty.Spec }
    exact hneq h
  }

lemma empty_set_unique (e₁ e₂ : Set) :
  (∀ x, ¬ x ∈ e₁) → (∀ x, ¬ x ∈ e₂) → e₁ = e₂ := by
  intro h₁ h₂
  apply extensionality
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

