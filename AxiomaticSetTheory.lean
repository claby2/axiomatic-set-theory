import Aesop
import Mathlib.Logic.Basic

-- Declare the constants
axiom Set : Type
axiom ElementOf : Set → Set → Prop

infix:50 " ∈ " => ElementOf
infix:40 " ∉ " => λ x y => ¬ ElementOf x y


def SubsetOf (x a : Set) : Prop := ∀ (t : Set), t ∈ x → t ∈ a

infix:50 " ⊆ " => SubsetOf

-- subset axiom
axiom comprehension (P : Set → Prop) (c : Set) :
  ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ P x

axiom extensionality : ∀ (A B : Set), (∀ (x : Set), (x ∈ A ↔ x ∈ B)) → A = B

axiom empty : ∃ (B : Set), ∀ (x : Set), x ∉ B

axiom pairing : ∀ (u v : Set), ∃ (B: Set), ∀ (x : Set), x ∈ B ↔ x = u ∨ x = v

axiom power : ∀ (a : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ⊆ a

axiom union_preliminary : ∀ (a b : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ a ∨ x ∈ b

axiom union : ∀ (A : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ (∃ (b : Set), b ∈ A ∧ x ∈ b)

def nonempty (A : Set) : Prop := ∃ (x : Set), x ∈ A

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
theorem intersection (A : Set) (h : nonempty A) : ∃! (B : Set), ∀ (x : Set), x ∈ B ↔ (∀ (a : Set), a ∈ A → x ∈ a) := by
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

theorem empty_set_unique (e₁ e₂ : Set) :
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

