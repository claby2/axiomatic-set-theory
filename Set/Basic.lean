import Aesop
import Mathlib.Logic.Basic
import Set.Axioms

namespace Set
  -- Empty set
  noncomputable def Empty : Set :=
    Classical.choose empty
  lemma Empty.Spec : ∀ x : Set, x ∉ Empty :=
    Classical.choose_spec empty
  notation "∅" => Empty

  -- Pair
  noncomputable def Pair (u v : Set) : Set := Classical.choose (pairing u v)
  @[simp]
  lemma Pair.Spec (u v : Set) : ∀ x : Set, x ∈ Pair u v ↔ x = u ∨ x = v := Classical.choose_spec (pairing u v)

  -- Singleton Set
  noncomputable def Singleton (x : Set) : Set := Classical.choose (pairing x x)
  @[simp]
  lemma Singleton.Spec (x : Set) : ∀ y : Set, y ∈ Singleton x ↔ y = x := by
    have h : ∀ y, y ∈ Singleton x ↔ y = x ∨ y = x :=
      Classical.choose_spec (pairing x x)
    aesop

  -- Power
  noncomputable def Power (A : Set) : Set := Classical.choose (power A)
  @[simp]
  lemma Power.Spec (A : Set) : ∀ (x : Set), x ∈ Power A ↔ x ⊆ A := Classical.choose_spec (power A)
  prefix:75 "𝒫" => Power

  -- Big Union
  noncomputable def BigUnion (A : Set) : Set := Classical.choose (union A)
  @[simp]
  lemma BigUnion.Spec (A : Set) : ∀ x : Set, x ∈ BigUnion A ↔ (∃ (b : Set), b ∈ A ∧ x ∈ b) :=
    Classical.choose_spec (union A)
  prefix:75 "⋃" => BigUnion


  -- Union [Enderton, p. 27]
  noncomputable def Union (A B : Set) : Set := Classical.choose (union (Classical.choose (pairing A B)))
  @[simp]
  lemma Union.Spec (A B : Set) : ∀ x : Set, x ∈ Union A B ↔ x ∈ A ∨ x ∈ B := by
    -- P = {A, B}
    let P := Classical.choose (pairing A B)
    have hP : ∀ x, x ∈ P ↔ x = A ∨ x = B := by
      have h := Classical.choose_spec (pairing A B)
      aesop
    -- U = ⋃P = ⋃{A, B}
    let U := Classical.choose (union P)
    have hU : ∀ x, x ∈ U ↔ ∃ b, b ∈ P ∧ x ∈ b := by
      have h := Classical.choose_spec (union P)
      aesop
    rw [Union]
    aesop
  infix:70 " ∪ " => Union

  -- Relative Complement [Enderton, p. 27]
  noncomputable def Difference (A B : Set) : Set := Classical.choose (comprehension (λ x ↦ x ∈ A ∧ x ∉ B) A)
  @[simp]
  lemma Difference.Spec (A B : Set) : ∀ x : Set, x ∈ Difference A B ↔ x ∈ A ∧ x ∉ B := by
    have h := Classical.choose_spec (comprehension (λ x ↦ x ∈ A ∧ x ∉ B) A)
    rw [Difference]
    aesop

  infix:70 " - " => Difference

  -- Intersection [Enderton, p. 27]
  noncomputable def Intersection (A B : Set) : Set := Classical.choose (comprehension (λ x ↦ x ∈ A ∧ x ∈ B) (Union A B))
  @[simp]
  lemma Intersection.Spec (A B : Set) : ∀ x : Set, x ∈ Intersection A B ↔ x ∈ A ∧ x ∈ B := by
    let U := Union A B
    have hU : ∀ x, x ∈ U ↔ x ∈ A ∨ x ∈ B := by apply Union.Spec
    let I := Classical.choose (comprehension (λ x ↦ x ∈ A ∧ x ∈ B) U)
    have hI : ∀ x, x ∈ I ↔ x ∈ U ∧ x ∈ A ∧ x ∈ B := Classical.choose_spec (comprehension (λ x ↦ x ∈ A ∧ x ∈ B) U)
    rw [Intersection]
    aesop
  infix:70 " ∩ " => Intersection

  -- Show that two sets are not equal if there exists an element that is in one set but not the other
  theorem not_eq (A B : Set) (x : Set) : (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A) → A ≠ B := by aesop

end Set
