-- Declare the constants
axiom Set : Type

namespace Set
  -- Set Membership
  axiom ElementOf : Set → Set → Prop
  infix:50 " ∈ " => ElementOf
  infix:40 " ∉ " => λ x y => ¬ ElementOf x y

  -- Nonempty
  def Nonempty (A : Set) : Prop := ∃ (x : Set), x ∈ A

  -- Subset
  @[simp]
  def SubsetOf (x a : Set) : Prop := ∀ (t : Set), t ∈ x → t ∈ a
  infix:50 " ⊆ " => SubsetOf
end Set
