import Set.Defs

namespace Set
  -- Comprehension axiom
  -- Roughly from [Enderton, p. 21, Subset Axioms]
  axiom comprehension (P : Set → Prop) (c : Set) :
    ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ c ∧ P x

  -- Extensionality axiom
  axiom extensionality : ∀ (A B : Set), (∀ (x : Set), (x ∈ A ↔ x ∈ B)) → A = B

  -- Empty Set axiom
  axiom empty : ∃ (B : Set), ∀ (x : Set), x ∉ B

  -- Pairing axiom
  axiom pairing : ∀ (u v : Set), ∃ (B: Set), ∀ (x : Set), x ∈ B ↔ x = u ∨ x = v

  -- Power axiom
  axiom power : ∀ (a : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ⊆ a

  -- Union axiom
  axiom union_preliminary : ∀ (a b : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ x ∈ a ∨ x ∈ b
  axiom union : ∀ (A : Set), ∃ (B : Set), ∀ (x : Set), x ∈ B ↔ (∃ (b : Set), b ∈ A ∧ x ∈ b)
end Set

