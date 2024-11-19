import Set.Relations

namespace Set
  -- Function [Enderton, p.42]
  noncomputable def Function (A B : Set) (prop : Set → Set → Prop) : Set :=
    Classical.choose (comprehension (λ R ↦ ∀ x, x ∈ (dom R) → ∃! y, ⟨x, y⟩ ∈ R) (Relation A B prop))
  @[simp]
  lemma Function.Spec (A B : Set) (prop : Set → Set → Prop) :
    ∀ (f : Set), f ∈ Function A B prop ↔
      f ∈ Relation A B prop ∧ ∀ x, x ∈ (dom f) → ∃! y, ⟨x, y⟩ ∈ f :=
      Classical.choose_spec (comprehension (λ R ↦ ∀ x, x ∈ (dom R) → ∃! y, x.OrderedPair y ∈ R) (Relation A B prop))

  structure FunctionT (A B : Set) (prop : Set → Set → Prop) :=
    (f : Set)
    (h : f ∈ Set.Function A B prop)


  -- A set R is single-rooted iff for each y ∈ ran R there is only one x such that xRy.
  def SingleRooted (R : Set) : Prop :=
    ∀ (y : Set), y ∈ (ran R) → ∃! (x: Set), ⟨x, y⟩ ∈ R

  /-
  Function operations [Enderton, p. 44]
  -/
  -- Arbitrary sets
  noncomputable def Inverse (F : Set) :=
    Classical.choose (comprehension (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ w = ⟨v, u⟩) ((ran F) ⨯ (dom F)))
  @[simp]
  lemma Inverse.Spec (F : Set) : ∀ x, x ∈ Inverse F ↔ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ x = ⟨v, u⟩ := by
    have h := Classical.choose_spec (comprehension (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ w = ⟨v, u⟩) ((ran F) ⨯ (dom F)))
    rw [Inverse]
    aesop
  noncomputable def Composition (F G : Set) :=
    Classical.choose (comprehension
      (λ w ↦ ∃ (u v t : Set), ⟨u, t⟩ ∈ F ∧ ⟨t, v⟩ ∈ G ∧ w = ⟨u, v⟩)
      (dom G ⨯ ran F))
  noncomputable def Restriction (F : Set) (C : Set) :=
    Classical.choose (comprehension (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ u ∈ C ∧ w = ⟨u, v⟩) F)
  noncomputable def Image (F : Set) (C : Set) :=
    ran (Restriction F C)
  -- Functions
  noncomputable def FunctionT.Inverse {A B : Set} {prop : Set → Set → Prop} (f : FunctionT A B prop) : Set :=
    Classical.choose (comprehension
      (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ f.f ∧ w = ⟨v, u⟩)
      (ran f.f ⨯ dom f.f))
  postfix:90 "⁻¹" => FunctionT.Inverse
  noncomputable def FunctionT.Composition {A B C : Set} {prop₁ : Set → Set → Prop} {prop₂ : Set → Set → Prop}
    (f : FunctionT A B prop₁) (g : FunctionT B C prop₂) : Set :=
    Classical.choose (comprehension
      (λ w ↦ ∃ (u v : Set), ∃ (t : Set), ⟨u, t⟩ ∈ f.f ∧ ⟨t, v⟩ ∈ g.f ∧ w = ⟨u, v⟩)
      (dom g.f ⨯ ran f.f))
  infixr:90 " ∘ " => FunctionT.Composition
  noncomputable def FunctionT.Restriction {A B : Set} {prop : Set → Set → Prop} (f : FunctionT A B prop) (C : Set) : Set :=
    Classical.choose (comprehension (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ f.f ∧ u ∈ C ∧ w = ⟨u, v⟩) f.f)
  infixr:90 " ↾ " => FunctionT.Restriction
  noncomputable def FunctionT.Image {A B : Set} {prop : Set → Set → Prop} (f : FunctionT A B prop) (C : Set) : Set :=
    ran (FunctionT.Restriction f C)

  /-
  [Enderton, Theorem 3E, p. 46]
  For a set F, dom F⁻¹ = ran F and ran F⁻¹ = dom F. For a relation F, (F⁻¹)⁻¹ = F.
  -/
  theorem domain_range_inverse (F : Set) : (dom (Inverse F)) = ran F := by
    apply extensionality
    intro x
    apply Iff.intro
    { intro h
      rw [Relation.Domain.Spec] at h
      obtain ⟨y, hy⟩ := h
      rw [Inverse.Spec] at hy
      obtain ⟨u, v, hu⟩ := hy
      rw [OrderedPair.uniqueness] at hu
      aesop
    }
    { aesop }
  theorem relation_inverse_inverse {A B : Set} {prop : Set → Set → Prop} (R : Set) :
    R = Relation A B prop → (Inverse (Inverse R)) = R := by
    intro h
    apply extensionality
    intro x
    apply Iff.intro
    { intro heq
      rw [Inverse.Spec] at heq
      obtain ⟨u, v, hu⟩ := heq
      obtain ⟨hu₁, hu₂⟩ := hu
      rw [Inverse.Spec] at hu₁
      obtain ⟨v', u', hvu'⟩ := hu₁
      rw [OrderedPair.uniqueness] at hvu'
      aesop
    }
    { intro heq
      rw [Inverse.Spec]
      rw [h] at heq
      rw [Relation.Spec] at heq
      obtain ⟨heq₁, heq₂⟩ := heq
      rw [Product.Spec] at heq₁
      obtain ⟨_, heq₁⟩ := heq₁
      obtain ⟨u, v, hu, hv, huv⟩ := heq₁
      apply Exists.intro v
      apply Exists.intro u
      apply And.intro
      { rw [Inverse.Spec]
        apply Exists.intro u
        apply Exists.intro v
        apply And.intro
        { aesop }
        { aesop }
      }
      { exact huv }
    }
end Set
