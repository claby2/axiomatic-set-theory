import Set.Relations

namespace Set
  -- Function [Enderton, p.42]
  def IsFunction (F : Set) : Prop :=
    IsRelation F ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟨x, y⟩ ∈ F
  -- A set R is single-rooted iff for each y ∈ ran R there is only one x such that xRy.
  def IsSingleRooted (R : Set) : Prop :=
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
  postfix:90 "⁻¹" => Inverse
  noncomputable def Composition (F G : Set) :=
    Classical.choose (comprehension
      (λ w ↦ ∃ (u v t : Set), ⟨u, t⟩ ∈ G ∧ ⟨t, v⟩ ∈ F ∧ w = ⟨u, v⟩)
      ((dom G) ⨯ (ran F)))
  @[simp]
  lemma Composition.Spec (F G : Set) : ∀ x, x ∈ Composition F G ↔ (x ∈ ((dom G) ⨯ (ran F))) ∧ ∃ (u v t : Set), ⟨u, t⟩ ∈ G ∧ ⟨t, v⟩ ∈ F ∧ x = ⟨u, v⟩ := by
    have h := Classical.choose_spec (comprehension
      (λ w ↦ ∃ (u v t : Set), ⟨u, t⟩ ∈ G ∧ ⟨t, v⟩ ∈ F ∧ w = ⟨u, v⟩)
      ((dom G) ⨯ (ran F)))
    rw [Composition]
    exact h
  infixr:90 " ∘ " => Composition
  noncomputable def Restriction (F : Set) (C : Set) :=
    Classical.choose (comprehension (λ w ↦ ∃ (u v : Set), ⟨u, v⟩ ∈ F ∧ u ∈ C ∧ w = ⟨u, v⟩) F)
  infixr:90 " ↾ " => Restriction
  noncomputable def Image (F : Set) (C : Set) :=
    ran (Restriction F C)
  notation:90 F "⟦" A "⟧" => Image F A

  /-
  [Enderton, Theorem 3E, p. 46]
  For a set F, dom F⁻¹ = ran F and ran F⁻¹ = dom F. For a relation F, (F⁻¹)⁻¹ = F.
  -/
  theorem domain_inverse (F : Set) : (dom (Inverse F)) = ran F := by
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
  theorem range_inverse (F : Set) : (ran (Inverse F)) = dom F := by
    apply extensionality
    intro x
    apply Iff.intro
    { intro h
      rw [Relation.Range.Spec] at h
      obtain ⟨y, hy⟩ := h
      rw [Inverse.Spec] at hy
      obtain ⟨u, v, hu⟩ := hy
      rw [OrderedPair.uniqueness] at hu
      aesop
    }
    { aesop }
  theorem relation_inverse_inverse (F : Set) {hF : IsRelation F} : (Inverse (Inverse F)) = F := by
    apply extensionality
    intro x
    apply Iff.intro
    { intro hx
      rw [Inverse.Spec] at hx
      obtain ⟨u, v, ⟨huv, huvx⟩⟩ := hx
      rw [Inverse.Spec] at huv
      obtain ⟨u', v', ⟨huv', huvx'⟩⟩ := huv
      subst huvx
      have heq : u = v' ∧ v = u' := by
        rw [OrderedPair.uniqueness] at huvx'
        exact huvx'
      rw [heq.left, heq.right]
      exact huv'
    }
    { intro hx
      have huv : ∃ u v, x = ⟨u, v⟩ := by aesop
      aesop
    }


  /-
  [Enderton, Theorem 3F, p. 46]
  For a set F, F⁻¹ is a function iff F is single-rooted. A relation F is a function iff F⁻¹ is single-rooted.
  -/
  theorem inverse_single_rooted (F : Set) : IsFunction (Inverse F) ↔ IsSingleRooted F := by
    apply Iff.intro
    { intro hFi
      rw [IsFunction, domain_inverse] at hFi
      obtain ⟨_, hFi⟩ := hFi
      rw [IsSingleRooted]
      intro x hx
      have hy := hFi x hx
      obtain ⟨y, hy, hy'⟩ := hy
      rw [Inverse.Spec] at hy
      obtain ⟨u, v, huv⟩ := hy
      have huveq : x = v ∧ y = u := by
        rw [OrderedPair.uniqueness] at huv
        exact huv.right
      rw [←huveq.right, ←huveq.left] at huv
      apply Exists.intro y
      apply And.intro
      { exact huv.left }
      { aesop }
    }
    {
      -- IsSingleRooted F → F⁻¹ is a function
      intro h
      rw [IsSingleRooted] at h
      apply And.intro
      { -- Show: F⁻¹ is a relation
        rw [IsRelation]
        aesop
      }
      {
        intro x hx
        rw [domain_inverse] at hx
        have h := h x hx
        obtain ⟨y, hy, hyuniq⟩ := h
        apply Exists.intro y
        apply And.intro
        { simp [Inverse.Spec]
          aesop
        }
        { intro y' hy'
          rw [Inverse.Spec] at hy'
          obtain ⟨u, v, huv⟩ := hy'
          have huveq : x = v ∧ y' = u := by
            rw [OrderedPair.uniqueness] at huv
            exact huv.right
          aesop
        }
      }
    }
  theorem relation_function_single_rooted (F : Set) {hR : IsRelation F} : IsFunction F ↔ IsSingleRooted (Inverse F) := by
    have h := inverse_single_rooted (Inverse F)
    rw [relation_inverse_inverse] at h
    exact h
    exact hR

  /-
  [Enderton, Theorem 3G, p. 46]
  Assume that F is a one-to-one function. If x ∈ dom F, then F⁻¹(F(x)) = x. If y ∈ ran F, then F(F⁻¹(y)) = y.
  -/
  theorem one_to_one_inverse (F : Set) : IsFunction F ∧ IsSingleRooted F → (∀ x, x ∈ (dom F) → ∃ y, ⟨x, y⟩ ∈ F ∧ ⟨y, x⟩ ∈ F⁻¹) := by
    intro ⟨hF, hSR⟩
    intro x hx
    rw [IsFunction] at hF
    obtain ⟨_, hF⟩ := hF
    have hy := hF x hx
    have ⟨y, hy, hyuniq⟩ := hy
    simp at hy
    have hyi : ⟨y, x⟩ ∈ F⁻¹ := by aesop
    have hydomi : y ∈ dom (F⁻¹) := by aesop
    have hFi : IsFunction (F⁻¹) := by
      rw [inverse_single_rooted]
      exact hSR
    aesop
  theorem one_to_one_inverse' (F : Set) : IsFunction F ∧ IsSingleRooted F → (∀ y, y ∈ (ran F) → ∃ x, ⟨y, x⟩ ∈ F⁻¹ ∧ ⟨x, y⟩ ∈ F) := by
    intro hF
    intro y hy
    have h := one_to_one_inverse (Inverse F)
    aesop

end Set
