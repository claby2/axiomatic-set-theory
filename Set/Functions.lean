import Set.Relations

namespace Set
  -- Function [Enderton, p.42]
  def IsFunction (F A B : Set) (prop : Set → Set → Prop) : Prop :=
    F = Relation A B prop ∧ ∀ x, x ∈ (dom F) → ∃! y, ⟨x, y⟩ ∈ F

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

  protected lemma function_dom {F A B : Set} {prop : Set → Set → Prop} (hF : F.IsFunction A B prop) :
    ∀ x, x ∈ (dom F) → x ∈ A := by
    intro x hx
    rw [IsFunction] at hF
    obtain ⟨hF, _⟩ := hF
    rw [Relation.Domain.Spec] at hx
    obtain ⟨x', hx'⟩ := hx
    rw [hF, Relation.Spec] at hx'
    obtain ⟨hx', _⟩ := hx'
    rw [Product.Spec] at hx'
    obtain ⟨_, hx'⟩ := hx'
    obtain ⟨u, v, hu, hv, heq⟩ := hx'
    rw [OrderedPair.uniqueness] at heq
    rw [←heq.left] at hu
    exact hu

  protected lemma function_ran {F A B : Set} {prop : Set → Set → Prop} (hF : F.IsFunction A B prop) :
    ∀ x, x ∈ (ran F) → x ∈ B := by
    intro x hx
    rw [IsFunction] at hF
    obtain ⟨hF, _⟩ := hF
    rw [Relation.Range.Spec] at hx
    obtain ⟨x', hx'⟩ := hx
    rw [hF, Relation.Spec] at hx'
    obtain ⟨hx', _⟩ := hx'
    rw [Product.Spec] at hx'
    obtain ⟨_, hx'⟩ := hx'
    obtain ⟨u, v, hu, hv, heq⟩ := hx'
    rw [OrderedPair.uniqueness] at heq
    rw [←heq.right] at hv
    exact hv

  protected lemma function_functional
    {F A B : Set} {prop : Set → Set → Prop} {hF : F.IsFunction A B prop} {x y y' : Set}
    (hxy : ⟨x, y⟩ ∈ F) (hxy' : ⟨x, y'⟩ ∈ F) : y = y' := by
    rw [IsFunction] at hF
    obtain ⟨hF₁, hF₂⟩ := hF
    have hx : x ∈ (dom F) := by
      rw [Relation.Domain.Spec]
      apply Exists.intro y
      exact hxy
    have huniq : ∃! y, ⟨x, y⟩ ∈ F := hF₂ x hx
    obtain ⟨u, hu, huniq⟩ := huniq
    have hy : y = u := by
      apply huniq
      exact hxy
    have hy' : y' = u := by
      apply huniq
      exact hxy'
    subst hy
    subst hy'
    trivial

  /-
  [Enderton, Theorem 3H, p. 47]
  Assume that F and G are functions. Then F ∘ G is a function, its domain is
    {x ∈ dom G | G(x) ∈ dom F},
  and for each x in its domain, (F ∘ G)(x) = F(G(x)).
  -/
  theorem function_composition_creates_function {F G A B C : Set} {prop₁ prop₂ : Set → Set → Prop}
    {hF : F.IsFunction B C prop₁} {hG : G.IsFunction A B prop₂} :
    (F ∘ G).IsFunction A C (λ u v ↦ ∃ t, t ∈ B ∧ prop₂ u t ∧ prop₁ t v) := by
    rw [IsFunction]
    apply And.intro
    { apply extensionality
      intro xy
      apply Iff.intro
      { intro h
        rw [Composition.Spec] at h
        rw [Relation.Spec]
        obtain ⟨h₁, u, v, t, hu, ht, hv⟩ := h
        apply And.intro
        { -- We can show that (dom G) ⨯ (ran F) ⊆ A ⨯ C
          have hsub : ((dom G) ⨯ (ran F)) ⊆ A ⨯ C := by
            rw [SubsetOf]
            intro t ht
            rw [Product.Spec] at ht
            obtain ⟨_, ht⟩ := ht
            obtain ⟨x', y', hx', hy', heq⟩ := ht
            rw [heq, Product.Spec]
            apply And.intro
            { apply OrderedPair.in_power_power
              rw [Union.Spec]
              apply Or.intro_left
              exact Set.function_dom hG x' hx'
              rw [Union.Spec]
              apply Or.intro_right
              exact Set.function_ran hF y' hy'
            }
            { apply Exists.intro x'
              apply Exists.intro y'
              apply And.intro
              { exact Set.function_dom hG x' hx' }
              apply And.intro
              { apply Set.function_ran hF y' hy' }
              { trivial }
            }
          rw [SubsetOf] at hsub
          apply hsub
          exact h₁
        }
        { rw [Set.relation_condition]
          apply Exists.intro u
          apply Exists.intro v
          have h₁ : u ∈ A := by
            rw [IsFunction] at hG
            obtain ⟨hG, _⟩ := hG
            rw [hG, Relation.Spec] at hu
            obtain ⟨_, hu⟩ := hu
            rw [Set.relation_condition] at hu
            obtain ⟨u', _, hu', _, _, hut⟩ := hu
            rw [OrderedPair.uniqueness] at hut
            rw [←hut.left] at hu'
            exact hu'
          have h₂ : v ∈ C := by
            rw [IsFunction] at hF
            obtain ⟨hF, _⟩ := hF
            rw [hF, Relation.Spec] at ht
            obtain ⟨_, ht⟩ := ht
            rw [Set.relation_condition] at ht
            obtain ⟨_, v', _, hv', _, htv⟩ := ht
            rw [OrderedPair.uniqueness] at htv
            rw [←htv.right] at hv'
            exact hv'
          have h₃ : ∃ t, t ∈ B ∧ prop₂ u t ∧ prop₁ t v := by
            apply Exists.intro t
            apply And.intro
            { rw [IsFunction] at hG
              obtain ⟨hG, _⟩ := hG
              rw [hG, Relation.Spec] at hu
              obtain ⟨hu, _⟩ := hu
              rw [Product.Spec] at hu
              obtain ⟨_, hu⟩ := hu
              obtain ⟨u', t', hu', ht', heq⟩ := hu
              rw [OrderedPair.uniqueness] at heq
              rw [←heq.right] at ht'
              exact ht'
            }
            apply And.intro
            { rw [IsFunction] at hG
              obtain ⟨hG, _⟩ := hG
              rw [hG, Relation.Spec] at hu
              obtain ⟨_, hu⟩ := hu
              rw [Set.relation_condition] at hu
              obtain ⟨u', v', hu', hv', hprop, heq⟩ := hu
              rw [OrderedPair.uniqueness] at heq
              rw [←heq.left, ←heq.right] at hprop
              exact hprop
            }
            { rw [IsFunction] at hF
              obtain ⟨hF, _⟩ := hF
              rw [hF, Relation.Spec] at ht
              obtain ⟨_, ht⟩ := ht
              rw [Set.relation_condition] at ht
              obtain ⟨t', v', ht', hv', hprop, heq⟩ := ht
              rw [OrderedPair.uniqueness] at heq
              rw [←heq.left, ←heq.right] at hprop
              exact hprop
            }
          apply And.intro h₁
          apply And.intro h₂
          apply And.intro h₃
          exact hv
        }
      }
      { intro h
        rw [Composition.Spec]
        apply And.intro
        { rw [Product.Spec]
          rw [Relation.Spec] at h
          obtain ⟨h₁, h₂⟩ := h
          apply And.intro
          rw [Product.Spec] at h₁
          obtain ⟨h₁, ⟨x, y, hx, hy, hxy⟩⟩ := h₁
          { subst hxy
            simp [Power.Spec, SubsetOf] at h₁
            apply OrderedPair.in_power_power
            { rw [Union.Spec]
              apply Or.intro_left
              rw [Relation.Domain.Spec]
              rw [Set.relation_condition] at h₂
              rw [IsFunction] at hG
              obtain ⟨hG, _⟩ := hG
              obtain ⟨x', y', _, _, ⟨t, ht⟩, heq⟩ := h₂
              rw [OrderedPair.uniqueness] at heq
              rw [←heq.left, ←heq.right] at ht
              apply Exists.intro t
              rw [hG, Relation.Spec]
              apply And.intro
              { rw [Product.Spec]
                apply And.intro
                { apply OrderedPair.in_power_power
                  rw [Union.Spec]
                  apply Or.intro_left
                  exact hx
                  rw [Union.Spec]
                  apply Or.intro_right
                  exact ht.left
                }
                { apply Exists.intro x
                  apply Exists.intro t
                  apply And.intro
                  exact hx
                  apply And.intro
                  exact ht.left
                  trivial
                }
              }
              { sorry }
            }
            { sorry }
          }
          { sorry }
        }
        { rw [Relation.Spec] at h
          obtain ⟨_, h⟩ := h
          rw [Set.relation_condition] at h
          obtain ⟨x, y, hx, hy, ht, hxyeq⟩ := h
          obtain ⟨t, ⟨ht, ht₂, ht₁⟩⟩ := ht
          apply Exists.intro x
          apply Exists.intro y
          apply Exists.intro t
          apply And.intro
          { rw [IsFunction] at hG
            rw [hG.left, Relation.Spec]
            apply And.intro
            { aesop }
            { rw [Set.relation_condition]
              apply Exists.intro x
              apply Exists.intro t
              apply And.intro
              exact hx
              apply And.intro
              exact ht
              apply And.intro
              exact ht₂
              trivial
            }
          }
          apply And.intro
          { rw [IsFunction] at hF
            obtain ⟨hF, _⟩ := hF
            rw [hF, Relation.Spec]
            apply And.intro
            { rw [Product.Spec]
              apply And.intro
              { apply OrderedPair.in_power_power
                rw [Union.Spec]
                apply Or.intro_left
                exact ht
                rw [Union.Spec]
                apply Or.intro_right
                exact hy
              }
              { apply Exists.intro t
                apply Exists.intro y
                apply And.intro
                exact ht
                apply And.intro
                exact hy
                trivial
              }
            }
            { rw [Set.relation_condition]
              apply Exists.intro t
              apply Exists.intro y
              apply And.intro
              exact ht
              apply And.intro
              exact hy
              apply And.intro
              exact ht₁
              trivial
            }
          }
          { trivial }
        }
      }
    }
    { intro x hx
      rw [Relation.Domain.Spec] at hx
      obtain ⟨y, hy⟩ := hx
      apply Exists.intro y
      apply And.intro
      { aesop }
      { intro y' hy'
        -- There is a unique t such that xGt
        -- There is a unique t' such that tFt'
        rw [Composition.Spec] at hy
        obtain ⟨hxy, ⟨u', v', t, hxt, hty, heq⟩⟩ := hy
        rw [OrderedPair.uniqueness] at heq
        rw [←heq.left] at hxt
        rw [←heq.right] at hty

        rw [Composition.Spec] at hy'
        obtain ⟨hxy', ⟨u', v', t', hxt', hty', heq⟩⟩ := hy'
        rw [OrderedPair.uniqueness] at heq
        rw [←heq.left] at hxt'
        rw [←heq.right] at hty'

        have hteq : t = t' := by
          apply Set.function_functional
          apply hG
          apply hxt
          exact hxt'
        subst hteq
        apply Set.function_functional
        apply hF
        apply hty'
        exact hty
      }
    }

end Set
