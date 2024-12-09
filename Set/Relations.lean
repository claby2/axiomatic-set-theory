import Set.Basic

namespace Set

  /-
  Ordered Pair [Enderton, p. 36]
  ⟨x, y⟩ = {{x}, {x, y}}
  -/
  noncomputable def OrderedPair (x y : Set) : Set := Pair (Singleton x) (Pair x y)
  @[simp]
  lemma OrderedPair.Spec (x y : Set) : ∀ w, w ∈ OrderedPair x y ↔ w = Singleton x ∨ w = Pair x y := by
    intro w
    simp [OrderedPair, Pair.Spec, Singleton.Spec]
  notation:90 "⟨" x ", " y "⟩" => OrderedPair x y

  protected lemma singleton_pair_eq : ∀ (a b c : Set), Singleton c = Pair a b → a = c ∧ b = c := by
      intro a b c h
      have _ : a ∈ Pair a b := by simp [Pair.Spec]
      have ha : a ∈ Singleton c := by simp_all only
      have ha : a = c := by rw [Singleton.Spec] at ha; exact ha
      have _ : b ∈ Pair a b := by simp [Pair.Spec]
      have hb : b ∈ Singleton c := by simp_all only
      have hb : b = c := by rw [Singleton.Spec] at hb; exact hb
      exact And.intro ha hb

  /-
  [Enderton, Theorem 3A, p. 36]
  The ordered pair ⟨x, y⟩ uniquely determines both what x and y are, and the order upon them.
  -/
  theorem OrderedPair.uniqueness (u v x y : Set) :
    ⟨u, v⟩ = ⟨x, y⟩ ↔ u = x ∧ v = y := by
    -- Helper: {c} = {a, b} → a = c ∧ b = c
    apply Iff.intro
    { intro h
      have _ : Singleton u ∈ OrderedPair u v := by simp [OrderedPair, Pair.Spec]
      have h₁ : Singleton u ∈ OrderedPair x y := by simp_all only
      have _ : Pair u v ∈ OrderedPair u v := by simp [OrderedPair, Pair.Spec, h]
      have h₂ : Pair u v ∈ OrderedPair x y := by simp_all only
      rw [OrderedPair] at h₁ h₂
      have h₁ : Singleton u = Singleton x ∨ Singleton u = Pair x y := by
        rw [Pair.Spec] at h₁
        exact h₁
      have h₂ : Pair u v = Singleton x ∨ Pair u v = Pair x y := by
        rw [Pair.Spec] at h₂
        exact h₂
      cases h₁ with
        | inl ha =>
          cases h₂ with
            | inl hc =>
              have hc : Singleton x = Pair u v := by aesop
              have hxub : u = x ∧ v = x := by apply Set.singleton_pair_eq u v x hc
              have huv : u = v := by aesop
              have _ : Pair x y ∈ OrderedPair x y := by simp [OrderedPair, Pair.Spec]
              have h₃ : Pair x y ∈ OrderedPair u v := by simp_all only
              rw [OrderedPair] at h₃
              have h₃ : Pair x y = Singleton u ∨ Pair x y = Pair u v := by
                rw [Pair.Spec] at h₃
                exact h₃
              cases h₃ with
                | inl he =>
                  have he : Singleton u = Pair x y := by aesop
                  have huxy : x = u ∧ y = u := Set.singleton_pair_eq x y u he
                  obtain ⟨_, huxy⟩ := huxy
                  subst huv huxy
                  apply And.intro hxub.left
                  trivial
                | inr hf =>
                  have hyuv : y = u ∨ y = v := by
                    have hy : y ∈ Pair x y := by simp [OrderedPair, Pair.Spec]
                    have hy : y ∈ Pair u v := by rw [hf] at hy; exact hy
                    aesop
                  aesop
            | inr hd =>
              have hux : u = x := by
                have _ : u ∈ Singleton u := by simp
                have hu : u ∈ Singleton x := by aesop
                aesop
              have hyuv : y = u ∨ y = v := by
                have hy : y ∈ Pair x y := by simp [OrderedPair, Pair.Spec]
                have hy : y ∈ Pair u v := by rw [←hd] at hy; exact hy
                rw [Pair.Spec] at hy
                exact hy
              apply And.intro hux
              cases hyuv with
                | inl hyuv =>
                  -- want u = v
                  have hvxy : v = x ∨ v = y := by
                    have hv : v ∈ Pair u v := by simp [OrderedPair, Pair.Spec]
                    have hv : v ∈ Pair x y := by rw [hd] at hv; exact hv
                    rw [Pair.Spec] at hv
                    exact hv
                  cases hvxy with
                    | inl h => aesop
                    | inr h => exact h
                | inr hyuv => rw [←hyuv]
        | inr hb =>
          have huxy : x = u ∧ y = u := Set.singleton_pair_eq x y u hb
          cases h₂ with
            | inl _ =>
              have huv : u = v := by
                have _ : v ∈ Pair u v := by simp [Pair.Spec]
                have hv : v ∈ Singleton x := by simp_all only
                have hv : v = x := by rw [Singleton.Spec] at hv; exact hv
                aesop
              rw [←huv]
              obtain ⟨hxu, hyu⟩ := huxy
              subst hxu hyu
              trivial
            | inr hd =>
              have hvxy : v = x ∨ v = y := by
                have hv : v ∈ Pair u v := by simp [OrderedPair, Pair.Spec]
                have hv : v ∈ Pair x y := by rw [hd] at hv; exact hv
                rw [Pair.Spec] at hv
                exact hv
              obtain ⟨huxy₁, huxy₂⟩ := huxy
              aesop
    }
    -- "One direction is trivial"... the following is that direction
    { intro h
      aesop
    }

  /-
  [Enderton, Lemma 3B, p.37]
  If x ∈ C and y ∈ C, then ⟨x, y⟩ ∈ 𝒫𝒫C.
  -/
  lemma OrderedPair.in_power_power (x y C : Set) :
    x ∈ C → y ∈ C → OrderedPair x y ∈ Power (Power C) := by
    intro hx hy
    simp [OrderedPair]
    exact And.intro hx hy


  /-
  [Enderton, Corollary 3B, p.38]
  For any sets A and B, there is a set whose members are exactly the pairs ⟨x, y⟩, with x ∈ A and y ∈ B.
  -/
  lemma OrderedPair.product (A B : Set) :
    ∃ (C : Set), ∀ (w : Set), w ∈ C ↔ w ∈ 𝒫 𝒫 (A ∪ B) ∧ ∃ (x y : Set), x ∈ A ∧ y ∈ B ∧ w = ⟨x, y⟩ := by
      have h := (comprehension (λ w ↦ ∃ (x y : Set), x ∈ A ∧ y ∈ B ∧ w = ⟨x, y⟩) (𝒫 𝒫 (A ∪ B)))
      aesop
  noncomputable def Product (A B : Set) : Set := Classical.choose (OrderedPair.product A B)
  @[simp]
  lemma Product.Spec (A B : Set) : ∀ (w : Set), w ∈ Product A B ↔ w ∈ 𝒫 𝒫 (A ∪ B) ∧ ∃ (x y : Set), x ∈ A ∧ y ∈ B ∧ w = ⟨x, y⟩ := by
    have h := Classical.choose_spec (OrderedPair.product A B)
    rw [Product]
    exact h
  infix:60 " ⨯ " => Product

  /-
  [Enderton, Lemma 3D, p. 41]
  If ⟨x, y⟩ ∈ A, then x and y belong to ⋃⋃A.
  -/
  lemma OrderedPair.in_union_union (x y A : Set) :
    ⟨x, y⟩ ∈ A → x ∈ ⋃⋃A ∧ y ∈ ⋃⋃A := by
      simp [OrderedPair]
      aesop

  -- Relation [Enderton, p. 40]
  def IsRelation (R : Set) : Prop :=
    ∀ w, w ∈ R → ∃ x y, w = ⟨x, y⟩

  /-
  [Enderton, p. 40]
  Defining the domain, range, and field of a relation.
  Here, we use the observation mentioned in p. 41:
    - Using Lemma 3D, "we can use subset axioms to construct the domain and range of R"
  -/
  -- Relation domain
  noncomputable def Relation.Domain (R : Set) : Set :=
    Classical.choose (comprehension (λ x ↦ ∃ (y : Set), ⟨x, y⟩ ∈ R) (⋃⋃R))
  @[simp]
  lemma Relation.Domain.Spec (R : Set) : ∀ x, x ∈ Relation.Domain R ↔ ∃ y, ⟨x, y⟩ ∈ R := by
    have h := Classical.choose_spec (comprehension (λ x ↦ ∃ (y : Set), ⟨x, y⟩ ∈ R) (⋃⋃R))
    rw [Relation.Domain]
    simp [OrderedPair]
    aesop
  notation:90 "dom " R => Relation.Domain R
  -- Relation range
  noncomputable def Relation.Range (R : Set) : Set :=
    Classical.choose (comprehension (λ y ↦ ∃ (x : Set), ⟨x, y⟩ ∈ R) (⋃⋃R))
  @[simp]
  lemma Relation.Range.Spec (R : Set) : ∀ y, y ∈ Relation.Range R ↔ ∃ x, ⟨x, y⟩ ∈ R := by
    have h := Classical.choose_spec (comprehension (λ y ↦ ∃ (x : Set), ⟨x, y⟩ ∈ R) (⋃⋃R))
    rw [Relation.Range]
    simp [OrderedPair]
    aesop
  notation:90 "ran " R => Relation.Range R
  -- Relation field
  noncomputable def Relation.Field (R : Set) : Set := (dom R) ∪ (ran R)
  @[simp]
  lemma Relation.Field.Spec (R : Set) : ∀ z, z ∈ Relation.Field R ↔ z ∈ (dom R) ∨ z ∈ (ran R) := by
    intro z
    apply Iff.intro
    { intro hz
      rw [Relation.Field, Union.Spec] at hz
      exact hz
    }
    { intro hz
      rw [Relation.Field, Union.Spec]
      exact hz
    }
  notation:90 "fld " R => Relation.Field R
end Set
