import Set.Basic

namespace Set

  -- Ordered Pair [Enderton, p. 36]
  @[simp]
  noncomputable def OrderedPair (x y : Set) : Set := Pair (Singleton x) (Pair x y)

  lemma hps : ∀ (a b c : Set), Singleton c = Pair a b → a = c ∧ b = c := by
      intro a b c h
      have _ : a ∈ Pair a b := by simp [Pair.Spec]
      have ha : a ∈ Singleton c := by simp_all only
      have ha : a = c := by rw [Singleton.Spec] at ha; exact ha
      have _ : b ∈ Pair a b := by simp [Pair.Spec]
      have hb : b ∈ Singleton c := by simp_all only
      have hb : b = c := by rw [Singleton.Spec] at hb; exact hb
      exact And.intro ha hb

  -- [Enderton, Theorem 3A, p. 36]
  -- The ordered pair ⟨x, y⟩ uniquely determineds both what x and y are, and the order upon them.
  theorem OrderedPair.uniqueness (u v x y : Set) :
    OrderedPair u v = OrderedPair x y ↔ u = x ∧ v = y := by
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
              have hxub : u = x ∧ v = x := by apply hps u v x hc
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
                  have huxy : x = u ∧ y = u := hps x y u he
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
          have huxy : x = u ∧ y = u := hps x y u hb
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

end Set
