import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

def limit (c l : ℝ) (f : ℝ → ℝ) := ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, (0 < |x - c| ∧ |x - c| < δ) → |f x - l| < ε

def f (x : ℝ) := x

-- limit x -> a (x) = a
theorem test (a : ℝ) : limit a a (λ x => x) := by
  intros ε ε_pos
  use ε
  apply And.intro
  exact ε_pos
  intro x
  intro h
  rcases h with ⟨h1, h2⟩
  simp
  exact h2

lemma lemma_1 {x x0 y y0 ε : ℝ}
              (h1 : |x - x0| < ε/2)
              (h2 : |y - y0| < ε/2) :
              |(x + y) - (x0 + y0)| < ε := by
  sorry

theorem lim_add {a l m : ℝ}
                {f g : ℝ → ℝ}
                (lim1 : limit a l f)
                (lim2 : limit a m g) :
                limit a (l + m) (f + g) := by
  rw [limit] at lim1 lim2
  intro ε ε_pos
  have ε2_pos : ε/2 > 0 := by linarith
  have lim1 := lim1 (ε/2) ε2_pos
  have lim2 := lim2 (ε/2) ε2_pos
  rcases lim1 with ⟨δ₁, δ₁_pos, lim1⟩
  rcases lim2 with ⟨δ₂, δ₂_pos, lim2⟩
  use min δ₁ δ₂
  apply And.intro
  simp
  exact ⟨δ₁_pos, δ₂_pos⟩
  intro x h
  rcases h with ⟨h1, h2⟩
  have h3 := lt_of_lt_of_le h2 (min_le_left δ₁ δ₂)
  have h4 := lt_of_lt_of_le h2 (min_le_right δ₁ δ₂)
  have lim1 := lim1 x ⟨h1, h3⟩
  have lim2 := lim2 x ⟨h1, h4⟩
  exact lemma_1 lim1 lim2

lemma lemma_2 {x x0 y y0 ε : ℝ}
              (h1 : |x - x0| < min 1 (ε / (2 * (|y0| + 1))))
              (h2 : |y - y0| < (ε / (2 * (|x0| + 1)))) :
              |x * y - x0 * y0| < ε := by
  sorry

theorem lim_mul {a l m : ℝ}
                {f g : ℝ → ℝ}
                (lim1 : limit a l f)
                (lim2 : limit a m g) :
                limit a (l * m) (f * g) := by
  rw [limit] at lim1 lim2
  intro ε ε_pos
  let ε₁ := min 1 (ε / (2 * (|m| + 1)))
  let ε₂ := (ε / (2 * (|l| + 1)))
  have ε1_pos : ε₁ > 0 := by 
    simp
    apply div_pos
    exact ε_pos
    apply mul_pos
    linarith
    -- 0 <= |m| < |m| + 1
    apply lt_of_le_of_lt
    exact abs_nonneg m
    linarith

  have ε2_pos : ε₂ > 0 := by
    simp
    apply div_pos
    exact ε_pos
    apply mul_pos
    linarith
    apply lt_of_le_of_lt
    exact abs_nonneg l
    linarith

  have lim1 := lim1 ε₁ ε1_pos
  have lim2 := lim2 ε₂ ε2_pos
  rcases lim1 with ⟨δ₁, δ₁_pos, lim1⟩
  rcases lim2 with ⟨δ₂, δ₂_pos, lim2⟩
  use min δ₁ δ₂
  apply And.intro
  simp
  exact ⟨δ₁_pos, δ₂_pos⟩
  intro x h
  rcases h with ⟨h1, h2⟩
  have h3 := lt_of_lt_of_le h2 (min_le_left δ₁ δ₂)
  have h4 := lt_of_lt_of_le h2 (min_le_right δ₁ δ₂)
  have lim1 := lim1 x ⟨h1, h3⟩
  have lim2 := lim2 x ⟨h1, h4⟩
  exact lemma_2 lim1 lim2

lemma lemma_3 {y y0 ε : ℝ}
              (h : |y - y0| <  min (|y0|/2) ((ε * |y0|^2)/2)) :
              |1/y - 1/y0| < ε := by sorry

theorem lim_inv {a m : ℝ} {h : m > 0}
                {g : ℝ → ℝ}
                (lim : limit a m g) :
                limit a (1 / m) (1 / g) := by
  rw [limit] at lim
  intro ε ε_pos
  let ε₁ := min (|m|/2) ((ε * |m|^2)/2)
  have ε1_pos : ε₁ > 0 := by
    simp
    apply And.intro
    apply div_pos
    apply abs_pos.mpr
    linarith
    linarith
    apply mul_pos
    apply mul_pos
    exact ε_pos
    apply sq_pos_of_pos h
    norm_num

  have lim := lim ε₁ ε1_pos
  rcases lim with ⟨δ, δ_pos, lim⟩
  use δ
  apply And.intro
  exact δ_pos
  intro x h
  have lim := lim x h
  apply lemma_3 lim

-- noncomputable section test

theorem no_7 : ¬ (∀ ε : ℝ, ε > 0 →
                  ∀ δ : ℝ, δ > 0 →
                  ∀ x : ℝ,
                  (((0 < |x| ∧ |x| < δ) → |Real.sqrt (abs x)| < ε) → 
                  (0 < |x| ∧ |x| < δ/2) → |Real.sqrt (abs x)| < ε/2)) := by
  push_neg
  let ε : ℝ := 1/2
  use ε
  apply And.intro
  simp
  use ε^2
  apply And.intro
  simp
  use ε^2/4
  apply And.intro
  sorry
  apply And.intro
  sorry
  norm_num
  sorry




