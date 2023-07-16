import Mathlib.Data.Real.Basic

open Classical

def HasLim (c l : ℝ) (f : ℝ → ℝ) := ∀ ε : ℝ, ε > 0 →
                                    ∃ δ : ℝ, δ > 0 ∧
                                    ∀ x : ℝ,
                                    (0 < |x - c| ∧ |x - c| < δ) → |f x - l| < ε

def LimExists (c : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ l, HasLim c l f

theorem lim_not_lt {c l m : ℝ}
                   {f : ℝ → ℝ}
                   (lim1 : HasLim c l f)
                   (lim2 : HasLim c m f) :
                   ¬ l < m := by
  intro h
  set ε := m - l with hε
  have hε : 0 < ε := sub_pos.mpr h
  obtain ⟨δ1, h1⟩ := lim1 (ε/2) (by linarith)
  obtain ⟨δ2, h2⟩ := lim2 (ε/2) (by linarith)
  cases' h1 with δ1_pos h1
  cases' h2 with δ2_pos h2
  have h3 : 0 < min δ1 δ2 := by exact lt_min δ1_pos δ2_pos
  specialize h1 ((min δ1 δ2)/2 + c) ⟨_, _⟩
  . norm_num
    rw [min_eq_iff]
    push_neg
    constructor
    . rintro rfl
      linarith
    . rintro rfl
      linarith
  . norm_num
    rw [abs_of_pos]
    have : (min δ1 δ2) / 2 < min δ1 δ2 := by linarith
    apply lt_of_lt_of_le this
    apply min_le_left
    linarith
  specialize h2 ((min δ1 δ2)/2 + c) ⟨_, _⟩
  . norm_num
    rw [min_eq_iff]
    push_neg
    constructor <;> rintro rfl <;> linarith
  . norm_num
    rw [abs_of_pos]
    have : (min δ1 δ2) / 2 < min δ1 δ2 := by linarith
    apply lt_of_lt_of_le this
    apply min_le_right
    linarith
  rw [abs_lt] at h1 h2
  linarith 

theorem lim_unique {c l m : ℝ}
                   {f : ℝ → ℝ}
                   (lim1 : HasLim c l f)
                   (lim2 : HasLim c m f) :
                   l = m := by
  by_contra h
  have h2 := Ne.lt_or_lt h
  cases' h2 with h2 h2
  . exact lim_not_lt lim1 lim2 h2
  . exact lim_not_lt lim2 lim1 h2


noncomputable def lim' (c : ℝ) (f : ℝ → ℝ) :=
  if h : LimExists c f then Classical.choose h else 0

theorem lim'_spec (c : ℝ)
                  (f : ℝ → ℝ)
                  (h : LimExists c f) :
                  HasLim c (lim' c f) f := by
  rw [lim', dif_pos h]
  exact Classical.choose_spec h

theorem test (a : ℝ) : HasLim a a (λ x => x) := by
  intros ε ε_pos
  use ε
  apply And.intro
  exact ε_pos
  intro x
  intro h
  rcases h with ⟨_, h2⟩
  simp
  exact h2

example (a : ℝ) : lim' a (λ x => x) = a := by
  apply lim_unique _ (test a)
  apply lim'_spec
  use a
  exact test a
