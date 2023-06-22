import Mathlib.Algebra.Module.Basic

variable [Field R] [AddCommGroup M] [Module R M] (v : M)

lemma test : v + (-1 : R) • v = 0 := by
  nth_rewrite 1 [← (one_smul R) v]
  rw [← add_smul, add_neg_self, zero_smul]

example : -v = (-1 : R) • v := by
  apply add_eq_zero_iff_neg_eq.mp
  exact (test v)

-- zero annihilates 
example :  (0 : R) • v = 0 := by simp

-- zero vector is unique
example (a b : M) (h1 : v + (-v) = a) (h2 : v + (-v) = b) : a = b := by
  rw [add_right_neg] at h1
  rw [add_right_neg] at h2
  rw [← h1, ← h2]

-- inverse vector is unique
example (a b : M) (h1 : v + a = 0) (h2 : v + b = 0) : a = b := by
  apply neg_unique h1 h2

