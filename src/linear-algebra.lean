import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

class AddCommGroup' (V : Type u) extends Add V, Zero V, Neg V where
  add_comm' : ∀ (v w : V), v + w = w + v
  add_assoc' : ∀ (u v w : V), (u + v) + w = u + (v + w)
  add_zero' : ∀ v : V, v + 0 = v
  add_right_neg' : ∀ v : V, v + (-v) = 0

class VectorSpace (K : Type u) (V: Type v) [Field K] [AddCommGroup' V] extends SMul K V where
  one_smul' : ∀ v : V, (1 : K) • v = v
  mul_smul' : ∀ α β : K, ∀ v : V, (α * β) • v = α • (β • v)
  smul_add' : ∀ α : K, ∀ u v : V, α • (u + v) = α • u + α • v

  /-- Scalar multiplication distributes over addition from the right. -/
  add_smul' : ∀ (r s : K) (x : V), (r + s) • x = r • x + s • x

open VectorSpace
open AddCommGroup'
attribute [simp] add_zero' add_right_neg' one_smul'

variable [Field K] [AddCommGroup' V] [VectorSpace K V] (v : V)

@[simp]
theorem AddCommGroup'.zero_add' (v : V) : 0 + v = v := by
  rw [add_comm', add_zero']

@[simp]
theorem AddCommGroup'.add_left_neg' (v : V) : -v + v = 0 := by
  rw [add_comm', add_right_neg']

theorem AddCommGroup'.add_eq_zero_iff_neg_eq' (a b : V) : a + b = 0 ↔ -a = b := by
  constructor
  . intro h
    apply_fun (-a + .) at h
    rw [← add_assoc', add_left_neg', zero_add', add_zero'] at h
    exact h.symm
  . rintro rfl
    exact add_right_neg' a

instance (V : Type u) [AddCommGroup' V] : Sub V where
  sub a b := a + (-b)

theorem AddCommGroup'.sub_eq_add_neg' (a b : V) : a - b = a + (-b) := rfl


@[simp]
theorem AddCommGroup'.sub_self (a : V) : a - a = 0 := by
  rw [sub_eq_add_neg', add_right_neg']

@[simp]
theorem VectorSpace.zero_smul' (v : V) : (0 : K) • v = 0 := by
  have h : (1 : K) • v = v := one_smul' v (K := K)
  rw [← add_zero 1, add_smul', one_smul'] at h
  apply_fun (-v + .) at h
  rw [← add_assoc', add_left_neg', zero_add'] at h
  exact h

lemma test : v + (-1 : K) • v = 0 := by 
  nth_rewrite 1 [← one_smul' (K := K) v]
  rw [← add_smul', add_neg_self, zero_smul']

example : -v = (-1 : K) • v := by
  rw [← add_eq_zero_iff_neg_eq']
  exact (test v)

-- zero annihilates 
example :  (0 : K) • v = 0 := by simp

-- zero vector is unique
example (a : V) (h1 : ∀ v : V, v + a = v) : a = 0 := by
  simpa using h1 0

theorem AddCommGroup'.eq_neg_of_add_eq_zero_right' {a v : V} (h : v + a = 0) : a = -v := by
  rw [← add_right_neg' v] at h
  apply_fun (-v + .) at h
  rw [← add_assoc', add_left_neg', add_right_neg', add_zero', zero_add'] at h
  exact h

-- inverse vector is unique
example (a b v : V) (h1 : v + a = 0) (h2 : v + b = 0) : a = b := by
  rw [eq_neg_of_add_eq_zero_right' h1,
      eq_neg_of_add_eq_zero_right' h2]

