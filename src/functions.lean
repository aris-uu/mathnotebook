import Mathlib.Data.Set.Function
import Mathlib.Tactic
open Function

variable (X Y : Type) (f : X → Y)

example : (Injective f) ↔ ∃h : Y → X, h ∘ f = id := by
  constructor <;> rintro h1
  . sorry
  . cases' h1 with h h_inv
    rw [Injective]
    intros x1 x2 fx1_eq_fx2
    apply_fun h at fx1_eq_fx2
    change (h ∘ f) (x1) = (h ∘ f) (x2) at fx1_eq_fx2
    rw [h_inv] at fx1_eq_fx2
    dsimp at fx1_eq_fx2
    exact fx1_eq_fx2