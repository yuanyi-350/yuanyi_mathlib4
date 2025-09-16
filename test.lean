import Mathlib

#check 1

variable (a b : ℝ)

open Pointwise

#check Set.mem_add

example {α : Type*} [Add α] {s t : Set α} {a : α} : a ∈ s + t ↔ ∃ x ∈ s, ∃ y ∈ t, x + y = a := by
  sorry
