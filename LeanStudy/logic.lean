import Mathlib

theorem double_negation (P : Prop) (h : ¬¬P) : P := by
  by_contra
  contradiction

#print axioms double_negation

open Classical in
noncomputable section
-- variable {α : Type*} [DecidableEq α] (a : α) (s t : Finset α)
variable {α : Type*} (a : α) (s t : Finset α)

#check a ∈ s
#check s ∩ t

end
