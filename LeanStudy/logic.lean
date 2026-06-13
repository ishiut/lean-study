import Mathlib

theorem double_negation (P : Prop) (h : ¬¬P) : P := by
  by_contra
  contradiction

-- The response contains Classical.choice
#print axioms double_negation

theorem safe_one (P : Prop) (h : P) : ¬¬P := by
  intro h1
  contradiction

-- The response contains nothing.
#print axioms safe_one

variable {α : Type*} (a : α) (s t : Finset α)

#check a ∈ s
-- Lean complains this.
-- #check s ∩ t

-- Set Type is not meant to be constructive.
variable {α : Type*} (a : α) (ss st : Set α)

#check a ∈ ss
-- Now, Lean does not complain this.
#check ss ∩ st


-- This lets you go classical.
open Classical in
noncomputable section

variable {α : Type*} (a : α) (s t : Finset α)

#check a ∈ s
#check s ∩ t

end

-- Once the section ends, Lean starts complaining the following.
-- #check s ∩ t
