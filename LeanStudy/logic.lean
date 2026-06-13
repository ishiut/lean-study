import Mathlib

theorem double_negation (P : Prop) (h : ¬¬P) : P := by
  by_contra
  contradiction

#print axioms double_negation
