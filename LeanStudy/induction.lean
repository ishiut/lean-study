import Mathlib

def sum (n : ℕ) :=
match n with
| 0 => 0
| k + 1 => sum k + (k + 1)

example (n : ℕ) : 2 * sum n = n * (n + 1) := by
  induction' n with k ih
  · unfold sum
    omega
  · unfold sum
    calc
      2 * (sum k + (k + 1)) = 2 * (sum k) + 2 * (k + 1)
        := by omega
      _ = k * (k + 1) + 2 * (k + 1)
        := by rw [ih]
      _ = (k + 1) * (k + 1 + 1)
        := by ring

example (n : ℕ) : 2 * sum n = n * (n + 1) := by
  induction n
  case zero =>
    unfold sum
    omega
  case succ k ih => 
    unfold sum
    calc
      2 * (sum k + (k + 1)) = 2 * (sum k) + 2 * (k + 1)
        := by omega
      _ = k * (k + 1) + 2 * (k + 1)
        := by rw [ih]
      _ = (k + 1) * (k + 1 + 1)
        := by ring
