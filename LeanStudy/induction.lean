import Mathlib

def sum (n : ℕ) :=
match n with
| 0 => 0
| k + 1 => sum k + (k + 1)

-- "Mathematics in Lean" tells you to use induction', but it is discouraged now.
example (n : ℕ) : 2 * sum n = n * (n + 1) := by
  induction' n with k ih
  case zero =>
    unfold sum
    omega
  case succ =>
    unfold sum
    calc
      2 * (sum k + (k + 1)) = 2 * (sum k) + 2 * (k + 1)
        := by omega
      _ = k * (k + 1) + 2 * (k + 1)
        := by rw [ih]
      _ = (k + 1) * (k + 1 + 1)
        := by ring

-- Instead, we should use induction.
-- I think it is better as the variables for the inductive hypothesis can be determined on site.
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
