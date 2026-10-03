import Mathlib

-- Type has type Type 1, not Type so that we can avoid Russell like paradox.
#check Type
-- Type 1 has Type 2 and so on.
#check Type 1

-- Sort 0 is defined to be Prop.
#check Sort
-- Sort 1 is Type. So, it has type Type 1.
#check Sort 1

-- When α is of Type u, List α is of Type u also.
#check List
-- So List Nat is of Type 0 while List Type is of Type 1.
#check List Nat
#check List Type
-- What is List Type? It is a list whose components are objects of Type 0.
#check [ℕ, ℚ]
