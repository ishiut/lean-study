import Mathlib

-- Differences between cases, rcases, and obtain

example (A B C D : Prop) (h : ∃ n : ℕ, A ∧ (∃ m : ℕ, B ∧ C) ∧ D) :
    D ∧ C ∧ B ∧ A := by
  -- Decompose the existential statement.
  cases h
  -- Use n and hn to capture it.
  case intro n hn =>
    -- Decompose the conjunction.
    cases hn
    case intro l r =>
      cases r
      case intro l1 r1 =>
        cases l1
        case intro m hm =>
          cases hm
          case intro l2 r2 =>
            constructor
            case left => exact r1
            case right =>
              constructor
              case left => exact r2
              case right =>
               constructor
               case left => exact l2
               case right => exact l

example (A B C D : Prop) (h : ∃ n : ℕ, A ∧ (∃ m : ℕ, B ∧ C) ∧ D) :
    D ∧ C ∧ B ∧ A := by
  -- rcases apply cases recursively.
  -- If you are not sure how it is decomposed, you can do it one by one.
  -- rcases h with ⟨n, h⟩
  --rcases h with ⟨n, hA, hBC, hD⟩
  rcases h with ⟨n, hA, ⟨m, hB, hC⟩, hD⟩
  /-
    The hypotheses appear.
    n : ℕ
    hA : A
    hD : D
    m : ℕ
    hB : B
    hC : C
  -/
  and_intros
  /-
    D ∧ C ∧ B ∧ A is broken into four subgoals.
  -/
  · exact hD
  · exact hC
  · exact hB
  · exact hA

example (A B C D : Prop) (h : ∃ n : ℕ, A ∧ (∃ m : ℕ, B ∧ C) ∧ D) :
    D ∧ C ∧ B ∧ A := by
  obtain ⟨n, hA, ⟨m, hB, hC⟩, hD⟩ := h
  and_intros
  · exact hD
  · exact hC
  · exact hB
  · exact hA

-- You can use rcases and obtain to decompose a disjunctive assumption.
example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  -- This does not work.
  -- rcases h with ⟨h1, h2⟩

  -- This works, but only by one step.
  -- rcases h with hA | hBC

  -- This will completely decompose h.
  rcases h with hA | ⟨hB, hC⟩
  case inl =>
    constructor
    case left =>
      left
      exact hA
    case right =>
      left
      exact hA
  case inr =>
    constructor
    case left =>
      right
      exact hB
    case right =>
      right
      exact hC

example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  obtain hA | ⟨hB, hC⟩ := h
  · constructor
    · left
      exact hA
    · left
      exact hA
  · constructor
    · right
      exact hB
    · right
      exact hC
