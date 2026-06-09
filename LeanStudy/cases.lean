import Mathlib

example (A B C D : Prop) (h : ∃ n : ℕ, A ∧ (∃ m : ℕ, B ∧ C) ∧ D) :
    D ∧ C ∧ B ∧ A := by
  cases h
  case intro n hn =>
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
  rcases h with ⟨n, hA, ⟨⟨m, hB, hC⟩, hD⟩⟩
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
