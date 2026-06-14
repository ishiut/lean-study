import Mathlib

def allListsOfLength (s : Finset ℕ) (k : ℕ) : Finset (List ℕ) :=
  match k with
  | 0 => {[]}
  | k + 1 =>
      Finset.biUnion s
        (fun a => Finset.image (fun t => a :: t) (allListsOfLength s k))

-- The definition of allListsOfLength has changed from perm_finset.lean
theorem allListsOfLength_int (s : Finset ℕ) (k : ℕ) (l : List ℕ) :
    l ∈ allListsOfLength s k ↔ l.length = k ∧ ∀ a ∈ l, a ∈ s := by
  revert l
  induction k
  case zero =>
    intro l
    unfold allListsOfLength
    simp only [Finset.mem_singleton, List.length_eq_zero_iff, iff_self_and]
    intro hl a ha
    rw [hl] at ha
    contradiction
  case succ k ih =>
    intro l
    unfold allListsOfLength
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    case mp =>
      intro h
      obtain ⟨a, ha, as, has1, has2⟩ := h
      -- rw wroks well for the iff statement
      rw [ih] at has1
      constructor
      case left =>
        rw [← has2]
        simp only [List.length_cons, has1.left]
      case right =>
        intro b hb
        rw [← has2] at hb
        simp only [List.mem_cons] at hb
        obtain hb_l | hb_r := hb
        case inl =>
          rw [hb_l]
          exact ha
        case inr =>
          apply has1.right b hb_r
    case mpr =>
      intro h
      cases l
      case nil =>
        simp only [List.length_nil, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true] at h
      case cons a as =>
        use a
        simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp] at h
        constructor
        case left =>
          apply h.right.left
        case right =>
          use as
          constructor
          case left =>
            rw [ih]
            -- when both are exact
            exact ⟨h.left, h.right.right⟩
          case right => rfl

#check allListsOfLength
#eval allListsOfLength {0, 1, 2, 3} 2
#eval allListsOfLength (Finset.range 4) 3

def comb_w_rep (n k : ℕ) : Finset (List ℕ) :=
  (allListsOfLength (Finset.range (k + 1)) n).filter (fun s => s.sum = k)

#eval comb_w_rep 3 4
#eval (comb_w_rep 3 4).card
#eval Nat.choose (3 + 4 - 1) 4

def listAddToHead (l : List ℕ) (m : ℕ) : List ℕ :=
  match l with
  | [] => []
  | a :: as => (a + m) :: as

#check List.modifyHead
#check [0, 3, 2, 4].modifyHead (· + 5)
#eval [0, 3, 2, 4].modifyHead (· + 5)
#check ({[0, 1], [0, 2]} : Finset (List ℕ)).image (List.modifyHead (· + 5))
#eval ({[0, 1], [0, 2]} : Finset (List ℕ)).image (List.modifyHead (· + 5))

lemma comb_w_rep_int (n k : ℕ) (l : List ℕ) : l ∈ comb_w_rep n k ↔
    l.length = n ∧ l.sum = k := by
  constructor
  case mp =>
    intro hl
    unfold comb_w_rep at hl
    simp only [Finset.mem_filter] at hl
    obtain ⟨hl1, hl2⟩ := hl
    apply (allListsOfLength_int (Finset.range (k + 1)) n l).mp at hl1
    exact ⟨hl1.left, hl2⟩
  case mpr =>
    intro h
    obtain ⟨h_length, h_sum⟩ := h
    unfold comb_w_rep
    simp only [Finset.mem_filter]
    constructor
    case left =>
      apply (allListsOfLength_int (Finset.range (k + 1)) n l).mpr
      constructor
      case left => exact h_length
      case right =>
        intro a ha
        simp only [Finset.mem_range, Order.lt_add_one_iff]
        have h1 : a ≤ l.sum := by
          exact List.le_sum_of_mem ha
        rw [h_sum] at h1
        exact h1
    case right => exact h_sum

lemma comb_w_rep_rec_sub1 (n k : ℕ) : comb_w_rep n (k + 1) =
  (comb_w_rep n k).image (List.modifyHead (· + 1)) ∪
  (comb_w_rep (n - 1) k).image (List.cons 0) := sorry
