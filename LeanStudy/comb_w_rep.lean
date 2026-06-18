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

lemma comb_w_rep_rec (n k : ℕ) : comb_w_rep (n + 1) (k + 1) =
    (comb_w_rep (n + 1) k).image (List.modifyHead (· + 1)) ∪
    (comb_w_rep n (k + 1)).image (List.cons 0) := by
  apply Finset.ext_iff.mpr
  intro l
  constructor
  case mp =>
    intro hl
    unfold comb_w_rep at hl
    simp only [Finset.mem_filter] at hl
    obtain ⟨hl_l, hl_sum⟩ := hl
    rw [allListsOfLength_int] at hl_l
    obtain ⟨hl_length, hl_range⟩ := hl_l
    cases l
    case nil =>
      simp only [List.sum_nil, reduceCtorEq] at hl_sum
    case cons a as =>
      simp only [Finset.mem_union, Finset.mem_image, List.cons.injEq, exists_eq_right_right]
      simp only [List.sum_cons] at hl_sum
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl_length
      by_cases ha_zero : a = 0
      case pos =>
        right
        constructor
        case left =>
          unfold comb_w_rep
          simp only [Finset.mem_filter]
          constructor
          case left =>
            rw [allListsOfLength_int]
            constructor
            case left => exact hl_length
            case right =>
              intro b hb
              apply hl_range
              right; exact hb
          case right => omega
        case right => omega
      case neg =>
        left
        cases a
        case zero => contradiction
        case succ ap =>
          use ap :: as
          constructor
          case h.left =>
            rw [comb_w_rep_int]
            simp only [List.length_cons, Nat.add_right_cancel_iff, List.sum_cons]
            constructor
            case left => exact hl_length
            case right => omega
          case h.right =>
            unfold List.modifyHead
            simp only
  case mpr =>
    intro hl
    simp only [Finset.mem_union, Finset.mem_image] at hl
    simp [comb_w_rep_int]
    cases hl
    case inl hl_a_pos =>
      obtain ⟨l1, ⟨hl1_l, hl1_r⟩⟩ := hl_a_pos
      rw [comb_w_rep_int] at hl1_l
      obtain ⟨hl1_length, hl1_sum⟩ := hl1_l
      rw [← hl1_r]
      constructor
      case left =>
        subst hl1_r
        simp_all only [List.length_modifyHead]
      case right =>
        cases l1
        case nil =>
          contradiction
        case cons a as =>
          unfold List.modifyHead
          simp only [List.sum_cons]
          simp only [List.sum_cons] at hl1_sum
          omega
    case inr hl_a_zero =>
      obtain ⟨as, ⟨has_l, has_r⟩⟩ := hl_a_zero
      rw [comb_w_rep_int] at has_l
      obtain ⟨has_length, has_sum⟩ := has_l
      rw [← has_r]
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.sum_cons, zero_add]
      exact ⟨has_length, has_sum⟩

-- lemma comb_w_rep_rec (n k : ℕ) : comb_w_rep (n + 1) (k + 1) =
--     (comb_w_rep (n + 1) k).image (List.modifyHead (· + 1)) ∪
--     (comb_w_rep n (k + 1)).image (List.cons 0) := by

theorem listN_sum_zero_all_zero (l : List ℕ) (h_sum : l.sum = 0) :
    l = List.replicate l.length 0 := by
  generalize h_length : l.length = n
  revert l
  induction n
  case zero =>
    simp only [List.length_eq_zero_iff, List.replicate_zero, imp_self, implies_true]
  case succ n ih =>
    intro l hl_sum hl_length
    cases l
    case nil =>
      simp only [List.length_nil, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero,
        and_false] at hl_length
    case cons a as =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl_length
      unfold List.replicate
      simp only [List.cons.injEq]
      simp only [List.sum_cons, Nat.add_eq_zero_iff] at hl_sum
      constructor
      case left =>
        exact hl_sum.left
      case right =>
        apply ih as hl_sum.right hl_length

theorem comb_w_rep_count (n k : ℕ) (hn : n ≥ 1) :
    (comb_w_rep n k).card = Nat.choose (n + k - 1) k := by
  cases n
  case zero => contradiction
  case succ n =>
    simp only [Nat.succ_add_sub_one]
    induction h : n + k using Nat.strong_induction_on generalizing n k
    case h d ih =>
      cases k
      case zero =>
        simp only [Nat.choose_zero_right]
        have h1 : comb_w_rep (n + 1) 0 = {List.replicate (n + 1) 0} := by
          apply Finset.ext_iff.mpr
          intro l
          simp only [Finset.mem_singleton]
          constructor
          case mp =>
            intro hl
            rw [comb_w_rep_int] at hl
            obtain ⟨hl_length, hl_sum⟩ := hl
            rw [← hl_length]
            apply listN_sum_zero_all_zero l hl_sum
          case mpr =>
            intro hl
            rw [comb_w_rep]
            simp only [zero_add, Finset.range_one, Finset.mem_filter]
            constructor
            case left =>
              rw [allListsOfLength_int]
              constructor
              case left =>
                apply?
