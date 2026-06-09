import Mathlib

#check Finset.image
#eval Finset.image (fun (a : ℕ) ↦ a :: [2, 3]) {0, 1}

def allListsOfLength (s : Finset ℕ) (k : ℕ) : Finset (List ℕ) :=
  match k with
  | 0 => {[]}
  | k + 1 =>
      Finset.biUnion (allListsOfLength s k)
        (fun t ↦ Finset.image (fun a ↦ a :: t) s)

theorem allListsOfLength_ext (s : Finset ℕ) (k : ℕ) (l : List ℕ) :
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
    constructor
    case mp =>
      intro hl
      simp only [Finset.mem_biUnion, Finset.mem_image] at hl
      obtain ⟨as, has⟩ := hl
      obtain ⟨a, ha⟩ := has.right
      constructor
      case left =>
        rw [← ha.right]
        simp only [List.length_cons, Nat.add_right_cancel_iff]
        apply ((ih as).mp has.left).left
      case right =>
        intro b hb
        rw [← ha.right] at hb
        simp only [List.mem_cons] at hb
        cases hb
        case inl hb_l =>
          rw [hb_l]
          exact ha.left
        case inr hb_r =>
          apply ((ih as).mp has.left).right b hb_r
    case mpr =>
      intro hl
      simp only [Finset.mem_biUnion, Finset.mem_image]
      cases l
      case nil =>
        unfold List.length at hl
        omega
      case cons b bs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons,
          forall_eq_or_imp] at hl
        use bs
        constructor
        case h.left =>
          apply (ih bs).mpr
          constructor
          case left =>
            apply hl.left
          case right =>
            apply hl.right.right
        use b
        simp only [and_true]
        exact hl.right.left

theorem disj_biUnion_card {α : Type} (s : Finset α) (f : α → Finset ℕ)
    (h_disj : ∀ a1 a2 : α, a1 ≠ a2 → Disjoint (f a1) (f a2)) :
    (Finset.biUnion s (fun a ↦ (f a))).card = Finset.sum s (fun a ↦ (f a).card) := by
  exact Finset.card_biUnion fun ⦃x⦄ a ⦃y⦄ a_1 ↦ h_disj x y

lemma finset_sum_of_constant (s : Finset ℕ) (f : ℕ → ℕ) (m : ℕ)
    (h : ∀ n ∈ s, f n = m) :
    Finset.sum s f = s.card * m := by
  exact Finset.sum_const_nat h

theorem allListsOfLength_card (s : Finset ℕ) (k : ℕ) :
    (allListsOfLength s k).card = (s.card)^k := by
  induction k
  case zero =>
    unfold allListsOfLength
    simp
  case succ k ih =>
    unfold allListsOfLength
    have h1_0 : ∀ a ∈ (allListsOfLength s k),
        (fun _ ↦ s.card) a = s.card := by simp
    have h1 : (s.card)^(k + 1)
        = Finset.sum (allListsOfLength s k) (fun _ ↦ s.card)
        := by
      calc
        (s.card)^(k + 1) = s.card ^ k * s.card
          := by exact Nat.pow_add_one s.card k
        _ = (allListsOfLength s k).card * s.card
          := by rw [ih]
        _ = Finset.sum (allListsOfLength s k) (fun _ ↦ s.card)
          := by apply (Finset.sum_const_nat h1_0).symm
    have h_disj : ∀ t1 t2 : List ℕ, t1 ≠ t2 → Disjoint
        (Finset.image (fun a ↦ a :: t1) s) (Finset.image (fun a ↦ a :: t2) s) := by
      simp only [ne_eq]
      intro t1 t2 ht
      rw [Finset.disjoint_iff_ne]
      intro l1 hl1 l2 hl2
      simp only [Finset.mem_image] at hl1
      obtain ⟨a1, ha1⟩ := hl1
      simp only [Finset.mem_image] at hl2
      obtain ⟨a2, ha2⟩ := hl2
      rw [← ha1.right, ← ha2.right]
      simp only [ne_eq, List.cons.injEq, not_and]
      intro h
      exact ht
    rw [h1]
    have h_disj2 : (allListsOfLength s k : Set (List ℕ)).PairwiseDisjoint
        (fun (t : List ℕ) ↦ Finset.image (fun a ↦ a :: t) s) := by
      intro t1 ht1 t2 ht2 ht
      simp only [SetLike.mem_coe] at ht1
      simp only [SetLike.mem_coe] at ht2
      unfold Function.onFun
      simp only
      apply h_disj
      apply ht
    rw [Finset.card_biUnion h_disj2]
    have h2 : ∀ t ∈ allListsOfLength s k, (Finset.image (fun a ↦ a :: t) s).card = s.card
        := by
      intro t ht
      apply Finset.card_image_iff.mpr
      simp
    exact Finset.sum_congr rfl h2

def permutation (s : Finset ℕ) (k : ℕ) : Finset (List ℕ) :=
  (allListsOfLength s k).filter (fun l ↦ l.Nodup)

theorem permutation_ext (s : Finset ℕ) (k : ℕ) (l : List ℕ) :
    l ∈ permutation s k ↔ l.length = k ∧ (∀ a ∈ l, a ∈ s) ∧ l.Nodup := by
  constructor
  case mp =>
    intro hl
    constructor
    case left =>
      unfold permutation at hl
      simp only [Finset.mem_filter] at hl
      apply ((allListsOfLength_ext s k l).mp hl.left).left
    case right =>
      unfold permutation at hl
      simp only [Finset.mem_filter] at hl
      constructor
      case left =>
        apply ((allListsOfLength_ext s k l).mp hl.left).right
      case right =>
        exact hl.right
  case mpr =>
    intro h
    unfold permutation
    simp only [Finset.mem_filter]
    constructor
    case left =>
      apply (allListsOfLength_ext s k l).mpr
      constructor
      case left => exact h.left
      case right => exact h.right.left
    exact h.right.right

def head' (l : List ℕ) :=
  match l with
  | [] => 0
  | a :: _ => a

def tail' (l : List ℕ) :=
  match l with
  | [] => []
  | _ :: as => as

def filter_and_omit_by_head (ss : Finset (List ℕ)) (a : ℕ) :=
  (ss.filter (fun l ↦ (head' l) = a)).image (fun l ↦ tail' l)

#eval filter_and_omit_by_head {[0, 1, 2], [0, 2, 1], [1, 2, 3], [0, 3, 1]} 0

lemma permutation_rec_sub (s : Finset ℕ) (k : ℕ) (a : ℕ) (h : a ∈ s) :
    filter_and_omit_by_head (permutation s (k + 1)) a = permutation (s.erase a) k
    := by
  apply Finset.ext_iff.mpr
  intro l
  constructor
  case mp =>
    intro hl
    unfold filter_and_omit_by_head at hl
    simp only [Finset.mem_image, Finset.mem_filter] at hl
    obtain ⟨l1, hl1⟩ := hl
    have hl1_length : l1.length = k + 1 := by
      apply ((permutation_ext s (k + 1) l1).mp hl1.left.left).left
    cases l1
    case nil => contradiction
    case cons b bs =>
      apply (permutation_ext (s.erase a) k l).mpr
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl1_length
      unfold head' tail' at hl1
      simp only at hl1
      rw [hl1.right] at hl1_length
      constructor
      case left => apply hl1_length
      case right =>
        constructor
        case left =>
          intro c hc
          rw [hl1.right] at hl1
          have h2 : ∀ d ∈ b :: l, d ∈ s := by
            apply ((permutation_ext s (k + 1) (b :: l)).mp hl1.left.left).right.left
          simp only [Finset.mem_erase, ne_eq]
          have h3 : (b :: l).Nodup := by
            apply ((permutation_ext s (k + 1) (b :: l)).mp hl1.left.left).right.right
          rw [hl1.left.right] at h3
          simp only [List.nodup_cons] at h3
          constructor
          case left =>
            by_contra
            absurd h3.left
            rw [this] at hc
            exact hc
          apply h2
          right
          exact hc
        case right =>
          have h4 : (b :: bs).Nodup := by
            apply ((permutation_ext s (k + 1) (b :: bs)).mp hl1.left.left).right.right
          rw [hl1.right] at h4
          simp only [List.nodup_cons] at h4
          exact h4.right
  case mpr =>
    intro hl
    unfold filter_and_omit_by_head
    simp only [Finset.mem_image, Finset.mem_filter]
    have h1 : l.length = k ∧ (∀ b ∈ l, b ∈ (s.erase a)) ∧ l.Nodup := by
      apply (permutation_ext (s.erase a) k l).mp hl
    use (a :: l)
    constructor
    case left =>
      constructor
      case left =>
        apply (permutation_ext s (k + 1) (a :: l)).mpr
        constructor
        case left =>
          simp only [List.length_cons, Nat.add_right_cancel_iff]
          exact h1.left
        constructor
        case left =>
          intro c hc
          simp only [List.mem_cons] at hc
          cases hc
          case inl hc_l =>
            rw [hc_l]
            exact h
          case inr hc_r =>
            have h2 : c ∈ s.erase a := by
              apply h1.right.left
              exact hc_r
            simp only [Finset.mem_erase, ne_eq] at h2
            exact h2.right
        simp only [List.nodup_cons]
        constructor
        case left =>
          by_contra
          have h2 : a ∈ s.erase a := by
            apply h1.right.left a this
          simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at h2
        exact h1.right.right
      case right =>
        unfold head'
        simp only
    case h.right =>
      unfold tail'
      simp only

def f (s : Finset ℕ) (k : ℕ) := Finset.biUnion s
  (fun a ↦ Finset.image (fun as ↦ a :: as ) (permutation (s.erase a) k))

#check f
#eval f {0, 1, 2, 3} 3

lemma permutation_rec (s : Finset ℕ) (k : ℕ) :
    permutation s (k + 1) = Finset.biUnion s
    (fun a ↦ Finset.image (fun as ↦ a :: as ) (permutation (s.erase a) k))
    := by
  ext l
  case h =>
    constructor
    case mp =>
      intro h
      simp
      apply (permutation_ext s (k + 1 ) l).mp at h
      cases l
      case nil =>
        unfold List.length at h
        omega
      case cons b bs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp,
          List.nodup_cons] at h
        use b
        and_intros
        case h.refine_1 =>
          apply h.right.left.left
        case h.refine_2 =>
          use bs
          constructor
          case h.left =>
            apply (permutation_ext (s.erase b) k bs).mpr
            and_intros
            case refine_1 =>
              exact h.left
            case refine_2.refine_1 =>
              intro a ha
              simp only [Finset.mem_erase, ne_eq]
              constructor
              case left =>
                by_contra
                absurd h.right.right.left
                rw [← this]
                exact ha
              obtain ⟨h1, h2, h3⟩ := h
              apply h2.right a ha
            apply h.right.right.right
          rfl
    case mpr =>
      intro h
      simp only [Finset.mem_biUnion, Finset.mem_image] at h
      obtain ⟨a, ha, ⟨as, ⟨has1, has2⟩⟩⟩ := h
      apply (permutation_ext s (k + 1) l).mpr
      apply (permutation_ext (s.erase a) k as).mp at has1
      obtain ⟨has1_length, has1_sub, has1_nodup⟩ := has1
      rw [← has2]
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp,
        List.nodup_cons]
      and_intros
      · exact has1_length
      · exact ha
      · intro b hb
        exact Finset.mem_of_mem_erase (has1_sub b hb)
      · by_contra
        have h1 : a ∈ s.erase a := by
          apply has1_sub a this
        simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at h1
      · exact has1_nodup

example (s : Finset ℕ) (f : ℕ → ℕ) (m : ℕ) (h : ∀ a ∈ s, f a = m) :
    Finset.sum s f = s.card * m := by
  exact finset_sum_of_constant s f m h

theorem permutation_card (s : Finset ℕ) (k : ℕ) :
    (permutation s k).card = (s.card).descFactorial k := by
  revert s
  induction k
  case _ =>
    intro s
    unfold permutation allListsOfLength
    exact Eq.symm (Nat.eq_of_beq_eq_true rfl)
  case succ k ih =>
    intro s
    rw [permutation_rec]
    rw [Finset.card_biUnion]
    · have h1 : ∀ a ∈ s, (permutation (s.erase a) k).card = (s.erase a).card.descFactorial k
          := by
        intro a ha
        apply ih (s.erase a)
      have h2 : ∀ a ∈ s, (Finset.image (fun as ↦ a :: as)
          (permutation (s.erase a) k)).card = (permutation (s.erase a) k).card := by
        intro a ha
        apply Finset.card_image_iff.mpr
        simp only [List.cons.injEq, true_and, implies_true, Set.injOn_of_eq_iff_eq]
      have h3 : ∀ a ∈ s, (Finset.image (fun as ↦ a :: as)
          (permutation (s.erase a) k)).card = (s.erase a).card.descFactorial k := by
        intro a ha
        rw [h2 a ha, h1 a ha]
      have h4 : s.card.descFactorial (k + 1)
          = (s.card) * (s.card - 1).descFactorial k := by
        cases s.card
        case zero => simp only [Nat.descFactorial_succ, zero_tsub, zero_mul]
        case succ m =>
          exact Nat.succ_descFactorial_succ m k
      rw [h4]
      have h5 : ∀ a ∈ s, s.card - 1 = (s.erase a).card := by
        exact fun a a_1 ↦ Eq.symm (Finset.card_erase_of_mem a_1)
      have h6 : ∀ a ∈ s, (Finset.image (fun as ↦ a :: as)
          (permutation (s.erase a) k)).card = (s.card - 1).descFactorial k := by
        intro a ha
        rw [h3]
        · rw [h5 a]
          exact ha
        · exact ha
      apply finset_sum_of_constant s (fun a ↦ (Finset.image (fun as ↦ a :: as)
          (permutation (s.erase a) k)).card) ((s.card - 1).descFactorial k)
          h6
    · intro a ha b hb h_diff
      simp only [SetLike.mem_coe] at ha
      simp only [SetLike.mem_coe] at hb
      unfold Function.onFun
      rw [Finset.disjoint_iff_ne]
      intro a1 ha1 b1 hb1
      simp only [Finset.mem_image] at ha1
      obtain ⟨as, has⟩ := ha1
      simp only [Finset.mem_image] at hb1
      obtain ⟨bs, hbs⟩ := hb1
      rw [← has.right, ← hbs.right]
      simp only [ne_eq, List.cons.injEq, not_and]
      intro hab
      contradiction
