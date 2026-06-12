import Mathlib

#eval Finset.powerset {0, 1, 2, 3}

theorem powerset_card_sub (n : ℕ) (s : Finset ℕ) (h : s.card = n) :
    s.powerset.card = 2 ^ n := by
  revert s
  induction n
  case zero =>
    intro s hs
    simp only [Finset.card_eq_zero] at hs
    rw [hs]
    simp only [Finset.powerset_empty, Finset.card_singleton, pow_zero]
  case succ k ih =>
    intro s hs
    have h1 : s.card ≠ 0 := by
      by_contra
      rw [this] at hs
      omega
    have hs_nonempty : s.Nonempty := by
      exact Finset.card_ne_zero.mp h1
    obtain ⟨a, ha⟩ := hs_nonempty
    have h_s_erase_a_card_sub : (s.erase a).card = s.card - 1 := by
      exact Finset.card_erase_of_mem ha
    have h_s_erase_a_card : (s.erase a).card = k := by
      omega
    have h2 : (s.erase a).powerset.card = 2 ^ k := by
      apply ih (s.erase a) h_s_erase_a_card
    have h_powerset_union : s.powerset =
        (s.erase a).powerset ∪
        Finset.image (fun t ↦ t ∪ {a}) (s.erase a).powerset := by
      apply Finset.ext_iff.mpr
      intro u
      constructor
      case mp =>
        intro hu
        simp only [Finset.union_singleton, Finset.mem_union, Finset.mem_powerset,
          Finset.mem_image]
        by_cases h_a_in_u : a ∈ u
        case pos =>
          right
          use u.erase a
          constructor
          case h.left =>
            apply Finset.erase_subset_erase a
            simp only [Finset.mem_powerset] at hu
            exact hu
          case h.right =>
            apply Finset.ext_iff.mpr
            intro b
            constructor
            case mp =>
              intro hb
              simp only [Finset.mem_insert, Finset.mem_erase, ne_eq] at hb
              obtain hb1 | ⟨hb2_l, hb2_r⟩ := hb
              · rw [hb1]
                exact h_a_in_u
              · exact hb2_r
            case mpr =>
              intro hb
              simp only [Finset.mem_insert, Finset.mem_erase, ne_eq]
              by_contra
              simp only [not_or, not_and] at this
              obtain ⟨this_1, this_2⟩ := this
              absurd hb
              apply this_2 this_1
        case neg =>
          left
          simp only [Finset.mem_powerset] at hu
          apply Finset.subset_erase.mpr
          exact ⟨hu, h_a_in_u⟩
      case mpr =>
        intro hu
        simp only [Finset.union_singleton, Finset.mem_union, Finset.mem_powerset,
          Finset.mem_image] at hu
        simp only [Finset.mem_powerset]
        obtain hu1 | hu2 := hu
        case inl =>
          apply (Finset.subset_erase.mp hu1).left
        case inr =>
          intro b hb
          obtain ⟨v, hv⟩ := hu2
          rw [← hv.right] at hb
          simp only [Finset.mem_insert] at hb
          by_cases hba : b = a
          case pos =>
            rw [hba]
            exact ha
          case neg =>
            have hbv : b ∈ v := by
              obtain hbl | hbr := hb
              case inl => contradiction
              case inr =>
                exact hbr
            have hb2 : b ∈ s.erase a := by
              apply hv.left
              exact hbv
            simp only [Finset.mem_erase, ne_eq] at hb2
            exact hb2.right
    rw [h_powerset_union]
    have h3 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k:= by omega
    rw [h3]
    have h4 : (s.erase a).powerset.card = 2 ^ k := by
      apply ih (s.erase a) h_s_erase_a_card
    have h5 : (Finset.image (fun t ↦ t ∪ {a}) (s.erase a).powerset).card = 2 ^ k := by
      rw [← h4]
      apply Finset.card_image_iff.mpr
      intro t ht u hu h
      simp only [Finset.union_singleton] at h
      apply Finset.ext_iff.mpr
      intro b
      simp only [Finset.coe_powerset, Finset.coe_erase, Set.mem_preimage,
        Set.mem_powerset_iff] at ht
      simp only [Finset.coe_powerset, Finset.coe_erase, Set.mem_preimage,
        Set.mem_powerset_iff] at hu
      have ht1 : t ⊆ s \ {a} := by
        apply Finset.coe_subset.mp
        simp only [Finset.coe_sdiff, Finset.coe_singleton]
        exact ht
      have hu1 : u ⊆ s \ {a} := by
        apply Finset.coe_subset.mp
        simp only [Finset.coe_sdiff, Finset.coe_singleton]
        exact hu
      constructor
      case mp =>
        intro hb
        have hb2 : b ∈ (t : Set ℕ) := by exact Finset.mem_coe.mpr hb
        have hb3 : b ∈ (s : Set ℕ) \ {a} := by
          exact Set.mem_diff_singleton.mpr (ht hb)
        have hb_neq_a : b ≠ a := by
          simp only [Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff] at hb3
          exact hb3.right
        have hb4 : b ∈ insert a t := by
          simp only [Finset.mem_insert]
          right
          exact hb
        rw [h] at hb4
        simp only [Finset.mem_insert] at hb4
        obtain hb4_l | hb4_r := hb4
        case inl => contradiction
        case inr => exact hb4_r
      case mpr =>
        intro hb
        have hb2 : b ∈ insert a t := by
          rw [h]
          simp only [Finset.mem_insert]
          right
          exact hb
        have hb3 : b ∈ s \ {a} := by
          apply hu1 at hb
          exact hb
        have hb4 : b ≠ a := by
          by_contra
          rw [this] at hb3
          simp only [Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false] at hb3
        simp only [Finset.mem_insert] at hb2
        obtain hb2_l | hb2_r := hb2
        case inl => contradiction
        case inr => exact hb2_r
    nth_rw 1 [← h4]
    rw [← h5]
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_iff_ne.mpr
    intro u hu v hv
    simp only [Finset.mem_powerset] at hu
    simp only [Finset.union_singleton, Finset.mem_image, Finset.mem_powerset] at hv
    obtain ⟨v1, hv1⟩ := hv
    have hau : a ∉ u := by
      by_contra
      apply hu at this
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at this
    by_contra
    rw [this] at hau
    rw [← hv1.right] at hau
    absurd hau
    simp only [Finset.mem_insert, true_or]

theorem powerset_card (s : Finset ℕ) : s.powerset.card = 2 ^ (s.card) := by
  apply powerset_card_sub
  rfl

-- The following definitions are the same.
-- def combination (s : Finset ℕ) (k : ℕ) : Finset (Finset ℕ) :=
--   s.powerset.filter (fun t ↦ t.card = k)

def combination (s : Finset ℕ) (k : ℕ) : Finset (Finset ℕ) :=
  {t ∈ s.powerset | t.card = k}

#eval combination {0, 1, 2, 3} 2

example (s : Finset ℕ) (a : ℕ) (h : a ∉ s) : (insert a s).card = s.card + 1
    := by
  exact Finset.card_insert_of_notMem h

lemma combination_rec (s : Finset ℕ) (k : ℕ) (a : ℕ) (ha : a ∈ s) :
    combination s (k + 1) = combination (s.erase a) (k + 1) ∪
    Finset.image (fun t ↦ t ∪ {a}) (combination (s.erase a) k) := by
  apply Finset.ext
  intro t
  constructor
  case h.mp =>
    intro ht
    simp only [Finset.union_singleton, Finset.mem_union, Finset.mem_image]
    unfold combination
    simp only [Finset.mem_filter, Finset.mem_powerset]
    unfold combination at ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    by_cases hat : a ∈ t
    case pos =>
      right
      use t.erase a
      and_intros
      · intro b hb
        simp only [Finset.mem_erase, ne_eq] at hb
        simp only [Finset.mem_erase, ne_eq]
        constructor
        · exact hb.left
        · apply ht.left hb.right
      · calc
          (t.erase a).card = t.card - 1 := by exact Finset.card_erase_of_mem hat
          _ = k + 1 -1 := by rw [ht.right]
          _ = k := by omega
      · exact Finset.insert_erase hat
    case neg =>
      left
      constructor
      · intro b hb
        simp only [Finset.mem_erase, ne_eq]
        constructor
        · by_contra
          rw [this] at hb
          contradiction
        · apply ht.left hb
      · exact ht.right
  case h.mpr =>
    intro ht
    simp only [Finset.union_singleton, Finset.mem_union, Finset.mem_image] at ht
    obtain ht_l | ht_r := ht
    case inl =>
      unfold combination at ht_l
      simp only [Finset.mem_filter, Finset.mem_powerset] at ht_l
      unfold combination
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro b hb
        apply ht_l.left at hb
        exact Finset.mem_of_mem_erase hb
      · exact ht_l.right
    case inr =>
      obtain ⟨as, has⟩ := ht_r
      unfold combination at has
      simp only [Finset.mem_filter, Finset.mem_powerset] at has
      unfold combination
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      case left =>
        intro b hb
        rw [← has.right] at hb
        simp only [Finset.mem_insert] at hb
        obtain hb_l | hb_r := hb
        case inl =>
          rw [hb_l]
          exact ha
        case inr =>
          apply has.left.left at hb_r
          exact Finset.mem_of_mem_erase hb_r
      case right =>
        rw [← has.right]
        rw [← has.left.right]
        apply Finset.card_insert_of_notMem
        by_contra
        apply has.left.left at this
        simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at this

lemma combination_k_eq_zero (s : Finset ℕ) : combination s 0 = {∅} := by
  unfold combination
  simp only [Finset.card_eq_zero]
  rw [Finset.ext_iff]
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton, and_iff_right_iff_imp,
    forall_eq, Finset.empty_subset]

lemma combination_k_eq_zero_card (s : Finset ℕ) : (combination s 0).card = 1
    := by
  rw [combination_k_eq_zero]
  simp only [Finset.card_singleton]

example (s : Finset ℕ) (k : ℕ) (h : s.card = k + 1) : s.Nonempty := by
  apply Finset.card_ne_zero.mp
  omega

example (n k : ℕ) (h : k ≤ n) : Nat.choose (n + 1) (k + 1)
    = Nat.choose n (k + 1) + Nat.choose n k := by
  rw [Nat.choose_succ_left]
  · simp only [add_tsub_cancel_right]
    omega
  · omega

lemma combination_card (n : ℕ) (k : ℕ) (hk : k ≤ n) (s : Finset ℕ)
    (hs : s.card = n) : (combination s k).card = Nat.choose n k := by
  revert s k
  induction n
  case zero =>
    intro k hk s hs
    have hk_zero : k = 0 := by omega
    rw [hk_zero]
    simp [combination_k_eq_zero_card]
  case succ n ih =>
    intro k hk s hs
    cases k
    case zero =>
      simp [combination_k_eq_zero_card]
    case succ k =>
      by_cases h_k_succ_leq_n : k + 1 ≤ n
      case pos =>
        have h_nonempty : s.Nonempty := by
          apply Finset.card_ne_zero.mp (by omega)
        obtain ⟨a, ha⟩ := h_nonempty
        rw [combination_rec s k a]
        · have h1 : (combination (s.erase a) (k + 1)) ∩
              (Finset.image (fun t ↦ t ∪ {a}) (combination (s.erase a) k)) = ∅ := by
            apply Finset.ext_iff.mpr
            intro b
            constructor
            case mp =>
              intro hb
              simp only [Finset.union_singleton, Finset.mem_inter, Finset.mem_image] at hb
              obtain ⟨hb_l, ⟨as, has⟩⟩ := hb
              have h1 : a ∈ b := by
                rw [← has.right]
                simp only [Finset.mem_insert, true_or]
              unfold combination at hb_l
              simp only [Finset.mem_filter, Finset.mem_powerset] at hb_l
              apply hb_l.left at h1
              simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at h1
            case mpr =>
              simp only [Finset.notMem_empty, Finset.union_singleton, Finset.mem_inter,
                Finset.mem_image, IsEmpty.forall_iff]
          have h2 : (combination (s.erase a) (k + 1)).card = Nat.choose n (k + 1)
              := by
            apply ih (k + 1)
            case hk => exact h_k_succ_leq_n
            case hs =>
              calc
                _ = s.card - 1 := by apply Finset.card_erase_of_mem ha
                _ = n + 1 - 1 := by rw [hs]
                _ = n := by omega
          have h3 : (Finset.image (fun t ↦ t ∪ {a}) (combination (s.erase a) k)).card
              = (combination (s.erase a) k).card := by
            apply Finset.card_image_iff.mpr
            intro t1 ht1 t2 ht2 h
            unfold combination at ht1
            simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at ht1
            unfold combination at ht2
            simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at ht2
            simp only [Finset.union_singleton] at h
            apply Finset.ext_iff.mpr
            intro b
            constructor
            case mp =>
              intro hb
              have h3 : b ≠ a := by
                apply ht1.left at hb
                simp only [Finset.mem_erase, ne_eq] at hb
                exact hb.left
              have h4 : b ∈ insert a t1 := by
                simp only [Finset.mem_insert]
                right
                exact hb
              rw [h] at h4
              simp only [Finset.mem_insert] at h4
              obtain h4l | h4r := h4
              case inl => contradiction
              case inr => exact h4r
            case mpr =>
              intro hb
              have h3 : b ≠ a := by
                apply ht2.left at hb
                simp only [Finset.mem_erase, ne_eq] at hb
                exact hb.left
              have h4 : b ∈ insert a t2 := by
                simp only [Finset.mem_insert]
                right
                exact hb
              rw [← h] at h4
              simp only [Finset.mem_insert] at h4
              obtain h4l | h4r := h4
              case inl => contradiction
              case inr => exact h4r
          have h4 : (Finset.image (fun t ↦ t ∪ {a}) (combination (s.erase a) k)).card
              = Nat.choose n k := by
            rw [h3]
            apply ih
            · omega
            · calc
                _ = s.card - 1 := by rw [Finset.card_erase_of_mem ha]
                _ = n + 1 - 1 := by rw [hs]
                _ = n := by omega
          have h5 : Nat.choose n (k + 1) + Nat.choose n k =
              Nat.choose n k + Nat.choose n (k + 1) := by omega
          have h6 : Nat.choose n k + Nat.choose n (k + 1) =
              Nat.choose (n + 1) (k + 1) := by
            exact Eq.symm (Nat.choose_succ_succ' n k)
          rw [Finset.card_union]
          rw [h1]
          rw [h2]
          rw [h4]
          rw [h5]
          rw [h6]
          simp only [Finset.card_empty, tsub_zero]
        · exact ha
      case neg =>
        have h1 : k = n := by omega
        rw [h1]
        unfold combination
        simp only [Nat.choose_self]
        have h1 : {t ∈ s.powerset | t.card = n + 1} = {s} := by
          apply Finset.ext_iff.mpr
          intro t
          simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
          constructor
          case mp =>
            intro ht
            symm
            -- It is notable that there is a theorem for this.
            apply (Finset.eq_iff_card_ge_of_superset ht.left).mp
            rw [hs, ht.right]
          case mpr =>
            intro hts
            rw [hts]
            simp only [subset_refl, true_and, hs]
        simp only [h1, Finset.card_singleton]
