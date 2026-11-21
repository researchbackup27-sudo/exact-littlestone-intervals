import ExactLittlestone.SwDefs

namespace ExactLittlestone

theorem dk_ge {k : ℕ} : k ≤ dk k := by
  unfold dk; omega

private theorem dk_eq (k : ℕ) : dk k = (3 * k + 1) / 2 := rfl

theorem Q_of_le {k d : ℕ} (h : d ≤ k) : Q k d = d + 1 := by
  rw [Q]; split_ifs; rfl

theorem Q_mid {k d : ℕ} (h1 : k < d) (h2 : d < dk k + k) : Q k d = 2 * d + 1 - k := by
  rw [Q]; split_ifs <;> omega

theorem Q_big {k d : ℕ} (hk : 0 < k) (h : dk k + k ≤ d) : Q k d = 2 * Q k (d - k) := by
  have := @dk_ge k
  rw [Q]; split_ifs <;> first | rfl | omega

private theorem Q_mid' {k d : ℕ} (h1 : k ≤ d) (h2 : d < dk k + k) : Q k d = 2 * d + 1 - k := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | h1
  · rw [Q_of_le le_rfl]; omega
  · exact Q_mid h1 h2

private theorem Q_two {k d : ℕ} (hk : 0 < k) (h1 : dk k + k ≤ d) (h2 : d < dk k + 2 * k) :
    Q k d = 2 * (2 * (d - k) + 1 - k) := by
  rw [Q_big hk h1, Q_mid' (by have := dk_eq k; omega) (by omega)]

theorem Q_small {k d : ℕ} (_hk : 0 < k) (h : d < dk k + k) :
    Q k d = if d ≤ k then d + 1 else 2 * d + 1 - k := by
  by_cases h' : d ≤ k
  · simp only [h', ite_true, Q_of_le h']
  · simp only [h', ite_false, Q_mid (by omega) h]

theorem Q_block {k i : ℕ} (hk : 0 < k) (hi : i < k) :
    Q k (dk k + k + i) = 2 * (2 * (dk k + i) + 1 - k) := by
  rw [Q_two hk (by omega) (by omega)]
  congr 2; omega

theorem Q_step_two {k : ℕ} (hk : 0 < k) {d : ℕ} (h : k ≤ d) : Q k d + 2 ≤ Q k (d + 1) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have := dk_eq k
    by_cases h1 : d + 1 < dk k + k
    · rw [Q_mid' h (by omega), Q_mid' (by omega) h1]; omega
    by_cases h2 : d + 1 < dk k + 2 * k
    · rw [Q_two hk (by omega) h2]
      by_cases h3 : d < dk k + k
      · rw [Q_mid' h h3]; omega
      · rw [Q_two hk (by omega) (by omega)]; omega
    · rw [Q_big hk (by omega) (d := d), Q_big hk (by omega) (d := d + 1)]
      have := ih (d - k) (by omega) (by omega)
      rw [show d - k + 1 = d + 1 - k by omega] at this
      omega

theorem Q_lt_succ {k : ℕ} (hk : 0 < k) (d : ℕ) : Q k d < Q k (d + 1) := by
  by_cases h : d < k
  · rw [Q_of_le h.le, Q_of_le h]; omega
  · have := Q_step_two hk (d := d) (by omega); omega

theorem Q_strictMono {k : ℕ} (hk : 0 < k) : StrictMono (Q k) :=
  strictMono_nat_of_lt_succ (Q_lt_succ hk)

theorem Q_le_Q_iff {k : ℕ} (hk : 0 < k) {a b : ℕ} : Q k a ≤ Q k b ↔ a ≤ b :=
  (Q_strictMono hk).le_iff_le

theorem Q_ge {k : ℕ} (hk : 0 < k) (d : ℕ) : d + 1 ≤ Q k d := by
  induction d with
  | zero => rw [Q_of_le (Nat.zero_le _)]
  | succ d ih => have := Q_lt_succ hk d; omega

theorem Q_ge_lin {k : ℕ} (hk : 0 < k) (d : ℕ) : 2 * d + 1 ≤ Q k d + k := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have := dk_eq k
    by_cases h1 : d ≤ k
    · rw [Q_of_le h1]; omega
    by_cases h2 : d < dk k + k
    · rw [Q_mid (by omega) h2]; omega
    · rw [Q_big hk (by omega)]
      have := ih (d - k) (by omega)
      omega

theorem Q_ge_add {k e : ℕ} (hk : 0 < k) (h : dk k + k ≤ e) : e + k ≤ Q k e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    have := dk_eq k
    by_cases h2 : e < dk k + 2 * k
    · rw [Q_two hk h h2]; omega
    · rw [Q_big hk h]
      have := ih (e - k) (by omega) (by omega)
      omega

theorem Q_pred_k {k d : ℕ} (hk : 2 ≤ k) (h1 : k + 1 ≤ d) (h2 : d + 2 ≤ dk k + k + k / 2) :
    Q (k - 1) (d - 2) + 2 ≤ Q k d := by
  have e1 := dk_eq k
  have e2 := dk_eq (k - 1)
  have hk1 : 0 < k - 1 := by omega
  by_cases h3 : d < dk k + k
  · rw [Q_mid' (by omega) h3]
    by_cases h4 : d - 2 ≤ k - 1
    · rw [Q_of_le h4]; omega
    by_cases h5 : d - 2 < dk (k - 1) + (k - 1)
    · rw [Q_mid (by omega) h5]; omega
    · rw [Q_big hk1 (by omega), Q_mid' (by omega) (by omega)]; omega
  · rw [Q_two (k := k) (d := d) (by omega) (by omega) (by omega),
      Q_two hk1 (by omega) (by omega)]
    omega

theorem Q_v_le {k x : ℕ} (_hk : 0 < k) (hx : 1 ≤ x) : Q k (v k x) ≤ x :=
  Nat.findGreatest_spec (P := fun d => Q k d ≤ x) (Nat.zero_le x)
    (by rw [Q_of_le (Nat.zero_le _)]; exact hx)

theorem lt_Q_v_succ {k x : ℕ} (hk : 0 < k) : x < Q k (v k x + 1) := by
  by_contra hc
  have h := Q_ge hk (v k x + 1)
  unfold v at hc h
  exact Nat.findGreatest_is_greatest (P := fun d => Q k d ≤ x) (n := x) (Nat.lt_succ_self _)
    (by omega) (Nat.not_lt.1 hc)

theorem le_v_iff {k x d : ℕ} (hk : 0 < k) (hx : 1 ≤ x) : d ≤ v k x ↔ Q k d ≤ x := by
  constructor
  · intro h
    exact ((Q_le_Q_iff hk).2 h).trans (Q_v_le hk hx)
  · intro h
    have := Q_ge hk d
    exact Nat.le_findGreatest (P := fun d => Q k d ≤ x) (by omega) h

end ExactLittlestone
