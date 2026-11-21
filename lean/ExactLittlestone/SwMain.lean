import ExactLittlestone.SwPot
import ExactLittlestone.SwPair
import ExactLittlestone.SwMoves
import ExactLittlestone.SwQ
import ExactLittlestone.SwUnions
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Group.Nat.Even

namespace ExactLittlestone

open Finset

variable {full a b : Bool} {k n d : ℕ}

theorem upper (hk : 1 ≤ k) : ∀ n d, Shatters (pathClass a b k n) d → Q k d ≤ n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro d hs
    by_contra hlt
    have hdn := hs.le
    have hdk : dk k = (3 * k + 1) / 2 := rfl
    rcases le_or_gt d k with h1 | h1
    · rw [Q_of_le h1] at hlt; omega
    by_cases h2 : d < dk k + k
    · rw [Q_mid h1 h2] at hlt
      have := pathClass_le_half hs
      omega
    · rw [Q_big (by omega) (by omega)] at hlt
      obtain ⟨D', hD, hs'⟩ := pair_bound hs
      have := IH ((n + 1) / 2 - 1) (by omega) (d - k) (hs'.mono (by omega))
      omega

theorem Sh.congr (h : Sh full a b k n d) {n' d' : ℕ} (hn : n = n') (hd : d = d') :
    Sh full a b k n' d' := by subst hn hd; exact h

theorem Sh.lift (h : Sh full a b k n d) {n' : ℕ} (hn : n ≤ n') : Sh full a b k n' d := by
  induction n' with
  | zero => exact h.congr (by omega) rfl
  | succ n' ih =>
    rcases Nat.lt_or_ge n (n' + 1) with h1 | h1
    · exact move_b (ih (by omega))
    · exact h.congr (by omega) rfl

def LB (k : ℕ) : Prop := ∀ a b : Bool, k % 2 = (if a = b then 0 else 1) → ∀ n d, Q k d ≤ n + 1 →
  Sh false a b k n d ∧ (d + k ≤ n + 1 → Sh true a b k n d)

theorem Q_one (d : ℕ) : Q 1 d = 2 ^ d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have hdk : dk 1 = 2 := rfl
    rcases Nat.lt_or_ge d 3 with h | h
    · interval_cases d
      · rw [Q_of_le (by omega)]; rfl
      · rw [Q_of_le (by omega)]; rfl
      · rw [Q_mid (by omega) (by omega)]; rfl
    · rw [Q_big (by omega) (by omega), ih (d - 1) (by omega)]
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      simp [pow_succ, Nat.mul_comm]

theorem lb_one : LB 1 := by
  intro a b hpar
  have hab : a ≠ b := by intro h; simp [h] at hpar
  have key : ∀ d n, 2 ^ d ≤ n + 1 → Sh true a b 1 n d := by
    intro d
    induction d with
    | zero => intro n _; exact exists_exact hpar (by omega)
    | succ d ih =>
      intro n hn
      have h0 := ih (2 ^ d - 1) (by have := Nat.one_le_two_pow (n := d); omega)
      have h1 := move_e h0
      refine h1.lift ?_
      rw [pow_succ] at hn
      have := Nat.one_le_two_pow (n := d)
      omega
  intro n d hQ
  rw [Q_one] at hQ
  exact ⟨(key d n hQ).to_false, fun _ => key d n hQ⟩

theorem par_pred (hk : 1 ≤ k) (hpar : k % 2 = if a = b then 0 else 1) :
    (k - 1) % 2 = if (!a) = b then 0 else 1 := by
  revert hpar; cases a <;> cases b <;> simp <;> omega

theorem lb_step (hk : 2 ≤ k) (ih : LB (k - 1)) : LB k := by
  intro a b hpar n
  induction n using Nat.strong_induction_on generalizing a b with
  | _ n IH =>
    intro d hQ
    have hk0 : 0 < k := by omega
    have hdk : dk k = (3 * k + 1) / 2 := rfl
    have hdk' : dk (k - 1) = (3 * (k - 1) + 1) / 2 := rfl
    have hpar' := par_pred (by omega) hpar
    -- refinement regime
    have big : dk k + k ≤ d → d + 2 > dk k + k + k / 2 → Sh true a b k (Q k d - 1) d := by
      intro h1 h2
      have hb := Q_big hk0 h1
      have hge := Q_ge hk0 (d - k)
      have cond : d ≤ Q k (d - k) := by
        by_cases h3 : d - k < dk k + k
        · rw [Q_mid (by omega) h3]; omega
        · have := Q_ge_add hk0 (e := d - k) (by omega); omega
      have hII := (IH (Q k (d - k) - 1) (by omega) a b hpar (d - k) (by omega)).2 (by omega)
      exact (move_e hII).congr (by omega) (by omega)
    -- distance-two regime
    have mid : ∀ f : Bool, k + 1 ≤ d → d + 2 ≤ dk k + k + k / 2 →
        (f = true → d + k + 1 ≤ Q k d) → Sh f a b k (Q k d - 1) d := by
      intro f h1 h2 hf
      have s2 := Q_step_two hk0 (d := d - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at s2
      have p := Q_pred_k hk h1 h2
      have hg := Q_ge hk0 (d - 1)
      have A := IH (Q k d - 3) (by omega) a b hpar (d - 1) (by omega)
      have B := ih (!a) b hpar' (Q k d - 3) (d - 2) (by omega)
      have hA : Sh f a b k (Q k d - 3) (d - 1) := by
        cases f
        · exact A.1
        · exact A.2 (by have := hf rfl; omega)
      have hB : Sh f (!a) b (k - 1) (Q k d - 3) (d - 1 - 1) := by
        cases f
        · exact B.1.congr rfl (by omega)
        · exact (B.2 (by have := hf rfl; omega)).congr rfl (by omega)
      exact (move_d (by omega) hA hB).congr (by omega) (by omega)
    refine ⟨?_, fun hdk1 => ?_⟩
    · -- claim (i)
      refine Sh.lift (n := Q k d - 1) ?_ (by omega)
      rcases le_or_gt d k with h1 | h1
      · rw [Q_of_le h1, Nat.add_sub_cancel]
        exact sh_false.mpr (move_a hpar h1)
      by_cases h2 : d + 2 ≤ dk k + k + k / 2
      · exact mid false h1 h2 (by simp)
      · exact (big (by omega) (by omega)).to_false
    · -- claim (ii)
      by_cases hc : Q k d ≤ d + k
      · refine Sh.lift (n := d + k - 1) ?_ (by omega)
        cases d with
        | zero => exact exists_exact hpar (by omega)
        | succ d' =>
          have hlt := Q_lt_succ hk0 d'
          have hlin := Q_ge_lin hk0 (d' + 1)
          have h1 := (IH (d' + k - 1) (by omega) a b hpar d' (by omega)).2 (by omega)
          have hQ' : Q (k - 1) d' ≤ d' + k - 1 + 1 := by
            rw [Q_small (by omega) (by omega)]
            split <;> omega
          have h2 := (ih (!a) b hpar' (d' + k - 1) d' hQ').2 (by omega)
          exact (move_c (by omega) h1 h2).congr (by omega) rfl
      · refine Sh.lift (n := Q k d - 1) ?_ (by omega)
        have h1 : k + 1 ≤ d := by
          by_contra h; rw [Q_of_le (by omega)] at hc; omega
        by_cases h2 : d + 2 ≤ dk k + k + k / 2
        · exact mid true h1 h2 (fun _ => by omega)
        · exact big (by omega) (by omega)

theorem lb : ∀ k, 1 ≤ k → LB k
  | 0, h => absurd h (by omega)
  | 1, _ => lb_one
  | k + 2, _ => lb_step (by omega) (by simpa using lb (k + 1) (by omega))

/-- Theorem 4 for any end labels `a`, `b` with `k ≡ [a ≠ b] (mod 2)`. -/
theorem shatters_pathClass_iff (hk : 1 ≤ k) (hpar : k % 2 = if a = b then 0 else 1) :
    Shatters (pathClass a b k n) d ↔ Q k d ≤ n + 1 :=
  ⟨upper hk n d, fun h => sh_false.mp (lb k hk a b hpar n d h).1⟩

theorem ldim_eq_v {m x : ℕ} {H : Finset (Hyp m)} (hk : 1 ≤ k) (hx : 1 ≤ x)
    (h : ∀ d, Shatters H d ↔ Q k d ≤ x) : ldim H = v k x := by
  have hne : H.Nonempty := ((h 0).mpr (by rw [Q_of_le (Nat.zero_le _)]; omega)).nonempty
  have e : ∀ d, d ≤ ldim H ↔ d ≤ v k x := fun d => by
    rw [← shatters_iff_le_ldim hne, h, le_v_iff (by omega) hx]
  exact le_antisymm ((e _).mp le_rfl) ((e _).mpr le_rfl)

theorem ldim_pathClass (hk : 1 ≤ k) (hpar : k % 2 = if a = b then 0 else 1) (n : ℕ) :
    ldim (pathClass a b k n) = v k (n + 1) :=
  ldim_eq_v hk (by omega) (fun _ => shatters_pathClass_iff hk hpar)

/-- Theorem 4. -/
theorem general (k x : ℕ) (hk : 1 ≤ k) (hx : 1 ≤ x) :
    (Even k → ldim (cyc k x) = v k x) ∧ (Odd k → ldim (gap k x) = v k x) := by
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · exact ldim_pathClass hk (by simpa using Nat.even_iff.mp he) n
  · exact ldim_pathClass hk (by simpa using Nat.odd_iff.mp ho) n

/-- Corollary 5. -/
theorem ldim_unions {j : ℕ} (hj : 1 ≤ j) (m : ℕ) : ldim (unions j m) = v (2 * j) (m + 1) := by
  rw [unions_eq]; exact ldim_pathClass (by omega) (by simp) m

theorem ldim_switchSeq {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    ldim (switchSeq n (2 * j)) = 1 + v (2 * j) n := by
  rw [ldim_switchSeq_even hn, ldim_unions hj, Nat.sub_add_cancel hn]

end ExactLittlestone
