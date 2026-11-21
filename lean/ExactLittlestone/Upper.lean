import ExactLittlestone.Defs
import ExactLittlestone.Game
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ExactLittlestone

open Multiset

def cmin (e : ℕ) : ℕ := if e % 2 = 0 then 2 ^ (e / 2 + 1) else 3 * 2 ^ (e / 2)

theorem cmin_even (p : ℕ) : cmin (2 * p) = 2 * 2 ^ p := by
  unfold cmin
  rw [ite_eq_left (by omega), show 2 * p / 2 + 1 = p + 1 by omega, pow_succ]
  ring

theorem cmin_odd (p : ℕ) : cmin (2 * p + 1) = 3 * 2 ^ p := by
  unfold cmin
  rw [ite_eq_right (by omega), show (2 * p + 1) / 2 = p by omega]

theorem pow_two_add (p k : ℕ) : 2 ^ (p + k) = 2 ^ k * 2 ^ p := by
  rw [pow_add, mul_comm]

theorem cmin_le_pow {α β e : ℕ} (h : e ≤ α + β) : cmin e ≤ 2 ^ α + 2 ^ β := by
  wlog hab : α ≤ β generalizing α β
  · have := this (α := β) (β := α) (by omega) (by omega)
    omega
  have pa : 0 < 2 ^ α := by positivity
  have pb : 0 < 2 ^ β := by positivity
  obtain ⟨p, hp | hp⟩ : ∃ p, e = 2 * p ∨ e = 2 * p + 1 := ⟨e / 2, by omega⟩
  · subst hp
    rw [cmin_even]
    rcases Nat.lt_or_ge α p with h1 | h1
    · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show p + 1 ≤ β by omega)
      rw [pow_two_add] at this
      omega
    · have a1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h1
      have a2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show p ≤ β by omega)
      omega
  · subst hp
    rw [cmin_odd]
    rcases Nat.lt_or_ge α p with h1 | h1
    · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show p + 2 ≤ β by omega)
      rw [pow_two_add] at this
      norm_num at this
      omega
    · have a1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h1
      have a2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show p + 1 ≤ β by omega)
      rw [pow_two_add] at a2
      omega

theorem cmin_le {a b e : ℕ} (ha : 0 < a) (hb : 0 < b) (h : e ≤ Nat.log 2 a + Nat.log 2 b) :
    cmin e ≤ a + b := by
  have h1 := cmin_le_pow h
  have h2 := Nat.pow_log_le_self 2 (show a ≠ 0 by omega)
  have h3 := Nat.pow_log_le_self 2 (show b ≠ 0 by omega)
  omega

theorem P_three (k : ℕ) : P (k + 3) = cmin (k + 1) + cmin k := by
  obtain ⟨p, hp | hp⟩ : ∃ p, k = 2 * p ∨ k = 2 * p + 1 := ⟨k / 2, by omega⟩
  · subst hp
    rw [cmin_odd, cmin_even]
    rcases p with _ | p
    · decide
    · show P ((2 * p + 1) + 4) = 3 * 2 ^ (p + 1) + 2 * 2 ^ (p + 1)
      simp only [P]
      rw [ite_eq_right (by omega), show (2 * p + 1 - 1) / 2 + 1 = p + 1 by omega]
      ring
  · subst hp
    rw [show 2 * p + 1 + 1 = 2 * (p + 1) by ring, cmin_even, cmin_odd]
    show P ((2 * p) + 4) = 2 * 2 ^ (p + 1) + 3 * 2 ^ p
    simp only [P]
    rw [ite_eq_left (by omega), show 2 * p / 2 = p by omega, pow_succ]
    ring

theorem case_inside {k u v a b : ℕ} (hv : 0 < v) (ha : 0 < a) (hb : 0 < b) (hab : a + b = u)
    (h1 : k + 2 ≤ Nat.log 2 u + Nat.log 2 v) (h2 : k + 1 ≤ Nat.log 2 a + Nat.log 2 b)
    (h3 : cmin k ≤ a) : cmin (k + 1) + cmin k ≤ u + v := by
  have hu : 0 < u := by omega
  have hu2 := cmin_le ha hb h2
  obtain ⟨p, hp | hp⟩ : ∃ p, k = 2 * p ∨ k = 2 * p + 1 := ⟨k / 2, by omega⟩
  · subst hp
    rw [cmin_odd, cmin_even] at *
    by_cases hv2 : 2 * 2 ^ p ≤ v
    · omega
    · have hβ : Nat.log 2 v ≤ p := log_le_of_lt_pow hv (by rw [pow_succ]; omega)
      by_cases hβp : p ≤ Nat.log 2 v
      · have hα : p + 2 ≤ Nat.log 2 u := by omega
        have := two_pow_le_of_le_log hu hα
        have := two_pow_le_of_le_log hv hβp
        rw [pow_two_add] at *
        norm_num at *
        omega
      · have hα : p + 3 ≤ Nat.log 2 u := by omega
        have := two_pow_le_of_le_log hu hα
        rw [pow_two_add] at this
        norm_num at this
        omega
  · subst hp
    rw [show 2 * p + 1 + 1 = 2 * (p + 1) by ring, cmin_even, cmin_odd] at *
    by_cases hv3 : 3 * 2 ^ p ≤ v
    · rw [pow_succ] at hu2
      omega
    · have hβ : Nat.log 2 v ≤ p + 1 := log_le_of_lt_pow hv (by rw [pow_succ, pow_succ]; omega)
      by_cases hα3 : p + 3 ≤ Nat.log 2 u
      · have := two_pow_le_of_le_log hu hα3
        rw [pow_two_add] at this
        norm_num at this
        omega
      · have hα : Nat.log 2 u = p + 2 := by omega
        have hβ1 : p + 1 ≤ Nat.log 2 v := by omega
        have hv2 := two_pow_le_of_le_log hv hβ1
        rw [pow_two_add] at hv2
        norm_num at hv2
        have hau : Nat.log 2 a ≤ p + 2 := hα ▸ Nat.log_mono_right (by omega)
        by_cases ha1 : Nat.log 2 a ≤ p + 1
        · have hb1 := two_pow_le_of_le_log hb (show p + 1 ≤ Nat.log 2 b by omega)
          rw [pow_two_add] at hb1
          norm_num at hb1
          omega
        · have ha4 := two_pow_le_of_le_log ha (show p + 2 ≤ Nat.log 2 a by omega)
          have hb1 := two_pow_le_of_le_log hb (show p ≤ Nat.log 2 b by omega)
          rw [pow_two_add] at ha4
          norm_num at ha4
          omega

theorem P_le_of_cut {ℓ d : ℕ} (hℓ : 0 < ℓ) (h : Cut {ℓ} d) : P d ≤ ℓ := by
  match d, h with
  | 0, _ => show 1 ≤ ℓ; omega
  | 1, h =>
      obtain ⟨u, v, hu, hv, hm, -, -⟩ := cut_succ.mp h
      rw [mem_singleton] at hm
      show 2 ≤ ℓ
      omega
  | 2, h =>
      obtain ⟨u, v, hu, hv, hm, hval, -⟩ := cut_succ.mp h
      rw [mem_singleton] at hm
      show 3 ≤ ℓ
      by_contra hc
      have hu1 : Nat.log 2 u = 0 := Nat.log_of_lt (by omega)
      have hv1 : Nat.log 2 v = 0 := Nat.log_of_lt (by omega)
      omega
  | k + 3, h =>
      obtain ⟨u, v, a, b, c, e, hv, ha, hb, hc, he, huv, hab, h1, h2, h3, hq⟩ := Cut.three h
      rw [P_three, ← huv]
      rcases hq with hq | hq
      · exact case_inside hv ha hb hab h1 h2 (hq ▸ cmin_le hc he h3)
      · have hu := cmin_le ha hb h2
        have hvv := cmin_le hc he h3
        omega

end ExactLittlestone
