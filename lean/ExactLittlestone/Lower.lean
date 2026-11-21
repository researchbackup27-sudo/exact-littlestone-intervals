import ExactLittlestone.Defs
import ExactLittlestone.Game
import Mathlib.Data.Multiset.MapFold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

namespace ExactLittlestone

open Multiset

def Cut2 : Multiset ℕ → ℕ → Prop
  | S, 0 => ∃ x ∈ S, 2 ≤ x
  | S, d + 1 => ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u + v ∈ S ∧ d ≤ Nat.log 2 u + Nat.log 2 v ∧
      Cut2 (u ::ₘ v ::ₘ S.erase (u + v)) d

theorem cut2_succ {S : Multiset ℕ} {d : ℕ} :
    Cut2 S (d + 1) ↔ ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u + v ∈ S ∧ d ≤ Nat.log 2 u + Nat.log 2 v ∧
      Cut2 (u ::ₘ v ::ₘ S.erase (u + v)) d := Iff.rfl

theorem Cut2.cut : ∀ {S : Multiset ℕ} {d : ℕ}, Cut2 S d → Cut S d
  | _, 0, _ => trivial
  | _, _ + 1, h => by
      obtain ⟨u, v, hu, hv, hm, hval, hr⟩ := cut2_succ.mp h
      exact cut_succ.mpr ⟨u, v, hu, hv, hm, hval, Cut2.cut hr⟩

theorem Cut2.double : ∀ {S : Multiset ℕ} {d : ℕ}, Cut2 S d → Cut2 (S.map (2 * ·)) (d + 2)
  | S, 0, h => by
      obtain ⟨x, hx, h2⟩ := h
      refine cut2_succ.mpr ⟨2, 2 * x - 2, by norm_num, by omega, ?_, ?_, ?_⟩
      · rw [show 2 + (2 * x - 2) = 2 * x by omega]
        exact mem_map_of_mem _ hx
      · have h1 : 1 ≤ Nat.log 2 (2 * x - 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
        have h2 : Nat.log 2 2 = 1 := by decide
        omega
      · refine cut2_succ.mpr ⟨1, 1, by norm_num, by norm_num, by simp, by simp, ?_⟩
        exact ⟨2 * x - 2, by simp, by omega⟩
  | S, d + 1, h => by
      obtain ⟨u, v, hu, hv, hm, hval, hr⟩ := cut2_succ.mp h
      refine cut2_succ.mpr ⟨2 * u, 2 * v, by omega, by omega, ?_, ?_, ?_⟩
      · rw [show 2 * u + 2 * v = 2 * (u + v) by ring]
        exact mem_map_of_mem _ hm
      · rw [log_two_mul hu, log_two_mul hv]
        omega
      · have h2 := Cut2.double hr
        rw [map_cons, map_cons, map_erase _ (mul_right_injective₀ (two_ne_zero)),
          show 2 * (u + v) = 2 * u + 2 * v by ring] at h2
        exact h2

theorem cut2_five : Cut2 {5} 3 := by
  refine cut2_succ.mpr ⟨2, 3, by norm_num, by norm_num, by decide, by decide, ?_⟩
  refine cut2_succ.mpr ⟨1, 2, by norm_num, by norm_num, by decide, by decide, ?_⟩
  refine cut2_succ.mpr ⟨1, 1, by norm_num, by norm_num, by decide, by decide, ?_⟩
  exact ⟨2, by decide, le_rfl⟩

theorem cut2_seven : Cut2 {7} 4 := by
  refine cut2_succ.mpr ⟨3, 4, by norm_num, by norm_num, by decide, by decide, ?_⟩
  refine cut2_succ.mpr ⟨2, 2, by norm_num, by norm_num, by decide, by decide, ?_⟩
  refine cut2_succ.mpr ⟨1, 2, by norm_num, by norm_num, by decide, by decide, ?_⟩
  refine cut2_succ.mpr ⟨1, 1, by norm_num, by norm_num, by decide, by decide, ?_⟩
  exact ⟨2, by decide, le_rfl⟩

theorem P_add_two {d : ℕ} (hd : 3 ≤ d) : P (d + 2) = 2 * P d := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
  rcases k with _ | k
  · decide
  · show P (k + 2 + 4) = 2 * P (k + 4)
    simp only [P]
    have hpar : (k + 2) % 2 = k % 2 := by omega
    rw [hpar]
    split_ifs with h
    · rw [show (k + 2) / 2 = k / 2 + 1 by omega, pow_succ]; ring
    · rw [show (k + 2 - 1) / 2 + 1 = (k - 1) / 2 + 1 + 1 by omega, pow_succ]; ring

theorem cut2_P : ∀ d, 3 ≤ d → Cut2 {P d} d
  | 3, _ => cut2_five
  | 4, _ => cut2_seven
  | d + 5, _ => by
      have ih := cut2_P (d + 3) (by omega)
      have h2 := Cut2.double ih
      rw [map_singleton, ← P_add_two (by omega : 3 ≤ d + 3)] at h2
      exact h2

theorem cut_of_P_le {d ℓ : ℕ} (h : P d ≤ ℓ) : Cut {ℓ} d := by
  rcases Nat.lt_or_ge d 3 with hd | hd
  · interval_cases d
    · trivial
    · exact Cut.single_le (cut_succ.mpr ⟨1, 1, by norm_num, by norm_num, by decide, by decide,
        trivial⟩) h
    · refine Cut.single_le (cut_succ.mpr ⟨1, 2, by norm_num, by norm_num, by decide, by decide,
        cut_succ.mpr ⟨1, 1, by norm_num, by norm_num, by decide, by decide, trivial⟩⟩) h
  · exact Cut.single_le (cut2_P d hd).cut h

end ExactLittlestone
