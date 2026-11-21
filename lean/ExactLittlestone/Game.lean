import Mathlib.Data.Nat.Log
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic.NormNum

namespace ExactLittlestone

open Multiset

def Cut : Multiset ℕ → ℕ → Prop
  | _, 0 => True
  | S, d + 1 => ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u + v ∈ S ∧ d ≤ Nat.log 2 u + Nat.log 2 v ∧
      Cut (u ::ₘ v ::ₘ S.erase (u + v)) d

theorem cut_succ {S : Multiset ℕ} {d : ℕ} :
    Cut S (d + 1) ↔ ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u + v ∈ S ∧ d ≤ Nat.log 2 u + Nat.log 2 v ∧
      Cut (u ::ₘ v ::ₘ S.erase (u + v)) d := Iff.rfl

theorem Cut.pred : ∀ {S : Multiset ℕ} {d : ℕ}, Cut S (d + 1) → Cut S d
  | _, 0, _ => trivial
  | _, _ + 1, h => by
      obtain ⟨u, v, hu, hv, hmem, hval, hrest⟩ := cut_succ.mp h
      exact cut_succ.mpr ⟨u, v, hu, hv, hmem, by omega, Cut.pred hrest⟩

theorem Cut.mono {S : Multiset ℕ} {d e : ℕ} (h : Cut S d) (hed : e ≤ d) : Cut S e := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hed
  clear hed
  induction k with
  | zero => simpa using h
  | succ k ih => exact ih (Cut.pred (by simpa [Nat.add_assoc] using h))

theorem Cut.grow : ∀ {S : Multiset ℕ} {d x : ℕ}, Cut S d → x ∈ S → Cut ((x + 1) ::ₘ S.erase x) d
  | _, 0, _, _, _ => trivial
  | S, d + 1, x, h, hx => by
      obtain ⟨u, v, hu, hv, hmem, hval, hrest⟩ := cut_succ.mp h
      by_cases hxy : x = u + v
      · subst hxy
        refine cut_succ.mpr ⟨u + 1, v, by omega, hv, ?_, ?_, ?_⟩
        · rw [show u + 1 + v = u + v + 1 by omega]; exact mem_cons_self _ _
        · have := Nat.log_mono_right (b := 2) (show u ≤ u + 1 by omega); omega
        · have h2 := Cut.grow hrest (mem_cons_self u _)
          rw [show u + 1 + v = u + v + 1 by omega, erase_cons_head]
          simpa [erase_cons_head] using h2
      ·
        have hyT : u + v ∈ S.erase x := (mem_erase_of_ne (Ne.symm hxy)).mpr hmem
        refine cut_succ.mpr ⟨u, v, hu, hv, mem_cons_of_mem hyT, hval, ?_⟩
        have hxS' : x ∈ u ::ₘ v ::ₘ S.erase (u + v) :=
          mem_cons_of_mem (mem_cons_of_mem ((mem_erase_of_ne hxy).mpr hx))
        have h2 := Cut.grow hrest hxS'
        rw [erase_cons_tail_of_mem hyT]
        have e1 : (u ::ₘ v ::ₘ S.erase (u + v)).erase x = u ::ₘ v ::ₘ (S.erase (u + v)).erase x := by
          rw [erase_cons_tail_of_mem (mem_cons_of_mem ((mem_erase_of_ne hxy).mpr hx)),
            erase_cons_tail_of_mem ((mem_erase_of_ne hxy).mpr hx)]
        rw [e1] at h2
        have e2 : (S.erase (u + v)).erase x = (S.erase x).erase (u + v) := erase_comm _ _ _
        rw [e2] at h2
        simpa [cons_swap] using h2

theorem Cut.single_le {ℓ ℓ' d : ℕ} (h : Cut {ℓ} d) (hle : ℓ ≤ ℓ') : Cut {ℓ'} d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have := Cut.grow ih (mem_singleton_self _)
      simpa [Nat.add_assoc] using this

theorem log_two_mul {u : ℕ} (hu : 0 < u) : Nat.log 2 (2 * u) = Nat.log 2 u + 1 := by
  rw [mul_comm]
  exact Nat.log_mul_base (by norm_num) (by omega)

theorem two_pow_le_of_le_log {u p : ℕ} (hu : 0 < u) (h : p ≤ Nat.log 2 u) : 2 ^ p ≤ u :=
  le_trans (Nat.pow_le_pow_right (by norm_num) h) (Nat.pow_log_le_self 2 (by omega))

theorem log_le_of_lt_pow {v p : ℕ} (hv : 0 < v) (h : v < 2 ^ (p + 1)) : Nat.log 2 v ≤ p :=
  Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) h)

theorem Cut.three {ℓ d : ℕ} (h : Cut {ℓ} (d + 3)) :
    ∃ u v a b c e : ℕ, 0 < v ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < e ∧ u + v = ℓ ∧ a + b = u ∧
      d + 2 ≤ Nat.log 2 u + Nat.log 2 v ∧ d + 1 ≤ Nat.log 2 a + Nat.log 2 b ∧
      d ≤ Nat.log 2 c + Nat.log 2 e ∧ (c + e = a ∨ c + e = v) := by
  obtain ⟨x, y, hx, hy, hm, hval, h1⟩ := cut_succ.mp h
  rw [mem_singleton] at hm
  subst hm
  rw [erase_singleton] at h1
  obtain ⟨a, b, ha, hb, hm2, hval2, h2⟩ := cut_succ.mp h1
  rcases mem_cons.mp hm2 with hax | hay
  · rw [hax, erase_cons_head] at h2
    obtain ⟨c, e, hc, he, hm3, hval3, -⟩ := cut_succ.mp h2
    rcases mem_cons.mp hm3 with h3 | h3
    · exact ⟨x, y, a, b, c, e, hy, ha, hb, hc, he, rfl, hax, hval, hval2, hval3, Or.inl h3⟩
    · rcases mem_cons.mp h3 with h4 | h4
      · exact ⟨x, y, b, a, c, e, hy, hb, ha, hc, he, rfl, by omega, hval, by omega, hval3,
          Or.inl h4⟩
      · have h5 : c + e = y := by simpa using h4
        exact ⟨x, y, a, b, c, e, hy, ha, hb, hc, he, rfl, hax, hval, hval2, hval3, Or.inr h5⟩
  · have hay' : a + b = y := by simpa using hay
    rw [hay', show (x ::ₘ y ::ₘ (0 : Multiset ℕ)) = y ::ₘ x ::ₘ 0 from cons_swap _ _ _,
      erase_cons_head] at h2
    obtain ⟨c, e, hc, he, hm3, hval3, -⟩ := cut_succ.mp h2
    rcases mem_cons.mp hm3 with h3 | h3
    · exact ⟨y, x, a, b, c, e, hx, ha, hb, hc, he, by omega, hay', by omega, hval2, hval3,
        Or.inl h3⟩
    · rcases mem_cons.mp h3 with h4 | h4
      · exact ⟨y, x, b, a, c, e, hx, hb, ha, hc, he, by omega, by omega, by omega, by omega, hval3,
          Or.inl h4⟩
      · have h5 : c + e = x := by simpa using h4
        exact ⟨y, x, a, b, c, e, hx, ha, hb, hc, he, by omega, hay', by omega, hval2, hval3,
          Or.inr h5⟩

end ExactLittlestone
