import ExactLittlestone.Basic
import ExactLittlestone.Game
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod

namespace ExactLittlestone

open Finset

variable {m : ℕ}

def rect (m a₁ a₂ b₁ b₂ : ℕ) : Finset (Hyp m) :=
  ((Icc a₁ a₂) ×ˢ (Icc b₁ b₂)).image (fun p => interval p.1 p.2)

theorem interval_true {a b : ℕ} (x : Fin m) : interval a b x = true ↔ a ≤ x.val ∧ x.val ≤ b := by
  simp [interval]

theorem interval_false {a b : ℕ} (x : Fin m) :
    interval a b x = false ↔ ¬ (a ≤ x.val ∧ x.val ≤ b) := by
  simp [interval]

theorem restrict_image {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Hyp m) (x : Fin m)
    (b : Bool) : restrict (s.image f) x b = (s.filter (fun p => f p x = b)).image f := by
  simp [restrict, filter_image]

theorem rect_nonempty {a₁ a₂ b₁ b₂ : ℕ} (h12 : a₁ ≤ a₂) (h34 : b₁ ≤ b₂) :
    (rect m a₁ a₂ b₁ b₂).Nonempty :=
  (Nonempty.product ⟨a₁, mem_Icc.mpr ⟨le_rfl, h12⟩⟩ ⟨b₁, mem_Icc.mpr ⟨le_rfl, h34⟩⟩).image _

section restrict_lemmas

variable {a₁ a₂ b₁ b₂ : ℕ} (x : Fin m)

theorem rect_restrict_a_true (_h1 : a₁ ≤ x.val) (h2 : x.val < a₂) (h3 : a₂ ≤ b₁) :
    restrict (rect m a₁ a₂ b₁ b₂) x true = rect m a₁ x.val b₁ b₂ := by
  unfold rect
  rw [restrict_image]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, interval_true]
  omega

theorem rect_restrict_a_false (h1 : a₁ ≤ x.val) (h2 : x.val < a₂) (h3 : a₂ ≤ b₁) :
    restrict (rect m a₁ a₂ b₁ b₂) x false = rect m (x.val + 1) a₂ b₁ b₂ := by
  unfold rect
  rw [restrict_image]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, interval_false]
  omega

theorem rect_restrict_b_true (h1 : b₁ < x.val) (_h2 : x.val ≤ b₂) (h3 : a₂ ≤ b₁) :
    restrict (rect m a₁ a₂ b₁ b₂) x true = rect m a₁ a₂ x.val b₂ := by
  unfold rect
  rw [restrict_image]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, interval_true]
  omega

theorem rect_restrict_b_false (h1 : b₁ < x.val) (h2 : x.val ≤ b₂) (h3 : a₂ ≤ b₁) :
    restrict (rect m a₁ a₂ b₁ b₂) x false = rect m a₁ a₂ b₁ (x.val - 1) := by
  unfold rect
  rw [restrict_image]
  congr 1
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, interval_false]
  omega

theorem rect_restrict_const (ha : ¬ (a₁ ≤ x.val ∧ x.val < a₂)) (hb : ¬ (b₁ < x.val ∧ x.val ≤ b₂))
    (_h3 : a₂ ≤ b₁) :
    restrict (rect m a₁ a₂ b₁ b₂) x true = ∅ ∨ restrict (rect m a₁ a₂ b₁ b₂) x false = ∅ := by
  unfold rect
  simp only [restrict_image, image_eq_empty, filter_eq_empty_iff, mem_product, mem_Icc,
    interval_true, interval_false, Prod.forall]
  by_cases hin : a₂ ≤ x.val ∧ x.val ≤ b₁
  · right
    intro a b hab
    omega
  · left
    intro a b hab
    omega

end restrict_lemmas

theorem split_up {u₁ u₂ d L : ℕ} (h₁ : 0 < u₁) (h₂ : 0 < u₂) (hd₁ : d ≤ Nat.log 2 u₁ + L)
    (hd₂ : d ≤ Nat.log 2 u₂ + L) : d + 1 ≤ Nat.log 2 (u₁ + u₂) + L := by
  by_cases hdL : d ≤ L
  · have : 1 ≤ Nat.log 2 (u₁ + u₂) := Nat.le_log_of_pow_le (by norm_num) (by omega)
    omega
  · have e₁ := two_pow_le_of_le_log h₁ (show d - L ≤ Nat.log 2 u₁ by omega)
    have e₂ := two_pow_le_of_le_log h₂ (show d - L ≤ Nat.log 2 u₂ by omega)
    have : d - L + 1 ≤ Nat.log 2 (u₁ + u₂) :=
      Nat.le_log_of_pow_le (by norm_num) (by rw [pow_succ]; omega)
    omega

theorem split_down {U : ℕ} (hU : 2 ≤ U) :
    ∃ u₁ u₂, 0 < u₁ ∧ 0 < u₂ ∧ u₁ + u₂ = U ∧ Nat.log 2 U ≤ Nat.log 2 u₁ + 1 ∧
      Nat.log 2 U ≤ Nat.log 2 u₂ + 1 := by
  refine ⟨U / 2, U - U / 2, by omega, by omega, by omega, ?_, ?_⟩
  · rw [Nat.log_div_base]; omega
  · have h1 : Nat.log 2 (U / 2) ≤ Nat.log 2 (U - U / 2) := Nat.log_mono_right (by omega)
    rw [Nat.log_div_base] at h1
    omega

theorem shatters_rect : ∀ {d a₁ a₂ b₁ b₂ : ℕ}, a₁ ≤ a₂ → a₂ ≤ b₁ → b₁ ≤ b₂ → b₂ < m →
    (Shatters (rect m a₁ a₂ b₁ b₂) d ↔
      d ≤ Nat.log 2 (a₂ - a₁ + 1) + Nat.log 2 (b₂ - b₁ + 1))
  | 0, _, _, _, _, h12, _, h34, _ => by
      simp only [Nat.zero_le, iff_true]
      exact rect_nonempty h12 h34
  | d + 1, a₁, a₂, b₁, b₂, h12, h23, h34, h4 => by
      constructor
      · intro h
        obtain ⟨x, h0, h1⟩ := shatters_succ.mp h
        by_cases ha : a₁ ≤ x.val ∧ x.val < a₂
        · rw [rect_restrict_a_false x ha.1 ha.2 h23] at h0
          rw [rect_restrict_a_true x ha.1 ha.2 h23] at h1
          have i0 := (shatters_rect (by omega) (by omega) h34 h4).mp h0
          have i1 := (shatters_rect ha.1 (by omega) h34 h4).mp h1
          have := split_up (d := d) (u₁ := x.val - a₁ + 1) (u₂ := a₂ - (x.val + 1) + 1) (by omega)
            (by omega) i1 i0
          rwa [show x.val - a₁ + 1 + (a₂ - (x.val + 1) + 1) = a₂ - a₁ + 1 by omega] at this
        · by_cases hb : b₁ < x.val ∧ x.val ≤ b₂
          · rw [rect_restrict_b_false x hb.1 hb.2 h23] at h0
            rw [rect_restrict_b_true x hb.1 hb.2 h23] at h1
            have i0 := (shatters_rect h12 h23 (by omega) (by omega)).mp h0
            have i1 := (shatters_rect h12 (by omega) hb.2 h4).mp h1
            have := split_up (d := d) (u₁ := x.val - 1 - b₁ + 1) (u₂ := b₂ - x.val + 1)
              (L := Nat.log 2 (a₂ - a₁ + 1)) (by omega) (by omega) (by omega) (by omega)
            rw [show x.val - 1 - b₁ + 1 + (b₂ - x.val + 1) = b₂ - b₁ + 1 by omega] at this
            omega
          · rcases rect_restrict_const x ha hb h23 with he | he
            · rw [he] at h1; exact absurd h1 not_shatters_empty
            · rw [he] at h0; exact absurd h0 not_shatters_empty
      · intro hd
        by_cases hA : 1 ≤ Nat.log 2 (a₂ - a₁ + 1)
        · have hA2 : 2 ≤ a₂ - a₁ + 1 := by
            have := two_pow_le_of_le_log (by omega) hA
            simpa using this
          obtain ⟨u₁, u₂, hu₁, hu₂, hsum, hl₁, hl₂⟩ := split_down hA2
          let x : Fin m := ⟨a₁ + u₁ - 1, by omega⟩
          refine shatters_succ.mpr ⟨x, ?_, ?_⟩
          · rw [rect_restrict_a_false x (by simp [x]; omega) (by simp [x]; omega) h23]
            refine (shatters_rect (by simp [x]; omega) h23 h34 h4).mpr ?_
            rw [show a₂ - (x.val + 1) + 1 = u₂ by simp [x]; omega]
            omega
          · rw [rect_restrict_a_true x (by simp [x]; omega) (by simp [x]; omega) h23]
            refine (shatters_rect (by simp [x]; omega) (by simp [x]; omega) h34 h4).mpr ?_
            rw [show x.val - a₁ + 1 = u₁ by simp [x]; omega]
            omega
        · have hB : d + 1 ≤ Nat.log 2 (b₂ - b₁ + 1) := by omega
          have hB2 : 2 ≤ b₂ - b₁ + 1 := by
            have := two_pow_le_of_le_log (by omega) (show 1 ≤ Nat.log 2 (b₂ - b₁ + 1) by omega)
            simpa using this
          obtain ⟨u₁, u₂, hu₁, hu₂, hsum, hl₁, hl₂⟩ := split_down hB2
          let x : Fin m := ⟨b₁ + u₁, by omega⟩
          refine shatters_succ.mpr ⟨x, ?_, ?_⟩
          · rw [rect_restrict_b_false x (by simp [x]; omega) (by simp [x]; omega) h23]
            refine (shatters_rect h12 h23 (by simp [x]; omega) (by omega)).mpr ?_
            rw [show x.val - 1 - b₁ + 1 = u₁ by simp [x]; omega]
            omega
          · rw [rect_restrict_b_true x (by simp [x]; omega) (by simp [x]; omega) h23]
            refine (shatters_rect h12 (by simp [x]; omega) (by simp [x]; omega) h4).mpr ?_
            rw [show b₂ - x.val + 1 = u₂ by simp [x]; omega]
            omega

theorem shatters_rect_point {d lo x hi : ℕ} (h1 : lo ≤ x) (h2 : x ≤ hi) (h3 : hi < m) :
    Shatters (rect m lo x x hi) d ↔ d ≤ Nat.log 2 (x - lo + 1) + Nat.log 2 (hi - x + 1) :=
  shatters_rect h1 le_rfl h2 h3

end ExactLittlestone
