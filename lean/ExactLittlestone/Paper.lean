import ExactLittlestone.Main
import Mathlib.Tactic.IntervalCases

namespace ExactLittlestone

inductive CTree (α : Type) : ℕ → Type
  | leaf : CTree α 0
  | node {n : ℕ} : α → CTree α n → CTree α n → CTree α (n + 1)

def paths {α : Type} : {n : ℕ} → CTree α n → List (List (α × Bool))
  | _, .leaf => [[]]
  | _, .node x l r => (paths l).map ((x, false) :: ·) ++ (paths r).map ((x, true) :: ·)

def ShatTree {m : ℕ} (H : Finset (Hyp m)) {d : ℕ} (t : CTree (Fin m) d) : Prop :=
  ∀ p ∈ paths t, ∃ h ∈ H, ∀ q ∈ p, h q.1 = q.2

/-- `Shatters` agrees with shattering of complete mistake trees. -/
theorem shatters_iff_tree {m : ℕ} : ∀ (d : ℕ) (H : Finset (Hyp m)),
    Shatters H d ↔ ∃ t : CTree (Fin m) d, ShatTree H t
  | 0, H => by
      constructor
      · intro h
        obtain ⟨g, hg⟩ := h
        exact ⟨.leaf, fun p _ => ⟨g, hg, by
          have : p = [] := by simpa [paths] using ‹p ∈ paths CTree.leaf›
          simp [this]⟩⟩
      · rintro ⟨t, ht⟩
        cases t
        obtain ⟨g, hg, -⟩ := ht [] (by simp [paths])
        exact ⟨g, hg⟩
  | d + 1, H => by
      rw [shatters_succ]
      constructor
      · rintro ⟨x, h0, h1⟩
        obtain ⟨l, hl⟩ := (shatters_iff_tree d _).mp h0
        obtain ⟨r, hr⟩ := (shatters_iff_tree d _).mp h1
        refine ⟨.node x l r, ?_⟩
        intro p hp
        simp only [paths, List.mem_append, List.mem_map] at hp
        rcases hp with ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
        · obtain ⟨g, hg, hc⟩ := hl p' hp'
          rw [mem_restrict] at hg
          exact ⟨g, hg.1, by
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hg.2
            · exact hc q hq⟩
        · obtain ⟨g, hg, hc⟩ := hr p' hp'
          rw [mem_restrict] at hg
          exact ⟨g, hg.1, by
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hg.2
            · exact hc q hq⟩
      · rintro ⟨t, ht⟩
        cases t with
        | node x l r =>
          refine ⟨x, (shatters_iff_tree d _).mpr ⟨l, ?_⟩, (shatters_iff_tree d _).mpr ⟨r, ?_⟩⟩
          · intro p hp
            obtain ⟨g, hg, hc⟩ := ht ((x, false) :: p) (by simp [paths, hp])
            exact ⟨g, mem_restrict.mpr ⟨hg, hc (x, false) (by simp)⟩,
              fun q hq => hc q (List.mem_cons_of_mem _ hq)⟩
          · intro p hp
            obtain ⟨g, hg, hc⟩ := ht ((x, true) :: p) (by simp [paths, hp])
            exact ⟨g, mem_restrict.mpr ⟨hg, hc (x, true) (by simp)⟩,
              fun q hq => hc q (List.mem_cons_of_mem _ hq)⟩

theorem main_tree (m d : ℕ) : (∃ t : CTree (Fin m) d, ShatTree (intervals m) t) ↔ P d ≤ m + 1 := by
  rw [← shatters_iff_tree]; exact main m d

theorem mem_intervals_paper {m : ℕ} (h : Hyp m) :
    h ∈ intervals m ↔ (∀ x, h x = false) ∨
      ∃ a b : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ m ∧ ∀ x : Fin m, (h x = true ↔ a ≤ x.val + 1 ∧ x.val + 1 ≤ b) := by
  unfold intervals
  rw [Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨⟨a, b⟩, hp, rfl⟩)
    · exact Or.inl fun _ => rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine Or.inr ⟨a.val + 1, b.val + 1, by omega, by simpa using hp, by have := b.isLt; omega, ?_⟩
      intro x; simp [interval]
  · rintro (h0 | ⟨a, b, ha, hab, hb, hx⟩)
    · exact Or.inl (funext h0)
    · refine Or.inr ⟨(⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.mk_le_mk]; omega
      · funext x
        have := hx x
        by_cases hh : h x = true
        · simp only [interval, hh, decide_eq_true_eq]; have := this.mp hh; omega
        · have h2 : ¬ (a ≤ x.val + 1 ∧ x.val + 1 ≤ b) := fun c => hh (this.mpr c)
          simp only [Bool.not_eq_true] at hh
          simp only [interval, hh, decide_eq_false_iff_not]; omega

theorem P_paper_small : P 0 = 1 ∧ P 1 = 2 ∧ P 2 = 3 ∧ P 3 = 5 := by decide
theorem P_paper_odd (t : ℕ) (ht : 1 ≤ t) : P (2 * t + 1) = 5 * 2 ^ (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rcases s with _ | s
  · decide
  · show P (2 * s + 1 + 4) = _
    simp only [P]
    rw [ite_eq_right (by omega)]
    congr 2; omega
theorem P_paper_even (t : ℕ) (ht : 2 ≤ t) : P (2 * t) = 7 * 2 ^ (t - 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  show P (2 * s + 4) = _
  simp only [P]
  rw [ite_eq_left (by omega)]
  congr 2; omega

theorem P_even_le_iff {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (t : ℕ) : P (2 * t) ≤ ℓ ↔ 7 * 2 ^ t ≤ 4 * ℓ := by
  rcases Nat.lt_or_ge t 2 with ht | ht
  · interval_cases t <;> simp [P] <;> omega
  · rw [P_paper_even t ht]
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
    rw [show s + 2 - 2 = s by omega, pow_add]
    omega

theorem P_odd_le_iff {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (t : ℕ) : P (2 * t + 1) ≤ ℓ ↔ 5 * 2 ^ t ≤ 2 * ℓ := by
  rcases Nat.lt_or_ge t 1 with ht | ht
  · interval_cases t; simp [P]; omega
  · rw [P_paper_odd t ht]
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [show s + 1 - 1 = s by omega, pow_succ]
    omega

/-- Theorem 1, closed form for `m ≥ 3`. -/
theorem ldim_intervals_closed_form (m : ℕ) (hm : 3 ≤ m) :
    ldim (intervals m) =
      max (2 * Nat.log 2 (4 * (m + 1) / 7)) (2 * Nat.log 2 (2 * (m + 1) / 5) + 1) := by
  have hℓ : 4 ≤ m + 1 := by omega
  set E := Nat.log 2 (4 * (m + 1) / 7)
  set O := Nat.log 2 (2 * (m + 1) / 5)
  have hE : ∀ t, t ≤ E ↔ P (2 * t) ≤ m + 1 := by
    intro t
    rw [P_even_le_iff hℓ, Nat.le_log_iff_pow_le (by norm_num) (by omega),
      Nat.le_div_iff_mul_le (by norm_num)]
    omega
  have hO : ∀ t, t ≤ O ↔ P (2 * t + 1) ≤ m + 1 := by
    intro t
    rw [P_odd_le_iff hℓ, Nat.le_log_iff_pow_le (by norm_num) (by omega),
      Nat.le_div_iff_mul_le (by norm_num)]
    omega
  have hG : IsGreatest {d | P d ≤ m + 1} (max (2 * E) (2 * O + 1)) := by
    constructor
    · rcases le_total (2 * E) (2 * O + 1) with h | h
      · rw [max_eq_right h]; exact (hO O).mp le_rfl
      · rw [max_eq_left h]; exact (hE E).mp le_rfl
    · intro d hd
      obtain ⟨t, rfl | rfl⟩ : ∃ t, d = 2 * t ∨ d = 2 * t + 1 := ⟨d / 2, by omega⟩
      · have := (hE t).mpr hd; omega
      · have := (hO t).mpr hd; omega
  exact (ldim_intervals_isGreatest m).unique hG

end ExactLittlestone
