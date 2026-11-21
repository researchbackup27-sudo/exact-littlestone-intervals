import ExactLittlestone.SwBasic

namespace ExactLittlestone

open Finset

theorem Shatters.two_pow_le_card {m d : ℕ} {H : Finset (Hyp m)} (h : Shatters H d) :
    2 ^ d ≤ H.card := by
  induction d generalizing H with
  | zero => simpa using h.card_pos
  | succ d ih =>
    obtain ⟨x, h0, h1⟩ := shatters_succ.mp h
    have hd : Disjoint (restrict H x false) (restrict H x true) := by
      rw [Finset.disjoint_left]
      intro g hg0 hg1
      rw [mem_restrict] at hg0 hg1
      rw [hg0.2] at hg1
      exact Bool.false_ne_true hg1.2
    have hs : restrict H x false ∪ restrict H x true ⊆ H :=
      union_subset (restrict_subset H x false) (restrict_subset H x true)
    have := card_le_card hs
    rw [card_union_of_disjoint hd] at this
    have := ih h0
    have := ih h1
    rw [pow_succ]
    omega

theorem switches_cons_ofFn {n : ℕ} (a : Bool) (g : Fin (n + 1) → Bool) :
    switches (a :: List.ofFn g) = (if a = g 0 then 0 else 1) + switches (List.ofFn g) := by
  rw [List.ofFn_succ, switches_cc]

theorem switches_ofFn_succ_succ {n : ℕ} (f : Fin (n + 2) → Bool) :
    switches (List.ofFn f) =
      (if f 0 = Fin.tail f 0 then 0 else 1) + switches (List.ofFn (Fin.tail f)) := by
  rw [List.ofFn_succ]
  exact switches_cons_ofFn _ _

theorem switchSeq_succ_subset (n k : ℕ) :
    switchSeq (n + 2) (k + 1) ⊆
      (switchSeq (n + 1) (k + 1)).image (fun g : Hyp (n + 1) => (Fin.cons (g 0) g : Hyp (n + 2))) ∪
        (switchSeq (n + 1) k).image
          (fun g : Hyp (n + 1) => (Fin.cons (!g 0) g : Hyp (n + 2))) := by
  intro f hf
  simp only [switchSeq, mem_filter, mem_univ, true_and] at hf
  rw [switches_ofFn_succ_succ] at hf
  rw [mem_union]
  by_cases h01 : f 0 = Fin.tail f 0
  · left
    rw [ite_eq_left_of_eq_true _ _ (eq_true h01)] at hf
    refine mem_image.mpr ⟨Fin.tail f, ?_, ?_⟩
    · simp only [switchSeq, mem_filter, mem_univ, true_and]
      omega
    · rw [← h01]
      exact Fin.cons_self_tail f
  · right
    rw [ite_eq_right_of_eq_false _ _ (eq_false h01)] at hf
    refine mem_image.mpr ⟨Fin.tail f, ?_, ?_⟩
    · simp only [switchSeq, mem_filter, mem_univ, true_and]
      omega
    · have hne : (!Fin.tail f 0) = f 0 := by
        cases h : f 0 <;> cases h' : Fin.tail f 0 <;> simp_all
      show Fin.cons (!Fin.tail f 0) (Fin.tail f) = f
      rw [hne]
      exact Fin.cons_self_tail f

theorem switchSeq_zero_subset (n : ℕ) :
    switchSeq (n + 2) 0 ⊆
      (switchSeq (n + 1) 0).image (fun g : Hyp (n + 1) => (Fin.cons (g 0) g : Hyp (n + 2))) := by
  intro f hf
  simp only [switchSeq, mem_filter, mem_univ, true_and] at hf
  rw [switches_ofFn_succ_succ] at hf
  have h01 : f 0 = Fin.tail f 0 := by
    by_contra h01
    rw [ite_eq_right_of_eq_false _ _ (eq_false h01)] at hf
    omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true h01)] at hf
  refine mem_image.mpr ⟨Fin.tail f, ?_, ?_⟩
  · simp only [switchSeq, mem_filter, mem_univ, true_and]
    omega
  · rw [← h01]
    exact Fin.cons_self_tail f

theorem card_hyp_one : (univ : Finset (Hyp 1)).card = 2 := by
  rw [card_univ]
  rfl

theorem card_switchSeq_zero_le (n : ℕ) : (switchSeq (n + 1) 0).card ≤ 2 := by
  induction n with
  | zero => exact (card_le_univ _).trans card_hyp_one.le
  | succ n ih =>
    exact ((card_le_card (switchSeq_zero_subset n)).trans card_image_le).trans ih

theorem card_switchSeq_one_le {n : ℕ} (hn : 1 ≤ n) : (switchSeq n 1).card ≤ 2 * n := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction n with
  | zero => exact (card_le_univ _).trans card_hyp_one.le
  | succ n ih =>
    have h1 := (card_le_card (switchSeq_succ_subset n 0)).trans (card_union_le _ _)
    have h3 : ((switchSeq (n + 1) (0 + 1)).image
        (fun g : Hyp (n + 1) => (Fin.cons (g 0) g : Hyp (n + 2)))).card ≤
        (switchSeq (n + 1) 1).card := card_image_le
    have h4 : ((switchSeq (n + 1) 0).image
        (fun g : Hyp (n + 1) => (Fin.cons (!g 0) g : Hyp (n + 2)))).card ≤
        (switchSeq (n + 1) 0).card := card_image_le
    have h5 := card_switchSeq_zero_le n
    have h6 : (switchSeq (n + 1 + 1) 1).card = (switchSeq (n + 2) (0 + 1)).card := rfl
    omega

end ExactLittlestone
