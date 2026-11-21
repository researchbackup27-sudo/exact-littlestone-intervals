import ExactLittlestone.SwBasic

namespace ExactLittlestone

open Finset

theorem length_filterMap_lt' {α β : Type*} (f : α → Option β) {l : List α} {a : α}
    (ha : a ∈ l) (hf : f a = none) : (l.filterMap f).length < l.length := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    rcases List.mem_cons.mp ha with h | ht
    · subst h
      rw [List.filterMap_cons, hf]
      simpa using Nat.lt_succ_of_le (List.length_filterMap_le f t)
    · have := ih ht
      rcases hfx : f x with _ | b
      · rw [List.filterMap_cons_none hfx]; simp only [List.length_cons]; omega
      · rw [List.filterMap_cons_some hfx]; simp only [List.length_cons]; omega

theorem switches_ff (l : List Bool) : switches (false :: false :: l) = switches (false :: l) := by
  simp [switches_cc]

theorem switches_ftt (l : List Bool) :
    switches (false :: true :: true :: l) = switches (false :: true :: l) := by
  simp [switches_cc]

theorem switches_ftf (l : List Bool) :
    switches (false :: true :: false :: l) = 2 + switches (false :: false :: l) := by
  simp [switches_cc]; omega

theorem switches_append_bounds : ∀ (A B : List Bool),
    switches A + switches B ≤ switches (A ++ B) ∧ switches (A ++ B) ≤ switches A + switches B + 1
  | [], B => by simp
  | [x], [] => by simp
  | [x], b :: B => by
      simp only [List.cons_append, List.nil_append, switches_cc, switches_single]
      split <;> omega
  | x :: y :: t, B => by
      have := switches_append_bounds (y :: t) B
      simp only [List.cons_append] at this ⊢
      rw [switches_cc, switches_cc]
      omega

def shiftDown (p : ℕ × ℕ) : Option (ℕ × ℕ) := if p.2 = 0 then none else some (p.1 - 1, p.2 - 1)

theorem cov_to_switches : ∀ (L : List Bool) (T : List (ℕ × ℕ)),
    (∀ i, L.getD i false = true ↔ ∃ p ∈ T, p.1 ≤ i ∧ i ≤ p.2) →
    switches (false :: L ++ [false]) ≤ 2 * T.length
  | [], _, _ => by simp [switches_cc]
  | x :: L, T, hT => by
    have hc : ∀ i, L.getD i false = true ↔ ∃ q ∈ T.filterMap shiftDown, q.1 ≤ i ∧ i ≤ q.2 := by
      intro i
      rw [show L.getD i false = (x :: L).getD (i + 1) false by simp, hT]
      simp only [List.mem_filterMap, shiftDown]
      constructor
      · rintro ⟨p, hp, h1, h2⟩
        exact ⟨(p.1 - 1, p.2 - 1), ⟨p, hp, by simp [show p.2 ≠ 0 by omega]⟩, by dsimp; omega,
          by dsimp; omega⟩
      · rintro ⟨q, ⟨p, hp, hpq⟩, h1, h2⟩
        by_cases h0 : p.2 = 0
        · simp [h0] at hpq
        · simp only [h0, ↓reduceIte, Option.some.injEq] at hpq
          subst hpq
          dsimp at h1 h2
          exact ⟨p, hp, by omega, by omega⟩
    have ih := cov_to_switches L _ hc
    have hle := List.length_filterMap_le shiftDown T
    rcases x with _ | _
    · simp only [List.cons_append, switches_ff] at ih ⊢; omega
    · rcases L with _ | ⟨y, L⟩
      · obtain ⟨p, hp, -⟩ := (hT 0).mp rfl
        have h2 : switches (false :: [true] ++ [false]) = 2 := rfl
        have := List.length_pos_of_mem hp
        omega
      · rcases y with _ | _
        · obtain ⟨p, hp, h1, h2⟩ := (hT 0).mp rfl
          have hp2 : p.2 = 0 := by
            by_contra hne
            have := (hT 1).mpr ⟨p, hp, by omega, by omega⟩
            simp at this
          have hlt := length_filterMap_lt' shiftDown hp (by simp [shiftDown, hp2])
          simp only [List.cons_append] at ih ⊢
          rw [switches_ftf]
          omega
        · simp only [List.cons_append] at ih ⊢
          rw [switches_ftt]
          omega

theorem switches_to_cov : ∀ (L : List Bool) (j : ℕ), switches (false :: L ++ [false]) ≤ 2 * j →
    ∃ T : List (ℕ × ℕ), T.length ≤ j ∧ ∀ i, L.getD i false = true ↔ ∃ p ∈ T, p.1 ≤ i ∧ i ≤ p.2
  | [], j, _ => ⟨[], by simp, by simp⟩
  | false :: L, j, h => by
      simp only [List.cons_append, switches_ff] at h
      obtain ⟨T, hl, hT⟩ := switches_to_cov L j (by simpa only [List.cons_append] using h)
      refine ⟨T.map (fun p => (p.1 + 1, p.2 + 1)), by simpa using hl, fun i => ?_⟩
      cases i with
      | zero => simp
      | succ i => rw [List.getD_cons_succ, hT]; simp
  | [true], j, h => by
      have h2 : switches (false :: [true] ++ [false]) = 2 := rfl
      refine ⟨[(0, 0)], by simp; omega, fun i => ?_⟩
      cases i <;> simp
  | true :: true :: L, j, h => by
      simp only [List.cons_append, switches_ftt] at h
      obtain ⟨T, hl, hT⟩ := switches_to_cov (true :: L) j (by simpa only [List.cons_append] using h)
      refine ⟨T.map (fun p => (if p.1 = 0 then 0 else p.1 + 1, p.2 + 1)),
        by simpa using hl, fun i => ?_⟩
      cases i with
      | zero =>
        obtain ⟨p, hp, h1, -⟩ := (hT 0).mp rfl
        simp only [List.getD_cons_zero, true_iff]
        exact ⟨_, List.mem_map_of_mem hp, by simp; omega, by simp⟩
      | succ i =>
        rw [List.getD_cons_succ, hT]
        constructor
        · rintro ⟨p, hp, h1, h2⟩
          exact ⟨_, List.mem_map_of_mem hp, by dsimp; split_ifs <;> omega, by dsimp; omega⟩
        · rintro ⟨q, hq, h1, h2⟩
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
          dsimp at h1 h2
          exact ⟨p, hp, by split_ifs at h1 <;> omega, by omega⟩
  | true :: false :: L, j, h => by
      simp only [List.cons_append, switches_ftf] at h
      obtain ⟨T, hl, hT⟩ := switches_to_cov (false :: L) (j - 1) (by simp only [List.cons_append]; omega)
      refine ⟨(0, 0) :: T.map (fun p => (p.1 + 1, p.2 + 1)), by simp; omega, fun i => ?_⟩
      cases i with
      | zero => simp
      | succ i => rw [List.getD_cons_succ, hT]; simp

theorem getD_ofFn_iff {m : ℕ} (h : Hyp m) (i : ℕ) :
    (List.ofFn h).getD i false = true ↔ ∃ x : Fin m, x.val = i ∧ h x = true := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hi : i < m
  · simp [hi]
    exact ⟨fun hh => ⟨⟨i, hi⟩, rfl, hh⟩, fun ⟨x, hx, hh⟩ => by subst hx; exact hh⟩
  · simp only [hi]
    simp
    intro x hx
    have := x.isLt
    omega

theorem intervals_to_list {m : ℕ} (S : Finset (Hyp m)) (hS : S ⊆ intervals m) :
    ∃ T : List (ℕ × ℕ), T.length ≤ S.card ∧
      ∀ i, (∃ I ∈ S, ∃ x : Fin m, x.val = i ∧ I x = true) ↔ ∃ p ∈ T, p.1 ≤ i ∧ i ≤ p.2 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp⟩
  | insert I S hI ih =>
    obtain ⟨T, hl, hT⟩ := ih ((Finset.subset_insert _ _).trans hS)
    have hIm := hS (Finset.mem_insert_self I S)
    simp only [intervals, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hIm
    rw [Finset.card_insert_of_notMem hI]
    rcases hIm with rfl | ⟨⟨a, b⟩, hab, rfl⟩
    · refine ⟨T, by omega, fun i => ?_⟩
      rw [Finset.exists_mem_insert, ← hT]
      simp
    · refine ⟨(a.val, b.val) :: T, by simp; omega, fun i => ?_⟩
      rw [Finset.exists_mem_insert, hT]
      simp only [List.mem_cons, exists_eq_or_imp]
      have := b.isLt
      refine or_congr_left ⟨fun ⟨x, hx, hh⟩ => ?_, fun hh => ⟨⟨i, by omega⟩, rfl, ?_⟩⟩
      · simp [interval] at hh; omega
      · simp [interval]; omega

theorem unions_iff_cov {j m : ℕ} (h : Hyp m) : h ∈ unions j m ↔ ∃ T : List (ℕ × ℕ),
    T.length ≤ j ∧ ∀ i, (List.ofFn h).getD i false = true ↔ ∃ p ∈ T, p.1 ≤ i ∧ i ≤ p.2 := by
  simp only [unions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
  constructor
  · rintro ⟨S, hS, hc, hh⟩
    obtain ⟨T, hl, hT⟩ := intervals_to_list S hS
    refine ⟨T, hl.trans hc, fun i => ?_⟩
    rw [getD_ofFn_iff, ← hT]
    constructor
    · rintro ⟨x, hx, hx'⟩
      obtain ⟨I, hI, hIx⟩ := (hh x).mp hx'
      exact ⟨I, hI, x, hx, hIx⟩
    · rintro ⟨I, hI, x, hx, hIx⟩
      exact ⟨x, hx, (hh x).mpr ⟨I, hI, hIx⟩⟩
  · rintro ⟨T, hl, hT⟩
    refine ⟨(T.map (fun p => (interval p.1 p.2 : Hyp m))).toFinset, ?_, ?_, fun x => ?_⟩
    · intro I hI
      simp only [List.mem_toFinset, List.mem_map] at hI
      obtain ⟨p, hp, rfl⟩ := hI
      by_cases hp12 : p.1 ≤ p.2
      · obtain ⟨y, hy, -⟩ := (getD_ofFn_iff h p.2).mp ((hT p.2).mpr ⟨p, hp, hp12, le_rfl⟩)
        have hy' := y.isLt
        apply Finset.mem_insert_of_mem
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(⟨p.1, by omega⟩, ⟨p.2, by omega⟩), Fin.mk_le_mk.mpr hp12, rfl⟩
      · have : (interval p.1 p.2 : Hyp m) = fun _ => false := by
          funext z; simp [interval]; omega
        rw [this]
        exact Finset.mem_insert_self _ _
    · exact (List.toFinset_card_le _).trans (by simpa using hl)
    · have := hT x.val
      rw [getD_ofFn_iff] at this
      simp only [List.mem_toFinset, List.mem_map]
      constructor
      · intro hx
        obtain ⟨p, hp, h1, h2⟩ := this.mp ⟨x, rfl, hx⟩
        exact ⟨_, ⟨p, hp, rfl⟩, by simp [interval]; omega⟩
      · rintro ⟨I, ⟨p, hp, rfl⟩, hI⟩
        simp [interval] at hI
        obtain ⟨y, hy, hy'⟩ := this.mpr ⟨p, hp, hI⟩
        rwa [Fin.ext hy] at hy'

theorem unions_eq (j m : ℕ) : unions j m = pathClass false false (2 * j) m := by
  ext h
  rw [unions_iff_cov, mem_pathClass]
  constructor
  · rintro ⟨T, hl, hT⟩
    have := cov_to_switches _ T hT
    omega
  · exact switches_to_cov _ j

def rot {n : ℕ} (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  ⟨if p.val + 1 + i.val ≤ n then p.val + 1 + i.val else i.val + p.val - n, by split_ifs <;> omega⟩

def unrot {n : ℕ} (p : Fin (n + 1)) (y : Fin (n + 1)) : ℕ :=
  if p.val < y.val then y.val - p.val - 1 else y.val + n - p.val

theorem unrot_rot {n : ℕ} (p : Fin (n + 1)) (i : Fin n) : unrot p (rot p i) = i.val := by
  have := i.isLt; have := p.isLt
  simp only [unrot, rot]; split_ifs <;> omega

theorem unrot_self {n : ℕ} (p : Fin (n + 1)) : unrot p p = n := by
  simp [unrot]

theorem unrot_lt {n : ℕ} (p : Fin (n + 1)) {y : Fin (n + 1)} (hy : y ≠ p) : unrot p y < n := by
  have := y.isLt; have := Fin.val_ne_of_ne hy
  simp only [unrot]; split_ifs <;> omega

theorem rot_unrot {n : ℕ} (p : Fin (n + 1)) {y : Fin (n + 1)} (hy : unrot p y < n) :
    rot p ⟨unrot p y, hy⟩ = y := by
  have := y.isLt; have := p.isLt
  ext; simp only [unrot, rot] at hy ⊢; split_ifs at hy ⊢ <;> omega

theorem ofFn_rot {n : ℕ} (p : Fin (n + 1)) (h : Hyp (n + 1)) :
    List.ofFn (fun i => h (rot p i)) =
      (List.ofFn h).drop (p.val + 1) ++ (List.ofFn h).take p.val := by
  have := p.isLt
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    rw [List.getElem_ofFn, List.getElem_append]
    split_ifs with hi
    · rw [List.getElem_drop, List.getElem_ofFn]
      congr 1; ext; simp only [rot]; simp at hi; split_ifs <;> omega
    · rw [List.getElem_take, List.getElem_ofFn]
      congr 1; ext; simp only [rot]; simp at hi ⊢; split_ifs <;> omega

theorem switches_rot {n j : ℕ} (p : Fin (n + 1)) {h : Hyp (n + 1)} (hp : h p = false) :
    switches (List.ofFn h) ≤ 2 * j ↔
      switches (false :: List.ofFn (fun i => h (rot p i)) ++ [false]) ≤ 2 * j := by
  have hlen : p.val < (List.ofFn h).length := by simp
  have hsplit : List.ofFn h = (List.ofFn h).take p.val ++ false :: (List.ofFn h).drop (p.val + 1) := by
    conv_lhs => rw [← List.take_append_drop p.val (List.ofFn h)]
    rw [List.drop_eq_getElem_cons hlen, List.getElem_ofFn]
    simp [hp]
  rw [ofFn_rot]
  set L₁ := (List.ofFn h).take p.val
  set L₂ := (List.ofFn h).drop (p.val + 1)
  rw [hsplit, switches_append]
  have hb := switches_append_bounds (false :: L₂) (L₁ ++ [false])
  have hm := switches_mod_two false false (L₂ ++ L₁)
  simp only [List.cons_append, List.append_assoc, ite_true] at hb hm ⊢
  have := switches_append_bounds L₁ [false]
  omega

theorem shatters_restrict_false {n j : ℕ} (p : Fin (n + 1)) (d : ℕ) :
    Shatters (restrict (switchSeq (n + 1) (2 * j)) p false) d ↔
      Shatters (pathClass false false (2 * j) n) d := by
  have hmem : ∀ h : Hyp (n + 1), h ∈ restrict (switchSeq (n + 1) (2 * j)) p false ↔
      h p = false ∧ switches (false :: List.ofFn (fun i => h (rot p i)) ++ [false]) ≤ 2 * j := by
    intro h
    rw [mem_restrict]
    simp only [switchSeq, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (switches_rot p h2).mp h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨(switches_rot p h1).mpr h2, h1⟩
  constructor
  · apply Shatters.transfer (fun h i => h (rot p i))
    · intro h hh; rw [hmem] at hh; exact mem_pathClass.mpr hh.2
    · intro x
      by_cases hx : x = p
      · right; intro h hh h' hh'; rw [hmem] at hh hh'; rw [hx, hh.1, hh'.1]
      · left; exact ⟨⟨unrot p x, unrot_lt p hx⟩, fun h _ => by simp only [rot_unrot]⟩
  · have e : ∀ g : Hyp n, ∀ i : Fin n,
        (if hy : unrot p (rot p i) < n then g ⟨unrot p (rot p i), hy⟩ else false) = g i := by
      intro g i
      simp [unrot_rot]
    apply Shatters.transfer (fun g y => if hy : unrot p y < n then g ⟨unrot p y, hy⟩ else false)
    · intro g hg
      rw [hmem]
      refine ⟨by simp [unrot_self], ?_⟩
      simp only [e]
      exact mem_pathClass.mp hg
    · intro x; left; exact ⟨rot p x, fun g _ => e g x⟩

theorem compl_mem_restrict {n k : ℕ} (p : Fin n) (b : Bool) :
    ∀ h ∈ restrict (switchSeq n k) p b, (fun x => !h x) ∈ restrict (switchSeq n k) p (!b) := by
  intro h hh
  rw [mem_restrict] at hh ⊢
  simp only [switchSeq, mem_filter, mem_univ, true_and] at hh ⊢
  refine ⟨?_, by rw [hh.2]⟩
  have : List.ofFn (fun x => !h x) = (List.ofFn h).map (!·) := by rw [List.map_ofFn]; rfl
  rw [this, switches_map_not]
  exact hh.1

theorem shatters_restrict_switchSeq {n j : ℕ} (p : Fin (n + 1)) (b : Bool) (d : ℕ) :
    Shatters (restrict (switchSeq (n + 1) (2 * j)) p b) d ↔
      Shatters (pathClass false false (2 * j) n) d := by
  cases b with
  | false => exact shatters_restrict_false p d
  | true =>
    rw [← shatters_restrict_false p d]
    exact ⟨Shatters.compl (compl_mem_restrict p true), Shatters.compl (compl_mem_restrict p false)⟩

theorem shatters_switchSeq_succ {n j d : ℕ} :
    Shatters (switchSeq (n + 1) (2 * j)) (d + 1) ↔ Shatters (pathClass false false (2 * j) n) d := by
  rw [shatters_succ]
  constructor
  · rintro ⟨x, h0, -⟩; exact (shatters_restrict_switchSeq x false d).mp h0
  · intro h
    exact ⟨0, (shatters_restrict_switchSeq 0 false d).mpr h,
      (shatters_restrict_switchSeq 0 true d).mpr h⟩

/-- Theorem 2. -/
theorem ldim_switchSeq_even {n j : ℕ} (hn : 1 ≤ n) :
    ldim (switchSeq n (2 * j)) = 1 + ldim (unions j (n - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, unions_eq]
  have hU : (pathClass false false (2 * j) n).Nonempty := by
    refine ⟨fun _ => false, ?_⟩
    rw [← unions_eq]
    simp only [unions, mem_filter, mem_univ, true_and, mem_powerset]
    exact ⟨∅, empty_subset _, by simp, by simp⟩
  have hA : (switchSeq (n + 1) (2 * j)).Nonempty :=
    (shatters_switchSeq_succ.mpr (show Shatters _ 0 from hU)).nonempty
  have h1 := (shatters_iff_le_ldim hA).mp
    (shatters_switchSeq_succ.mpr ((shatters_iff_le_ldim hU).mpr le_rfl))
  have h2 : Shatters (switchSeq (n + 1) (2 * j)) (ldim (switchSeq (n + 1) (2 * j))) :=
    (shatters_iff_le_ldim hA).mpr le_rfl
  rcases hk : ldim (switchSeq (n + 1) (2 * j)) with _ | k
  · omega
  · rw [hk] at h2
    have := (shatters_iff_le_ldim hU).mp (shatters_switchSeq_succ.mp h2)
    omega

end ExactLittlestone
