import ExactLittlestone.Rect
import Mathlib.Data.Multiset.AddSub

namespace ExactLittlestone

open Finset

variable {m : ℕ}

def seps : ℕ → List ℕ → Finset ℕ
  | _, [] => ∅
  | s, ℓ :: L => insert (s + ℓ - 1) (seps (s + ℓ) L)

def segD (m : ℕ) (D : Finset ℕ) : Finset (Hyp m) :=
  insert (fun _ => false)
    (((range m ×ˢ range m).filter (fun p => p.1 ≤ p.2 ∧ ∀ y ∈ Icc p.1 p.2, y ∉ D)).image
      (fun p => interval p.1 p.2))

theorem mem_segD {D : Finset ℕ} {h : Hyp m} :
    h ∈ segD m D ↔ h = (fun _ => false) ∨
      ∃ a b, a ≤ b ∧ b < m ∧ (∀ y, a ≤ y → y ≤ b → y ∉ D) ∧ interval a b = h := by
  unfold segD
  rw [mem_insert, mem_image]
  simp only [mem_filter, mem_product, mem_range, mem_Icc, Prod.exists]
  constructor
  · rintro (h0 | ⟨a, b, ⟨⟨_, hb⟩, hab, hav⟩, rfl⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨a, b, hab, hb, fun y h1 h2 => hav y ⟨h1, h2⟩, rfl⟩
  · rintro (h0 | ⟨a, b, hab, hb, hav, rfl⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨a, b, ⟨⟨by omega, hb⟩, hab, fun y hy => hav y hy.1 hy.2⟩, rfl⟩

theorem segD_nonempty (D : Finset ℕ) : (segD m D).Nonempty := insert_nonempty _ _

theorem restrict_segD_false (D : Finset ℕ) (x : Fin m) :
    restrict (segD m D) x false = segD m (insert x.val D) := by
  ext h
  rw [mem_restrict, mem_segD, mem_segD]
  constructor
  · rintro ⟨h0 | ⟨a, b, hab, hbm, hav, rfl⟩, hx⟩
    · exact Or.inl h0
    · refine Or.inr ⟨a, b, hab, hbm, ?_, rfl⟩
      intro y hy1 hy2 hy
      rcases mem_insert.mp hy with rfl | hy
      · exact (interval_false x).mp hx ⟨hy1, hy2⟩
      · exact hav y hy1 hy2 hy
  · rintro (h0 | ⟨a, b, hab, hbm, hav, rfl⟩)
    · subst h0
      exact ⟨Or.inl rfl, rfl⟩
    · refine ⟨Or.inr ⟨a, b, hab, hbm, fun y h1 h2 hy => hav y h1 h2 (mem_insert_of_mem hy), rfl⟩, ?_⟩
      rw [interval_false]
      rintro ⟨h1, h2⟩
      exact hav x.val h1 h2 (mem_insert_self _ _)

theorem restrict_segD_true_of_mem {D : Finset ℕ} (x : Fin m) (hx : x.val ∈ D) :
    restrict (segD m D) x true = ∅ := by
  ext h
  simp only [mem_restrict, mem_segD, Finset.notMem_empty, iff_false]
  rintro ⟨h0 | ⟨a, b, _, _, hav, rfl⟩, hxt⟩
  · subst h0
    simp at hxt
  · rw [interval_true] at hxt
    exact hav _ hxt.1 hxt.2 hx

theorem restrict_segD_true {D : Finset ℕ} {lo hi : ℕ} (x : Fin m) (h1 : lo ≤ x.val)
    (h2 : x.val ≤ hi) (hhi : hi < m) (hfree : ∀ y, lo ≤ y → y ≤ hi → y ∉ D)
    (hlo : lo = 0 ∨ lo - 1 ∈ D) (hhi1 : hi + 1 ∈ D) :
    restrict (segD m D) x true = rect m lo x.val x.val hi := by
  ext h
  rw [mem_restrict, mem_segD]
  unfold rect
  rw [mem_image]
  simp only [mem_product, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨h0 | ⟨a, b, hab, hbm, hav, rfl⟩, hxt⟩
    · subst h0
      simp at hxt
    · rw [interval_true] at hxt
      refine ⟨a, b, ⟨⟨?_, hxt.1⟩, hxt.2, ?_⟩, rfl⟩
      · by_contra hc
        rcases hlo with h0 | h0
        · omega
        · exact hav (lo - 1) (by omega) (by omega) h0
      · by_contra hc
        exact hav (hi + 1) (by omega) (by omega) hhi1
  · rintro ⟨a, b, ⟨⟨ha1, ha2⟩, hb1, hb2⟩, rfl⟩
    refine ⟨Or.inr ⟨a, b, by omega, by omega, fun y hy1 hy2 => hfree y (by omega) (by omega), rfl⟩,
      ?_⟩
    rw [interval_true]
    omega

theorem seps_ge : ∀ {s : ℕ} {L : List ℕ} {y : ℕ}, (∀ ℓ ∈ L, 0 < ℓ) → y ∈ seps s L → s ≤ y
  | _, [], _, _, hy => by simp [seps] at hy
  | s, ℓ :: L, y, hpos, hy => by
      rw [seps, mem_insert] at hy
      have hℓ := hpos ℓ List.mem_cons_self
      rcases hy with rfl | hy
      · omega
      · have := seps_ge (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) hy
        omega

theorem seps_block_free : ∀ {s : ℕ} (L₁ : List ℕ) {ℓ : ℕ} {L₂ : List ℕ} {y : ℕ},
    (∀ x ∈ L₁ ++ ℓ :: L₂, 0 < x) → s + L₁.sum ≤ y → y + 2 ≤ s + L₁.sum + ℓ →
      y ∉ seps s (L₁ ++ ℓ :: L₂)
  | s, [], ℓ, L₂, y, hpos, h1, h2 => by
      rw [List.nil_append, seps, mem_insert]
      rintro (rfl | hy)
      · simp at h1 h2
        omega
      · have := seps_ge (fun x hx => hpos x (by simp [hx])) hy
        simp at h1 h2
        omega
  | s, a :: L₁, ℓ, L₂, y, hpos, h1, h2 => by
      rw [List.cons_append, seps, mem_insert]
      have ha := hpos a (by simp)
      simp only [List.sum_cons] at h1 h2
      rintro (rfl | hy)
      · omega
      · exact seps_block_free L₁ (s := s + a) (fun x hx => hpos x (by simp_all)) (by omega)
          (by omega) hy

theorem seps_block_end : ∀ {s : ℕ} (L₁ : List ℕ) {ℓ : ℕ} {L₂ : List ℕ},
    s + L₁.sum + ℓ - 1 ∈ seps s (L₁ ++ ℓ :: L₂)
  | s, [], ℓ, L₂ => by simp [seps]
  | s, a :: L₁, ℓ, L₂ => by
      rw [List.cons_append, seps]
      apply mem_insert_of_mem
      have := seps_block_end L₁ (s := s + a) (ℓ := ℓ) (L₂ := L₂)
      simp only [List.sum_cons]
      rwa [show s + (a + L₁.sum) + ℓ - 1 = s + a + L₁.sum + ℓ - 1 by omega]

theorem seps_block_start {s : ℕ} (L₁ : List ℕ) {ℓ : ℕ} {L₂ : List ℕ} (hne : L₁ ≠ []) :
    s + L₁.sum - 1 ∈ seps s (L₁ ++ ℓ :: L₂) := by
  obtain ⟨L₀, a, rfl⟩ := List.eq_nil_or_concat L₁ |>.resolve_left hne
  have := seps_block_end L₀ (s := s) (ℓ := a) (L₂ := ℓ :: L₂)
  rw [List.concat_eq_append, List.append_assoc, List.singleton_append, List.sum_append,
    List.sum_singleton,
    show s + (L₀.sum + a) - 1 = s + L₀.sum + a - 1 by omega]
  exact this

theorem seps_cut : ∀ {s : ℕ} (L₁ : List ℕ) {u v : ℕ} {L₂ : List ℕ},
    seps s (L₁ ++ u :: v :: L₂) = insert (s + L₁.sum + u - 1) (seps s (L₁ ++ (u + v) :: L₂))
  | s, [], u, v, L₂ => by
      simp only [List.nil_append, seps, List.sum_nil]
      rw [show s + u + v = s + (u + v) by omega, show s + (u + v) - 1 = s + u + v - 1 by omega,
        show s + 0 + u - 1 = s + u - 1 by omega]
  | s, a :: L₁, u, v, L₂ => by
      simp only [List.cons_append, seps, List.sum_cons]
      rw [seps_cut L₁ (s := s + a), Finset.insert_comm]
      congr 2
      omega

theorem locate : ∀ {s : ℕ} {L : List ℕ} {y : ℕ}, (∀ ℓ ∈ L, 0 < ℓ) → s ≤ y → y + 1 < s + L.sum →
    y ∈ seps s L ∨
      ∃ L₁ ℓ L₂, L = L₁ ++ ℓ :: L₂ ∧ s + L₁.sum ≤ y ∧ y + 2 ≤ s + L₁.sum + ℓ
  | s, [], y, _, h1, h2 => by simp at h2; omega
  | s, ℓ :: L, y, hpos, h1, h2 => by
      simp only [List.sum_cons] at h2
      by_cases hin : y + 2 ≤ s + ℓ
      · exact Or.inr ⟨[], ℓ, L, rfl, by simpa using h1, by simpa using hin⟩
      · by_cases hsep : y = s + ℓ - 1
        · left
          rw [seps, hsep]
          exact mem_insert_self _ _
        · have hℓ := hpos ℓ List.mem_cons_self
          rcases locate (s := s + ℓ) (L := L) (y := y) (fun x hx => hpos x (List.mem_cons_of_mem _ hx))
            (by omega) (by omega) with hy | ⟨L₁, ℓ', L₂, rfl, h3, h4⟩
          · left
            rw [seps]
            exact mem_insert_of_mem hy
          · right
            refine ⟨ℓ :: L₁, ℓ', L₂, rfl, ?_, ?_⟩ <;> simp only [List.sum_cons] <;> omega

theorem coe_cut (L₁ L₂ : List ℕ) (u v : ℕ) :
    ((L₁ ++ u :: v :: L₂ : List ℕ) : Multiset ℕ) =
      u ::ₘ v ::ₘ ((L₁ ++ (u + v) :: L₂ : List ℕ) : Multiset ℕ).erase (u + v) := by
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.add_cons, Multiset.erase_cons_head]

theorem shatters_seg_iff : ∀ {d : ℕ} {L : List ℕ}, (∀ ℓ ∈ L, 0 < ℓ) → L.sum = m + 1 →
    (Shatters (segD m (seps 0 L)) d ↔ Cut (L : Multiset ℕ) d)
  | 0, _, _, _ => ⟨fun _ => trivial, fun _ => segD_nonempty _⟩
  | d + 1, L, hpos, hsum => by
      constructor
      · intro h
        obtain ⟨x, h0, h1⟩ := shatters_succ.mp h
        rcases locate (s := 0) hpos (Nat.zero_le x.val) (by have := x.isLt; omega) with
          hx | ⟨L₁, ℓ, L₂, rfl, hx1, hx2⟩
        · rw [restrict_segD_true_of_mem x hx] at h1
          exact absurd h1 not_shatters_empty
        · simp only [Nat.zero_add] at hx1 hx2
          obtain ⟨u, hu⟩ : ∃ u, u = x.val - L₁.sum + 1 := ⟨_, rfl⟩
          obtain ⟨v, hv⟩ : ∃ v, v = ℓ - u := ⟨_, rfl⟩
          have hℓ : ℓ = u + v := by omega
          subst hℓ
          have hsum' : L₁.sum + (u + v) + L₂.sum = m + 1 := by
            simp only [List.sum_append, List.sum_cons] at hsum
            omega
          rw [restrict_segD_true (lo := L₁.sum) (hi := L₁.sum + (u + v) - 2) x hx1 (by omega)
            (by omega)
            (fun y hy1 hy2 => seps_block_free L₁ hpos (by simpa using hy1) (by simp; omega))
            (by
              rcases eq_or_ne L₁ [] with hL | hL
              · left; simp [hL]
              · right; simpa using seps_block_start (s := 0) L₁ (ℓ := u + v) (L₂ := L₂) hL)
            (by
              have := seps_block_end (s := 0) L₁ (ℓ := u + v) (L₂ := L₂)
              rwa [show L₁.sum + (u + v) - 2 + 1 = 0 + L₁.sum + (u + v) - 1 by omega])] at h1
          have hval := (shatters_rect_point (d := d) (lo := L₁.sum) (x := x.val)
            (hi := L₁.sum + (u + v) - 2) hx1 (by omega) (by omega)).mp h1
          rw [show x.val - L₁.sum + 1 = u by omega,
            show L₁.sum + (u + v) - 2 - x.val + 1 = v by omega] at hval
          rw [restrict_segD_false, show x.val = 0 + L₁.sum + u - 1 by omega, ← seps_cut L₁] at h0
          have hpos' : ∀ y ∈ L₁ ++ u :: v :: L₂, 0 < y := by
            intro y hy
            simp only [List.mem_append, List.mem_cons] at hy
            rcases hy with hy | rfl | rfl | hy
            · exact hpos y (by simp [hy])
            · omega
            · omega
            · exact hpos y (by simp [hy])
          have hsum'' : (L₁ ++ u :: v :: L₂).sum = m + 1 := by
            simp only [List.sum_append, List.sum_cons]
            omega
          have ih := (shatters_seg_iff hpos' hsum'').mp h0
          refine cut_succ.mpr ⟨u, v, by omega, by omega, by simp, hval, ?_⟩
          rw [← coe_cut]
          exact ih
      · intro h
        obtain ⟨u, v, hu, hv, hm, hval, hrest⟩ := cut_succ.mp h
        obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem (Multiset.mem_coe.mp hm)
        have hsum' : L₁.sum + (u + v) + L₂.sum = m + 1 := by
          simp only [List.sum_append, List.sum_cons] at hsum
          omega
        have hpos' : ∀ y ∈ L₁ ++ u :: v :: L₂, 0 < y := by
          intro y hy
          simp only [List.mem_append, List.mem_cons] at hy
          rcases hy with hy | rfl | rfl | hy
          · exact hpos y (by simp [hy])
          · exact hu
          · exact hv
          · exact hpos y (by simp [hy])
        have hsum'' : (L₁ ++ u :: v :: L₂).sum = m + 1 := by
          simp only [List.sum_append, List.sum_cons]
          omega
        rw [← coe_cut] at hrest
        have ih := (shatters_seg_iff hpos' hsum'').mpr hrest
        let x : Fin m := ⟨L₁.sum + u - 1, by omega⟩
        have hxv : x.val = L₁.sum + u - 1 := rfl
        refine shatters_succ.mpr ⟨x, ?_, ?_⟩
        · rw [restrict_segD_false, show x.val = 0 + L₁.sum + u - 1 by omega, ← seps_cut L₁]
          exact ih
        · rw [restrict_segD_true (lo := L₁.sum) (hi := L₁.sum + (u + v) - 2) x (by omega)
            (by omega) (by omega)
            (fun y hy1 hy2 => seps_block_free L₁ hpos (by simpa using hy1) (by simp; omega))
            (by
              rcases eq_or_ne L₁ [] with hL | hL
              · left; simp [hL]
              · right; simpa using seps_block_start (s := 0) L₁ (ℓ := u + v) (L₂ := L₂) hL)
            (by
              have := seps_block_end (s := 0) L₁ (ℓ := u + v) (L₂ := L₂)
              rwa [show L₁.sum + (u + v) - 2 + 1 = 0 + L₁.sum + (u + v) - 1 by omega])]
          refine (shatters_rect_point (d := d) (lo := L₁.sum) (x := x.val)
            (hi := L₁.sum + (u + v) - 2) (by omega) (by omega) (by omega)).mpr ?_
          rw [show x.val - L₁.sum + 1 = u by omega,
            show L₁.sum + (u + v) - 2 - x.val + 1 = v by omega]
          exact hval

theorem seg_single : segD m (seps 0 [m + 1]) = intervals m := by
  ext h
  rw [mem_segD]
  unfold intervals
  rw [mem_insert, mem_image]
  simp only [seps, Nat.zero_add, Nat.add_sub_cancel, insert_empty_eq, mem_singleton, mem_filter,
    mem_univ, true_and, Prod.exists]
  constructor
  · rintro (h0 | ⟨a, b, hab, hbm, _, rfl⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨⟨a, by omega⟩, ⟨b, hbm⟩, Fin.mk_le_mk.mpr hab, rfl⟩
  · rintro (h0 | ⟨a, b, hab, rfl⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨a.val, b.val, hab, b.isLt, ?_, rfl⟩
      intro y _ hy hym
      have := b.isLt
      omega

end ExactLittlestone
