import ExactLittlestone.SwDefs
import ExactLittlestone.Basic

namespace ExactLittlestone

open Finset

theorem switches_cc (a b : Bool) (l : List Bool) :
    switches (a :: b :: l) = (if a = b then 0 else 1) + switches (b :: l) := rfl

@[simp] theorem switches_nil : switches [] = 0 := rfl

@[simp] theorem switches_single (a : Bool) : switches [a] = 0 := rfl

theorem switches_append (l₁ : List Bool) (a : Bool) (l₂ : List Bool) :
    switches (l₁ ++ a :: l₂) = switches (l₁ ++ [a]) + switches (a :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons x t ih =>
    cases t with
    | nil => simp [switches_cc]
    | cons y t' =>
      simp only [List.cons_append] at ih ⊢
      rw [switches_cc, switches_cc, ih]; omega

theorem switches_le_cons (a : Bool) : ∀ l : List Bool, switches l ≤ switches (a :: l)
  | [] => le_rfl
  | b :: l => by rw [switches_cc]; omega

theorem switches_triangle (a x : Bool) : ∀ l : List Bool,
    switches (a :: l) ≤ (if a = x then 0 else 1) + switches (x :: l)
  | [] => by simp
  | b :: l => by
      rw [switches_cc, switches_cc]
      cases a <;> cases x <;> cases b <;> simp <;> omega

theorem switches_sublist {l₁ l₂ : List Bool} (h : l₁.Sublist l₂) :
    switches l₁ ≤ switches l₂ ∧ ∀ a, switches (a :: l₁) ≤ switches (a :: l₂) := by
  induction h with
  | slnil => exact ⟨le_rfl, fun _ => le_rfl⟩
  | cons x _ ih =>
    refine ⟨ih.1.trans (switches_le_cons x _), fun a => ?_⟩
    rw [switches_cc]
    exact (ih.2 a).trans (switches_triangle a x _)
  | cons_cons x _ ih =>
    refine ⟨ih.2 x, fun a => ?_⟩
    rw [switches_cc, switches_cc]
    exact Nat.add_le_add_left (ih.2 x) _

theorem switches_map_not : ∀ l : List Bool, switches (l.map (!·)) = switches l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
      have := switches_map_not (b :: l)
      simp only [List.map_cons] at this ⊢
      rw [switches_cc, switches_cc, this]
      cases a <;> cases b <;> rfl

theorem switches_mod_two (a b : Bool) : ∀ l : List Bool,
    switches (a :: l ++ [b]) % 2 = if a = b then 0 else 1
  | [] => by cases a <;> cases b <;> rfl
  | x :: l => by
      have := switches_mod_two x b l
      simp only [List.cons_append] at this ⊢
      rw [switches_cc]
      cases a <;> cases x <;> cases b <;> simp at this ⊢ <;> omega

theorem switches_le_length (a b : Bool) : ∀ l : List Bool, switches (a :: l ++ [b]) ≤ l.length + 1
  | [] => by cases a <;> cases b <;> decide
  | x :: l => by
      have := switches_le_length x b l
      simp only [List.cons_append, List.length_cons] at this ⊢
      rw [switches_cc]; split <;> omega

theorem mem_pathClass {a b : Bool} {k n : ℕ} {h : Hyp n} :
    h ∈ pathClass a b k n ↔ switches (a :: List.ofFn h ++ [b]) ≤ k := by
  simp [pathClass]

section Transfer

variable {m n : ℕ}

def ShattersP (P : Hyp m → Prop) : Finset (Hyp m) → ℕ → Prop
  | H, 0 => ∃ h ∈ H, P h
  | H, d + 1 => ∃ x : Fin m, ShattersP P (restrict H x false) d ∧ ShattersP P (restrict H x true) d

theorem shattersP_true : ∀ {H : Finset (Hyp m)} {d : ℕ}, ShattersP (fun _ => True) H d ↔ Shatters H d
  | H, 0 => by simp [ShattersP, shatters_zero, Finset.Nonempty]
  | H, d + 1 => by
      simp only [ShattersP, shatters_succ, shattersP_true]

theorem ShattersP.shatters {P : Hyp m → Prop} :
    ∀ {H : Finset (Hyp m)} {d : ℕ}, ShattersP P H d → Shatters H d
  | _, 0, ⟨h, hh, _⟩ => ⟨h, hh⟩
  | _, _ + 1, ⟨x, h0, h1⟩ => shatters_succ.mpr ⟨x, h0.shatters, h1.shatters⟩

theorem ShattersP.nonempty {P : Hyp m → Prop} {H : Finset (Hyp m)} {d : ℕ}
    (h : ShattersP P H d) : H.Nonempty := h.shatters.nonempty

theorem ShattersP.transfer {P : Hyp n → Prop} {P' : Hyp m → Prop} (φ : Hyp n → Hyp m) :
    ∀ {d : ℕ} {H : Finset (Hyp n)} {H' : Finset (Hyp m)},
    (∀ h ∈ H, φ h ∈ H') → (∀ h ∈ H, P h → P' (φ h)) →
    (∀ x : Fin n, (∃ y, ∀ h ∈ H, φ h y = h x) ∨ (∀ h ∈ H, ∀ h' ∈ H, h x = h' x)) →
    ShattersP P H d → ShattersP P' H' d
  | 0, _, _, hφ, hP, _, ⟨h, hh, hp⟩ => ⟨φ h, hφ h hh, hP h hh hp⟩
  | d + 1, H, H', hφ, hP, hpt, ⟨x, h0, h1⟩ => by
      rcases hpt x with ⟨y, hy⟩ | hc
      · have hpt' : ∀ b : Bool, ∀ z : Fin n, (∃ w, ∀ h ∈ restrict H x b, φ h w = h z) ∨
            (∀ h ∈ restrict H x b, ∀ h' ∈ restrict H x b, h z = h' z) := by
          intro b z
          rcases hpt z with ⟨w, hw⟩ | hc
          · exact Or.inl ⟨w, fun h hh => hw h (restrict_subset _ _ _ hh)⟩
          · exact Or.inr fun h hh h' hh' =>
              hc h (restrict_subset _ _ _ hh) h' (restrict_subset _ _ _ hh')
        have hφ' : ∀ b : Bool, ∀ h ∈ restrict H x b, φ h ∈ restrict H' y b := by
          intro b h hh
          rw [mem_restrict] at hh ⊢
          exact ⟨hφ h hh.1, by rw [hy h hh.1, hh.2]⟩
        have hP' : ∀ b : Bool, ∀ h ∈ restrict H x b, P h → P' (φ h) :=
          fun b h hh => hP h (restrict_subset _ _ _ hh)
        exact ⟨y, ShattersP.transfer φ (hφ' false) (hP' false) (hpt' false) h0,
          ShattersP.transfer φ (hφ' true) (hP' true) (hpt' true) h1⟩
      · obtain ⟨g, hg⟩ := h0.nonempty
        obtain ⟨g', hg'⟩ := h1.nonempty
        rw [mem_restrict] at hg hg'
        have := hc g hg.1 g' hg'.1
        rw [hg.2, hg'.2] at this
        exact absurd this (by decide)

theorem Shatters.transfer {H : Finset (Hyp n)} {H' : Finset (Hyp m)} (φ : Hyp n → Hyp m)
    (hφ : ∀ h ∈ H, φ h ∈ H')
    (hpt : ∀ x : Fin n, (∃ y, ∀ h ∈ H, φ h y = h x) ∨ (∀ h ∈ H, ∀ h' ∈ H, h x = h' x))
    {d : ℕ} (hs : Shatters H d) : Shatters H' d :=
  shattersP_true.mp (ShattersP.transfer φ hφ (fun _ _ _ => trivial) hpt (shattersP_true.mpr hs))

theorem ShattersP.subset {P : Hyp m → Prop} {H H' : Finset (Hyp m)} (hs : H ⊆ H') {d : ℕ}
    (h : ShattersP P H d) : ShattersP P H' d :=
  ShattersP.transfer id (fun _ hh => hs hh) (fun _ _ hp => hp)
    (fun x => Or.inl ⟨x, fun _ _ => rfl⟩) h

theorem ShattersP.pred {P : Hyp m → Prop} :
    ∀ {H : Finset (Hyp m)} {d : ℕ}, ShattersP P H (d + 1) → ShattersP P H d
  | _, 0, ⟨_, ⟨h, hh, hp⟩, _⟩ => ⟨h, restrict_subset _ _ _ hh, hp⟩
  | _, _ + 1, ⟨x, h0, h1⟩ => ⟨x, h0.pred, h1.pred⟩

theorem ShattersP.mono {P : Hyp m → Prop} {H : Finset (Hyp m)} {d e : ℕ}
    (h : ShattersP P H d) (hed : e ≤ d) : ShattersP P H e := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hed
  clear hed
  induction k with
  | zero => simpa using h
  | succ k ih => exact ih (ShattersP.pred (by simpa [Nat.add_assoc] using h))

theorem shattersP_cube (P : Hyp m → Prop) (S : Finset (Fin m)) :
    ∀ (g : Hyp m), (∀ h : Hyp m, (∀ i ∉ S, h i = g i) → P h) →
    ShattersP P (univ.filter (fun h => ∀ i ∉ S, h i = g i)) S.card := by
  induction S using Finset.induction_on with
  | empty => intro g hP; exact ⟨g, by simp, hP g (fun _ _ => rfl)⟩
  | insert s S hs ih =>
    intro g hP
    rw [card_insert_of_notMem hs]
    have key : ∀ b : Bool, ShattersP P
        (restrict (univ.filter (fun h => ∀ i ∉ insert s S, h i = g i)) s b) S.card := by
      intro b
      refine ShattersP.subset ?_ (ih (Function.update g s b) ?_)
      · intro h hh
        simp only [mem_filter, mem_univ, true_and] at hh
        rw [mem_restrict]
        refine ⟨?_, by simpa using hh s hs⟩
        simp only [mem_filter, mem_univ, true_and]
        intro i hi
        rw [hh i (fun h' => hi (mem_insert_of_mem h')),
          Function.update_of_ne (by rintro rfl; exact hi (mem_insert_self _ _))]
      · intro h hh
        apply hP
        intro i hi
        rw [hh i (fun h' => hi (mem_insert_of_mem h')),
          Function.update_of_ne (by rintro rfl; exact hi (mem_insert_self _ _))]
    exact ⟨s, key false, key true⟩

theorem ShattersP.compl {P P' : Hyp m → Prop} :
    ∀ {d : ℕ} {H H' : Finset (Hyp m)}, (∀ h ∈ H, (fun x => !h x) ∈ H') →
    (∀ h ∈ H, P h → P' (fun x => !h x)) → ShattersP P H d → ShattersP P' H' d
  | 0, _, _, hφ, hP, ⟨h, hh, hp⟩ => ⟨_, hφ h hh, hP h hh hp⟩
  | d + 1, H, H', hφ, hP, ⟨x, h0, h1⟩ => by
      have key : ∀ c : Bool, ShattersP P (restrict H x c) d →
          ShattersP P' (restrict H' x (!c)) d := fun c hc =>
        ShattersP.compl (fun h hh => by
            rw [mem_restrict] at hh ⊢; exact ⟨hφ h hh.1, by simp [hh.2]⟩)
          (fun h hh => hP h (restrict_subset _ _ _ hh)) hc
      exact ⟨x, key true h1, key false h0⟩

theorem Shatters.compl {H H' : Finset (Hyp m)} (hφ : ∀ h ∈ H, (fun x => !h x) ∈ H') {d : ℕ}
    (hs : Shatters H d) : Shatters H' d :=
  shattersP_true.mp (ShattersP.compl hφ (fun _ _ _ => trivial) (shattersP_true.mpr hs))

theorem ShattersP.graft {P : Hyp n → Prop} {P' : Hyp m → Prop} (ι : Fin n → Fin m) {e : ℕ} :
    ∀ {d : ℕ} {H : Finset (Hyp n)} {H' : Finset (Hyp m)}, ShattersP P H d →
    (∀ h ∈ H, P h → ShattersP P' (H'.filter (fun h' => ∀ i, h' (ι i) = h i)) e) →
    ShattersP P' H' (d + e)
  | 0, H, H', ⟨h, hh, hp⟩, hg => by
      rw [Nat.zero_add]; exact (hg h hh hp).subset (filter_subset _ _)
  | d + 1, H, H', ⟨x, h0, h1⟩, hg => by
      have key : ∀ c : Bool, ShattersP P (restrict H x c) d →
          ShattersP P' (restrict H' (ι x) c) (d + e) := fun c hc =>
        ShattersP.graft ι hc (fun h hh hp => by
          rw [mem_restrict] at hh
          refine (hg h hh.1 hp).subset ?_
          intro h' hh'
          simp only [mem_filter, mem_restrict] at hh' ⊢
          exact ⟨⟨hh'.1, by rw [hh'.2 x, hh.2]⟩, hh'.2⟩)
      rw [Nat.add_right_comm]
      exact ⟨ι x, key false h0, key true h1⟩

end Transfer

end ExactLittlestone
