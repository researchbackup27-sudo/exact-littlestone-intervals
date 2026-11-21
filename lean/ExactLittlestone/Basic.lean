import ExactLittlestone.Defs

namespace ExactLittlestone

open Finset

variable {m : ℕ}

theorem mem_restrict {H : Finset (Hyp m)} {x : Fin m} {b : Bool} {h : Hyp m} :
    h ∈ restrict H x b ↔ h ∈ H ∧ h x = b := mem_filter

theorem restrict_subset (H : Finset (Hyp m)) (x : Fin m) (b : Bool) : restrict H x b ⊆ H :=
  filter_subset _ _

theorem shatters_zero {H : Finset (Hyp m)} : Shatters H 0 ↔ H.Nonempty := Iff.rfl

theorem shatters_succ {H : Finset (Hyp m)} {d : ℕ} :
    Shatters H (d + 1) ↔
      ∃ x : Fin m, Shatters (restrict H x false) d ∧ Shatters (restrict H x true) d := Iff.rfl

theorem Shatters.nonempty : ∀ {H : Finset (Hyp m)} {d : ℕ}, Shatters H d → H.Nonempty
  | _, 0, h => h
  | H, _ + 1, h => by
      obtain ⟨x, h0, _⟩ := shatters_succ.mp h
      exact (Shatters.nonempty h0).mono (restrict_subset H x false)

theorem Shatters.subset : ∀ {H H' : Finset (Hyp m)} {d : ℕ}, H ⊆ H' → Shatters H d → Shatters H' d
  | _, _, 0, hs, h => Finset.Nonempty.mono hs h
  | _, _, _ + 1, hs, h => by
      obtain ⟨x, h0, h1⟩ := shatters_succ.mp h
      exact shatters_succ.mpr ⟨x, Shatters.subset (filter_subset_filter _ hs) h0,
        Shatters.subset (filter_subset_filter _ hs) h1⟩

theorem Shatters.pred : ∀ {H : Finset (Hyp m)} {d : ℕ}, Shatters H (d + 1) → Shatters H d
  | _, 0, h => Shatters.nonempty h
  | _, _ + 1, h => by
      obtain ⟨x, h0, h1⟩ := shatters_succ.mp h
      exact shatters_succ.mpr ⟨x, Shatters.pred h0, Shatters.pred h1⟩

theorem Shatters.mono {H : Finset (Hyp m)} {d e : ℕ} (h : Shatters H d) (hed : e ≤ d) :
    Shatters H e := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hed
  clear hed
  induction k with
  | zero => simpa using h
  | succ k ih => exact ih (Shatters.pred (by simpa [Nat.add_assoc] using h))

theorem not_shatters_empty : ∀ {d : ℕ}, ¬ Shatters (∅ : Finset (Hyp m)) d
  | 0, h => by simp [shatters_zero] at h
  | _ + 1, h => by
      obtain ⟨x, h0, -⟩ := shatters_succ.mp h
      exact not_shatters_empty (by simpa [restrict] using h0)

open Classical in
noncomputable def splitPoints (H : Finset (Hyp m)) : Finset (Fin m) :=
  univ.filter (fun x => ∃ h ∈ H, ∃ h' ∈ H, h x ≠ h' x)

theorem mem_splitPoints {H : Finset (Hyp m)} {x : Fin m} :
    x ∈ splitPoints H ↔ ∃ h ∈ H, ∃ h' ∈ H, h x ≠ h' x := by
  classical
  simp [splitPoints]

theorem Shatters.le_card_splitPoints :
    ∀ {H : Finset (Hyp m)} {d : ℕ}, Shatters H d → d ≤ (splitPoints H).card
  | _, 0, _ => Nat.zero_le _
  | H, d + 1, h => by
      obtain ⟨x, h0, h1⟩ := shatters_succ.mp h
      have ih := Shatters.le_card_splitPoints h0
      have hsub : splitPoints (restrict H x false) ⊆ (splitPoints H).erase x := by
        intro y hy
        rw [mem_splitPoints] at hy
        obtain ⟨g, hg, g', hg', hne⟩ := hy
        rw [mem_restrict] at hg hg'
        rw [mem_erase, mem_splitPoints]
        refine ⟨?_, g, hg.1, g', hg'.1, hne⟩
        rintro rfl
        exact hne (hg.2.trans hg'.2.symm)
      have hx : x ∈ splitPoints H := by
        obtain ⟨a, ha⟩ := Shatters.nonempty h0
        obtain ⟨b, hb⟩ := Shatters.nonempty h1
        rw [mem_restrict] at ha hb
        rw [mem_splitPoints]
        exact ⟨a, ha.1, b, hb.1, by rw [ha.2, hb.2]; decide⟩
      have hc := card_le_card hsub
      rw [card_erase_of_mem hx] at hc
      have hpos : 0 < (splitPoints H).card := card_pos.mpr ⟨x, hx⟩
      omega

theorem Shatters.le {H : Finset (Hyp m)} {d : ℕ} (h : Shatters H d) : d ≤ m := by
  have h1 := Shatters.le_card_splitPoints h
  have h2 : (splitPoints H).card ≤ m := by
    simpa using card_le_univ (splitPoints H)
  omega

theorem shatters_iff_le_ldim {H : Finset (Hyp m)} (hH : H.Nonempty) {d : ℕ} :
    Shatters H d ↔ d ≤ ldim H := by
  constructor
  · intro h
    exact Nat.le_findGreatest (Shatters.le h) h
  · intro hd
    have hspec : Shatters H (ldim H) := Nat.findGreatest_spec (Nat.zero_le m) hH
    exact hspec.mono hd

end ExactLittlestone
