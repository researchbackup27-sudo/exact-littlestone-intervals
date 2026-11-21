import ExactLittlestone.Basic
import ExactLittlestone.Seg
import ExactLittlestone.Upper
import ExactLittlestone.Lower

namespace ExactLittlestone

theorem cut_single_iff {ℓ d : ℕ} (hℓ : 0 < ℓ) : Cut {ℓ} d ↔ P d ≤ ℓ :=
  ⟨P_le_of_cut hℓ, cut_of_P_le⟩

/-- Theorem 1: `Int_m` shatters depth `d` iff `P(d) ≤ m + 1`. -/
theorem main (m d : ℕ) : Shatters (intervals m) d ↔ P d ≤ m + 1 := by
  rw [← seg_single, shatters_seg_iff (L := [m + 1]) (by simp) (by simp), Multiset.coe_singleton]
  exact cut_single_iff (by omega)

theorem intervals_nonempty (m : ℕ) : (intervals m).Nonempty := Finset.insert_nonempty _ _

/-- Theorem 1: `Ldim(Int_m) = max {d : P(d) ≤ m + 1}`. -/
theorem ldim_intervals_isGreatest (m : ℕ) :
    IsGreatest {d | P d ≤ m + 1} (ldim (intervals m)) := by
  constructor
  · exact (main m _).mp ((shatters_iff_le_ldim (intervals_nonempty m)).mpr le_rfl)
  · intro d hd
    exact (shatters_iff_le_ldim (intervals_nonempty m)).mp ((main m d).mpr hd)

/-- Theorem 1 with the maximum as `Nat.findGreatest`. -/
theorem ldim_intervals (m : ℕ) :
    ldim (intervals m) = Nat.findGreatest (fun d => P d ≤ m + 1) m := by
  have hG := ldim_intervals_isGreatest m
  have hle : ldim (intervals m) ≤ m :=
    Shatters.le ((shatters_iff_le_ldim (intervals_nonempty m)).mpr le_rfl)
  apply le_antisymm
  · exact Nat.le_findGreatest hle hG.1
  · have hspec : P (Nat.findGreatest (fun d => P d ≤ m + 1) m) ≤ m + 1 :=
      Nat.findGreatest_spec (P := fun d => P d ≤ m + 1) (Nat.zero_le m) (by simp [P])
    exact hG.2 hspec

end ExactLittlestone
