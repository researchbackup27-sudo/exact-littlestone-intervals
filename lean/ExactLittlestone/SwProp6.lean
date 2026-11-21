import ExactLittlestone.SwMain
import ExactLittlestone.SwFree
import ExactLittlestone.SwOne

namespace ExactLittlestone

open Finset

variable {m n k d : ℕ}

theorem le_ldim_of_shatters {H : Finset (Hyp m)} (h : Shatters H d) : d ≤ ldim H :=
  Nat.le_findGreatest h.le h

theorem ldim_le_succ_of {H : Finset (Hyp m)} {B : ℕ} (h : ∀ d, Shatters H (d + 1) → d ≤ B) :
    ldim H ≤ 1 + B := by
  rcases Nat.eq_zero_or_pos (ldim H) with h0 | hpos
  · omega
  · obtain ⟨e, he⟩ : ∃ e, ldim H = e + 1 := ⟨ldim H - 1, by omega⟩
    have hs : Shatters H (e + 1) := Nat.findGreatest_of_ne_zero he (by omega)
    have := h e hs
    omega

theorem compl_mem_switchSeq {h : Hyp n} (hh : h ∈ switchSeq n k) :
    (fun x => !h x) ∈ switchSeq n k := by
  simp only [switchSeq, mem_filter, mem_univ, true_and] at hh ⊢
  have e : List.ofFn (fun x => !h x) = (List.ofFn h).map (!·) := by simp [List.map_ofFn]; rfl
  rw [e, switches_map_not]; exact hh

theorem restrict_switchSeq_compl {p : Fin n} {c : Bool} (hs : Shatters (restrict (switchSeq n k) p c) d) :
    Shatters (restrict (switchSeq n k) p (!c)) d :=
  Shatters.compl (fun h hh => by
    rw [mem_restrict] at hh ⊢
    exact ⟨compl_mem_switchSeq hh.1, by simp [hh.2]⟩) hs

theorem shatters_switchSeq_succ_iff :
    Shatters (switchSeq n k) (d + 1) ↔ ∃ p, Shatters (restrict (switchSeq n k) p false) d := by
  rw [shatters_succ]
  constructor
  · rintro ⟨p, h0, _⟩; exact ⟨p, h0⟩
  · rintro ⟨p, h0⟩; exact ⟨p, h0, by simpa using restrict_switchSeq_compl (c := false) h0⟩

theorem gap_into_switchSeq (hs : Shatters (pathClass false true k m) d) :
    Shatters (restrict (switchSeq (m + 1) k) 0 false) d := by
  refine Shatters.transfer (fun h => (Fin.cons false h : Hyp (m + 1))) ?_
    (fun x => Or.inl ⟨x.succ, fun h _ => Fin.cons_succ _ _ _⟩) hs
  intro h hh
  rw [mem_pathClass] at hh
  simp only [mem_restrict, switchSeq, mem_filter, mem_univ, true_and, Fin.cons_zero, and_true]
  have hsub : (false :: List.ofFn h).Sublist ((false :: List.ofFn h) ++ [true]) :=
    List.sublist_append_left _ _
  have := (switches_sublist hsub).1
  rw [List.ofFn_succ]; simp only [Fin.cons_zero, Fin.cons_succ]
  exact this.trans hh

theorem odd_par (hk : Odd k) : k % 2 = if false = true then 0 else 1 := by
  simpa using Nat.odd_iff.mp hk

theorem switchSeq_lower (hk : Odd k) (hQ : Q k d ≤ m + 1) : Shatters (switchSeq (m + 1) k) (d + 1) :=
  shatters_switchSeq_succ_iff.mpr ⟨0, gap_into_switchSeq
    ((shatters_pathClass_iff (by have := hk.pos; omega) (odd_par hk)).mpr hQ)⟩

theorem switchSeq_upper_v (hk : Odd k) (hs : Shatters (switchSeq (m + 1) k) (d + 1)) :
    Q (k + 1) d ≤ m + 1 := by
  obtain ⟨j, hj⟩ : ∃ j, k + 1 = 2 * j := ⟨(k + 1) / 2, by have := Nat.odd_iff.mp hk; omega⟩
  obtain ⟨p, hp⟩ := shatters_switchSeq_succ_iff.mp hs
  have hsub : restrict (switchSeq (m + 1) k) p false ⊆ restrict (switchSeq (m + 1) (2 * j)) p false := by
    intro h hh
    simp only [mem_restrict, switchSeq, mem_filter, mem_univ, true_and] at hh ⊢
    exact ⟨by omega, hh.2⟩
  have h2 := (shatters_restrict_switchSeq p false d).mp (hp.subset hsub)
  rw [hj]; exact upper (by omega) m d h2

theorem switchSeq_upper_half (hk : Odd k) (hs : Shatters (switchSeq n k) (d + 1)) : d ≤ (n + k - 1) / 2 := by
  obtain ⟨p, hp⟩ := shatters_switchSeq_succ_iff.mp hs
  exact free_le_half (Nat.odd_iff.mp hk) p false hp

/-- Proposition 6, lower bound. -/
theorem prop6_lower (hn : 1 ≤ n) (hk : Odd k) : 1 + v k n ≤ ldim (switchSeq n k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := le_ldim_of_shatters (switchSeq_lower hk (Q_v_le hk.pos (by omega)))
  omega

/-- Proposition 6, upper bound. -/
theorem prop6_upper (hn : 1 ≤ n) (hk : Odd k) :
    ldim (switchSeq n k) ≤ 1 + min ((n + k - 1) / 2) (v (k + 1) n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ldim_le_succ_of (fun d hs => le_min (switchSeq_upper_half hk hs) ?_)
  exact (le_v_iff (by omega) (by omega)).mpr (switchSeq_upper_v hk hs)

theorem v_one (hn : 1 ≤ n) : v 1 n = Nat.log 2 n := by
  refine le_antisymm ?_ ?_
  · have := Q_v_le (k := 1) (by omega) hn
    rw [Q_one] at this
    exact Nat.le_log_of_pow_le (by omega) this
  · rw [le_v_iff (by omega) hn, Q_one]
    exact Nat.pow_log_le_self 2 (by omega)

/-- Proposition 6, the case `k = 1`. -/
theorem prop6_one (hn : 1 ≤ n) : ldim (switchSeq n 1) = 1 + Nat.log 2 n := by
  refine le_antisymm (ldim_le_succ_of fun d hs => ?_) ?_
  · have h1 := hs.two_pow_le_card
    have h2 := card_switchSeq_one_le hn
    rw [pow_succ] at h1
    exact Nat.le_log_of_pow_le (by omega) (by omega)
  · rw [← v_one hn]; exact prop6_lower hn ⟨0, rfl⟩

end ExactLittlestone
