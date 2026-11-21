import ExactLittlestone.SwPot

namespace ExactLittlestone

open Finset

theorem switches_cons_le (a : Bool) : ∀ l : List Bool, switches (a :: l) ≤ switches l + 1
  | [] => by simp
  | x :: l => by rw [switches_cc]; split <;> omega

theorem switches_append_le (a : Bool) : ∀ l : List Bool, switches (l ++ [a]) ≤ switches l + 1
  | [] => by simp
  | [x] => by simp only [List.cons_append, List.nil_append, switches_cc]; simp; split <;> omega
  | x :: y :: l => by
      have := switches_append_le a (y :: l)
      simp only [List.cons_append] at this ⊢
      rw [switches_cc, switches_cc]; omega

theorem pad_le {k n : ℕ} (hk : k % 2 = 1) (a : Bool) {h : Hyp n}
    (hh : switches (List.ofFn h) ≤ k) : switches (a :: List.ofFn h ++ [a]) ≤ k + 1 := by
  have h1 := switches_cons_le a (List.ofFn h ++ [a])
  have h2 := switches_append_le a (List.ofFn h)
  have h3 := switches_mod_two a a (List.ofFn h)
  simp only [List.cons_append] at h1 h3 ⊢
  simp at h3
  omega

theorem eq_rep_of_append {A B : List (Option Bool)} {n : ℕ}
    (h : List.replicate n none = A ++ none :: B) :
    A = List.replicate A.length none ∧ B = List.replicate B.length none ∧
      A.length + B.length + 1 = n := by
  have hm : ∀ x ∈ A ++ none :: B, x = none := fun x hx => by
    rw [← h] at hx; exact List.eq_of_mem_replicate hx
  refine ⟨List.eq_replicate_iff.mpr ⟨rfl, fun x hx => hm x (by simp [hx])⟩,
    List.eq_replicate_iff.mpr ⟨rfl, fun x hx => hm x (by simp [hx])⟩, ?_⟩
  have := congrArg List.length h
  simp at this
  omega

/-- A sequence with at most `k` switches (odd `k`) and one fixed label has Littlestone dimension at most `(n + k - 1) / 2`. -/
theorem free_le_half {n k D : ℕ} (hk : k % 2 = 1) (p : Fin n) (b : Bool)
    (hs : Shatters (restrict (switchSeq n k) p b) D) : D ≤ (n + k - 1) / 2 := by
  have key : ∀ a : Bool, D ≤ pot a a (k + 1) n (Function.update (fun _ => none) p (some b)) := by
    intro a
    refine shatters_vs_le D _ (hs.subset ?_)
    intro h hh
    rw [mem_restrict] at hh
    simp only [switchSeq, mem_filter, mem_univ, true_and] at hh
    simp only [vs, mem_filter, mem_pathClass]
    refine ⟨pad_le hk a hh.1, fun i v hv => ?_⟩
    by_cases hi : i = p
    · subst hi; simp at hv; rw [← hv, hh.2]
    · simp [Function.update_of_ne hi] at hv
  obtain ⟨A, B, h1, h2⟩ := ofFn_split (fun _ : Fin n => (none : Option Bool)) p
  rw [List.ofFn_const] at h1
  obtain ⟨hA, hB, hn⟩ := eq_rep_of_append h1
  generalize A.length = j at hA hn
  generalize B.length = m at hB hn
  subst hA hB
  have hb := key b
  have hnb := key (!b)
  simp only [pot, h2, List.append_assoc, List.cons_append, numA_rep, gsum_rep, numA,
    gsum] at hb hnb
  cases b <;> simp at hb hnb <;> omega

end ExactLittlestone
