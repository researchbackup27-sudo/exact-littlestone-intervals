import ExactLittlestone.SwBasic

namespace ExactLittlestone

open Finset

def Pm {n : ℕ} (full a b : Bool) (k : ℕ) (h : Hyp n) : Prop :=
  full = true → switches (a :: List.ofFn h ++ [b]) = k

def Sh (full a b : Bool) (k n d : ℕ) : Prop := ShattersP (Pm full a b k) (pathClass a b k n) d

variable {full a b : Bool} {k n d : ℕ}

theorem sh_false : Sh false a b k n d ↔ Shatters (pathClass a b k n) d := by
  have : (Pm false a b k : Hyp n → Prop) = fun _ => True := by funext h; simp [Pm]
  rw [Sh, this, shattersP_true]

theorem Sh.plain (h : Sh full a b k n d) : Shatters (pathClass a b k n) d := ShattersP.shatters h

theorem Sh.to_false (h : Sh full a b k n d) : Sh false a b k n d := sh_false.mpr h.plain

theorem ofFn_cons (c : Bool) (h : Hyp n) : List.ofFn (Fin.cons c h : Hyp (n + 1)) = c :: List.ofFn h := by
  simp [List.ofFn_succ]

theorem sw_cons (a c b : Bool) (h : Hyp n) :
    switches (a :: List.ofFn (Fin.cons c h : Hyp (n + 1)) ++ [b]) =
      (if a = c then 0 else 1) + switches (c :: List.ofFn h ++ [b]) := by
  rw [ofFn_cons]; simp only [List.cons_append]; rw [switches_cc]

theorem ShattersP.of_eq {m : ℕ} {P : Hyp m → Prop} {H : Finset (Hyp m)} {d e : ℕ}
    (h : ShattersP P H d) (he : d = e) : ShattersP P H e := he ▸ h

theorem sh_cons {c : Bool} {k' : ℕ} (hk : (if a = c then 0 else 1) + k' = k) (hs : Sh full c b k' n d) :
    ShattersP (Pm full a b k) (restrict (pathClass a b k (n + 1)) 0 c) d := by
  refine ShattersP.transfer (fun h => (Fin.cons c h : Hyp (n + 1))) ?_ ?_ ?_ hs
  · intro h hh
    rw [mem_restrict, mem_pathClass, sw_cons]
    rw [mem_pathClass] at hh
    exact ⟨by omega, rfl⟩
  · intro h _ hp hf
    rw [sw_cons, hp hf, hk]
  · intro x; exact Or.inl ⟨x.succ, fun h _ => Fin.cons_succ _ _ _⟩

theorem move_b (hs : Sh full a b k n d) : Sh full a b k (n + 1) d :=
  (sh_cons (c := a) (by simp) hs).subset (restrict_subset _ _ _)

theorem move_c (hk : 1 ≤ k) (h1 : Sh full a b k n d) (h2 : Sh full (!a) b (k - 1) n d) :
    Sh full a b k (n + 1) (d + 1) := by
  refine ⟨0, ?_, ?_⟩ <;> cases a
  · exact sh_cons (by simp) h1
  · exact sh_cons (by simp; omega) h2
  · exact sh_cons (by simp; omega) h2
  · exact sh_cons (by simp) h1

theorem sh_cons2 {y c : Bool} {k' : ℕ}
    (hk : (if a = y then 0 else 1) + (if y = c then 0 else 1) + k' = k) (hs : Sh full c b k' n d) :
    ShattersP (Pm full a b k)
      (restrict (restrict (pathClass a b k (n + 2)) (Fin.succ 0) c) 0 y) d := by
  refine ShattersP.transfer (fun h => (Fin.cons y (Fin.cons c h : Hyp (n + 1)) : Hyp (n + 2)))
    ?_ ?_ ?_ hs
  · intro h hh
    rw [mem_pathClass] at hh
    simp only [mem_restrict, mem_pathClass, sw_cons, Fin.cons_succ, Fin.cons_zero]
    exact ⟨⟨by omega, trivial⟩, trivial⟩
  · intro h _ hp hf
    rw [sw_cons, sw_cons, hp hf, ← hk, Nat.add_assoc]
  · intro x; exact Or.inl ⟨x.succ.succ, fun h _ => by simp⟩

theorem move_d (hk : 1 ≤ k) (h1 : Sh full a b k n d) (h2 : Sh full (!a) b (k - 1) n (d - 1)) :
    Sh full a b k (n + 2) (d + 1) := by
  have hA : ShattersP (Pm full a b k) (restrict (pathClass a b k (n + 2)) (Fin.succ 0) a) d :=
    (sh_cons2 (y := a) (by simp) h1).subset (restrict_subset _ _ _)
  have hB : ShattersP (Pm full a b k) (restrict (pathClass a b k (n + 2)) (Fin.succ 0) (!a)) d := by
    cases d with
    | zero =>
      exact (sh_cons2 (y := a) (by cases a <;> simp <;> omega) h2).subset (restrict_subset _ _ _)
    | succ e =>
      exact ⟨0, sh_cons2 (by cases a <;> simp <;> omega) h2,
        sh_cons2 (by cases a <;> simp <;> omega) h2⟩
  refine ⟨Fin.succ 0, ?_, ?_⟩ <;> cases a
  · exact hA
  · exact hB
  · exact hB
  · exact hA

theorem switches_const (c : Bool) : ∀ l : List Bool, (∀ x ∈ l, x = c) → switches (c :: l) = 0
  | [], _ => rfl
  | x :: l, hl => by
      rw [switches_cc, hl x (by simp), ite_eq_left_iff.mpr (fun h => absurd rfl h),
        ← hl x (by simp), switches_const x l (fun y hy => by rw [hl y (by simp [hy]), hl x (by simp)])]

theorem exists_exact : ∀ {a : Bool} {k n : ℕ}, k % 2 = (if a = b then 0 else 1) → k ≤ n + 1 →
    Sh true a b k n 0
  | a, 0, n, hpar, _ => by
      have hab : a = b := by by_contra h; simp [h] at hpar
      subst hab
      have h0 : switches (a :: List.ofFn (fun _ : Fin n => a) ++ [a]) = 0 := by
        rw [List.cons_append]
        refine switches_const a _ (fun x hx => ?_)
        rw [List.ofFn_const, List.mem_append, List.mem_replicate, List.mem_singleton] at hx
        rcases hx with ⟨_, h⟩ | h <;> exact h
      exact ⟨fun _ => a, by rw [mem_pathClass, h0], fun _ => h0⟩
  | a, k + 1, 0, hpar, _ => by
      have hk : k = 0 := by omega
      subst hk
      have hab : a ≠ b := by intro h; simp [h] at hpar
      refine ⟨Fin.elim0, ?_, fun _ => ?_⟩ <;> cases a <;> cases b <;> simp_all [mem_pathClass, switches_cc]
  | a, k + 1, n + 1, hpar, hkn => by
      obtain ⟨h, hh, hp⟩ := exists_exact (a := !a) (k := k) (n := n)
        (by revert hpar; cases a <;> cases b <;> simp <;> omega) (by omega)
      rw [mem_pathClass] at hh
      have hd : (if a = !a then 0 else 1) = 1 := by cases a <;> rfl
      refine ⟨Fin.cons (!a) h, ?_, fun _ => ?_⟩
      · rw [mem_pathClass, sw_cons, hd]; omega
      · rw [sw_cons, hp rfl, hd]; omega

theorem move_a (hpar : k % 2 = if a = b then 0 else 1) (hn : n ≤ k) :
    Shatters (pathClass a b k n) n := by
  have hc := shattersP_cube (fun _ : Hyp n => True) univ (fun _ => false) (fun _ _ => trivial)
  rw [card_univ, Fintype.card_fin, shattersP_true] at hc
  refine hc.subset ?_
  intro h _
  rw [mem_pathClass]
  have h1 := switches_le_length a b (List.ofFn h)
  have h2 := switches_mod_two a b (List.ofFn h)
  rw [List.length_ofFn] at h1
  split at h2 <;> split at hpar <;> simp_all <;> omega

def ι (n : ℕ) (i : Fin n) : Fin (2 * n + 1) := ⟨2 * i + 1, by omega⟩

def fib (a b : Bool) (n : ℕ) (h : Hyp n) : Finset (Hyp (2 * n + 1)) :=
  univ.filter (fun h' => (∀ i, h' (ι n i) = h i) ∧
    switches (a :: List.ofFn h' ++ [b]) ≤ switches (a :: List.ofFn h ++ [b]))

theorem fib_shatters (b : Bool) : ∀ (n : ℕ) (a : Bool) (h : Hyp n),
    ShattersP (fun h' : Hyp (2 * n + 1) =>
      switches (a :: List.ofFn h' ++ [b]) = switches (a :: List.ofFn h ++ [b]))
      (fib a b n h) (switches (a :: List.ofFn h ++ [b]))
  | 0, a, h => by
      have key : ∀ c : Bool, (if a = c then 0 else 1) + (if c = b then 0 else 1) =
          switches (a :: List.ofFn h ++ [b]) →
          ∀ H : Finset (Hyp (2 * 0 + 1)), (fun _ => c) ∈ H →
          ShattersP (fun h' : Hyp (2 * 0 + 1) =>
            switches (a :: List.ofFn h' ++ [b]) = switches (a :: List.ofFn h ++ [b])) H 0 := by
        intro c hc H hH
        refine ⟨fun _ => c, hH, ?_⟩
        rw [← hc]; cases a <;> cases b <;> cases c <;> rfl
      have mem : ∀ c : Bool, (if a = c then 0 else 1) + (if c = b then 0 else 1) =
          switches (a :: List.ofFn h ++ [b]) → (fun _ => c) ∈ fib a b 0 h := by
        intro c hc
        simp only [fib, mem_filter, mem_univ, true_and]
        refine ⟨fun i => i.elim0, ?_⟩
        rw [← hc]; cases a <;> cases b <;> cases c <;> decide
      by_cases hab : a = b
      · subst hab
        have e : switches (a :: List.ofFn h ++ [a]) = 0 := by cases a <;> rfl
        exact ShattersP.of_eq (key a (by rw [e]; simp) _ (mem a (by rw [e]; simp))) e.symm
      · have e : switches (a :: List.ofFn h ++ [b]) = 0 + 1 := by
          cases a <;> cases b <;> first | exact absurd rfl hab | rfl
        have br : ∀ c : Bool, ShattersP (fun h' : Hyp (2 * 0 + 1) =>
            switches (a :: List.ofFn h' ++ [b]) = switches (a :: List.ofFn h ++ [b]))
            (restrict (fib a b 0 h) 0 c) 0 := by
          intro c
          have hc : (if a = c then 0 else 1) + (if c = b then 0 else 1) =
              switches (a :: List.ofFn h ++ [b]) := by
            rw [e]; cases a <;> cases b <;> cases c <;> simp_all
          exact key c hc _ (by rw [mem_restrict]; exact ⟨mem c hc, rfl⟩)
        exact ShattersP.of_eq (d := 0 + 1) ⟨0, br false, br true⟩ e.symm
  | n + 1, a, h => by
      have ih := fib_shatters b n (h 0) (fun i => h i.succ)
      have hsw : switches (a :: List.ofFn h ++ [b]) =
          (if a = h 0 then 0 else 1) + switches (h 0 :: List.ofFn (fun i => h i.succ) ++ [b]) := by
        rw [List.ofFn_succ]; simp only [List.cons_append]; rw [switches_cc]
      have tr : ∀ c : Bool, (if a = c then 0 else 1) + (if c = h 0 then 0 else 1) =
          (if a = h 0 then 0 else 1) →
          ShattersP (fun h' : Hyp (2 * (n + 1) + 1) =>
            switches (a :: List.ofFn h' ++ [b]) = switches (a :: List.ofFn h ++ [b]))
            (restrict (fib a b (n + 1) h) 0 c) (switches (h 0 :: List.ofFn (fun i => h i.succ) ++ [b])) := by
        intro c hc
        refine ShattersP.transfer
          (fun r => (Fin.cons c (Fin.cons (h 0) r : Hyp (2 * n + 1 + 1)) : Hyp (2 * (n + 1) + 1)))
          ?_ ?_ ?_ ih
        · intro r hr
          simp only [fib, mem_filter, mem_univ, true_and] at hr
          simp only [mem_restrict, fib, mem_filter, mem_univ, true_and, Fin.cons_zero, and_true]
          refine ⟨fun i => ?_, ?_⟩
          · refine Fin.cases ?_ (fun j => ?_) i
            · show (Fin.cons c (Fin.cons (h 0) r : Hyp (2 * n + 1 + 1)) : Hyp (2 * (n + 1) + 1))
                (Fin.succ 0) = h 0
              simp
            · have : ι (n + 1) j.succ = (ι n j).succ.succ := by ext; simp [ι]; omega
              rw [this]; simpa using hr.1 j
          · rw [sw_cons, sw_cons, hsw]; omega
        · intro r _ hp
          rw [sw_cons, sw_cons, hp, hsw]; omega
        · intro x; exact Or.inl ⟨x.succ.succ, fun r _ => by simp⟩
      by_cases ha : a = h 0
      · refine ShattersP.of_eq ((tr a (by simp [ha])).subset (restrict_subset _ _ _)) ?_
        rw [hsw]; simp [ha]
      · refine ShattersP.of_eq (d := switches (h 0 :: List.ofFn (fun i => h i.succ) ++ [b]) + 1)
          ⟨0, tr false (by cases a <;> cases h0 : h 0 <;> simp_all),
          tr true (by cases a <;> cases h0 : h 0 <;> simp_all)⟩ ?_
        rw [hsw]; simp [ha, Nat.add_comm]

theorem move_e (hs : Sh true a b k n d) : Sh true a b k (2 * n + 1) (d + k) := by
  refine ShattersP.graft (ι n) hs (fun h hh hp => ?_)
  have hk := hp rfl
  have := fib_shatters b n a h
  rw [hk] at this
  refine ShattersP.transfer id ?_ ?_ (fun x => Or.inl ⟨x, fun _ _ => rfl⟩) this
  · intro h' hh'
    simp only [fib, mem_filter, mem_univ, true_and] at hh'
    simp only [id, mem_filter, mem_pathClass]
    exact ⟨by omega, hh'.1⟩
  · intro h' _ hp' _; simpa [hk] using hp'

end ExactLittlestone
