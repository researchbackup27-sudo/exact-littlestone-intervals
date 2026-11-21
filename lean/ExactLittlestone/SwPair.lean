import ExactLittlestone.SwPot
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ExactLittlestone

open Finset

variable {a b : Bool} {k n m : ℕ}

def padB (a b : Bool) (f : Fin n → Bool) (p : ℕ) : Bool :=
  if p = 0 then a else if h : p - 1 < n then f ⟨p - 1, h⟩ else b

def padO (a b : Bool) (σ : Fin n → Option Bool) (p : ℕ) : Option Bool :=
  if p = 0 then some a else if h : p - 1 < n then σ ⟨p - 1, h⟩ else some b

theorem getElem?_pad (f : Fin n → Bool) (p : ℕ) :
    (a :: List.ofFn f ++ [b])[p]? = if p ≤ n + 1 then some (padB a b f p) else none := by
  rcases p with _ | p
  · simp [padB]
  · simp only [List.getElem?_cons_succ, padB, List.getElem?_append]
    split_ifs <;> simp_all <;> omega

theorem switches_eq_card : ∀ l : List Bool,
    switches l = ((range (l.length - 1)).filter (fun i => l.getD i false ≠ l.getD (i + 1) false)).card
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
      rw [switches_cc, switches_eq_card (y :: t), card_eq_sum_ones, card_eq_sum_ones, sum_filter,
        sum_filter]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      split_ifs <;> simp_all [Nat.add_comm]

theorem padB_of_padO {σ : Fin n → Option Bool} {f : Hyp n} (hc : Consistent σ f) {p : ℕ}
    {u : Bool} (h : padO a b σ p = some u) : padB a b f p = u := by
  unfold padO at h; unfold padB
  split_ifs at h ⊢
  · simpa using h
  · exact hc _ _ h
  · simpa using h

theorem padO_update (σ : Fin n → Option Bool) (z : Fin n) (v : Option Bool) (p : ℕ) :
    padO a b (Function.update σ z v) p = if p = z.val + 1 then v else padO a b σ p := by
  unfold padO
  simp only [Function.update_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem padO_succ (σ : Fin n → Option Bool) (z : Fin n) : padO a b σ (z.val + 1) = σ z := by
  unfold padO; rw [ite_eq_right (by omega), dite_eq_left (by omega)]; rfl

theorem padO_none {σ : Fin n → Option Bool} {p : ℕ} (h : padO a b σ p = none) : 1 ≤ p ∧ p ≤ n := by
  unfold padO at h; split_ifs at h; omega

theorem padO_mono {σ : Fin n → Option Bool} {z : Fin n} (hz : σ z = none) (v : Option Bool)
    {p : ℕ} {u : Bool} (h : padO a b σ p = some u) : padO a b (Function.update σ z v) p = some u := by
  rw [padO_update]; split_ifs with hp
  · subst hp; rw [padO_succ, hz] at h; cases h
  · exact h

def Rev (a b : Bool) (σ : Fin n → Option Bool) (s : ℕ) : Prop :=
  ∃ u, padO a b σ s = some u ∧ padO a b σ (s + 1) = some (!u)

instance (σ : Fin n → Option Bool) : DecidablePred (Rev a b σ) := fun _ => by
  unfold Rev; infer_instance

def w (a b : Bool) (σ : Fin n → Option Bool) : ℕ := ((range (n + 1)).filter (Rev a b σ)).card

theorem w_le {σ : Fin n → Option Bool} {f : Hyp n} (hf : f ∈ vs a b k n σ) : w a b σ ≤ k := by
  simp only [vs, mem_filter, mem_pathClass] at hf
  refine le_trans ?_ hf.1
  rw [switches_eq_card]
  simp only [List.length_cons, List.length_append, List.length_ofFn]
  apply card_le_card
  intro s hs
  simp only [mem_filter, mem_range] at hs ⊢
  obtain ⟨hs, u, h1, h2⟩ := hs
  refine ⟨hs, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_pad, getElem?_pad,
    ite_eq_left (by omega), ite_eq_left (by omega), Option.getD_some, Option.getD_some,
    padB_of_padO hf.2 h1, padB_of_padO hf.2 h2]
  cases u <;> simp

theorem w_mono {σ : Fin n → Option Bool} {z : Fin n} (hz : σ z = none) (v : Option Bool) :
    w a b σ ≤ w a b (Function.update σ z v) := by
  apply card_le_card
  intro s hs
  simp only [mem_filter, Rev] at hs ⊢
  obtain ⟨hs, u, h1, h2⟩ := hs
  exact ⟨hs, u, padO_mono hz v h1, padO_mono hz v h2⟩

theorem w_succ {σ : Fin n → Option Bool} {z : Fin n} (hz : σ z = none) {q : ℕ} {u : Bool}
    (hq : q = z.val + 2 ∨ q = z.val) (hu : padO a b σ q = some u) :
    w a b σ + 1 ≤ w a b (Function.update σ z (some (!u))) := by
  have hsub : (range (n + 1)).filter (Rev a b σ) ⊆
      (range (n + 1)).filter (Rev a b (Function.update σ z (some (!u)))) := by
    intro s hs
    simp only [mem_filter, Rev] at hs ⊢
    obtain ⟨hs, u', h1, h2⟩ := hs
    exact ⟨hs, u', padO_mono hz _ h1, padO_mono hz _ h2⟩
  have hp := padO_succ (a := a) (b := b) σ z
  rw [hz] at hp
  have hz' := z.2
  refine card_lt_card ((ssubset_iff_of_subset hsub).mpr ⟨min q (z.val + 1), ?_, ?_⟩)
  · simp only [mem_filter, mem_range, Rev]
    refine ⟨by omega, ?_⟩
    rcases hq with rfl | rfl
    · refine ⟨!u, ?_, ?_⟩
      · rw [padO_update, ite_eq_left (by omega)]
      · rw [padO_update, ite_eq_right (by omega), Bool.not_not, show min (z.val + 2) (z.val + 1) + 1 =
          z.val + 2 by omega, hu]
    · refine ⟨u, ?_, ?_⟩
      · rw [padO_update, ite_eq_right (by omega), show min z.val (z.val + 1) = z.val by omega, hu]
      · rw [padO_update, ite_eq_left (by omega)]
  · simp only [mem_filter, Rev, not_and, not_exists]
    intro _ u' h1 h2
    rcases hq with rfl | rfl
    · rw [show min (z.val + 2) (z.val + 1) = z.val + 1 by omega, hp] at h1; cases h1
    · rw [show min z.val (z.val + 1) + 1 = z.val + 1 by omega, hp] at h2; cases h2

def Compat (a b : Bool) (σ : Fin n → Option Bool) (τ : Fin m → Option Bool) : Prop :=
  ∀ j : Fin m, (τ j = none → padO a b σ (2 * j.val + 2) = none ∧ padO a b σ (2 * j.val + 3) = none) ∧
    ∀ v, τ j = some v → padO a b σ (2 * j.val + 2) = some v ∨ padO a b σ (2 * j.val + 3) = some v

theorem compat_keep {σ : Fin n → Option Bool} {τ : Fin m → Option Bool} (hC : Compat a b σ τ)
    {z : Fin n} (hz : σ z = none) {q : ℕ} {u : Bool}
    (hq : (z.val + 1) % 2 = 0 ∧ q = z.val + 2 ∨ (z.val + 1) % 2 = 1 ∧ q = z.val)
    (hu : padO a b σ q = some u) (c : Option Bool) : Compat a b (Function.update σ z c) τ := by
  intro j
  obtain ⟨h1, h2⟩ := hC j
  refine ⟨fun hj => ?_, fun v hv => (h2 v hv).imp (padO_mono hz c) (padO_mono hz c)⟩
  obtain ⟨e2, e3⟩ := h1 hj
  rw [padO_update, padO_update]
  refine ⟨?_, ?_⟩ <;> split_ifs with h <;> try assumption
  · rw [show q = 2 * j.val + 3 by omega, e3] at hu; cases hu
  · rw [show q = 2 * j.val + 2 by omega, e2] at hu; cases hu

theorem compat_new {σ : Fin n → Option Bool} {τ : Fin m → Option Bool} (hC : Compat a b σ τ)
    {z : Fin n} (hz : σ z = none) {q : ℕ} (hq : padO a b σ q = none) (J : Fin m)
    (hJ : 2 * J.val + 2 = z.val + 1 ∧ 2 * J.val + 3 = q ∨ 2 * J.val + 2 = q ∧ 2 * J.val + 3 = z.val + 1)
    (c : Bool) : τ J = none ∧ Compat a b (Function.update σ z (some c)) (Function.update τ J (some c)) := by
  have hp := padO_succ (a := a) (b := b) σ z
  rw [hz] at hp
  have hτ : τ J = none := by
    cases h : τ J with
    | none => rfl
    | some v =>
      exfalso
      rcases hJ with ⟨e2, e3⟩ | ⟨e2, e3⟩ <;> rcases (hC J).2 v h with h' | h'
      · rw [e2, hp] at h'; cases h'
      · rw [e3, hq] at h'; cases h'
      · rw [e2, hq] at h'; cases h'
      · rw [e3, hp] at h'; cases h'
  refine ⟨hτ, fun j => ?_⟩
  by_cases hj : j = J
  · subst hj
    simp only [Function.update_self, reduceCtorEq, false_imp_iff, true_and, Option.some.injEq]
    rintro v rfl
    rw [padO_update, padO_update]
    rcases hJ with ⟨e2, e3⟩ | ⟨e2, e3⟩
    · left; rw [ite_eq_left e2]
    · right; rw [ite_eq_left e3]
  · rw [Function.update_of_ne hj]
    have hne : j.val ≠ J.val := fun h => hj (Fin.ext h)
    obtain ⟨h1, h2⟩ := hC j
    rw [padO_update, padO_update, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact ⟨h1, h2⟩

theorem vs_nonempty_coarse (hm : m = (n + 1) / 2 - 1) {σ : Fin n → Option Bool}
    {τ : Fin m → Option Bool} (hC : Compat a b σ τ) {f : Hyp n} (hf : f ∈ vs a b k n σ) :
    (vs a b k m τ).Nonempty := by
  let τN : ℕ → Option Bool := fun j => if h : j < m then τ ⟨j, h⟩ else none
  let idx : ℕ → ℕ := fun j => if padO a b σ (2 * j + 3) = τN j then 2 * j + 2 else 2 * j + 1
  let g : Hyp m := fun j => padB a b f (idx j.val + 1)
  let φ : ℕ → ℕ := fun i => if i = 0 then 0 else if i ≤ m then idx (i - 1) + 1 else i + n - m
  have hidx : ∀ j, 2 * j + 1 ≤ idx j ∧ idx j ≤ 2 * j + 2 := fun j => by
    simp only [idx]; split_ifs <;> omega
  have hφ : StrictMono φ := by
    intro i i' hii
    have := hidx (i - 1); have := hidx (i' - 1)
    simp only [φ]; split_ifs <;> omega
  simp only [vs, mem_filter, mem_pathClass] at hf
  refine ⟨g, mem_filter.mpr ⟨mem_pathClass.mpr (le_trans (switches_sublist ?_).1 hf.1), ?_⟩⟩
  · refine List.sublist_iff_exists_orderEmbedding_getElem?_eq.mpr
      ⟨OrderEmbedding.ofStrictMono φ hφ, fun i => ?_⟩
    simp only [OrderEmbedding.coe_ofStrictMono, getElem?_pad]
    have := hidx (i - 1)
    by_cases hi : i ≤ m + 1
    · rw [ite_eq_left hi, ite_eq_left (by simp only [φ]; split_ifs <;> omega)]
      congr 1
      by_cases h0 : i = 0
      · subst h0; simp [padB, φ]
      by_cases hl : i ≤ m
      · simp only [padB, φ, g, ite_eq_right h0, ite_eq_left hl, dite_eq_left (show i - 1 < m by omega),
          Nat.add_sub_cancel]
      · simp only [padB, φ, ite_eq_right h0, ite_eq_right hl, dite_eq_right (show ¬ i - 1 < m by omega)]
        rw [ite_eq_right (by omega), dite_eq_right (by omega)]
    · rw [ite_eq_right hi, ite_eq_right (by simp only [φ]; split_ifs <;> omega)]
  · intro j v hv
    have hτ : τN j.val = τ j := dite_eq_left j.2
    simp only [g, idx, hτ, hv]
    split_ifs with h
    · exact padB_of_padO hf.2 h
    · rcases (hC j).2 v hv with h' | h'
      · exact padB_of_padO hf.2 h'
      · exact absurd h' h

theorem shatters_coarse (hm : m = (n + 1) / 2 - 1) : ∀ (D : ℕ) (σ : Fin n → Option Bool)
    (τ : Fin m → Option Bool), Compat a b σ τ → Shatters (vs a b k n σ) D →
    ∃ D', D ≤ D' + (k - w a b σ) ∧ Shatters (vs a b k m τ) D'
  | 0, σ, τ, hC, hs => by
      obtain ⟨f, hf⟩ := hs.nonempty
      exact ⟨0, by omega, vs_nonempty_coarse hm hC hf⟩
  | D + 1, σ, τ, hC, hs => by
      obtain ⟨z, s0, s1⟩ := shatters_succ.mp hs
      cases hz : σ z with
      | some v =>
        exfalso
        have hne : (restrict (vs a b k n σ) z (!v)).Nonempty := by
          cases v
          · exact s1.nonempty
          · exact s0.nonempty
        obtain ⟨h, hh⟩ := hne
        simp only [restrict, vs, mem_filter, Consistent] at hh
        have := hh.1.2 z v hz
        rw [hh.2] at this; cases v <;> simp at this
      | none =>
        rw [restrict_vs hz] at s0 s1
        have hs' : ∀ c, Shatters (vs a b k n (Function.update σ z (some c))) D := fun c => by
          cases c <;> assumption
        have hz' := z.2
        have hq : (z.val + 1) % 2 = 0 ∧ (if (z.val + 1) % 2 = 0 then z.val + 2 else z.val) = z.val + 2 ∨
            (z.val + 1) % 2 = 1 ∧ (if (z.val + 1) % 2 = 0 then z.val + 2 else z.val) = z.val := by
          split_ifs <;> omega
        generalize (if (z.val + 1) % 2 = 0 then z.val + 2 else z.val) = q at hq
        cases hu : padO a b σ q with
        | some u =>
          obtain ⟨D', h1, h2⟩ :=
            shatters_coarse hm D _ τ (compat_keep hC hz hq hu (some (!u))) (hs' (!u))
          have hw := w_succ hz (by omega) hu
          obtain ⟨f, hf⟩ := (hs' (!u)).nonempty
          have hk := w_le hf
          exact ⟨D', by omega, h2⟩
        | none =>
          have hq' := padO_none hu
          let J : Fin m := ⟨(z.val + 1) / 2 - 1, by omega⟩
          have hJ : 2 * J.val + 2 = z.val + 1 ∧ 2 * J.val + 3 = q ∨
              2 * J.val + 2 = q ∧ 2 * J.val + 3 = z.val + 1 := by simp only [J]; omega
          have hn := fun c => compat_new hC hz hu J hJ c
          obtain ⟨E0, e0, t0⟩ := shatters_coarse hm D _ _ (hn false).2 (hs' false)
          obtain ⟨E1, e1, t1⟩ := shatters_coarse hm D _ _ (hn true).2 (hs' true)
          have w0 := w_mono (a := a) (b := b) hz (some false)
          have w1 := w_mono (a := a) (b := b) hz (some true)
          refine ⟨min E0 E1 + 1, by omega, shatters_succ.mpr ⟨J, ?_, ?_⟩⟩
          · rw [restrict_vs (hn false).1]; exact t0.mono (min_le_left _ _)
          · rw [restrict_vs (hn true).1]; exact t1.mono (min_le_right _ _)

theorem pair_bound {a b : Bool} {k n D : ℕ} (hs : Shatters (pathClass a b k n) D) :
    ∃ D', D ≤ D' + k ∧ Shatters (pathClass a b k ((n + 1) / 2 - 1)) D' := by
  rw [← vs_none] at hs
  have hC : Compat a b (fun _ : Fin n => none) (fun _ : Fin ((n + 1) / 2 - 1) => none) := by
    intro j
    have := j.2
    refine ⟨fun _ => ⟨?_, ?_⟩, fun v h => by cases h⟩ <;> unfold padO <;>
      rw [ite_eq_right (by omega), dite_eq_left (by omega)]
  obtain ⟨D', h1, h2⟩ := shatters_coarse rfl D _ _ hC hs
  exact ⟨D', by omega, by rwa [vs_none] at h2⟩

end ExactLittlestone
