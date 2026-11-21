import ExactLittlestone.SwBasic

namespace ExactLittlestone

open Finset

def numA : Bool → List (Option Bool) → ℕ
  | _, [] => 0
  | u, none :: l => numA u l
  | u, some w :: l => (if u = w then 0 else 1) + numA w l

def gsum : Bool → ℕ → List (Option Bool) → ℕ
  | _, _, [] => 0
  | u, g, none :: l => gsum u (g + 1) l
  | u, g, some w :: l => (g + if u = w then 0 else 1) / 2 + gsum w 0 l

theorem numA_rep (u : Bool) (j : ℕ) (l : List (Option Bool)) :
    numA u (List.replicate j none ++ l) = numA u l := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.cons_append, numA, ih]

theorem gsum_rep (u : Bool) (j : ℕ) : ∀ (g : ℕ) (l : List (Option Bool)),
    gsum u g (List.replicate j none ++ l) = gsum u (g + j) l := by
  induction j with
  | zero => intro g l; rfl
  | succ j ih => intro g l; rw [List.replicate_succ, List.cons_append, gsum, ih]; congr 1; omega

theorem pot_step (g' : ℕ) (w : Bool) (l₃ : List (Option Bool)) :
    ∀ (l₁ : List (Option Bool)) (k : ℕ) (u : Bool) (g : ℕ),
    numA u (l₁ ++ some false :: (List.replicate g' none ++ some w :: l₃)) ≤ k →
    numA u (l₁ ++ some true :: (List.replicate g' none ++ some w :: l₃)) ≤ k →
    ∃ c : Bool,
      (k - numA u (l₁ ++ some c :: (List.replicate g' none ++ some w :: l₃))) / 2 +
        gsum u g (l₁ ++ some c :: (List.replicate g' none ++ some w :: l₃)) + 1 ≤
      (k - numA u (l₁ ++ none :: (List.replicate g' none ++ some w :: l₃))) / 2 +
        gsum u g (l₁ ++ none :: (List.replicate g' none ++ some w :: l₃)) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro k u g h0 h1
    simp only [List.nil_append, numA, gsum, numA_rep, gsum_rep] at h0 h1 ⊢
    cases u <;> cases w <;> simp at h0 h1 ⊢ <;>
    rcases Nat.mod_two_eq_zero_or_one g with hr | hr <;>
    rcases Nat.mod_two_eq_zero_or_one g' with hs | hs <;>
    first
      | exact Or.inl (by omega)
      | exact Or.inr (by omega)
  | cons e l₁ ih =>
    intro k u g h0 h1
    cases e with
    | none =>
      simp only [List.cons_append, numA, gsum] at h0 h1 ⊢
      exact ih k u (g + 1) h0 h1
    | some x =>
      simp only [List.cons_append, numA, gsum] at h0 h1 ⊢
      obtain ⟨c, hc⟩ := ih (k - if u = x then 0 else 1) x 0 (by omega) (by omega)
      exact ⟨c, by
        cases u <;> cases x <;> simp at hc ⊢ <;> omega⟩

def labels : List (Option Bool) → List Bool
  | [] => []
  | none :: l => labels l
  | some w :: l => w :: labels l

theorem labels_append : ∀ l l' : List (Option Bool), labels (l ++ l') = labels l ++ labels l'
  | [], _ => rfl
  | none :: l, l' => labels_append l l'
  | some w :: l, l' => by rw [List.cons_append, labels, labels, labels_append]; rfl

theorem numA_eq_switches : ∀ (u : Bool) (l : List (Option Bool)),
    numA u l = switches (u :: labels l)
  | _, [] => rfl
  | u, none :: l => by rw [numA, labels, numA_eq_switches]
  | u, some w :: l => by
      rw [numA, labels, switches_cc, numA_eq_switches]

variable {a b : Bool} {k n : ℕ}

def Consistent {n : ℕ} (σ : Fin n → Option Bool) (h : Hyp n) : Prop := ∀ i v, σ i = some v → h i = v

instance {n : ℕ} (σ : Fin n → Option Bool) (h : Hyp n) : Decidable (Consistent σ h) := by
  unfold Consistent; infer_instance

def vs (a b : Bool) (k n : ℕ) (σ : Fin n → Option Bool) : Finset (Hyp n) :=
  (pathClass a b k n).filter (Consistent σ)

def pot (a b : Bool) (k n : ℕ) (σ : Fin n → Option Bool) : ℕ :=
  (k - numA a (List.ofFn σ ++ [some b])) / 2 + gsum a 0 (List.ofFn σ ++ [some b])

theorem labels_sublist : ∀ {n : ℕ} (σ : Fin n → Option Bool) (h : Hyp n), Consistent σ h →
    (labels (List.ofFn σ)).Sublist (List.ofFn h)
  | 0, _, _, _ => by simp [labels]
  | n + 1, σ, h, hc => by
      have ih := labels_sublist (fun i => σ i.succ) (fun i => h i.succ)
        (fun i v hv => hc i.succ v hv)
      rw [List.ofFn_succ, List.ofFn_succ]
      cases h0 : σ 0 with
      | none => rw [labels]; exact ih.cons _
      | some v =>
        rw [labels, hc 0 v h0]; exact ih.cons_cons _

theorem numA_le {σ : Fin n → Option Bool} {h : Hyp n} (hh : h ∈ vs a b k n σ) :
    numA a (List.ofFn σ ++ [some b]) ≤ k := by
  simp only [vs, mem_filter, mem_pathClass] at hh
  rw [numA_eq_switches, labels_append]
  refine le_trans ?_ hh.1
  have hs : (a :: (labels (List.ofFn σ) ++ [b])).Sublist (a :: (List.ofFn h ++ [b])) :=
    List.Sublist.cons_cons a ((labels_sublist σ h hh.2).append (List.Sublist.refl [b]))
  simpa [labels] using (switches_sublist hs).1

theorem ofFn_split : ∀ {n : ℕ} (σ : Fin n → Option Bool) (z : Fin n),
    ∃ l₁ l₂, List.ofFn σ = l₁ ++ σ z :: l₂ ∧
      ∀ v, List.ofFn (Function.update σ z v) = l₁ ++ v :: l₂
  | 0, _, z => z.elim0
  | n + 1, σ, z => by
      refine Fin.cases ?_ (fun z' => ?_) z
      · refine ⟨[], List.ofFn (fun i => σ i.succ), by rw [List.ofFn_succ]; rfl, fun v => ?_⟩
        rw [List.ofFn_succ]
        simp
      · obtain ⟨l₁, l₂, h1, h2⟩ := ofFn_split (fun i => σ i.succ) z'
        refine ⟨σ 0 :: l₁, l₂, by rw [List.ofFn_succ, h1]; rfl, fun v => ?_⟩
        rw [List.ofFn_succ, Function.update_of_ne (Fin.succ_ne_zero _).symm]
        have : (fun i : Fin n => Function.update σ z'.succ v i.succ) =
            Function.update (fun i => σ i.succ) z' v := by
          funext i
          by_cases hi : i = z'
          · subst hi; simp
          · rw [Function.update_of_ne (fun h => hi (Fin.succ_injective _ h)),
              Function.update_of_ne hi]
        rw [this, h2]; rfl

theorem ends_decomp (c : Bool) : ∀ l : List (Option Bool),
    ∃ g' w l₃, l ++ [some c] = List.replicate g' none ++ some w :: l₃
  | [] => ⟨0, c, [], rfl⟩
  | none :: l => by
      obtain ⟨g', w, l₃, h⟩ := ends_decomp c l
      exact ⟨g' + 1, w, l₃, by rw [List.cons_append, h]; rfl⟩
  | some w :: l => ⟨0, w, l ++ [some c], rfl⟩

theorem restrict_vs {σ : Fin n → Option Bool} {z : Fin n} (hz : σ z = none) (c : Bool) :
    restrict (vs a b k n σ) z c = vs a b k n (Function.update σ z (some c)) := by
  ext h
  simp only [restrict, vs, mem_filter, Consistent]
  constructor
  · rintro ⟨⟨hp, hc⟩, hzc⟩
    refine ⟨hp, fun i v hv => ?_⟩
    by_cases hi : i = z
    · subst hi; simp at hv; rw [← hv, hzc]
    · rw [Function.update_of_ne hi] at hv; exact hc i v hv
  · rintro ⟨hp, hc⟩
    refine ⟨⟨hp, fun i v hv => hc i v ?_⟩, hc z c (by simp)⟩
    by_cases hi : i = z
    · subst hi; rw [hz] at hv; cases hv
    · rw [Function.update_of_ne hi]; exact hv

theorem pot_decrease {σ : Fin n → Option Bool} {z : Fin n} (hz : σ z = none)
    (h0 : (vs a b k n (Function.update σ z (some false))).Nonempty)
    (h1 : (vs a b k n (Function.update σ z (some true))).Nonempty) :
    ∃ c, pot a b k n (Function.update σ z (some c)) + 1 ≤ pot a b k n σ := by
  obtain ⟨l₁, l₂, hσ, hupd⟩ := ofFn_split σ z
  obtain ⟨g', w, l₃, hl⟩ := ends_decomp b l₂
  obtain ⟨f0, hf0⟩ := h0
  obtain ⟨f1, hf1⟩ := h1
  have n0 := numA_le hf0
  have n1 := numA_le hf1
  simp only [pot, hupd, hσ, hz, List.append_assoc, List.cons_append, hl] at n0 n1 ⊢
  exact pot_step g' w l₃ l₁ k a 0 n0 n1

theorem shatters_vs_le : ∀ (D : ℕ) (σ : Fin n → Option Bool),
    Shatters (vs a b k n σ) D → D ≤ pot a b k n σ
  | 0, _, _ => Nat.zero_le _
  | D + 1, σ, hs => by
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
        obtain ⟨c, hc⟩ := pot_decrease hz s0.nonempty s1.nonempty
        have := shatters_vs_le D (Function.update σ z (some c)) (by cases c <;> assumption)
        omega

theorem vs_none : vs a b k n (fun _ => none) = pathClass a b k n := by
  ext h; simp [vs, Consistent]

theorem pathClass_le_half {D : ℕ} (hs : Shatters (pathClass a b k n) D) : D ≤ (n + k) / 2 := by
  rw [← vs_none] at hs
  obtain ⟨h, hh⟩ := hs.nonempty
  have hk := numA_le hh
  have := shatters_vs_le D _ hs
  simp only [pot, List.ofFn_const, numA_rep, gsum_rep, numA, gsum] at this hk
  cases a <;> cases b <;> simp at this hk <;> omega

end ExactLittlestone
