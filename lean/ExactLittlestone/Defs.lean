import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Log

namespace ExactLittlestone

abbrev Hyp (m : ℕ) := Fin m → Bool

def restrict {m : ℕ} (H : Finset (Hyp m)) (x : Fin m) (b : Bool) : Finset (Hyp m) :=
  H.filter (fun h => h x = b)

def Shatters {m : ℕ} : Finset (Hyp m) → ℕ → Prop
  | H, 0 => H.Nonempty
  | H, d + 1 => ∃ x : Fin m, Shatters (restrict H x false) d ∧ Shatters (restrict H x true) d

instance decShatters {m : ℕ} : ∀ (H : Finset (Hyp m)) (d : ℕ), Decidable (Shatters H d)
  | H, 0 => inferInstanceAs (Decidable H.Nonempty)
  | H, d + 1 =>
    haveI : ∀ x : Fin m, Decidable (Shatters (restrict H x false) d ∧
        Shatters (restrict H x true) d) := fun _ =>
      @instDecidableAnd _ _ (decShatters _ d) (decShatters _ d)
    inferInstanceAs (Decidable (∃ x : Fin m, Shatters (restrict H x false) d ∧
        Shatters (restrict H x true) d))

def ldim {m : ℕ} (H : Finset (Hyp m)) : ℕ :=
  Nat.findGreatest (fun d => Shatters H d) m

def interval {m : ℕ} (a b : ℕ) : Hyp m := fun x => decide (a ≤ x.val ∧ x.val ≤ b)

def intervals (m : ℕ) : Finset (Hyp m) :=
  insert (fun _ => false)
    (((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≤ p.2)).image
      (fun p => interval p.1.val p.2.val))

def P : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 5
  | d + 4 => if d % 2 = 0 then 7 * 2 ^ (d / 2) else 5 * 2 ^ ((d - 1) / 2 + 1)

end ExactLittlestone
