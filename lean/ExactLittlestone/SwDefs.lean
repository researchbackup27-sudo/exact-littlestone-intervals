import ExactLittlestone.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset

namespace ExactLittlestone

def switches : List Bool → ℕ
  | a :: b :: l => (if a = b then 0 else 1) + switches (b :: l)
  | _ => 0

def pathClass (a b : Bool) (k n : ℕ) : Finset (Hyp n) :=
  Finset.univ.filter (fun h => switches (a :: List.ofFn h ++ [b]) ≤ k)

def cyc (k x : ℕ) : Finset (Hyp (x - 1)) := pathClass false false k (x - 1)

def gap (k x : ℕ) : Finset (Hyp (x - 1)) := pathClass false true k (x - 1)

def switchSeq (n k : ℕ) : Finset (Hyp n) :=
  Finset.univ.filter (fun h => switches (List.ofFn h) ≤ k)

def unions (j m : ℕ) : Finset (Hyp m) :=
  Finset.univ.filter (fun h =>
    ∃ S ∈ (intervals m).powerset, S.card ≤ j ∧ ∀ x, h x = true ↔ ∃ I ∈ S, I x = true)

def dk (k : ℕ) : ℕ := (3 * k + 1) / 2

def Q (k d : ℕ) : ℕ :=
  if d ≤ k then d + 1
  else if d < dk k + k then 2 * d + 1 - k
  else if k = 0 then 0
  else 2 * Q k (d - k)
termination_by d
decreasing_by omega

def v (k x : ℕ) : ℕ := Nat.findGreatest (fun d => Q k d ≤ x) x

end ExactLittlestone
