import ExactLittlestone.Defs

namespace ExactLittlestone

example : (List.range 12).map P = [1, 2, 3, 5, 7, 10, 14, 20, 28, 40, 56, 80] := by decide

example : (intervals 3).card = 7 := by decide
example : (intervals 4).card = 11 := by decide

example : Shatters (intervals 1) 1 ∧ ¬ Shatters (intervals 1) 2 := by decide
example : Shatters (intervals 2) 2 ∧ ¬ Shatters (intervals 2) 3 := by decide
example : Shatters (intervals 3) 2 ∧ ¬ Shatters (intervals 3) 3 := by decide
example : Shatters (intervals 4) 3 ∧ ¬ Shatters (intervals 4) 4 := by decide

set_option maxRecDepth 100000 in
example : Shatters (intervals 6) 4 ∧ ¬ Shatters (intervals 5) 4 := by decide

example : ¬ Shatters (∅ : Finset (Hyp 3)) 0 := by decide
example : Shatters (intervals 0) 0 ∧ ¬ Shatters (intervals 0) 1 := by decide

example : (List.range 4).map (fun i => ldim (intervals (i + 1))) = [1, 2, 2, 3] := by decide

end ExactLittlestone
