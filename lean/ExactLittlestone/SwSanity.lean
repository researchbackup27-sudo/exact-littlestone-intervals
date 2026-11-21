import ExactLittlestone.SwQ

namespace ExactLittlestone

set_option maxRecDepth 100000

example : (List.range 6).map (fun x => ldim (cyc 2 (x + 1))) = [0, 1, 2, 2, 3, 3] := by decide
example : (List.range 6).map (fun x => ldim (gap 1 (x + 1))) = [0, 1, 1, 2, 2, 2] := by decide
example : (List.range 6).map (fun x => ldim (gap 3 (x + 1))) = [0, 1, 2, 3, 3, 4] := by decide
example : (List.range 6).map (fun x => ldim (cyc 4 (x + 1))) = [0, 1, 2, 3, 4, 4] := by decide
example : (List.range 5).map (fun n => ldim (switchSeq (n + 1) 2)) = [1, 2, 3, 3, 4] := by decide
example : unions 1 3 = intervals 3 := by decide
example : unions 2 3 = cyc 4 4 := by decide

example : (List.range 12).map (Q 1) = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048] := by
  simp [List.range_succ, Q, dk]
example : (List.range 12).map (Q 2) = [1, 2, 3, 5, 7, 10, 14, 20, 28, 40, 56, 80] := by
  simp [List.range_succ, Q, dk]
example : (List.range 12).map (Q 3) = [1, 2, 3, 4, 6, 8, 10, 12, 16, 20, 24, 32] := by
  simp [List.range_succ, Q, dk]
example : (List.range 12).map (Q 4) = [1, 2, 3, 4, 5, 7, 9, 11, 13, 15, 18, 22] := by
  simp [List.range_succ, Q, dk]

end ExactLittlestone
