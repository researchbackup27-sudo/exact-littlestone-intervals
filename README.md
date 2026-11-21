# exact-littlestone-intervals

Reference implementation for:

**How many mistakes does it take to learn an interval? Exact Littlestone dimensions of intervals and their unions**

## Contents

- `littlestone_intervals.py`: the definitions, recursions and dynamic programs of the paper, in its notation.
- `optimal_learner.py`: the explicit optimal online learner from the upper-bound proof (gap potential and block pairing), for intervals, unions of intervals and switch-bounded sequences with fixed ends (the families R_k and G_k of the paper); O(log m) time per round for a fixed number of switches.
- `demo.py`: reruns the computational checks of the paper and prints PASS or FAIL for each; its last step plays the learner against an exhaustive adaptive adversary on small domains.
- `benchmark.py`: mistakes and time per round of the optimal learner and the natural learner on random interval targets and random orders. Optimal refers to the worst case; on these random streams the natural learner makes fewer mistakes on average.

```
python3 demo.py           # about 40 seconds
python3 demo.py --full    # the paper's full ranges, about 15 minutes
python3 benchmark.py      # a few seconds
```

Python 3.9 or later, standard library only.

## Formal proof

`lean/` contains formal proofs, in Lean 4 with Mathlib, of Theorem 1 (both formulas), Theorems 2 and 4, the
two identities of Corollary 5 and Proposition 6. See `lean/README.md` for what is proved and how to build it.

## License

MIT, see `LICENSE`.
