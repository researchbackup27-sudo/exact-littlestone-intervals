# Formal proof of Theorems 1, 2 and 4 and Proposition 6 (Lean 4)

Formal proof, in Lean 4 with Mathlib, of Theorems 1, 2 and 4, of the two identities of Corollary 5 and of
Proposition 6 of the paper "How many mistakes does it take to
learn an interval? Exact Littlestone dimensions of intervals and their unions".

## What is proved

### Theorem 1

For the class `Int_m` of intervals on `m` points (all sets of consecutive points of `{1, ..., m}`,
plus the empty set):

- `main`: for every `m` and `d`, `Int_m` shatters depth `d` exactly when `P(d) ≤ m + 1` (and
  `main_tree`: the same with shattered complete mistake trees);
- `ldim_intervals_isGreatest`, `ldim_intervals`: `Ldim(Int_m) = max {d : P(d) ≤ m + 1}`;
- `ldim_intervals_closed_form`: for `m ≥ 3`,
  `Ldim(Int_m) = max(2 ⌊lg (4(m+1)/7)⌋, 2 ⌊lg (2(m+1)/5)⌋ + 1)`. The quotients are integer divisions
  in Lean; this is the paper's expression because `⌊lg x⌋ = ⌊lg ⌊x⌋⌋` for `x ≥ 1`.

The Littlestone dimension is defined by the recursion of Fact 7 (i) (`Shatters` in `Defs.lean`);
`shatters_iff_tree` proves that this is the dimension defined by complete shattered mistake trees,
and `mem_intervals_paper` and the `P_paper_*` lemmas restate `Int_m` and `P` in the paper's
notation.

### Theorems 2 and 4, Corollary 5

`pathClass a b k n` is the class of sequences `a, f(1), ..., f(n), b` with at most `k` switches, as a
class on the `n` free points. The cycle family `R_k(x)` is `cyc k x = pathClass false false k (x - 1)`:
the cycle of `x` points is read from its fixed point `0` around and back to it. The gap family
`G_k(x)` is `gap k x = pathClass false true k (x - 1)`. `switchSeq n k` is `C_{n,k}`, `unions j m` is
`U_j(m)` (unions of at most `j` members of `intervals m`), and `Q`, `v` are `Q_k`, `v_k`.

- `general` (Theorem 4): for `k ≥ 1` and `x ≥ 1`, `Ldim(R_k(x)) = v_k(x)` for even `k` and
  `Ldim(G_k(x)) = v_k(x)` for odd `k`;
- `shatters_pathClass_iff`: for any end labels `a`, `b` with `k ≡ [a ≠ b] (mod 2)` and `k ≥ 1`,
  `pathClass a b k n` shatters depth `d` exactly when `Q_k(d) ≤ n + 1`;
- `ldim_switchSeq_even` (Theorem 2): `Ldim(C_{n,2j}) = 1 + Ldim(U_j(n-1))` for `n ≥ 1`;
- `ldim_unions`, `ldim_switchSeq` (Corollary 5): `Ldim(U_j(m)) = v_{2j}(m+1)` and
  `Ldim(C_{n,2j}) = 1 + v_{2j}(n)` for `j ≥ 1` (and `n ≥ 1`);
- `unions_eq`: `U_j(m)` is exactly the class `R_{2j}(m+1)`.

`Q_of_le`, `Q_mid` and `Q_big` are the three lines of the paper's definition of `Q_k`. The proof
follows Section 7 of the paper: the potential of Lemma 19 (`SwPot.lean`, for paths with both ends
labelled), the moves of Lemma 21 (`SwMoves.lean`) and Lemma 22 (`SwQ.lean`). The pairing bound of
Lemma 20 (`SwPair.lean`) is proved by a shattering argument that charges the same switches, without
formalising learners.

### Proposition 6

- `prop6_lower`: for `n ≥ 1` and odd `k`, `1 + v_k(n) ≤ Ldim(C_{n,k})`;
- `prop6_upper`: for `n ≥ 1` and odd `k`, `Ldim(C_{n,k}) ≤ 1 + min(⌊(n+k-1)/2⌋, v_{k+1}(n))`;
- `prop6_one`: `Ldim(C_{n,1}) = 1 + ⌊lg n⌋` for `n ≥ 1`.

The bound `⌊(n+k-1)/2⌋` comes from the potential of Lemma 19 for two labelled ends after adding virtual end
labels (`SwFree.lean`). For `k = 1` the upper bound uses `|C_{n,1}| ≤ 2n` and the fact that a class shattering
depth `d` has at least `2^d` members (`SwOne.lean`).

### Not formalised

That the Littlestone dimension equals the optimal worst-case number of mistakes of an online learner
is Littlestone's theorem (1988), which is cited and not formalised here. Corollary 3, the estimates of
Corollary 5 and the results on randomised learners are also not formalised.

## Files

| File | Content |
|---|---|
| `Defs.lean` | hypotheses, `Shatters`, `ldim`, `intervals`, `P` |
| `Basic.lean` | basic facts about `Shatters` and `ldim` |
| `Game.lean` | the cutting game `Cut` on multisets of piece measures (Lemma 13) |
| `Lower.lean` | a rod of measure at least `P(d)` admits `d` cuts (Proposition 17) |
| `Upper.lean` | a rod admitting `d` cuts has measure at least `P(d)` (Proposition 18) |
| `Rect.lean` | dimension of the class left after a positive label (Lemma 12 (a)) |
| `Seg.lean` | segment classes and `Shatters ↔ Cut` (Definition 11, Lemmas 12 and 13) |
| `Main.lean` | Theorem 1 |
| `Paper.lean` | tree definition, paper notation, closed form of Theorem 1 |
| `SwDefs.lean` | `switches`, `pathClass`, `cyc`, `gap`, `switchSeq`, `unions`, `Q`, `v` |
| `SwBasic.lean` | switch counts, transfer of shattering between classes, full trees, grafting |
| `SwQ.lean` | properties of `Q_k` and `v_k` (Lemma 22) |
| `SwPot.lean` | the gap potential and `Ldim ≤ ⌊(x+k-1)/2⌋` (Lemma 19, equation (1)) |
| `SwPair.lean` | the pairing bound `L_k(x) ≤ L_k(⌊x/2⌋) + k` (Lemma 20) |
| `SwMoves.lean` | adversary moves (a)-(e) (Lemma 21) |
| `SwUnions.lean` | `U_j(m) = R_{2j}(m+1)`, the rotation of Lemma 10, Theorem 2 |
| `SwMain.lean` | Theorem 4, the general end labels, Corollary 5 |
| `SwOne.lean` | `2^d ≤ |H|` for a class shattering depth `d`; `|C_{n,1}| ≤ 2n` |
| `SwFree.lean` | the bound `⌊(n+k-1)/2⌋` after the first query on `C_{n,k}` (Proposition 6) |
| `SwProp6.lean` | Proposition 6 |
| `SwSanity.lean` | kernel checks: `Q_1..Q_4` tables, `Ldim` of small `R_k`, `G_k`, `C_{n,2}`, `U_1(3) = Int_3`, `U_2(3) = R_4(4)` |
| `Sanity.lean` | `decide` checks from the definitions: `P(0..11)`, `|Int_3|`, `|Int_4|`, `Ldim(Int_m)` for small `m`, the empty class, `m = 0` |
| `Check.lean` | prints the axioms used by the main theorems |

## Building

Install Lean with [elan](https://github.com/leanprover/elan), then in this folder:

```
lake exe cache get    # download the prebuilt Mathlib files
lake build
```

The toolchain is pinned in `lean-toolchain` (Lean 4.36.0) and Mathlib in `lakefile.toml` and
`lake-manifest.json` (tag `v4.36.0`). `Check.lean` prints the axioms of every main theorem:
`[propext, Classical.choice, Quot.sound]` or a subset, the standard axioms of Lean and nothing else. The files
contain no `sorry` and no `native_decide`.
