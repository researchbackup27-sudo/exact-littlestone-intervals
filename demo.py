"""Reproduces the computational verification of the paper

    How many mistakes does it take to learn an interval?
    Exact Littlestone dimensions of intervals and their unions.

Steps [1/11] to [9/11] rerun the rows of the verification table in the paper's
section "Computational verification" (Table 5 of the submitted version); each
step header names the statements it checks. Step [10/11] compares independently
written implementations with each other. Step [11/11] reruns the last row of the
table: the explicit optimal learner of optimal_learner.py and the natural
learner against an exhaustive adaptive adversary, and the mistake bound of the
learner's recursion. Every line prints PASS or FAIL together with the range it
covers, and the exit status is nonzero if any check fails.

    python3 demo.py            all checks; the four long runs use smaller ranges
                               (about 40 seconds on a laptop CPU)
    python3 demo.py --full     the paper's ranges everywhere (about 15 minutes,
                               about 2 GB of memory)
    python3 demo.py --steps 4,9 --full    selected steps only

The ranges that differ between the two modes are the tree minimisation
(d <= 16 by default, d <= 19 with --full), the cyclic gap game for U_2 and U_3
(m <= 30 and m <= 22 by default, m <= 45 and m <= 28 with --full), the
discounted cutting game for randomised learners (m <= 40 by default, m <= 70
with --full), and the exhaustive adversary of step 11 (m <= 8 and k <= 4,
x <= 9 by default; m <= 10, k <= 6, x <= 10 and G_3(x) for x <= 13 with --full).
In these ranges the pairing step of the learner is reached for k = 1 and 2, and
with --full also for k = 3. All other checks always run on the paper's ranges.
Standard library only; everything is computed exactly unless a line says
"float".
"""

import argparse
import math
import sys
import time
from fractions import Fraction
from functools import lru_cache

import littlestone_intervals as li
import optimal_learner as ol

QUICK = {"tree_d": 16, "U2_m": 30, "U3_m": 22, "rl_m": 40, "adv_m": 8, "adv_k": 4, "adv_x": 9, "adv_g3": 0}
FULL = {"tree_d": 19, "U2_m": 45, "U3_m": 28, "rl_m": 70, "adv_m": 10, "adv_k": 6, "adv_x": 10, "adv_g3": 13}

FAILED = []


def check(ok, text, detail=""):
    """Print one PASS/FAIL line; remember failures for the exit status."""
    print(f"  {'PASS' if ok else 'FAIL'}  {text}" + ("" if ok else f"   {detail}"))
    if not ok:
        FAILED.append(text)


def mismatches(items):
    """Short description of a list of mismatches."""
    items = list(items)
    return f"{len(items)} mismatches, first: {items[:4]}"


# ---------------------------------------------------------------------------
# A second generic Littlestone recursion, written separately from the module
# (it builds its own function tables and shares no code with it).
# ---------------------------------------------------------------------------

def independent_ldim(funcs, npts):
    """Ldim by Fact 7 on tuples of functions; functions are ints (bit x = value at x)."""
    @lru_cache(maxsize=None)
    def L(vs):
        if len(vs) <= 1:
            return 0
        best = 0
        for x in range(npts):
            one = tuple(f for f in vs if f >> x & 1)
            if not one or len(one) == len(vs):
                continue
            a = L(one)
            if a < best:
                continue
            zero = tuple(f for f in vs if not f >> x & 1)
            best = max(best, 1 + min(a, L(zero)))
        return best
    return L(tuple(sorted(set(funcs))))


def independent_intervals(m):
    return [0] + [sum(1 << x for x in range(a, b + 1)) for a in range(m) for b in range(a, m)]


def independent_c2(n):
    return [f for f in range(1 << n)
            if sum((f >> i & 1) != (f >> (i + 1) & 1) for i in range(n - 1)) <= 2]


def independent_P_formula(m):
    def P(d):
        return [1, 2, 3, 5][d] if d <= 3 else (5 * 2 ** (d // 2 - 1) if d % 2 else 7 * 2 ** (d // 2 - 2))
    d = 0
    while P(d + 1) <= m + 1:
        d += 1
    return d


# ---------------------------------------------------------------------------
# Steps
# ---------------------------------------------------------------------------

def step1(rng):
    print("[1/11] Generic Littlestone recursion on explicit classes "
          "(Fact 7, Theorems 1 and 2)")
    bad = [m for m in range(13)
           if li.generic_ldim(*li.intervals_class(m)) != li.ldim_intervals_formula(m)]
    check(not bad, "Ldim(Int_m) = max{d : P(d) <= m+1}, generic recursion, 0 <= m <= 12",
          mismatches(bad))
    bad = [n for n in range(1, 12)
           if li.generic_ldim(*li.switch_class(n, 2)) != 1 + li.ldim_intervals_formula(n - 1)]
    check(not bad, "Ldim(C_{n,2}) = 1 + max{d : P(d) <= n}, generic recursion, 1 <= n <= 11",
          mismatches(bad))
    bad = [m for m in range(17)
           if independent_ldim(independent_intervals(m), m) != independent_P_formula(m)]
    check(not bad, "independently written recursion: Int_m, 0 <= m <= 16", mismatches(bad))
    bad = [n for n in range(1, 14)
           if independent_ldim(independent_c2(n), n) != 1 + independent_P_formula(n - 1)]
    check(not bad, "independently written recursion: C_{n,2}, 1 <= n <= 13", mismatches(bad))


def step2(rng):
    print("[2/11] Gap-state dynamic program for C_{n,k} (Theorems 2 and 4; subsection 'Gap states and a "
          "potential')")
    bad = [n for n in range(1, 29) if li.ldim_switch_class(n, 2) != 1 + li.v(2, n)]
    check(not bad, "gap DP: Ldim(C_{n,2}) = 1 + v_2(n), 1 <= n <= 28", mismatches(bad))
    bad = [(k, n) for k in range(5) for n in range(1, 12)
           if li.ldim_switch_class(n, k) != li.generic_ldim(*li.switch_class(n, k))]
    check(not bad, "gap DP = generic recursion on explicit C_{n,k}, 0 <= k <= 4, 1 <= n <= 11",
          mismatches(bad))


def step3(rng):
    print("[3/11] Segment recursion (Lemmas 12 and 13)")
    bad = [m for m in range(61) if li.segment_ldim([m]) != li.ldim_intervals_formula(m)]
    check(not bad, "Ldim(J_{m}) = Ldim(Int_m) = max{d : P(d) <= m+1}, 0 <= m <= 60",
          mismatches(bad))


def step4(rng):
    D = rng["tree_d"]
    print("[4/11] Tree minimisation P*(d) (Lemma 15, Propositions 17 and 18)")
    table = li.tree_min_table(D)
    bad = [d for d in range(D + 1) if table[d] != li.P(d)]
    check(not bad, f"P*(d) = P(d) for 0 <= d <= {D} (up to m+1 = {li.P(D)})", mismatches(bad))
    print(f"        P*(0..{D}) = {table}")


def g_table(r, lim=300):
    """h[a][b] = min{u+v : a <= u < lim, b <= v < lim, lambda(u)+lambda(v) >= r}, by
    exhaustive search over all pairs (u, v) with suffix minima. For a, b < 40 and r <= 8 the
    optimum is at most 2^8 + 39 < lim, so the cut-off at lim does not change the minimum."""
    inf = 10 ** 9
    h = [[inf] * (lim + 1) for _ in range(lim + 1)]
    for u in range(lim - 1, 0, -1):
        row, nxt = h[u], h[u + 1]
        for vv in range(lim - 1, 0, -1):
            here = u + vv if li.lam(u) + li.lam(vv) >= r else inf
            row[vv] = min(here, nxt[vv], row[vv + 1])
    return h


def step5(rng):
    print("[5/11] Formula for g, closed form of Theorem 1, Remarks 25 and 26")
    tables = [g_table(r) for r in range(9)]
    bad = [(a, b, r) for a in range(1, 40) for b in range(1, 40) for r in range(9)
           if li.g(a, b, r) != tables[r][a][b]]
    check(not bad, "Lemma 16(b): g(a,b,r) formula = exhaustive search, "
          "1 <= a, b < 40, 0 <= r <= 8", mismatches(bad))
    bad = [r for r in range(13)
           if li.c(r) != min(u + v for u in range(1, 2 ** (r // 2 + 2)) for v in range(1, 2 ** (r // 2 + 2))
                             if li.lam(u) + li.lam(v) >= r)]
    bad += [r for r in range(31) if li.c(r) != li.g(1, 1, r)]
    check(not bad, "Lemma 16(a): c(r) formula = definition by exhaustive search for 0 <= r <= 12, "
          "and c(r) = g(1,1,r) for 0 <= r <= 30", mismatches(bad))
    M = 10 ** 5
    bad = [m for m in range(3, M) if li.ldim_intervals_closed_form(m) != li.ldim_intervals_formula(m)]
    check(not bad, "Theorem 1 closed form = max{d : P(d) <= m+1}, 3 <= m < 10^5", mismatches(bad))
    bad, eq = [], []
    for m in range(3, M):
        l, d = m + 1, li.ldim_intervals_formula(m)
        # 2 lg l - (2 lg 5 - 2) < d <= 2 lg l - (2 lg 7 - 4), as exact integer inequalities
        if not (4 * l * l < 25 * 2 ** d and 49 * 2 ** d <= 16 * l * l):
            bad.append(m)
        if 49 * 2 ** d == 16 * l * l:
            eq.append(l)
    expect_eq = [7 * 2 ** (t - 2) for t in range(2, 40) if 4 <= 7 * 2 ** (t - 2) <= M]
    check(not bad and eq == expect_eq, "Corollary 3: bounds hold for 3 <= m < 10^5, "
          "upper bound attained exactly at m+1 = 7*2^(t-2)", mismatches(bad) + f" eq={eq[:5]}")
    gaps = [li.natural_learner_mistakes(m) - li.ldim_intervals_formula(m) for m in range(1, M)]
    first = [m for m in range(1, 17) if gaps[m - 1] == 1]
    check(set(gaps) == {0, 1} and gaps.count(1) == 50847 and first == [3, 5, 7, 8, 11, 12, 15, 16],
          "natural learner: N(m) - Ldim(Int_m) in {0,1}, = 1 for exactly 50,847 of 1 <= m < 10^5 "
          "(first m = 3, 5, 7, 8, 11, 12, 15, 16)",
          f"values {sorted(set(gaps))}, count {gaps.count(1)}, first {first}")
    bad = [d for d in range(61) if not li.P(d) <= li.c(d) <= li.P(d + 1)]
    check(not bad, "P(d) <= c(d) <= P(d+1), 0 <= d <= 60", mismatches(bad))
    cb = [li.counting_bound(m) - li.ldim_intervals_formula(m) for m in range(1, M)]
    first = 1 + cb.index(1)
    check(set(cb) == {0, 1} and cb.count(1) == 62063 and first == 5,
          "counting bound: floor lg|Int_m| - Ldim(Int_m) in {0,1}, = 1 for exactly 62,063 of "
          "1 <= m < 10^5 (first m = 5)",
          f"values {sorted(set(cb))}, count {cb.count(1)}, first {first}")


def step6(rng):
    print("[6/11] Theorem 2: Ldim(C_{n,2j}) = 1 + Ldim(U_j(n-1))")
    for j in (1, 2, 3):
        bad = []
        for n in range(1, 12):
            lhs = li.ldim_switch_class(n, 2 * j)
            rhs = 1 + (li.generic_ldim(*li.unions_class(j, n - 1)) if n > 1 else 0)
            if lhs != rhs or lhs != 1 + li.v(2 * j, n):
                bad.append((n, lhs, rhs))
        check(not bad, f"k = {2 * j}: gap DP on C_{{n,{2 * j}}} = 1 + generic recursion on "
              f"U_{j}(n-1) = 1 + v_{2 * j}(n), 1 <= n <= 11", mismatches(bad))


def step7(rng):
    print("[7/11] Theorem 4 and Corollary 5: arbitrary switch budgets")
    # (a) cyclic gap game against the generic recursion on explicit U_j(m)
    bad = [(j, m) for j in (2, 3) for m in range(12)
           if not li.ldim_unions(j, m) == li.generic_ldim(*li.unions_class(j, m)) == li.v(2 * j, m + 1)]
    check(not bad, "cyclic gap game = generic recursion on U_2(m), U_3(m) = v_{2j}(m+1), "
          "0 <= m <= 11", mismatches(bad))
    # (b) cyclic gap game against v_{2j}
    for j, M in ((1, 40), (2, rng["U2_m"]), (3, rng["U3_m"])):
        bad = [m for m in range(M + 1) if li.ldim_unions(j, m) != li.v(2 * j, m + 1)]
        check(not bad, f"Ldim(U_{j}(m)) = v_{2 * j}(m+1) by the cyclic gap game, 0 <= m <= {M}",
              mismatches(bad))
        li.clear_caches()
    # (c) single-gap states G_{2s+1}(x)
    for s, X in ((0, 40), (1, 30), (2, 22), (3, 18)):
        bad = [x for x in range(1, X + 1) if li.ldim_G(2 * s + 1, x) != li.v(2 * s + 1, x)]
        check(not bad, f"single-gap states: Ldim(G_{2 * s + 1}(x)) = v_{2 * s + 1}(x), "
              f"1 <= x <= {X}", mismatches(bad))
    # (d) Theorem 4 on explicit R_k, G_k, and Lemma 10 as an identity of function tables
    bad = [(k, x) for k in range(1, 9) for x in range(1, 13)
           if li.generic_ldim(*(li.cycle_class(k, x) if k % 2 == 0 else li.fixed_ends_class(k, x)))
           != li.v(k, x)]
    check(not bad, "generic recursion on explicit R_k(x) (k even), G_k(x) (k odd) = v_k(x), "
          "1 <= k <= 8, 1 <= x <= 12", mismatches(bad))
    bad = [(j, m) for j in (1, 2, 3) for m in range(12)
           if sorted(li.cycle_class(2 * j, m + 1)[0]) != sorted(li.unions_class(j, m)[0])]
    check(not bad, "Lemma 10: R_{2j}(m+1) = U_j(m) as function tables, 1 <= j <= 3, 0 <= m <= 11",
          mismatches(bad))
    # (e) upper-bound recursion (potential lemma, pairing lemma)
    X = 200000
    bad = []
    for k in range(1, 17):
        U = li.upper_bound_recursion(k, X)
        bad += [(k, x) for x in range(1, X + 1) if U[x] != li.v(k, x)]
    check(not bad, "upper-bound recursion min(x-1, floor((x+k-1)/2), L(floor(x/2))+k) = v_k(x), "
          "1 <= k <= 16, 1 <= x <= 2*10^5", mismatches(bad))
    # (f) lower-bound system of Lemma 21, exactly as printed
    K, X = 25, 3000
    Lo, La = li.lower_bound_system(K, X)
    bad = [(k, x) for k in range(1, K + 1) for x in range(1, X + 1) if Lo[k][x] != li.v(k, x)]
    check(not bad, f"lower-bound system of Lemma 21(a)-(e) = v_k(x), 1 <= k <= {K}, "
          f"1 <= x <= {X}", mismatches(bad))
    bad = [(k, x) for k in range(1, K + 1) for x in range(k, X + 1) if La[k][x] < li.tau(k, x)]
    check(not bad, f"same system: Lambda_k(x) >= tau_k(x) = min(x-k, v_k(x)), 1 <= k <= {K}, "
          f"k <= x <= {X}", mismatches(bad))
    # (g) the move prescribed by the proof in each range
    bad = [f for k in range(2, 41) for f in li.prescribed_move_failures(k, 200000, 6000)]
    check(not bad, "proof of Theorem 4, move by move: the prescribed move certifies (i) at every "
          "threshold Q_k(d) <= 2*10^5 and (ii) at every x < 6000, 2 <= k <= 40", mismatches(bad))
    # (h) Lemma 22 and the explicit forms of Q_k
    bad = [f for k in range(1, 61) for f in li.Q_property_failures(k, li.d_k(k) + 8 * k)]
    check(not bad, "Lemma 22(a)-(d), 1 <= k <= 60, d <= d_k + 8k", mismatches(bad))
    ok = (all(li.Q(1, d) == 2 ** d for d in range(40))
          and all(li.Q(2, d) == li.P(d) for d in range(60))
          and all(li.Q(2 * j, 3 * j + 2 * j * t + i) == (4 * j + 2 * i + 1) * 2 ** t
                  for j in range(1, 20) for t in range(8) for i in range(2 * j))
          and [li.Q(4, d) for d in range(16)] == [1, 2, 3, 4, 5, 7, 9, 11, 13, 15, 18, 22, 26, 30, 36, 44])
    check(ok, "Q_1(d) = 2^d, Q_2 = P, Q_{2j}(3j+2jt+i) = (4j+2i+1)2^t (j < 20, t < 8), "
          "Q_4 = 1, 2, 3, 4, 5, 7, 9, 11, 13, 15, 18, 22, 26, 30, 36, 44")
    # (i) Corollary 5, asymptotic bounds (float)
    lo, hi = math.inf, -math.inf
    for j in range(1, 31):
        for x in range(4 * j + 1, 40000):
            d = li.v(2 * j, x)
            a = 2 * j * math.log2(x / j)
            lo = min(lo, d - (a - 1.173 * j - 1.722))
            hi = max(hi, d - (a - j))
    check(lo > 0 and hi <= -0.61, "Corollary 5 bounds (float), 1 <= j <= 30, "
          f"4j+1 <= m+1 < 4*10^4: slack of the lower bound >= {lo:.3f} > 0, "
          f"slack of the upper bound >= {-hi:.3f} >= 0.61")


def step8(rng):
    print("[8/11] Odd budgets: Ldim(C_{n,k}) = 1 + v_k(n) (Proposition 6, "
          "proved for k = 1, conjectured for odd k >= 3)")
    for k, N in ((1, 40), (3, 26), (5, 18), (7, 15)):
        bad = []
        for n in range(1, N + 1):
            val = li.ldim_switch_class(n, k)
            upper = 1 + min((n + k - 1) // 2, li.v(k + 1, n))
            if val != 1 + li.v(k, n) or val > upper:
                bad.append((n, val))
        check(not bad, f"k = {k}: gap DP gives Ldim(C_{{n,{k}}}) = 1 + v_{k}(n), within the bounds "
              f"of Proposition 6, 1 <= n <= {N}", mismatches(bad))
    bad = [n for n in range(1, 41) if li.ldim_switch_class(n, 1) != 1 + li.lam(n)]
    check(not bad, "k = 1: Ldim(C_{n,1}) = 1 + floor(lg n), 1 <= n <= 40", mismatches(bad))


def _multisets(total_max, min_part):
    """All nonempty multisets (sorted tuples) of integers >= min_part with sum <= total_max."""
    out = []

    def rec(rem, maxp, cur):
        if cur:
            out.append(tuple(sorted(cur)))
        for p in range(min(maxp, rem), min_part - 1, -1):
            cur.append(p)
            rec(rem - p, p, cur)
            cur.pop()

    rec(total_max, total_max, [])
    return out


def step9(rng):
    M = rng["rl_m"]
    print("[9/11] Randomised learners (Lemmas 27 and 29, Proposition 28, Eq. (2), Theorem 30, "
          "Conjecture 31, Proposition 32)")
    bad = [cc for cc in range(1, 18) if li.rl_generic(*li.chain_class(cc)) != li.rl_chain(cc)]
    check(not bad, "Proposition 28: generic RL of a chain of c thresholds = lambda~(c)/2, "
          "1 <= c <= 17", mismatches(bad))
    bad = []
    for a in range(1, 7):
        for b in range(1, 7):
            fa, na = li.chain_class(a)
            fb, nb = li.chain_class(b)
            prod = [x | (y << na) for x in fa for y in fb]
            if li.rl_generic(prod, na + nb) != li.rl_generic(fa, na) + li.rl_generic(fb, nb):
                bad.append((a, b))
    check(not bad, "Lemma 27: RL(chain_a x chain_b) = RL(chain_a) + RL(chain_b), "
          "1 <= a, b <= 6", mismatches(bad))
    bad = [m for m in range(13) if li.rl_generic(*li.intervals_class(m)) != li.rl_intervals(m)]
    check(not bad, "Eq. (2) (cutting game) = generic RL recursion on explicit Int_m, 0 <= m <= 12",
          mismatches(bad))
    first = [li.rl_intervals(m) for m in range(8)]
    expect = [Fraction(0), Fraction(1, 2), Fraction(1), Fraction(11, 8), Fraction(27, 16),
              Fraction(63, 32), Fraction(139, 64), Fraction(303, 128)]
    check(first == expect, "RL(Int_m), m = 0..7: 0, 1/2, 1, 11/8, 27/16, 63/32, 139/64, 303/128",
          f"got {[str(q) for q in first]}")
    t0 = time.time()
    exact = [li.rl_intervals(m) for m in range(M + 1)]
    bad = [m for m in range(M + 1) if exact[m] != li.R(m + 1)]
    check(not bad, f"Conjecture 31: RL(Int_m) (Eq. (2), exact) = R(m+1), 0 <= m <= {M} "
          f"({time.time() - t0:.0f} s)", mismatches(bad))
    # Optimal first cuts for m = 16 and the peeling line
    target = li.rl_intervals(16)

    def cut_value(pieces, p, u):
        rest = list(pieces)
        rest.remove(p)
        nxt = rest + [u, p - u]
        return (1 + (li.interp_lg(u) + li.interp_lg(p - u)) / 2 + li.rl_cut_game(nxt)) / 2

    firsts = [(u, 17 - u) for u in range(1, 9) if cut_value([17], 17, u) == target]
    line = [([17], 17, 4), ([4, 13], 13, 4), ([4, 4, 9], 9, 2), ([2, 4, 4, 7], 7, 2),
            ([2, 2, 4, 4, 5], 5, 2)]
    line_ok = all(cut_value(S, p, u) == li.rl_cut_game(S) for S, p, u in line)
    check(firsts == [(4, 13), (5, 12), (8, 9)] and line_ok,
          "m = 16: optimal first cuts of 17 are exactly 4+13, 5+12, 8+9; the line 13=4+9, 9=2+7, "
          "7=2+5, 5=2+3 is optimal at every step", f"first cuts {firsts}, line {line_ok}")

    # Greedy adversary (Theorem 30) and the balanced tie-break
    def balanced_rule(pieces):
        p = max(pieces)
        u = max(range(1, p // 2 + 1),
                key=lambda u: (li.interp_lg(u) + li.interp_lg(p - u), -abs(p - 2 * u)))
        return p, u

    def greedy_rule(pieces):
        p = max(pieces)
        return p, li.greedy_cut(p)[0]

    bal, opt = li.schedule_value([6], balanced_rule), li.rl_intervals(5)
    check(bal == Fraction(61, 32) and opt == Fraction(63, 32),
          "m = 5: largest piece with balanced tie-break (6 = 3+3) gives 61/32, optimum 63/32",
          f"got {bal}, {opt}")
    bad = [m for m in range(31) if li.greedy_value([m + 1]) != exact[m]
           or li.schedule_value([m + 1], greedy_rule) != exact[m]]
    check(not bad, "greedy adversary value = exact solver, 0 <= m <= 30", mismatches(bad))
    bad = [m for m in range(600) if li.greedy_value([m + 1]) != li.R(m + 1)]
    check(not bad, "Theorem 30: greedy adversary value = R(m+1), 0 <= m < 600", mismatches(bad))
    # Lemma 29 and the steps (i)-(iv) of the proof of Theorem 30
    bad = []
    for l in range(2, 400):
        L = li.lam(l)
        ps = li.greedy_cut_sequence(l)
        spine = sorted([p for p in ps if p & (p - 1)], reverse=True)
        ok = (li.R_closed(l) == li.R(l)
              and all(1 + (li.interp_lg(li.greedy_cut(p)[0]) + li.interp_lg(li.greedy_cut(p)[1])) / 2
                      == li.interp_lg(p) for p in ps)
              and all(sum(1 for p in ps if p >= 2 ** q) == (l >> (q - 1)) - 1 for q in range(1, L + 1))
              and spine == [2 ** t + l % 2 ** t for t in range(L, 0, -1) if l % 2 ** t]
              and li.greedy_value([l]) == li.R(l))
        if not ok:
            bad.append(l)
    check(not bad, "Lemma 29 = recurrence R; proof of Theorem 30: cut values "
          "lambda~(p), level counts C_q = f_(q-1) - 1, spine 2^t + (l mod 2^t), value = R(l); "
          "2 <= l < 400", mismatches(bad))
    positions = _multisets(30, 2)
    bad = [S for S in positions if li.greedy_value(S) != li.rl_cut_game(S)]
    check(not bad and len(positions) == 5603,
          f"greedy schedule = exact optimum of Eq. (2) from every position: all {len(positions):,} "
          "multisets of pieces of measure >= 2 with total measure <= 30", mismatches(bad))
    cstar = sum(Fraction(2, 2 ** (2 ** s)) for s in range(1, 7))
    ok = all(li.R(2 ** t) == t - sum(Fraction(2, 2 ** (2 ** s)) for s in range(1, t + 1))
             for t in range(1, 12))
    check(ok and f"{float(cstar):.9f}" == "0.632843018",
          f"R(2^t) = t - sum_(s<=t) 2^(1-2^s), 1 <= t <= 11; c* = {float(cstar):.9f}")
    N = 200000
    Rf = [0.0] * (N + 1)
    for l in range(2, N + 1):
        Rf[l] = 1 - 2.0 ** (1 - l) + (Rf[l // 2] + Rf[(l + 1) // 2]) / 2
    offs = [Rf[l] - math.log2(l) for l in range(4, N + 1)]
    check(-0.6428 < min(offs) and max(offs) < -0.6162,
          f"lg(m+1) - 0.6428 < R(m+1) < lg(m+1) - 0.6162 for 3 <= m < 2*10^5 (float; "
          f"range {min(offs):.4f} .. {max(offs):.4f})")
    bad = [l for l in range(1, 2000) if li.R(2 * l) != li.R(l) + 1 - Fraction(2, 2 ** (2 * l))]
    check(not bad, "R(2l) = R(l) + 1 - 2^(1-2l), 1 <= l < 2000", mismatches(bad))
    # Proposition 32: RL(J_S) <= max lambda~(l) on every position, and lambda~(l) - R(l) <= c_L on [2^L, 2^(L+1))
    small = _multisets(26, 2)
    bad = [S for S in small if li.rl_cut_game(S) > max(li.interp_lg(p) for p in S)]
    check(not bad and len(small) == 2435,
          f"Proposition 32 (upper bound): RL(J_S) <= max lambda~(l) on all {len(small):,} positions "
          "(pieces of measure >= 2, total measure <= 26)", mismatches(bad))
    bad = [m for m in range(M + 1) if li.rl_intervals(m) > li.interp_lg(m + 1)]
    check(not bad, f"Proposition 32: RL(Int_m) <= lambda~(m+1), 0 <= m <= {M}", mismatches(bad))

    def c_L(L):
        return sum(Fraction(2, 2 ** (2 ** s)) for s in range(1, L + 1))
    bad = [l for l in range(1, 2049) if li.interp_lg(l) - li.R(l) > c_L(li.lam(l))]
    eq = all(li.interp_lg(2 ** L) - li.R(2 ** L) == c_L(L) for L in range(0, 12))
    check(not bad and eq, "Proposition 32 (gap): lambda~(l) - R(l) <= c_L for 2^L <= l < 2^(L+1), "
          "1 <= l <= 2048, with equality at l = 2^L", mismatches(bad) + f", equality {eq}")
    lamf = [0.0] + [li.lam(l) + (l - 2 ** li.lam(l)) / 2 ** li.lam(l) for l in range(1, N + 1)]
    cLf = [float(c_L(L)) for L in range(0, 20)]
    bad = [l for l in range(1, N + 1) if lamf[l] - Rf[l] > cLf[li.lam(l)] + 1e-12]
    check(not bad, "Proposition 32 (gap): lambda~(l) - R(l) <= c_L (L = floor(lg l)) "
          "for 1 <= l <= 2*10^5 (float)",
          mismatches(bad))


def compare(ok, text, detail=""):
    """Print IDENTICAL or *** DIFFERS *** for two implementations; failures count."""
    print(f"  {'IDENTICAL' if ok else '*** DIFFERS ***'}  {text}" + ("" if ok else f"   {detail}"))
    if not ok:
        FAILED.append(text)


def step10(rng):
    print("[10/11] Implementation checks (independent implementations compared)")
    bad = [m for m in range(17)
           if independent_ldim(independent_intervals(m), m) != li.generic_ldim(*li.intervals_class(m))]
    compare(not bad, "separately written recursion vs module generic_ldim on Int_m, 0 <= m <= 16",
            mismatches(bad))
    bad = [n for n in range(1, 14)
           if independent_ldim(independent_c2(n), n) != li.generic_ldim(*li.switch_class(n, 2))]
    compare(not bad, "separately written recursion vs module generic_ldim on C_{n,2}, 1 <= n <= 13",
            mismatches(bad))
    bad = [(k, x) for k in range(1, 9) for x in range(1, 25)
           if (li.ldim_R(k, x) if k % 2 == 0 else li.ldim_G(k, x))
           != (li.gap_state_ldim(k, B=[x - 1]) if k % 2 == 0 else li.gap_state_ldim(k - 1, A=[x - 1]))]
    compare(not bad, "cyclic gap game vs gap-state DP on R_k(x) (k even), G_k(x) (k odd), "
            "1 <= k <= 8, 1 <= x <= 24", mismatches(bad))
    tree = li.tree_min_table(12)                  # P*(12) = 80 > 61
    bad = [m for m in range(61)
           if li.segment_ldim([m]) != max(d for d in range(13) if tree[d] <= m + 1)]
    compare(not bad, "segment recursion vs tree DP via Lemma 15, 0 <= m <= 60",
            mismatches(bad))


def step11(rng):
    print("[11/11] Explicit learners against an exhaustive adaptive adversary "
          "(Lemmas 19 and 20, Theorems 1 and 4, Remark 25)")
    M, K, X = rng["adv_m"], rng["adv_k"], rng["adv_x"]
    rows = []
    for m in range(1, M + 1):
        funcs, n = li.intervals_class(m)
        opt = ol.worst_case_mistakes(lambda: ol.OptimalIntervalLearner(m), funcs, n)
        nat = ol.worst_case_mistakes(lambda: ol.NaturalLearner(m), funcs, n)
        rows.append((m, li.ldim_intervals_formula(m), opt, li.natural_learner_mistakes(m), nat))
    for label, col in (("m", 0), ("Ldim(Int_m)", 1), ("optimal learner, worst case", 2),
                       ("natural learner, worst case", 4)):
        print(f"  {label:<28}" + " ".join(f"{r[col]:2d}" for r in rows))
    bad = [r for r in rows if r[2] != r[1]]
    check(not bad, f"optimal learner: worst case = Ldim(Int_m), 1 <= m <= {M}", mismatches(bad))
    bad = [r for r in rows if r[4] != r[3]]
    check(not bad, f"natural learner: worst case = N(m) of Remark 25, 1 <= m <= {M}", mismatches(bad))
    bad = []
    for k in range(1, K + 1):
        for x in range(1, X + 1):
            funcs, n = li.cycle_class(k, x) if k % 2 == 0 else li.fixed_ends_class(k, x)
            w = ol.worst_case_mistakes(lambda: ol.OptimalLearner(k, x), funcs, n)
            if w != li.v(k, x):
                bad.append((k, x, w, li.v(k, x)))
    check(not bad, f"optimal learner: worst case = v_k(x) on R_k(x) (k even) and G_k(x) (k odd), "
          f"1 <= k <= {K}, 1 <= x <= {X}", mismatches(bad))
    if rng["adv_g3"]:                           # G_3(x), x = 12, 13 reach the pairing step with k = 3
        bad = []
        for x in range(X + 1, rng["adv_g3"] + 1):
            funcs, n = li.fixed_ends_class(3, x)
            w = ol.worst_case_mistakes(lambda: ol.OptimalLearner(3, x), funcs, n)
            if w != li.v(3, x):
                bad.append((3, x, w, li.v(3, x)))
        check(not bad, f"optimal learner: worst case = v_3(x) on G_3(x), {X + 1} <= x <= {rng['adv_g3']} "
              "(pairing step with k = 3)", mismatches(bad))
    bad = []
    for k in range(1, 17):                      # mistake bound of the learner's recursion (paper range)
        base = li.Q(k, li.d_k(k) + k - 1)
        bound = [0] * 200001
        for x in range(1, 200001):
            bound[x] = min(x - 1, (x + k - 1) // 2) if x < base else bound[x // 2] + k
            if bound[x] != li.v(k, x):
                bad.append((k, x))
    check(not bad, "optimal learner: mistake bound of its recursion (potential below Q_k(d_k+k-1), "
          "pairing above) = v_k(x), 1 <= k <= 16, 1 <= x <= 200000", mismatches(bad))


STEPS = [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--full", action="store_true",
                    help="use the paper's ranges for the long runs (about 15 minutes)")
    ap.add_argument("--steps", default="",
                    help="comma-separated step numbers to run, e.g. 4,9 (default: all)")
    args = ap.parse_args(argv)
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)   # progress is visible when redirected
    rng = FULL if args.full else QUICK
    try:
        chosen = [int(s) for s in args.steps.split(",") if s.strip()] or list(range(1, 12))
    except ValueError:
        ap.error("--steps takes comma-separated integers from 1 to 11")
    if any(not 1 <= i <= 11 for i in chosen):
        ap.error("--steps takes comma-separated integers from 1 to 11")
    print(f"Mode: {'--full (paper ranges)' if args.full else 'default (quick ranges for the long runs)'}")
    t_all = time.time()
    for i in chosen:
        t0 = time.time()
        STEPS[i - 1](rng)
        li.clear_caches()
        print(f"        ({time.time() - t0:.1f} s)")
    print(f"\nTotal time {time.time() - t_all:.0f} s. "
          + ("ALL CHECKS PASSED" if not FAILED else f"{len(FAILED)} CHECK(S) FAILED"))
    return 0 if not FAILED else 1


if __name__ == "__main__":
    sys.exit(main())
