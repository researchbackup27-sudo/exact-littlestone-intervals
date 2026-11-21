"""Reference implementation for the paper

    How many mistakes does it take to learn an interval?
    Exact Littlestone dimensions of intervals and their unions.

Every function corresponds to a definition, lemma, theorem or named procedure
of the paper, and uses the paper's notation. Numbers of results follow the
submitted version of the paper. Ranges and sizes are always
arguments; nothing is computed at import time. Arithmetic is exact (integers
or fractions.Fraction) unless a docstring says otherwise.

Classes of functions are represented explicitly as a pair (funcs, npts): a
list of integers, bit p of a function being its value at the domain point p,
and the number of domain points.

Paper element                                         function
--------------------------------------------------------------------------
lambda(x) = floor(lg x)                               lam
P(d), Theorem 1                                       P, ldim_intervals_formula
closed form of Theorem 1                              ldim_intervals_closed_form
c(r), g(a, b, r), Lemma 16                            c, g
d_k, Q_k(d), v_k(x), tau_k(x)                         d_k, Q, v, tau
Int_m, U_j(m), C_{n,k}, R_k(x), G_k(x), Th_c          intervals_class, unions_class,
                                                      switch_class, cycle_class,
                                                      fixed_ends_class, chain_class
Fact 7 (generic Littlestone recursion)                generic_ldim
Lemma 13 (segment classes J_S)                        segment_ldim
P*(d), admissible trees, Lemma 15                     tree_min_table
gap states and potential (C_{n,k})                    gap_state_ldim, ldim_switch_class
cyclic gap game (U_j, R_{2j}, G_{2s+1})               cyclic_gap_ldim, ldim_unions,
                                                      ldim_R, ldim_G
Lemmas 19 and 20 (upper bound)                        upper_bound_recursion
Lemma 21(a)-(e), verbatim (lower bound)              lower_bound_system
case analysis in the proof of Theorem 4               prescribed_move_failures
Lemma 22(a)-(d)                                      Q_property_failures
Remarks 25 and 26                                     natural_learner_mistakes,
                                                      counting_bound
Section 'Randomised learners'
  interpolated lg, lambda~                            interp_lg
  Lemma 27 (generic RL recursion)                     rl_generic
  Proposition 28 (chains)                             rl_chain
  Eq. (2), discounted cutting game                    rl_cut_game, rl_intervals
  recurrence R, Lemma 29                              R, R_closed
  greedy adversary of Theorem 30                      greedy_cut, greedy_value,
                                                      greedy_cut_sequence,
                                                      schedule_value
  Proposition 32 (upper bound lambda~, gap c_L)       rl_cut_game, interp_lg, R
"""

from bisect import bisect_right
from fractions import Fraction
from functools import lru_cache
from math import comb
import heapq

__all__ = [
    "lam", "P", "ldim_intervals_formula", "ldim_intervals_closed_form",
    "c", "g", "d_k", "Q", "v", "tau",
    "intervals_class", "unions_class", "switch_class", "cycle_class",
    "fixed_ends_class", "chain_class",
    "generic_ldim", "segment_ldim", "tree_min_table",
    "gap_state_ldim", "ldim_switch_class", "cyclic_gap_ldim", "ldim_unions", "ldim_R", "ldim_G",
    "upper_bound_recursion", "lower_bound_system", "prescribed_move_failures",
    "Q_property_failures", "natural_learner_mistakes", "counting_bound",
    "interp_lg", "rl_generic", "rl_chain", "rl_cut_game", "rl_intervals",
    "R", "R_closed", "greedy_cut", "greedy_value", "greedy_cut_sequence",
    "schedule_value", "clear_caches",
]

NEG = -10 ** 9          # stands for -infinity (no full tree exists)


def _popcount(x):
    return bin(x).count("1")


# ---------------------------------------------------------------------------
# Formulas: lambda, P, c, g, Q_k, v_k, tau_k
# ---------------------------------------------------------------------------

def lam(x):
    """lambda(x) = floor(lg x) for an integer x >= 1."""
    return x.bit_length() - 1


def P(d):
    """P(0..2) = 1, 2, 3; P(2t+1) = 5 * 2^(t-1) (t >= 1); P(2t) = 7 * 2^(t-2) (t >= 2)."""
    if d <= 2:
        return (1, 2, 3)[d]
    t = d // 2
    return 5 * 2 ** (t - 1) if d % 2 else 7 * 2 ** (t - 2)


def ldim_intervals_formula(m):
    """Theorem 1: Ldim(Int_m) = max{d >= 0 : P(d) <= m + 1}."""
    d = 0
    while P(d + 1) <= m + 1:
        d += 1
    return d


def _floor_lg_ratio(a, b):
    """floor(lg(a / b)) for positive integers a, b, exactly."""
    def fits(t):                       # b * 2^t <= a
        return (b << t) <= a if t >= 0 else b <= (a << -t)

    t = a.bit_length() - b.bit_length()
    while not fits(t):
        t -= 1
    while fits(t + 1):
        t += 1
    return t


def ldim_intervals_closed_form(m):
    """Theorem 1, closed form for m >= 3:
    max(2 floor(lg(4(m+1)/7)), 2 floor(lg(2(m+1)/5)) + 1), in exact integer arithmetic."""
    if m < 3:
        raise ValueError("the closed form is stated for m >= 3")
    return max(2 * _floor_lg_ratio(4 * (m + 1), 7), 2 * _floor_lg_ratio(2 * (m + 1), 5) + 1)


def c(r):
    """Lemma 16(a): c(r) = min{u+v : lambda(u)+lambda(v) >= r}
    = 2^floor(r/2) + 2^ceil(r/2)."""
    return (1 << (r // 2)) + (1 << ((r + 1) // 2))


def g(a, b, r):
    """Lemma 16(b): g(a, b, r) = min{u+v : u >= a, v >= b,
    lambda(u)+lambda(v) >= r} = min over 0 <= p <= r of max(a, 2^p) + max(b, 2^(r-p))."""
    return min(max(a, 1 << p) + max(b, 1 << (r - p)) for p in range(r + 1))


def d_k(k):
    """d_k = ceil(3k/2)."""
    return (3 * k + 1) // 2


def Q(k, d):
    """Q_k(d) = d+1 for 0 <= d <= k; 2d-k+1 for k <= d <= d_k+k-1; 2 Q_k(d-k) beyond.
    For k = 2 this is P; for k = 1 it is 2^d."""
    if d <= k:
        return d + 1
    if d <= d_k(k) + k - 1:
        return 2 * d - k + 1
    return 2 * Q(k, d - k)


_Q_LISTS = {}


def _thresholds(k, x):
    """List [Q_k(0), Q_k(1), ...] extended past x (cached per k)."""
    lst = _Q_LISTS.setdefault(k, [1])
    while lst[-1] <= x:
        lst.append(Q(k, len(lst)))
    return lst


def v(k, x):
    """v_k(x) = max{d >= 0 : Q_k(d) <= x}, for k >= 1 and x >= 1. v_0 = 0."""
    if k == 0:
        return 0
    return bisect_right(_thresholds(k, x), x) - 1


def tau(k, x):
    """tau_k(x) = min(x - k, v_k(x)) for x >= k (the target for full trees); NEG for x < k."""
    if x < k:
        return NEG
    return min(x - k, v(k, x))


# ---------------------------------------------------------------------------
# Explicit classes
# ---------------------------------------------------------------------------

def intervals_class(m):
    """Int_m = {empty} U {[a, b] : 1 <= a <= b <= m} on [m]. Returns (funcs, m)."""
    funcs = [0] + [((1 << (b + 1)) - 1) ^ ((1 << a) - 1) for a in range(m) for b in range(a, m)]
    return funcs, m


def unions_class(j, m):
    """U_j(m): subsets of [m] that are unions of at most j intervals. Returns (funcs, m)."""
    funcs = [f for f in range(1 << m) if _popcount(f & ~(f << 1)) <= j]
    return funcs, m


def switch_class(n, k):
    """C_{n,k}: f : [n] -> {0,1} with at most k indices i < n such that f(i) != f(i+1).
    Returns (funcs, n)."""
    inner = (1 << (n - 1)) - 1 if n >= 1 else 0
    funcs = [f for f in range(1 << n) if _popcount((f ^ (f >> 1)) & inner) <= k]
    return funcs, n


def cycle_class(k, x):
    """R_k(x): labellings of a cycle of x points, one of them fixed to 0, with at most k
    switches around the cycle; a class on the x - 1 free points. Returns (funcs, x - 1)."""
    n = x - 1
    funcs = []
    for f in range(1 << n):
        seq = [0] + [(f >> p) & 1 for p in range(n)]
        if sum(seq[i] != seq[(i + 1) % x] for i in range(x)) <= k:
            funcs.append(f)
    return funcs, n


def fixed_ends_class(k, x):
    """G_k(x): sequences f(0), ..., f(x) with f(0) = 0, f(x) = 1 and at most k switches;
    a class on the x - 1 free points. Returns (funcs, x - 1)."""
    n = x - 1
    funcs = []
    for f in range(1 << n):
        seq = [0] + [(f >> p) & 1 for p in range(n)] + [1]
        if sum(seq[i] != seq[i + 1] for i in range(x)) <= k:
            funcs.append(f)
    return funcs, n


def chain_class(c_):
    """Th_c: the c threshold functions y -> 1[y >= a], a in [c], on the domain [c-1]."""
    n = c_ - 1
    funcs = [((1 << n) - 1) ^ ((1 << (a - 1)) - 1) for a in range(1, c_ + 1)]
    return funcs, n


# ---------------------------------------------------------------------------
# Generic Littlestone recursion (Fact 7)
# ---------------------------------------------------------------------------

def generic_ldim(funcs, npts):
    """Ldim of an explicit finite class by the recursion of Fact 7:
    Ldim(V) >= d + 1 iff some point x splits V with Ldim(V_x^0), Ldim(V_x^1) >= d.

    No structure of the class is used. A version space is a bitmask over the
    function indices. Two pruning rules are used, both exact: a query whose
    positive branch is below the current best cannot improve it, and the search
    stops at the counting bound floor(lg |V|)."""
    funcs = sorted(set(funcs))
    ones = []
    for p in range(npts):
        mask = 0
        for i, f in enumerate(funcs):
            if (f >> p) & 1:
                mask |= 1 << i
        ones.append(mask)
    memo = {}

    def L(vs):
        if vs & (vs - 1) == 0:
            return 0
        got = memo.get(vs)
        if got is not None:
            return got
        cap = _popcount(vs).bit_length() - 1
        best = 0
        for o in ones:
            v1 = vs & o
            if v1 == 0 or v1 == vs:
                continue
            a = L(v1)
            if a < best:
                continue
            val = 1 + min(a, L(vs ^ v1))
            if val > best:
                best = val
                if best == cap:
                    break
        memo[vs] = best
        return best

    if not funcs:
        raise ValueError("empty class")
    return L((1 << len(funcs)) - 1)


# ---------------------------------------------------------------------------
# Segment classes J_S and the cutting game (Lemmas 12 and 13)
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def _J(seg):
    best = 0
    for idx, gl in enumerate(seg):
        if idx and seg[idx - 1] == gl:
            continue
        rest = seg[:idx] + seg[idx + 1:]
        for i in range(1, (gl + 1) // 2 + 1):      # i-th point; i <-> gl-i+1 is a reflection
            one = lam(i) + lam(gl - i + 1)         # Lemma 12(a)
            if one < best:
                continue
            zero = _J(tuple(sorted(s for s in rest + (i - 1, gl - i) if s > 0)))  # Lemma 12(b)
            best = max(best, 1 + min(one, zero))
    return best


def segment_ldim(S):
    """Ldim(J_S) for a multiset S of block lengths, by the recursion behind Lemma 13:
    querying the i-th point of a block of length g gives a positive branch of dimension
    lambda(i) + lambda(g-i+1) and a negative branch J_{S - {g} + {i-1, g-i}}.
    Ldim(Int_m) = segment_ldim([m])."""
    return _J(tuple(sorted(s for s in S if s > 0)))


# ---------------------------------------------------------------------------
# Admissible trees and P*(d) (sections 'From intervals to a cutting game' and 'Solving the tree problem')
# ---------------------------------------------------------------------------

def tree_min_table(D):
    """[P*(0), ..., P*(D)]: P*(d) is the minimum root measure of an admissible tree whose
    internal labels are exactly {0, ..., d-1}.

    Exact dynamic program over label sets L (bitmasks): the root carries max(L), its two
    subtrees carry a partition (L1, L2) of the other labels, and the smallest root measure is
    g(f(L1), f(L2), max(L)) by Lemma 16(b) and monotonicity of lambda
    (a subtree's root measure can be raised by raising a leaf). A partition is skipped when
    f(L1) + f(L2) already reaches the best value, which is exact because g(a, b, r) >= a + b.
    Time grows like 3^D (D = 16: seconds; D = 19: minutes)."""
    size = 1 << D
    f = [0] * size
    f[0] = 1
    for mask in range(1, size):
        top = mask.bit_length() - 1
        rest = mask ^ (1 << top)
        if rest == 0:
            f[mask] = g(1, 1, top)
            continue
        low = rest & -rest
        free = rest ^ low
        best = None
        sub = free
        while True:
            s1 = sub | low
            a = f[s1]
            b = f[rest ^ s1]
            if best is None or a + b < best:
                val = g(a, b, top)
                if best is None or val < best:
                    best = val
            if sub == 0:
                break
            sub = (sub - 1) & free
        f[mask] = best
    return [f[(1 << d) - 1] for d in range(D + 1)]


# ---------------------------------------------------------------------------
# Gap states of C_{n,k} (subsection 'Gap states and a potential'): exact dynamic program
# ---------------------------------------------------------------------------

def _count_completions(r, E, A, B):
    """|V| for a gap state: completions using at most r spare switches."""
    poly = [1] + [0] * r

    def mul(p, q):
        out = [0] * (r + 1)
        for i, a in enumerate(p):
            if a:
                for j, b in enumerate(q):
                    if i + j > r:
                        break
                    out[i + j] += a * b
        return out

    for e in E:          # an E gap of length e has e slots, any number of switches
        poly = mul(poly, [comb(e, s) for s in range(r + 1)])
    for a in A:          # an A gap has a+1 slots and an odd number 1 + s of switches
        poly = mul(poly, [comb(a + 1, s + 1) if s % 2 == 0 else 0 for s in range(r + 1)])
    for b in B:          # a B gap has b+1 slots and an even number of switches
        poly = mul(poly, [comb(b + 1, s) if s % 2 == 0 else 0 for s in range(r + 1)])
    return sum(poly)


def _gap_norm(r, E, A, B):
    """Normal form of a gap state; returns (additive constant, state) or None if r < 0.

    Empty gaps are dropped. With r < 2 no A gap can take 3 switches and no B gap can take 2,
    so B gaps are constant and each A gap of length a is an independent chain of a+1
    thresholds (Lemmas 8 and 9), contributing lambda(a+1). With r = 0 the E gaps are
    constant as well."""
    if r < 0:
        return None
    E = [e for e in E if e > 0]
    A = [a for a in A if a > 0]
    B = [b for b in B if b > 0]
    add = 0
    if r < 2:
        B = []
        add = sum(lam(a + 1) for a in A)
        A = []
    if r == 0:
        E = []
    return add, (r, tuple(sorted(E)), tuple(sorted(A)), tuple(sorted(B)))


@lru_cache(maxsize=None)
def _gap_L(state):
    """Ldim of the version space given by a normalised gap state (r, E, A, B).

    Convention: the labelled neighbour on the left of the queried gap has label 0
    (complementation symmetry). Children of a query at the point with j unlabelled points
    to its left in a gap of length g (right part g-1-j):
      E gap: label 0 -> B gap j + E gap; label 1 -> A gap j + E gap, r - 1;
      A gap: the two labels give (B j, A g-1-j) and (A j, B g-1-j), same r;
      B gap: label 0 -> two B gaps; label 1 -> two A gaps, r - 2."""
    r, E, A, B = state
    ub = _count_completions(r, E, A, B).bit_length() - 1   # Ldim <= floor(lg |V|)
    if ub == 0:
        return 0
    best = 0
    for kind, lst in (("E", E), ("A", A), ("B", B)):
        seen = set()
        for idx, gl in enumerate(lst):
            if gl in seen:
                continue
            seen.add(gl)
            E2, A2, B2 = list(E), list(A), list(B)
            {"E": E2, "A": A2, "B": B2}[kind].pop(idx)
            for j in sorted(range(gl), key=lambda j: abs(2 * j - (gl - 1))):
                left, right = j, gl - 1 - j
                kids = []
                for lab in (0, 1):
                    e, a, b, rr = list(E2), list(A2), list(B2), r
                    if kind == "E":
                        (a if lab else b).append(left)
                        e.append(right)
                        rr -= lab
                    elif kind == "A":
                        if lab == 0:
                            b.append(left)
                            a.append(right)
                        else:
                            a.append(left)
                            b.append(right)
                    else:
                        if lab == 0:
                            b += [left, right]
                        else:
                            a += [left, right]
                            rr -= 2
                    kids.append(_gap_norm(rr, e, a, b))
                if kids[0] is None or kids[1] is None:
                    continue
                val = 1 + min(add + _gap_L(st) for add, st in kids)
                if val > best:
                    best = val
                    if best == ub:
                        return best
    return best


def gap_state_ldim(r, E=(), A=(), B=()):
    """Ldim of the version space given by spare budget r and multisets of E, A, B gap lengths
    (subsection 'Gap states and a potential'). For example R_k(x) is (k, B = [x-1]) and
    G_k(x) is (k-1, A = [x-1])."""
    nf = _gap_norm(r, E, A, B)
    if nf is None:
        raise ValueError("negative spare budget: empty version space")
    return nf[0] + _gap_L(nf[1])


def ldim_switch_class(n, k):
    """Ldim(C_{n,k}) by the exact gap-state dynamic program (subsection 'Gap states and a
    potential').

    By complementation the first query may be answered 0; it splits [n] into two E gaps of
    lengths j and n-1-j with spare budget k. The version space after any sample depends only
    on the spare budget r and the multisets of E, A, B gap lengths."""
    if n == 0:
        return 0
    best = 0
    for j in range(n):
        add, st = _gap_norm(k, [j, n - 1 - j], [], [])
        best = max(best, 1 + add + _gap_L(st))
    return best


# ---------------------------------------------------------------------------
# Cyclic gap game for U_j(m) = R_{2j}(m+1) and for G_{2s+1} (single A gap)
# ---------------------------------------------------------------------------

def _cyc_norm(s, A, B):
    """Normal form (additive constant, state) of a cyclic gap state with s spare switch pairs.
    Empty gaps are dropped (an empty A gap holds its forced switch and nothing else). With s = 0
    every B gap is constant and every A gap of length a is a chain of a+1 thresholds."""
    A = tuple(sorted(a for a in A if a > 0))
    B = tuple(sorted(b for b in B if b > 0))
    if s == 0:
        return sum(lam(a + 1) for a in A), (0, (), ())
    return 0, (s, A, B)


@lru_cache(maxsize=None)
def _cyc_L(state):
    s, A, B = state
    if s == 0:
        return 0
    best = 0
    for kind, lst in (("A", A), ("B", B)):
        seen = set()
        for idx, gl in enumerate(lst):
            if gl in seen:
                continue
            seen.add(gl)
            restA, restB = list(A), list(B)
            (restA if kind == "A" else restB).pop(idx)
            for i in range(gl):
                left, right = i, gl - 1 - i
                if kind == "A":                    # neighbours labelled 0 ... 1
                    k0 = _cyc_norm(s, restA + [right], restB + [left])
                    k1 = _cyc_norm(s, restA + [left], restB + [right])
                else:                              # neighbours labelled 0 ... 0
                    k0 = _cyc_norm(s, restA, restB + [left, right])
                    k1 = _cyc_norm(s - 1, restA + [left, right], restB)
                v1 = k1[0] + _cyc_L(k1[1])
                if v1 < best:
                    continue
                val = 1 + min(k0[0] + _cyc_L(k0[1]), v1)
                if val > best:
                    best = val
    return best


def cyclic_gap_ldim(s, A, B):
    """Ldim of the cyclic gap state with s spare switch pairs, A gaps (between opposite labels,
    odd number of switches) and B gaps (between equal labels, even number of switches)."""
    add, st = _cyc_norm(s, A, B)
    return add + _cyc_L(st)


def ldim_unions(j, m):
    """Ldim(U_j(m)) = Ldim(R_{2j}(m+1)) (Lemma 10): a cycle of m+1 points with one point
    labelled 0 is a single B gap of length m with j spare pairs."""
    return 0 if m == 0 else cyclic_gap_ldim(j, (), (m,))


def ldim_R(k, x):
    """L_k(x) = Ldim(R_k(x)) for even k, by the cyclic gap game."""
    if k % 2:
        raise ValueError("R_k is defined for even k")
    return ldim_unions(k // 2, x - 1)


def ldim_G(k, x):
    """L_k(x) = Ldim(G_k(x)) for odd k = 2s+1: a single A gap of length x-1 with s spare pairs."""
    if k % 2 == 0:
        raise ValueError("G_k is defined for odd k")
    return cyclic_gap_ldim((k - 1) // 2, (x - 1,), ())


# ---------------------------------------------------------------------------
# Theorem 4: upper-bound recursion and lower-bound system
# ---------------------------------------------------------------------------

def upper_bound_recursion(k, X):
    """U[x] for 0 <= x <= X, where U[1] = 0 and, for x >= 2,
    U[x] = min(x - 1, floor((x+k-1)/2), U[floor(x/2)] + k).
    x - 1 counts the free points, floor((x+k-1)/2) is Eq. (1) from the potential lemma,
    and U[floor(x/2)] + k is the pairing lemma. Each U[x] is an upper bound on L_k(x)."""
    U = [0] * (X + 1)
    for x in range(2, X + 1):
        U[x] = min(x - 1, (x + k - 1) // 2, U[x // 2] + k)
    return U


def lower_bound_system(K, X):
    """Tables (Lo, La) with Lo[k][x] <= L_k(x) and La[k][x] <= Lambda_k(x) for 0 <= k <= K,
    1 <= x <= X, obtained from Lemma 21 exactly as printed and nothing else.

    Base: L_0 = Lambda_0 = 0; L_1 = Lambda_1 = lambda (Lemma 8); for k >= 2, Lambda_k(k) >= 0
    (a function with exactly k switches exists) and L_k(x) >= 0. Moves for k >= 2, with M
    standing for L or Lambda throughout each line:
      (a) L_k(x) >= x - 1 for 1 <= x <= k + 1                        (shattering)
      (b) M_k(x) >= M_k(x - 1)                                        (monotonicity)
      (c) M_k(x) >= 1 + min(M_k(x-1), M_{k-1}(x-1)),  x >= 2          (adjacent query)
      (d) M_k(x) >= 1 + min(M_k(x-2), 1 + M_{k-1}(x-2)),  x >= 3      (query at distance two)
      (e) L_k(2y) >= Lambda_k(y) + k and Lambda_k(2y) >= Lambda_k(y) + k if Lambda_k(y) >= 0.
    NEG marks 'no full tree known'."""
    Lo = [[0] * (X + 1) for _ in range(K + 1)]
    La = [[0] * (X + 1) for _ in range(K + 1)]
    for x in range(1, X + 1):
        if K >= 1:
            Lo[1][x] = La[1][x] = lam(x)
    for k in range(2, K + 1):
        lo, la, lo1, la1 = Lo[k], La[k], Lo[k - 1], La[k - 1]
        la[0] = NEG
        for x in range(1, X + 1):
            a = 0
            b = 0 if x == k else NEG
            if x <= k + 1:
                a = max(a, x - 1)                                     # (a)
            if x >= 2:
                a = max(a, lo[x - 1], 1 + min(lo[x - 1], lo1[x - 1]))  # (b), (c)
                b = max(b, la[x - 1], 1 + min(la[x - 1], la1[x - 1]))
            if x >= 3:
                a = max(a, 1 + min(lo[x - 2], 1 + lo1[x - 2]))          # (d)
                b = max(b, 1 + min(la[x - 2], 1 + la1[x - 2]))
            if x % 2 == 0 and la[x // 2] >= 0:
                a = max(a, la[x // 2] + k)                              # (e)
                b = max(b, la[x // 2] + k)
            lo[x] = a
            la[x] = b if b >= 0 else NEG
    return Lo, La


def prescribed_move_failures(k, max_threshold=200000, max_x_full=6000):
    """Checks, for one k >= 2, that in every range the move prescribed by the proof of
    Theorem 4 certifies the induction step from the induction hypotheses
    L_k' >= v_k' and Lambda_k' >= tau_k' on smaller instances. Returns a list of failures.

    (i) at x = Q_k(d) <= max_threshold:
        d <= k: shattering (a); k+1 <= d <= d_k+k+floor(k/2)-2: query at distance two (d);
        larger d: refinement (e) from x/2.
    (ii) at every k < x < max_x_full where tau_k increases:
        tau_k(x) = x - k: adjacent query (c) for Lambda;
        otherwise x = Q_k(d) with d >= k+1: (d) for Lambda in the same range as in (i), and
        refinement (e) beyond."""
    fails = []
    dk = d_k(k)
    top = dk + k + k // 2 - 2
    d = 1
    while Q(k, d) <= max_threshold:
        x = Q(k, d)
        if d <= k:
            ok = x <= k + 1 and x - 1 >= d
            move = "a"
        elif d <= top:
            ok = x >= 3 and 1 + min(v(k, x - 2), 1 + v(k - 1, x - 2)) >= d
            move = "d"
        else:
            ok = x % 2 == 0 and x // 2 >= k and tau(k, x // 2) + k >= d
            move = "e"
        if not ok:
            fails.append(("i", k, d, x, move))
        d += 1
    for x in range(k + 1, max_x_full):
        t = tau(k, x)
        if t <= tau(k, x - 1):
            continue
        if t == x - k:
            ok = 1 + min(tau(k, x - 1), tau(k - 1, x - 1)) >= t
            move = "c"
        else:
            dd = v(k, x)
            ok = x == Q(k, dd) and dd >= k + 1
            if ok and dd <= top:
                ok = 1 + min(tau(k, x - 2), 1 + tau(k - 1, x - 2)) >= dd
                move = "d"
            elif ok:
                ok = x % 2 == 0 and x // 2 >= k and tau(k, x // 2) + k >= dd
                move = "e"
            else:
                move = "?"
        if not ok:
            fails.append(("ii", k, x, t, move))
    return fails


def Q_property_failures(k, D):
    """Lemma 22(a)-(d) for one k >= 1 and 0 <= d <= D. Returns failures."""
    fails = []
    dk = d_k(k)
    for d in range(1, D + 1):
        diff = Q(k, d) - Q(k, d - 1)
        if diff < 1 or (d >= k + 1 and diff < 2):
            fails.append(("a", k, d))
    for d in range(D + 1):
        if Q(k, d) < 2 * d - k + 1:
            fails.append(("b", k, d))
        if d >= dk + k and Q(k, d) < d + k:
            fails.append(("c", k, d))
        if k >= 2 and k + 1 <= d <= dk + k + k // 2 - 2 and Q(k - 1, d - 2) > Q(k, d) - 2:
            fails.append(("d", k, d))
    return fails


# ---------------------------------------------------------------------------
# Remarks: natural learner and counting bound
# ---------------------------------------------------------------------------

def natural_learner_mistakes(m):
    """N(m) = 1 + max{d : c(d) <= m+1}: mistakes forced on a learner that predicts 0 until
    the first positive example (remark 'the natural learner is not optimal')."""
    d = 0
    while c(d + 1) <= m + 1:
        d += 1
    return 1 + d


def counting_bound(m):
    """floor(lg |Int_m|) = floor(lg(1 + m(m+1)/2)), the halving bound."""
    return lam(1 + m * (m + 1) // 2)


# ---------------------------------------------------------------------------
# Section 'Randomised learners'
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def interp_lg(l):
    """lambda~(l) = t + (l - 2^t) / 2^t with t = floor(lg l): the piecewise-linear
    interpolation of lg between powers of two (exact Fraction, integer l >= 1)."""
    t = lam(l)
    return t + Fraction(l - (1 << t), 1 << t)


def rl_generic(funcs, npts):
    """RL of an explicit finite class by Lemma 27:
    RL(V) = max(0, max_x (1 + RL(V_x^0) + RL(V_x^1)) / 2) over points x splitting V.
    Exact rational arithmetic; no structure of the class is used."""
    funcs = sorted(set(funcs))
    ones = []
    for p in range(npts):
        mask = 0
        for i, f in enumerate(funcs):
            if (f >> p) & 1:
                mask |= 1 << i
        ones.append(mask)
    memo = {}

    def RL(vs):
        if vs & (vs - 1) == 0:
            return Fraction(0)
        got = memo.get(vs)
        if got is not None:
            return got
        best = Fraction(0)
        for o in ones:
            v1 = vs & o
            if v1 == 0 or v1 == vs:
                continue
            val = (1 + RL(v1) + RL(vs ^ v1)) / 2
            if val > best:
                best = val
        memo[vs] = best
        return best

    if not funcs:
        raise ValueError("empty class")
    return RL((1 << len(funcs)) - 1)


def rl_chain(c_):
    """Proposition 28: a chain of c threshold functions has RL = lambda~(c) / 2."""
    return interp_lg(c_) / 2


@lru_cache(maxsize=None)
def _rl_pieces(pieces):
    best = Fraction(0)
    for idx, l in enumerate(pieces):
        if idx and pieces[idx - 1] == l:
            continue
        rest = pieces[:idx] + pieces[idx + 1:]
        for u in range(1, l // 2 + 1):            # cut l = u + v; (u, v) and (v, u) agree
            w = l - u
            nxt = tuple(sorted(rest + tuple(p for p in (u, w) if p >= 2)))
            val = (1 + (interp_lg(u) + interp_lg(w)) / 2 + _rl_pieces(nxt)) / 2
            if val > best:
                best = val
    return best


def rl_cut_game(pieces):
    """RL(J_S) by Eq. (2), the discounted cutting game, for a multiset of piece measures
    l = g + 1 (block length plus one):
    RL = max(0, max over cuts l = u + v of (1 + lambda~(u)/2 + lambda~(v)/2 + RL(S')) / 2),
    where S' replaces the piece l by u and v. Pieces of measure 1 cannot be cut."""
    return _rl_pieces(tuple(sorted(p for p in pieces if p >= 2)))


def rl_intervals(m):
    """RL(Int_m) = rl_cut_game([m + 1])."""
    return rl_cut_game([m + 1])


@lru_cache(maxsize=None)
def R(l):
    """R(1) = 0, R(l) = 1 - 2^(1-l) + (R(floor(l/2)) + R(ceil(l/2))) / 2 for l >= 2 (exact).
    Theorem 30: RL(Int_m) >= R(m+1)."""
    if l == 1:
        return Fraction(0)
    return 1 - Fraction(2, 1 << l) + (R(l // 2) + R((l + 1) // 2)) / 2


def R_closed(l):
    """Lemma 29: R(l) = sum_{j=0}^{L} (1 - 2^(1-f_j) + pi_j 2^(-f_j)),
    L = floor(lg l), f_j = floor(l / 2^j), pi_j = l / 2^j - f_j."""
    total = Fraction(0)
    for j in range(lam(l) + 1):
        f = l >> j
        pi = Fraction(l, 1 << j) - f
        total += 1 - Fraction(2, 1 << f) + pi / (1 << f)
    return total


def greedy_cut(p):
    """The cut of the greedy adversary (Theorem 30) on a piece p >= 2, t = floor(lg p):
    u = max(2^(t-1), p - 2^t), v = p - u."""
    t = lam(p)
    u = max(1 << (t - 1), p - (1 << t))
    return u, p - u


def schedule_value(pieces, rule):
    """Discounted value sum_i 2^-i (1 + lambda~(u_i)/2 + lambda~(v_i)/2) of the complete cut
    schedule produced by rule(current pieces) -> (piece, u), starting from the given piece
    measures. Each such value is a lower bound on rl_cut_game(pieces) (Eq. (2))."""
    cur = sorted(p for p in pieces if p >= 2)
    total, scale = Fraction(0), Fraction(1, 2)
    while cur:
        p, u = rule(tuple(cur))
        w = p - u
        total += scale * (1 + (interp_lg(u) + interp_lg(w)) / 2)
        scale /= 2
        cur.remove(p)
        cur = sorted(cur + [q for q in (u, w) if q >= 2])
    return total


def greedy_value(pieces):
    """Value of the greedy schedule of Theorem 30 from a position (multiset of piece
    measures): always cut a largest piece p by greedy_cut(p)."""
    heap = [-p for p in pieces if p >= 2]
    heapq.heapify(heap)
    total, scale = Fraction(0), Fraction(1, 2)
    while heap:
        p = -heapq.heappop(heap)
        u, w = greedy_cut(p)
        total += scale * (1 + (interp_lg(u) + interp_lg(w)) / 2)
        scale /= 2
        for q in (u, w):
            if q >= 2:
                heapq.heappush(heap, -q)
    return total


def greedy_cut_sequence(l):
    """The pieces p_1 >= p_2 >= ... cut by the greedy schedule from a rod of measure l."""
    out, stack = [], [l]
    while stack:
        p = stack.pop()
        if p >= 2:
            out.append(p)
            stack.extend(greedy_cut(p))
    return sorted(out, reverse=True)


def clear_caches():
    """Free the memo tables of the exact solvers."""
    for fn in (_J, _gap_L, _cyc_L, _rl_pieces, R, interp_lg):
        fn.cache_clear()
    _Q_LISTS.clear()
