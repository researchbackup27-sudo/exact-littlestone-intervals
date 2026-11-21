"""Explicit optimal online learners for intervals, unions of intervals and the
families R_k, G_k of the paper

    How many mistakes does it take to learn an interval?
    Exact Littlestone dimensions of intervals and their unions.

The learner is the one built in the upper-bound proof of Theorem 4. On a domain
of size x it uses the gap-potential learner of Lemma 19 while
x < Q_k(d_k + k - 1), and otherwise the block-pairing learner of Lemma 20 around
a learner for size floor(x/2). It makes at most v_k(x) mistakes on R_k(x)
(k even) or G_k(x) (k odd), and at most Ldim(Int_m) mistakes on intervals over
[m], which are run as R_2(m + 1). The base learner has constant size for fixed
k, so a round costs O(log x) dictionary operations, and the labels kept at all
levels take O(x) memory.

Numbers of results follow the submitted version of the paper.

Paper element                                         class / function
--------------------------------------------------------------------------
gap potential Phi, Lemma 19                           PotentialLearner
block pairing, Lemma 20; upper bound of Theorem 4     OptimalLearner
Int_m as R_2(m + 1), Lemma 10, Theorems 1 and 4       OptimalIntervalLearner
learner of Remark 25                                  NaturalLearner
adaptive adversary, by exhaustive search              worst_case_mistakes

Every learner has the interface predict(z) -> 0 or 1, update(z, y), and key(),
a hashable description of its whole state (used to memoise the adversary search).
"""

from bisect import bisect_left, insort
from copy import deepcopy

from littlestone_intervals import Q, d_k

__all__ = ["PotentialLearner", "OptimalLearner", "OptimalIntervalLearner",
           "NaturalLearner", "worst_case_mistakes"]


# ---------------------------------------------------------------------------
# Lemma 19: gap-potential learner
# ---------------------------------------------------------------------------

class PotentialLearner:
    """Gap-potential learner on R_k(x) (cycle) or G_k(x) (path with fixed ends).

    Cycle: points 0, ..., x-1, point 0 fixed to 0. Path: points 0, ..., x, point 0
    fixed to 0 and point x fixed to 1. Between two consecutive labelled points lies a
    gap of type A (different labels) or B (equal labels); with r = k - #A the spare
    switch budget, the potential is

        Phi = floor(r/2) + sum_A ceil(a/2) + sum_B floor(b/2)      (Lemma 19, no E gaps).

    The learner predicts the label whose branch has the larger potential (0 on a
    tie). By Lemma 19 the smaller branch has potential at most Phi - 1, so every
    mistake lowers Phi by at least 1.
    """

    def __init__(self, k, x, cycle):
        self.k, self.x, self.cycle = k, x, cycle
        self.pos = [0] if cycle else [0, x]          # labelled points, sorted
        self.lab = {0: 0} if cycle else {0: 0, x: 1}

    def _gap(self, a, b):
        """Number of unlabelled points strictly between labelled points a and b."""
        return (b - a - 1) % self.x if self.cycle else b - a - 1

    def _stats(self):
        """(number of A gaps, sum of the gap terms of Phi). On the cycle with only point 0
        labelled, the pair (0, 0) is one B gap of length x - 1."""
        pos, lab = self.pos, self.lab
        if self.cycle:
            pairs = zip(pos, pos[1:] + pos[:1])
        else:
            pairs = zip(pos, pos[1:])
        n_a = s = 0
        for a, b in pairs:
            g, is_a = self._gap(a, b), lab[a] != lab[b]
            n_a += is_a
            s += (g + 1) // 2 if is_a else g // 2
        return n_a, s

    def _phi_after(self, z, y, n_a, s):
        """Phi after labelling the unlabelled point z with y; None if no function is left."""
        pos, lab = self.pos, self.lab
        i = bisect_left(pos, z)
        if self.cycle:
            left, right = pos[i - 1], pos[i % len(pos)]
        else:
            left, right = pos[i - 1], pos[i]
        old_a = lab[left] != lab[right]
        new_l, new_r = lab[left] != y, y != lab[right]
        r = self.k - (n_a - old_a + new_l + new_r)
        if r < 0:
            return None

        def term(g, is_a):
            return (g + 1) // 2 if is_a else g // 2
        s2 = (s - term(self._gap(left, right), old_a)
              + term(self._gap(left, z), new_l) + term(self._gap(z, right), new_r))
        return r // 2 + s2

    def predict(self, z):
        if z in self.lab:
            return self.lab[z]
        n_a, s = self._stats()
        p0, p1 = self._phi_after(z, 0, n_a, s), self._phi_after(z, 1, n_a, s)
        if p1 is None:
            return 0
        if p0 is None:
            return 1
        return 1 if p1 > p0 else 0

    def update(self, z, y):
        if z in self.lab:
            return
        insort(self.pos, z)
        self.lab[z] = y

    def key(self):
        return ("P", tuple(sorted(self.lab.items())))


# ---------------------------------------------------------------------------
# Lemma 20 and Theorem 4: the optimal learner
# ---------------------------------------------------------------------------

class OptimalLearner:
    """Optimal learner for R_k(x) (k even, cycle 0..x-1) or G_k(x) (k odd, path 0..x).

    For x < Q_k(d_k + k - 1) this is the PotentialLearner. Otherwise the points are
    grouped into the blocks of Lemma 20, a learner for size floor(x/2) runs on the
    blocks, and each block is represented by its fixed point or by its first
    presented point; a non-representative point is predicted with the label of its
    block's representative. Mistakes: at most v_k(x).
    """

    def __init__(self, k, x):
        self.k, self.x = k, x
        self.cycle = (k % 2 == 0)
        self.base = x < Q(k, d_k(k) + k - 1)
        if self.base:
            self.inner = PotentialLearner(k, x, self.cycle)
            return
        self.h = x // 2
        self.sub = OptimalLearner(k, self.h)
        self.lab = {0: 0} if self.cycle else {0: 0, x: 1}
        self.rep = {0: 0} if self.cycle else {0: 0, self.h: x}   # block -> representative

    def block(self, z):
        """Block of point z, numbered as the points of the coarse instance (Lemma 20)."""
        x = self.x
        if self.cycle:
            if x % 2 == 1 and z == x - 1:
                return 0                              # block {x-1, 0, 1}
            return z // 2
        if x % 2 == 0 and z == x:
            return self.h                             # block {x}
        return z // 2

    def predict(self, z):
        if self.base:
            return self.inner.predict(z)
        if z in self.lab:
            return self.lab[z]
        b = self.block(z)
        if b in self.rep:
            return self.lab[self.rep[b]]
        return self.sub.predict(b)

    def update(self, z, y):
        if self.base:
            self.inner.update(z, y)
            return
        if z in self.lab:
            return
        self.lab[z] = y
        b = self.block(z)
        if b not in self.rep:
            self.rep[b] = z
            self.sub.update(b, y)

    def key(self):
        if self.base:
            return self.inner.key()
        return ("R", tuple(sorted(self.rep.items())), tuple(sorted(self.lab.items())),
                self.sub.key())


class OptimalIntervalLearner:
    """Optimal learner for Int_m: domain point i in [m] is point i of the cycle of
    R_2(m + 1), whose point 0 is fixed to 0 (Lemma 10). Mistakes: at most Ldim(Int_m)."""

    def __init__(self, m):
        self.m = m
        self.inner = OptimalLearner(2, m + 1)

    def predict(self, i):
        return self.inner.predict(i)

    def update(self, i, y):
        self.inner.update(i, y)

    def key(self):
        return self.inner.key()


# ---------------------------------------------------------------------------
# Remark 25: the natural learner
# ---------------------------------------------------------------------------

class NaturalLearner:
    """Predicts 0 until the first positive example; afterwards predicts 1 inside the
    span of the positives and runs a binary search (majority over the candidates,
    ties to 0) for each endpoint. Its worst case is N(m) of Remark 25."""

    def __init__(self, m):
        self.m = m
        self.neg = []                 # sorted negative points
        self.lo = self.hi = None      # smallest and largest positive point
        self.lab = {}

    def update(self, i, y):
        if i in self.lab:
            return
        self.lab[i] = y
        if y:
            self.lo = i if self.lo is None else min(self.lo, i)
            self.hi = i if self.hi is None else max(self.hi, i)
        else:
            insort(self.neg, i)

    def predict(self, i):
        if i in self.lab:
            return self.lab[i]
        if self.lo is None:
            return 0
        if self.lo <= i <= self.hi:
            return 1
        t = bisect_left(self.neg, self.lo)
        left = self.neg[t - 1] if t > 0 else 0                       # left endpoint in [left+1, lo]
        t = bisect_left(self.neg, self.hi)
        right = self.neg[t] if t < len(self.neg) else self.m + 1     # right endpoint in [hi, right-1]
        if i < self.lo:
            if i <= left:
                return 0
            return 1 if 2 * (i - left) > self.lo - left else 0
        if i >= right:
            return 0
        return 1 if 2 * (right - i) > right - self.hi else 0

    def key(self):
        return ("N", tuple(sorted(self.lab.items())))


# ---------------------------------------------------------------------------
# Exhaustive adaptive adversary
# ---------------------------------------------------------------------------

def worst_case_mistakes(make_learner, funcs, npts):
    """Largest number of mistakes an adaptive adversary can force on the learner
    make_learner() over the class (funcs, npts) of the module littlestone_intervals
    (bit p of a function is its value at the learner's point p + 1). The adversary
    may present any unlabelled point and give any label that leaves the version
    space nonempty (also a label that is already forced, which a learner may still
    predict wrongly); the search is exhaustive, memoised on the learner's state,
    which determines the labels seen.
    Exponential in npts: meant for small classes."""
    memo = {}

    def rec(learner, version, labelled):
        key = learner.key()
        if key in memo:
            return memo[key]
        best = 0
        for p in range(npts):
            z = p + 1
            if z in labelled:
                continue
            ones = [f for f in version if (f >> p) & 1]
            zeros = [f for f in version if not (f >> p) & 1]
            yhat = learner.predict(z)
            for y, rest in ((0, zeros), (1, ones)):
                if not rest:
                    continue           # this label would leave no function
                nxt = deepcopy(learner)
                nxt.update(z, y)
                best = max(best, (y != yhat) + rec(nxt, rest, labelled | {z}))
        memo[key] = best
        return best

    return rec(make_learner(), list(funcs), frozenset())
