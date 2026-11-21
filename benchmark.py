"""Random-stream benchmark of the learners in optimal_learner.py on intervals.

For each m, a target is drawn uniformly from Int_m (the empty set included) and
the points of [m] arrive in a uniformly random order. The script reports, for
the optimal learner and the natural learner of Remark 25, the mean, the
population standard deviation and the maximum number of mistakes over the
trials, and the mean time per round. Ldim(Int_m), the worst case over all
targets and orders, is printed for comparison. Optimal refers to the worst case;
on these random streams the natural learner makes fewer mistakes on average
(Table 4 of the submitted version). Seeded; a few seconds on a laptop CPU.

    python3 benchmark.py
"""

import random
import statistics
import sys
import time

import littlestone_intervals as li
import optimal_learner as ol

SIZES = [(15, 5000), (63, 5000), (255, 2000), (1023, 1000), (4095, 300)]   # (m, trials)
SEED = 12345
LEARNERS = {"optimal": ol.OptimalIntervalLearner, "natural": ol.NaturalLearner}


def random_interval(m, rnd):
    """Uniform element of Int_m as (a, b); the empty interval is (1, 0)."""
    t = rnd.randrange(1 + m * (m + 1) // 2)
    if t == 0:
        return 1, 0
    t -= 1
    a = 1
    while t >= m - a + 1:
        t -= m - a + 1
        a += 1
    return a, a + t


def run(make, m, target, order):
    """Mistakes of make(m) on the stream, and the mean time per round in seconds."""
    a, b = target
    learner = make(m)
    mistakes = 0
    t0 = time.perf_counter()
    for i in order:
        y = 1 if a <= i <= b else 0
        if learner.predict(i) != y:
            mistakes += 1
        learner.update(i, y)
    return mistakes, (time.perf_counter() - t0) / len(order)


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)
    print(f"{'m':>5} {'trials':>6} {'Ldim':>4} | {'learner':<8} {'mean':>6} {'sd':>5} {'max':>4} "
          f"{'us/round':>8}")
    t_all = time.time()
    for m, trials in SIZES:
        rnd = random.Random(SEED + m)
        mistakes = {name: [] for name in LEARNERS}
        times = {name: [] for name in LEARNERS}
        for _ in range(trials):
            target = random_interval(m, rnd)
            order = list(range(1, m + 1))
            rnd.shuffle(order)
            for name, make in LEARNERS.items():
                k, t = run(make, m, target, order)
                mistakes[name].append(k)
                times[name].append(t)
        for j, name in enumerate(LEARNERS):
            head = f"{m:>5} {trials:>6} {li.ldim_intervals_formula(m):>4}" if j == 0 else " " * 17
            print(f"{head} | {name:<8} {statistics.mean(mistakes[name]):6.2f} "
                  f"{statistics.pstdev(mistakes[name]):5.2f} {max(mistakes[name]):4d} "
                  f"{1e6 * statistics.mean(times[name]):8.2f}")
    print(f"\nTotal time {time.time() - t_all:.0f} s.")


if __name__ == "__main__":
    main()
