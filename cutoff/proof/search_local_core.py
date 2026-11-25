#!/usr/bin/env python3
"""Local search for violations of P(s) (overfull-core note, Erdos 617).

Question P_loc(r, s): is there an r-colouring of the edges of K_n, n = s*r+1
(or --n), in which
  (B) every (r+1)-set of vertices sees all r colours,
  (A) colour 0 has independence number at most s on the whole vertex set,
  (K) colour 0 has no clique of size r,
  (E) optionally colour 0 has at most --emax edges?
A model shows that the statement P(s) of the note fails locally at order r.
UNSAT shows that it holds there. With --n s*r the same search tests the
stronger statement for sets of exactly s*r vertices.

Example:  python3 -B search_local_core.py --r 5 --s 2 --n 10

CNF + cadical. Balance clauses are added up front when few, else lazily
(counterexample-guided): after each model, independent (r+1)-sets of each
colour are found by search and their clauses added.
"""
import argparse, itertools, os, random, subprocess, sys, tempfile, time
from math import comb


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses = []

    def new(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        self.clauses.append(cl)

    def at_most(self, lits, k):
        n = len(lits)
        if k >= n:
            return
        s = [[self.new() for _ in range(k)] for _ in range(n - 1)]
        self.add([-lits[0], s[0][0]])
        for j in range(1, k):
            self.add([-s[0][j]])
        for i in range(1, n - 1):
            self.add([-lits[i], s[i][0]])
            self.add([-s[i - 1][0], s[i][0]])
            for j in range(1, k):
                self.add([-lits[i], -s[i - 1][j - 1], s[i][j]])
                self.add([-s[i - 1][j], s[i][j]])
            self.add([-lits[i], -s[i - 1][k - 1]])
        self.add([-lits[n - 1], -s[n - 2][k - 1]])

    def solve(self, seconds, seed=0):
        fd, path = tempfile.mkstemp(suffix='.cnf', dir=tempfile.gettempdir())
        with os.fdopen(fd, 'w') as f:
            f.write('p cnf %d %d\n' % (self.nv, len(self.clauses)))
            f.write('\n'.join(' '.join(map(str, cl)) + ' 0' for cl in self.clauses))
            f.write('\n')
        try:
            out = subprocess.run(['cadical', '-q', '-t', str(max(1, int(seconds))), '--seed=%d' % seed, path],
                                 capture_output=True, text=True)
        finally:
            os.unlink(path)
        if out.returncode == 20:
            return 'UNSAT', None
        if out.returncode != 10:
            return 'UNKNOWN', None
        model = set()
        for line in out.stdout.splitlines():
            if line.startswith('v '):
                for tok in line[2:].split():
                    v = int(tok)
                    if v > 0:
                        model.add(v)
        return 'SAT', model


def indep_sets(adjmask, n, size, limit):
    """Up to `limit` independent sets of the given size in the graph with adjacency bitmasks."""
    out = []

    def rec(start, chosen, allowed):
        if len(out) >= limit:
            return
        if len(chosen) == size:
            out.append(tuple(chosen))
            return
        need = size - len(chosen)
        cand = [v for v in range(start, n) if (allowed >> v) & 1]
        if len(cand) < need:
            return
        for idx, v in enumerate(cand):
            if len(cand) - idx < need:
                break
            rec(v + 1, chosen + [v], allowed & ~adjmask[v] & ~(1 << v))
            if len(out) >= limit:
                return

    rec(0, [], (1 << n) - 1)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--r', type=int, required=True)
    ap.add_argument('--s', type=int, required=True)
    ap.add_argument('--n', type=int, default=0)
    ap.add_argument('--emax', type=int, default=-1)
    ap.add_argument('--nokfree', action='store_true')
    ap.add_argument('--noalpha', action='store_true', help='drop (A) and (K): plain balanced colouring')
    ap.add_argument('--seconds', type=int, default=900)
    ap.add_argument('--upfront', type=int, default=3500000, help='max balance clauses to add up front')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--tag', default='')
    a = ap.parse_args()
    r, s = a.r, a.s
    n = a.n or s * r + 1
    random.seed(a.seed)
    t0 = time.time()
    pairs = list(itertools.combinations(range(n), 2))
    F = CNF()
    x = {(p, c): F.new() for p in pairs for c in range(r)}
    for p in pairs:
        F.add([x[(p, c)] for c in range(r)])
        for c1 in range(r):
            for c2 in range(c1 + 1, r):
                F.add([-x[(p, c1)], -x[(p, c2)]])
    if not a.noalpha:
        for S in itertools.combinations(range(n), s + 1):
            F.add([x[(p, 0)] for p in itertools.combinations(S, 2)])
        if not a.nokfree and comb(n, r) <= 3000000:
            for S in itertools.combinations(range(n), r):
                F.add([-x[(p, 0)] for p in itertools.combinations(S, 2)])
    if a.emax >= 0:
        F.at_most([x[(p, 0)] for p in pairs], a.emax)
    lazy = comb(n, r + 1) * r > a.upfront
    if not lazy:
        for S in itertools.combinations(range(n), r + 1):
            ps = list(itertools.combinations(S, 2))
            for c in range(r):
                F.add([x[(p, c)] for p in ps])
    it = 0
    while True:
        left = a.seconds - (time.time() - t0)
        if left <= 0:
            print('RESULT', a.tag, 'TIMEOUT after %d rounds' % it, flush=True)
            return
        res, model = F.solve(left, a.seed + it)
        if res != 'SAT':
            print('RESULT', a.tag, res, 'after %d rounds, %.1fs, %d clauses' % (it, time.time() - t0, len(F.clauses)), flush=True)
            return
        it += 1
        col = {}
        for p in pairs:
            for c in range(r):
                if x[(p, c)] in model:
                    col[p] = c
        added = 0
        for c in range(r):
            adj = [0] * n
            for (u, v), cc in col.items():
                if cc == c:
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
            for S in indep_sets(adj, n, r + 1, 400):
                F.add([x[(p, c)] for p in itertools.combinations(S, 2)])
                added += 1
            if c == 0 and not a.noalpha and not a.nokfree:
                comp = [((1 << n) - 1) & ~adj[v] & ~(1 << v) for v in range(n)]
                for S in indep_sets(comp, n, r, 400):
                    F.add([-x[(p, 0)] for p in itertools.combinations(S, 2)])
                    added += 1
        if added == 0:
            e0 = sorted(p for p, c in col.items() if c == 0)
            print('RESULT', a.tag, 'SAT after %d rounds, %.1fs' % (it, time.time() - t0))
            print('n', n, 'r', r, 's', s, 'colour0_edges', len(e0))
            print('colouring', sorted(col.items()), flush=True)
            return
        if it % 10 == 0:
            print('round', it, 'added', added, 'clauses', len(F.clauses), 'time %.0f' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
