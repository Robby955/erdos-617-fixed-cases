#!/usr/bin/env python3
"""One-hue feasibility search for the overfull-core note (Erdos 617).

Searches for a graph G on n vertices with
  (A) independence number exactly h, with vertices 0..h-1 independent,
  (B) with --krfree, no clique of size r,
  (C) every vertex set S spanning at most
          cap(|S|) = C(|S|,2) - (r-1) * p_r(|S|)
      edges, where p_r(m) is the least number of edges of a graph on m
      vertices with independence number at most r,
  (D) at most emax edges.
Condition (C) is necessary for one hue of a balanced r-colouring: on S each of
the other r-1 hues has independence number at most r, hence p_r(|S|) edges.

Method: CNF with sequential-counter cardinality constraints, solved by cadical.
Independence clauses and the two smallest caps are added at the start. The
remaining caps are checked exactly on every model over all 2^n vertex sets
(n <= 26) and violated ones are added until the solver answers UNSAT or a
model passes every check. Symmetry breaking: the first h vertices are a
maximum independent set and the other vertices are ordered by their least
neighbour in it.

Example:  python3 -B search_one_colour.py --r 3 --n 10 --h 3 --emax 17
"""
import argparse, itertools, os, subprocess, sys, tempfile, time
from math import comb
import numpy as np


def pturan(m, r):
    q, s = divmod(m, r)
    return r * q * (q - 1) // 2 + s * q


def cap(m, r):
    return m * (m - 1) // 2 - (r - 1) * pturan(m, r)


PC16 = np.zeros(1 << 16, dtype=np.int8)
for _i in range(16):
    PC16 += ((np.arange(1 << 16) >> _i) & 1).astype(np.int8)


def popcount(a):
    a = a.astype(np.uint32)
    return PC16[a & 0xFFFF] + PC16[(a >> 16) & 0xFFFF]


def subset_edge_counts(adj, n):
    E = np.zeros(1 << n, dtype=np.int16)
    for v in range(n):
        low = 0
        for u in range(v):
            if adj[v][u]:
                low |= 1 << u
        size = 1 << v
        idx = np.arange(size, dtype=np.uint32)
        E[size:2 * size] = E[:size] + popcount(idx & np.uint32(low)).astype(np.int16)
    return E


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses = []

    def new(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        self.clauses.append(list(cl))

    def at_most(self, lits, k):
        """Sinz sequential counter: sum(lits) <= k."""
        n = len(lits)
        if k >= n:
            return
        if k == 0:
            for l in lits:
                self.add([-l])
            return
        if comb(n, k + 1) <= 64:
            for sub in itertools.combinations(lits, k + 1):
                self.add([-l for l in sub])
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

    def solve(self, seconds):
        fd, path = tempfile.mkstemp(suffix='.cnf', dir=tempfile.gettempdir())
        with os.fdopen(fd, 'w') as f:
            f.write('p cnf %d %d\n' % (self.nv, len(self.clauses)))
            for cl in self.clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')
        try:
            out = subprocess.run(['cadical', '-q', '-t', str(max(1, int(seconds))), path],
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


def max_indep_set(adj, n, limit):
    nb = [set(u for u in range(n) if adj[v][u]) for v in range(n)]

    def rec(cur, cand):
        if len(cur) > limit:
            return cur
        cand = list(cand)
        while cand:
            if len(cur) + len(cand) <= limit:
                return None
            v = cand.pop()
            res = rec(cur + [v], [u for u in cand if u not in nb[v]])
            if res:
                return res
        return None

    return rec([], list(range(n)))


def find_clique(adj, n, size):
    nb = [set(u for u in range(n) if adj[v][u]) for v in range(n)]

    def rec(cur, cand):
        if len(cur) >= size:
            return cur
        cand = list(cand)
        while cand:
            if len(cur) + len(cand) < size:
                return None
            v = cand.pop()
            res = rec(cur + [v], [u for u in cand if u in nb[v]])
            if res:
                return res
        return None

    return rec([], list(range(n)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--r', type=int, required=True)
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--h', type=int, required=True)
    ap.add_argument('--emax', type=int, required=True)
    ap.add_argument('--krfree', action='store_true')
    ap.add_argument('--nocaps', action='store_true')
    ap.add_argument('--seconds', type=int, default=600)
    ap.add_argument('--tag', default='')
    a = ap.parse_args()
    r, n, h = a.r, a.n, a.h
    t0 = time.time()
    pairs = list(itertools.combinations(range(n), 2))
    F = CNF()
    x = {p: F.new() for p in pairs}
    X = lambda u, v: x[(u, v) if u < v else (v, u)]
    # (A) WLOG independent h-set on 0..h-1, everything else dominated by it
    for p in itertools.combinations(range(h), 2):
        F.add([-x[p]])
    for u in range(h, n):
        F.add([X(i, u) for i in range(h)])
    # symmetry: outside vertices sorted by lowest neighbour in the h-set
    for u in range(h, n - 1):
        for i in range(h):
            F.add([-X(i, u + 1)] + [X(j, u) for j in range(i + 1)])
    if comb(n, h + 1) <= 600000:
        for S in itertools.combinations(range(n), h + 1):
            F.add([x[p] for p in itertools.combinations(S, 2)])
    # (D)
    F.at_most([x[p] for p in pairs], a.emax)
    # (C) smallest caps up front
    if not a.nocaps:
        for msize in (r + 1, r + 2):
            if msize <= n and comb(n, msize) * 60 <= 3000000:
                c = cap(msize, r)
                for S in itertools.combinations(range(n), msize):
                    F.at_most([x[p] for p in itertools.combinations(S, 2)], c)
    it = 0
    exact = n <= 26
    pc = popcount(np.arange(1 << n, dtype=np.uint32)) if exact else None
    while True:
        left = a.seconds - (time.time() - t0)
        if left <= 0:
            print('RESULT', a.tag, 'TIMEOUT after %d refinements' % it, flush=True)
            return
        res, model = F.solve(left)
        if res != 'SAT':
            print('RESULT', a.tag, res, 'after %d refinements, %.1fs' % (it, time.time() - t0), flush=True)
            return
        adj = [[False] * n for _ in range(n)]
        for (u, v) in pairs:
            if x[(u, v)] in model:
                adj[u][v] = adj[v][u] = True
        it += 1
        added = 0
        I = max_indep_set(adj, n, h)
        if I:
            F.add([x[p] for p in itertools.combinations(sorted(I), 2)])
            added += 1
        if a.krfree:
            K = find_clique(adj, n, r)
            if K:
                F.add([-x[p] for p in itertools.combinations(sorted(K), 2)])
                added += 1
        if exact and not a.nocaps:
            E = subset_edge_counts(adj, n)
            for msize in range(r + 1, n + 1):
                c = cap(msize, r)
                sel = np.nonzero(pc == msize)[0]
                bad = sel[E[sel] > c]
                if len(bad):
                    order = np.argsort(-E[bad].astype(np.int32))[:60]
                    for S in bad[order]:
                        verts = [v for v in range(n) if (int(S) >> v) & 1]
                        F.at_most([x[p] for p in itertools.combinations(verts, 2)], c)
                        added += 1
            del E
        if added == 0:
            edges = [(u, v) for (u, v) in pairs if adj[u][v]]
            print('RESULT', a.tag, 'SAT after %d refinements, %.1fs' % (it, time.time() - t0))
            print('edges', len(edges), edges)
            print('degrees', sorted(sum(adj[v]) for v in range(n)), flush=True)
            return


if __name__ == '__main__':
    main()
