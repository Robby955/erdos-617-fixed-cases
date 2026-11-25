#!/usr/bin/env python3
"""Second replay of the arithmetic in four-rows.md, written from the note.

This file shares no code with verify_four_rows.py.  It rebuilds every bound
from the statements in Sections 2 to 5 of the note with exact rational
arithmetic, reads the weights in four-row-certificates.json, and checks

  1. the uniform exclusion of all 109 profiles at order 28 (Section 4),
  2. for each order 17..27, that every profile is excluded by the threshold
     test or by its certificate (Section 5).

Run:  python3 -B replay_four_rows_second.py
"""
import json
import sys
from fractions import Fraction
from itertools import combinations, product
from math import comb
from pathlib import Path


def p4(z):
    """Fewest edges of a graph on z vertices with independence number <= 4."""
    q, x = divmod(z, 4)
    return 4 * comb(q, 2) + x * q


def all_profiles():
    out = []
    for b1 in range(8):
        for b2 in range(b1, 8):
            for b3 in range(b2, 8):
                for b4 in range(b3, 8):
                    s = b1 + b2 + b3 + b4
                    for k in range(s, 8):
                        out.append(((b1, b2, b3, b4), k))
    return out


def row_need(r, b, z, f):
    """F(z): nontarget edges forced on a row of size r-1-b plus z exterior points."""
    if z == b + 1:
        return f
    return max(0, (r - 1) * (z - b - 1))


def marking_cap(r, b, P, L):
    """Largest possible number of incident vertices with at most L misses (f = r-10)."""
    if L < 0:
        return 0
    for z in range(1, P + 1):
        if z * L + comb(z, 2) - p4(z) < row_need(r, b, z, r - 10):
            return z - 1
    return P


def pair_bound(bi, bj, pi, pj, r):
    """Upper bound on the chance that a random pair from two lists is a target edge."""
    cut = pi + pj if r is None else min(r - 1, pi + pj)
    return min(Fraction(1), Fraction(bi * bj + cut, pi * pj))


def cover_possible(bs, ps, r):
    """Necessary condition (5); with r given, the four-list refinement is used."""
    if any(p == 0 for p in ps):
        return True
    n = len(ps)
    t = {}
    for i in range(n):
        for j in range(i + 1, n):
            t[i, j] = pair_bound(bs[i], bs[j], ps[i], ps[j], r)
    total = sum(t.values())
    if r is not None and n == 4:
        total -= t[0, 1] * t[2, 3] + t[0, 2] * t[1, 3] + t[0, 3] * t[1, 2]
    return total >= 1


def threshold_excluded(r, b, k):
    P = 4 + sum(b)
    excess = k - sum(b)
    options = []
    for bi in b:
        best = {}
        for L in range(-1, r - 1 - bi):
            c = marking_cap(r, bi, P, L)
            if c < P:
                best[c] = max(best.get(c, -1), L)
        options.append(sorted(best.items()))
    for choice in product(*options):
        U = P - sum(c for c, _ in choice)
        if U <= 0:
            continue
        most = min(4, 2 + excess // U)
        lows = [L + 1 for _, L in choice]
        alive = False
        for size in range(2, most + 1):
            for J in combinations(range(4), size):
                if cover_possible([b[i] for i in J], [lows[i] for i in J], None):
                    alive = True
                    break
            if alive:
                break
        if not alive:
            return True
    return False


def finite_budgets(r, k):
    assert k >= 5
    # k >= 5 forces a colour of surplus at most two: (r-4)k <= 2r+6 fails.
    assert (r - 4) * k > 2 * r + 6
    S = ((8 - k) * r) // 2
    Q = max(min(2 + t // 3, (8 - k) * r + k - 2 * t) for t in range(S + 1))
    f = r - 7 if r > 4 * (1 + S // 3) else r - 10
    return Q, f


def phi_table(r, b, P, f):
    phi = [0]
    for z in range(1, P + 1):
        best = max(0, row_need(r, b, z, f) - comb(z, 2) + p4(z))
        for u in range(1, z):
            need = Fraction(z * phi[u], u)
            ceil = -((-need.numerator) // need.denominator)
            best = max(best, ceil)
        phi.append(best)
    return phi


def vertex_types(r, b, k, Q, f, box):
    """Every (J, p) that an exterior vertex could have, per Sections 3 and 5."""
    s = [r - 1 - bi for bi in b]
    most = min(4, 2 + k - sum(b))
    for size in range(2, most + 1):
        for J in combinations(range(4), size):
            ranges = [range(f if b[i] == 0 else 0, s[i]) for i in J]
            for ps in product(*ranges):
                # target degree at least sum of (s_i - p_i), at most r + Q
                if sum(s[i] - p for i, p in zip(J, ps)) > r + Q:
                    continue
                if size == 2:
                    i, j = J
                    pi, pj = ps
                    if pi + pj > r - 1:
                        continue
                    if pi > 0 and pj > 0:
                        if pi + pj == r - 1 and min(pi, pj) < f:
                            continue
                        if pj > Q + b[i] + 2 or pi > Q + b[j] + 2:
                            continue
                        if 2 * f > r - 1 and (b[i] == 0 or b[j] == 0):
                            continue
                    if box is not None and J == (2, 3):
                        t, u, present = box
                        if present:
                            both = t * u + pi * pj - min(t, pi) * min(u, pj)
                            if both > b[i] * b[j] + min(r - 1, pi + pj):
                                continue
                        elif pi >= t and pj >= u:
                            continue
                if not cover_possible([b[i] for i in J], list(ps), r):
                    continue
                yield J, ps


def check_leaf(r, b, k, weights, box, counter):
    Q, f = finite_budgets(r, k)
    P = 4 + sum(b)
    rhs = 0
    rows = []
    for label, w in weights:
        assert isinstance(w, int) and w > 0
        if label == 'count-':
            rhs += w * (-P)
            rows.append((w, 'count', None, None))
        elif label == 'arity+':
            rhs += w * (k - sum(b))
            rows.append((w, 'arity', None, None))
        else:
            tag, i = label[0], label[1]
            assert 0 <= i < 4
            if tag == 'root':
                rhs += w * (-(b[i] + 2))
                rows.append((w, 'root', i, None))
            elif tag == 'long singleton':
                assert b[i] == 0 and r - 1 > 12
                rhs += w * 1
                rows.append((w, 'single', i, None))
            elif tag == 'cap':
                L = label[2]
                assert 0 <= L <= r - 1 - b[i]
                rhs += w * marking_cap(r, b[i], P, L)
                rows.append((w, 'cap', i, L))
            elif tag == 'miss':
                L = label[2]
                assert 0 <= L <= r - 1 - b[i]
                phi = phi_table(r, b[i], P, f)
                rhs += w * max(z * L - phi[z] for z in range(P + 1))
                rows.append((w, 'miss', i, L))
            else:
                raise ValueError(label)
    assert rhs < 0, ('right side not negative', r, b, k, rhs)
    for J, ps in vertex_types(r, b, k, Q, f, box):
        miss = dict(zip(J, ps))
        val = 0
        for w, kind, i, L in rows:
            if kind == 'count':
                val -= w
            elif kind == 'arity':
                val += w * (len(J) - 2)
            elif kind == 'root':
                if i in miss:
                    val -= w
            elif kind == 'single':
                if len(J) == 2 and i in miss and all(p > 0 for p in ps):
                    val += w
            elif kind == 'cap':
                if i in miss and miss[i] <= L:
                    val += w
            elif kind == 'miss':
                if i in miss and miss[i] < L:
                    val += w * (L - miss[i])
        assert val >= 0, ('negative coefficient', r, b, k, box, J, ps, val)
        counter['types'] += 1
    counter['leaves'] += 1


def check_node(r, b, k, node, counter, box=None):
    if 'box' in node:
        assert box is None
        t, u = node['box']
        assert t > 0 and u > 0
        counter['splits'] += 1
        check_node(r, b, k, node['absent'], counter, (t, u, False))
        check_node(r, b, k, node['present'], counter, (t, u, True))
    else:
        check_leaf(r, b, k, node['weights'], box, counter)


def main():
    here = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent
    profs = all_profiles()
    assert len(profs) == 109
    for b, k in profs:
        assert threshold_excluded(28, b, k), (b, k)
    print('order 28: all 109 profiles excluded by the threshold test')
    data = json.loads((here / 'four-row-certificates.json').read_text())
    counter = {'types': 0, 'leaves': 0, 'splits': 0, 'threshold': 0, 'certified': 0}
    per_order = {}
    used = set()
    for r in range(17, 28):
        for b, k in profs:
            if threshold_excluded(r, b, k):
                counter['threshold'] += 1
                continue
            key = '%d/%s/%d' % (r, ''.join(map(str, b)), k)
            assert key in data, ('no certificate', key)
            check_node(r, b, k, data[key], counter)
            used.add(key)
            counter['certified'] += 1
            per_order[r] = per_order.get(r, 0) + 1
    assert used == set(data)
    print('orders 17..27:', counter)
    print('certified per order:', per_order)
    if '--below' in sys.argv:
        for r in range(11, 17):
            alive = [(b, k) for b, k in profs if not threshold_excluded(r, b, k)]
            print('order', r, 'profiles not excluded by the threshold test:', len(alive))


if __name__ == '__main__':
    main()
