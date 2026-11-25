"""Replay the four-row descent certificates using integer arithmetic (Python 3.10+)."""

import argparse
import json
from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
from math import comb, prod
from pathlib import Path

from verify_four_rows import inequality as original_inequality
from verify_four_rows import possible_misses, threshold_exclusion, turan_floor

ROWS = range(4)
PAIRS = tuple(combinations(ROWS, 2))
DATA = Path(__file__).with_name("four-row-descent-certificates.json")


def members(mask):
    return tuple(i for i in ROWS if mask & (1 << i))


def profiles():
    for b in combinations_with_replacement(range(9), 4):
        for k in range(sum(b), 9):
            yield b, k


@lru_cache(maxsize=None)
def budgets(r, k):
    choices = []
    for m in range(5):
        h = r if m <= 2 else r - m
        for surplus in range((r - 1) * m, (8 * r - h * k) // 2 + 1):
            x = 8 * r - 2 * surplus
            deficient = surplus // 3
            if m < 3:
                deficient = min(deficient, (surplus - (r - 1) * m) // (3 - m))
            q = min(2 + deficient, x - (h - 1) * k)
            if q >= 0:
                choices.append((surplus, x, q))
    return choices


@dataclass(frozen=True)
class Sender:
    p: tuple
    mask: int
    hits: tuple
    cost: int

    def uses(self, i):
        return (self.mask >> i) & 1


@dataclass(frozen=True)
class Context:
    r: int
    b: tuple
    k: int
    surplus: int
    x: int
    q: int
    floor: int
    sizes: tuple
    senders: tuple

    @property
    def exterior(self):
        return 4 + sum(self.b)

    @property
    def tight_pair(self):
        return int(2 * self.q < self.r - 4)

    @property
    def rare(self):
        return 2 if self.surplus >= 6 else 0


@lru_cache(maxsize=8192)
def legal_lists(r, shape, q, floor):
    sizes = tuple(r - 1 - b for b in shape)
    mu = 1 + 2 * q - int(2 * q < r - 4)
    result = []
    for p in possible_misses(r, shape, q, floor, None):
        if any(miss and size - miss > mu for miss, size in zip(p, sizes)):
            continue
        if len(p) == 2:
            valid = True
            for i, j in ((0, 1), (1, 0)):
                need = shape[i] + 1
                h = sizes[i] - p[i]
                if p[j] >= need and need * h < floor:
                    valid = False
                if p[j] >= need - 1 and p[i] + (need - 1) * (h + 1) < floor:
                    valid = False
                if p[j] * h < (r - 1) * (p[j] - need):
                    valid = False
            if not valid:
                continue
        result.append(p)
    return tuple(result)


@lru_cache(maxsize=12)
def context(r, b, k, lo, hi):
    choices = [(s, x, q) for s, x, q in budgets(r, k) if lo <= s <= hi]
    if not choices:
        return None
    surplus, x, q = map(max, zip(*choices))
    if k == 8 or surplus < 4:
        q = min(q, 2)
    elif surplus < 6:
        q = min(q, 3)
    if r >= 14 and q <= 2:
        return None  # Lyle's nonjoin bound and the two-row theorem.
    floor = max(j * (r // 4) + min(j, r % 4) - comb(j + 1, 2) for j in range(1, 5))
    if r > 4 * (1 + surplus // 3):
        floor = max(floor, r - 7)
    sizes = tuple(r - 1 - bi for bi in b)
    senders = []
    for mask in range(1, 16):
        rows = members(mask)
        if not 2 <= len(rows) <= 2 + k - sum(b):
            continue
        for misses in legal_lists(r, tuple(b[i] for i in rows), q, floor):
            p = [r] * 4
            for i, v in zip(rows, misses):
                p[i] = v
            hits = tuple(max(0, size - v) for size, v in zip(sizes, p))
            partial = [hits[i] - 1 - q for i in rows if p[i] > 0]
            cost = 2 if k == 8 else max(0, sum(hits) - r, *partial)
            senders.append(Sender(tuple(p), mask, hits, cost))
    return Context(r, b, k, surplus, x, q, floor, sizes, tuple(senders))


def row_floor(c, i, z):
    off = c.b[i] + 1
    return c.floor if z == off else max(0, (c.r - 1) * (z - off))


def positive_budget(c, q0):
    z = min(4 * c.r * max(0, c.q - q0), 3 * max(0, c.surplus - 3))
    if q0 == 3 and c.surplus <= 8:
        z = min(z, c.rare)
    return z


def clique_cap(c, n):
    other = c.floor if n == c.r else (c.r - 1) * turan_floor(n, c.r)
    return comb(n, 2) - other


def ceildiv(a, b):
    return -((-a) // b)


def subset_loads(c, rows, g):
    size = sum(c.sizes[i] for i in rows)
    base = sum(comb(c.sizes[i], 2) for i in rows)
    cap = [clique_cap(c, size + z) - base - turan_floor(z, g)
           for z in range(c.exterior + 1)]
    if len(rows) == 1:
        i = rows[0]
        s = c.sizes[i]
        for z in range(2, len(cap)):
            f = row_floor(c, i, z)
            misses = ceildiv((s - 1) * f - z * (z - 1) * c.q, s + z - 2)
            for q0 in {2, 3, c.q}:
                a = s - 1 + c.tight_pair - 2 * q0
                if q0 > c.q or a <= 0:
                    continue
                # A conservative bound on the excess over q0.
                extra = 0 if q0 == c.q else 3 * max(0, c.surplus - 3)
                if q0 == 3 and c.surplus <= 8:
                    extra = min(extra, c.rare)
                misses = max(misses, ceildiv(a * f - (z - 1) * extra, a + z - 1))
            cap[z] = min(cap[z], z * s - misses)
    for z in range(2, len(cap)):
        cap[z] = min(cap[z], *(z * cap[t] // t for t in range(1, z)))
    return cap


def small_cap(c, i, g, t):
    a = c.sizes[i] - 2 * t - 1 + c.tight_pair
    for z in range(1, c.exterior + 1):
        edges = comb(z, 2) - turan_floor(z, g)
        if a > 2 * c.q:
            edges = 0
        if c.surplus <= 8:
            h = min(z, c.rare)
            if a > 6:
                edges = min(edges, comb(z, 2) - comb(z - h, 2))
            if a > c.q + 3:
                edges = min(edges, comb(h, 2))
        if z * t + edges < row_floor(c, i, z):
            return z - 1
    return c.exterior


@dataclass
class Inequality:
    rhs: int
    coefficient: Callable[[Sender], int]
    aux: tuple


def inequalities(c):
    """Columns are exterior types, followed by six inter-row cuts and four excess sums."""
    table = {}
    zero = (0,) * 10
    def add(name, rhs, term=lambda y: 0, aux=zero):
        assert name not in table and len(aux) == 10
        table[name] = Inequality(rhs, term, tuple(aux))
    def vector(edges=None, degrees=None):
        edges = edges or {}
        degrees = degrees or {}
        return tuple(edges.get(ij, 0) for ij in PAIRS) + tuple(degrees.get(i, 0) for i in ROWS)
    r, b, q, p = c.r, c.b, c.q, c.exterior
    add('count+', p, lambda y: 1)
    add('count-', -p, lambda y: -1)
    sig = c.k - sum(b)
    add('arity+', sig, lambda y: y.mask.bit_count() - 2)
    add('arity-', -sig, lambda y: 2 - y.mask.bit_count())
    for i, s in enumerate(c.sizes):
        add(('root-', i), -b[i] - 2 - 2 * (c.k == 8), lambda y, i=i: -y.uses(i))
        cap = 2 if c.k == 8 or b[i] == 0 else q
        add(('root+', i), b[i] + 2 + cap, lambda y, i=i: y.uses(i))
        add(('rootbudget', i), s * (b[i] + 2), lambda y, i=i, s=s: s * y.uses(i),
            vector(degrees={i: -1}))
        add(('rowmax', i), s * (min(q, 2) if b[i] == 0 else q), aux=vector(degrees={i: 1}))
        add(('edgeuse', i), s * (b[i] + 2), lambda y, i=i: y.hits[i],
            vector({ij: 1 for ij in PAIRS if i in ij}, {i: -1}))
        if s > 1 + 2 * q - c.tight_pair:
            add(('complete', i), b[i], lambda y, i=i: int(y.p[i] == 0))
        if c.floor > 3 or r >= 14:
            add(('singleton', i), 1, lambda y, i=i: int(b[i] == 0 and y.uses(i)
                 and y.mask.bit_count() == 2 and 0 not in y.p))
        if c.surplus <= 8:
            if s > c.rare:
                add(('rare root', i), b[i] + 5, lambda y, i=i: y.uses(i))
            if s > 6 and c.tight_pair:
                add(('rare complete', i), b[i] + c.rare, lambda y, i=i: int(y.p[i] == 0))
    add('total', c.x, lambda y: y.cost, vector(degrees=dict.fromkeys(ROWS, 1)))
    for q0 in (2, 3):
        for mask in range(16):
            rows = members(mask)
            add(('positive', q0, mask), positive_budget(c, q0) + q0 * sum(c.sizes[i] for i in rows),
                lambda y, q0=q0: max(0, y.cost - q0), vector(degrees=dict.fromkeys(rows, 1)))
    for i in ROWS:
        if b[i] != 0:
            continue
        for mask in range(1, 16):
            rows = members(mask)
            edges = {tuple(sorted((i, j))): 1 for j in rows if j != i}
            add(('palette', i, mask), (r - 1) * len(rows),
                lambda y, i=i, mask=mask: y.hits[i] if y.mask & ~mask == 0 else 0, vector(edges))
    for i, j in PAIRS:
        mask = (1 << i) | (1 << j)
        bound = 1 + b[i] + b[j] - c.tight_pair
        add(('pairnum', i, j), bound, lambda y, mask=mask: int(y.mask == mask))
        add(('paircap', i, j), r - 1 + b[i] * b[j], aux=vector({(i, j): 1}))
        add(('pairroot', i, j), -3 - b[i] - b[j], lambda y, mask=mask: -int(bool(y.mask & mask)))
        if bound:
            add(('rectcost', i, j), 0, lambda y, i=i, j=j, mask=mask:
                y.p[i] * y.p[j] if y.mask == mask else 0, vector({(i, j): -bound}))
    for mask in range(1, 16):
        rows = members(mask)
        size = sum(c.sizes[i] for i in rows)
        base = sum(comb(c.sizes[i], 2) for i in rows)
        def load(y, rows=rows):
            return sum(y.hits[i] for i in rows)
        add(('all', mask), clique_cap(c, size + p) - base - turan_floor(p, 4), load,
            vector(dict.fromkeys(combinations(rows, 2), 1)))
        if not c.senders:
            continue
        lo = min(map(load, c.senders))
        maxima = {}
        for y in c.senders:
            maxima[y.mask] = max(maxima.get(y.mask, 0), load(y))
        for pool in range(1, 16):
            if mask & ~pool or pool.bit_count() < 2 or (len(rows) > 1 and pool != 15):
                continue
            relevant = [v for hit, v in maxima.items() if hit & ~pool == 0]
            if not relevant:
                continue
            caps = subset_loads(c, rows, pool.bit_count())
            for threshold in range(lo, max(relevant)):
                bound = max(cap - z * threshold for z, cap in enumerate(caps))
                add(('load', mask, pool, threshold), bound,
                    lambda y, pool=pool, load=load, t=threshold: max(0, load(y) - t) if y.mask & ~pool == 0 else 0)
            if len(rows) == 1:
                i = rows[0]
                for t in range(c.sizes[i]):
                    bound = small_cap(c, i, pool.bit_count(), t)
                    if bound < p:
                        add(('small', mask, pool, t), bound,
                            lambda y, i=i, pool=pool, t=t: int(y.mask & ~pool == 0 and y.p[i] <= t))
    return table


@lru_cache(maxsize=8)
def base_rows(r, b, k, lo, hi):
    c = context(r, b, k, lo, hi)
    return inequalities(c) if c and c.senders else {}


def regular_coverage(r, b, y):
    rows = members(y.mask)
    if any(y.p[i] == 0 for i in rows):
        return True
    area = prod(y.p[i] for i in rows)
    covered = 0
    caps = []
    for i, j in combinations(rows, 2):
        pair = y.p[i] * y.p[j]
        cap = min(pair, 4 * min(y.p[i], y.p[j]), b[i] * b[j] + min(r - 1, y.p[i] + y.p[j]))
        caps.append(cap)
        covered += cap * (area // pair)
    if len(rows) == 4:
        covered -= sum(caps[i] * caps[5 - i] for i in range(3))
    return covered >= area


def allowed_by_cuts(y, b, cuts):
    for (i, j), (lo, hi) in cuts.items():
        if y.uses(i) and y.uses(j):
            if y.p[i] + y.p[j] + b[i] * b[j] < lo:
                return False
            if y.mask.bit_count() == 2 and y.p[i] * y.p[j] > hi:
                return False
    return True


def signature(name, y):
    if name[0] == 'root':
        return y.uses(name[1])
    if name[0] == 'mask':
        return int(y.mask == name[1])
    assert name[0] == 'type'
    return int(y.p == name[1:])


def check_witness(r, b, k, data, stats):
    assert set(data) == {'surplus', 'witness'}
    s = data['surplus']
    assert type(s) is int
    c = context(r, b, k, s, s)
    assert c and c.senders
    w = data['witness']
    den = w['den']
    assert type(den) is int and den > 0
    aux = tuple(w['edges']) + tuple(w['degree'])
    assert len(w['edges']) == 6 and len(w['degree']) == 4
    assert all(type(v) is int and v >= 0 for v in aux)
    lookup = {y.p: y for y in c.senders}
    counts = {}
    for p, count in w['types']:
        y = lookup[tuple(p)]
        assert y not in counts and type(count) is int and count > 0
        counts[y] = count
        assert k != 8 or regular_coverage(r, b, y)
        for edge, (i, j) in zip(w['edges'], PAIRS):
            if y.uses(i) and y.uses(j):
                upper = min(r - 1, y.p[i] + y.p[j]) + b[i] * b[j]
                assert edge <= den * upper
                if y.mask.bit_count() == 2:
                    assert den * y.p[i] * y.p[j] <= edge
    for name, row in base_rows(r, b, k, s, s).items():
        lhs = sum(v * row.coefficient(y) for y, v in counts.items())
        lhs += sum(v * a for v, a in zip(aux, row.aux))
        assert lhs <= row.rhs * den, (r, b, k, name, lhs, row.rhs * den)
    stats['survivors'] += 1
    stats['integral witnesses'] += den == 1
    stats['common-cut witnesses'] += 1


def check_leaf(c, table, proof, cuts, branches, stats):
    assert set(proof) == {'weights'}
    terms = proof['weights']
    assert terms and all(type(m) is int and m > 0 for _, m in terms)
    stats['leaves'] += 1
    if c is None or not c.senders:
        assert terms == [['count-', 1]]
        return
    terms_checked = []
    for name, multiplier in terms:
        name = tuple(name) if isinstance(name, list) else name
        if isinstance(name, tuple) and name[0] in ('cut+', 'cut-'):
            pair = name[1:]
            lo, hi = cuts[pair]
            sign = 1 if name[0] == 'cut+' else -1
            aux = tuple(sign * int(ij == pair) for ij in PAIRS) + (0,) * 4
            row = Inequality(hi if sign == 1 else -lo, lambda y: 0, aux)
        elif isinstance(name, tuple) and name[0] == 'branch':
            sig, sign, n = name[1:-2], name[-2], name[-1]
            assert (sig, sign, n) in branches
            row = Inequality(sign * n, lambda y, sig=sig, sign=sign: sign * signature(sig, y), (0,) * 10)
        else:
            row = table[name]
        terms_checked.append((multiplier, row))
    assert sum(m * row.rhs for m, row in terms_checked) < 0
    for col in range(10):
        assert sum(m * row.aux[col] for m, row in terms_checked) >= 0
    for y in c.senders:
        if allowed_by_cuts(y, c.b, cuts) and (c.k != 8 or regular_coverage(c.r, c.b, y)):
            assert sum(m * row.coefficient(y) for m, row in terms_checked) >= 0, (c.r, c.b, c.k, y)
            stats['columns'] += 1


def verify_tree(r, b, k, lo, hi, node, cuts, branches, stats):
    if 'weights' in node:
        check_leaf(context(r, b, k, lo, hi), base_rows(r, b, k, lo, hi),
                   node, cuts, branches, stats)
        return
    if 'surplus_split' in node:
        assert not cuts and not branches
        mid = node['surplus_split']
        assert type(mid) is int and lo <= mid < hi
        verify_tree(r, b, k, lo, mid, node['low'], cuts, branches, stats)
        verify_tree(r, b, k, mid + 1, hi, node['high'], cuts, branches, stats)
    elif 'cut' in node:
        i, j, t = node['cut']
        assert (i, j) in PAIRS and type(t) is int
        a, z = cuts.get((i, j), (0, r - 1 + b[i] * b[j]))
        assert a <= t < z
        for child, bounds in [('low', (a, t)), ('high', (t + 1, z))]:
            verify_tree(r, b, k, lo, hi, node[child], {**cuts, (i, j): bounds}, branches, stats)
    else:
        sig, t = node['integer']
        sig = tuple(sig)
        assert type(t) is int
        assert ((len(sig) == 2 and sig[0] == 'root' and sig[1] in ROWS) or
                (len(sig) == 2 and sig[0] == 'mask' and sig[1] in range(16)) or
                (len(sig) == 5 and sig[0] == 'type' and all(type(v) is int for v in sig[1:])))
        for child, sign, n in [('low', 1, t), ('high', -1, t + 1)]:
            verify_tree(r, b, k, lo, hi, node[child], cuts, branches + ((sig, sign, n),), stats)


def replay_original_16(data):
    expected = set()
    survivors = []
    for b, k in profiles():
        if k == 8 or threshold_exclusion(16, b, k):
            continue
        key = ''.join(map(str, b)) + '/' + str(k)
        expected.add(key)
        proof = data[key]
        p = 4 + sum(b)
        sigma = k - sum(b)
        s = (8 - k) * 8
        q = max(min(2 + t // 3, (8 - k) * 16 + k - 2 * t) for t in range(s + 1))
        floor = 9 if 16 > 4 * (1 + s // 3) else 6
        types = set()
        for mask in range(1, 16):
            rows = members(mask)
            if not 2 <= len(rows) <= 2 + sigma:
                continue
            for misses in possible_misses(16, tuple(b[i] for i in rows), q, floor, None):
                y = [16] * 4
                for i, v in zip(rows, misses):
                    y[i] = v
                types.add((tuple(y), len(rows)))
        table = {'count+': (p, lambda y, j: 1), 'arity-': (-sigma, lambda y, j: 2 - j)}
        for name in ['count-', 'arity+']:
            table[name] = original_inequality(16, b, k, floor, name)
        for i in ROWS:
            labels = [['root', i]]
            if b[i] == 0:
                labels.append(['long singleton', i])
            for t in range(16 - b[i]):
                labels.extend([['cap', i, t], ['miss', i, t]])
            for label in labels:
                table[tuple(label)] = original_inequality(16, b, k, floor, label)
        if 'weights' in proof:
            weighted = [(n, table[tuple(label) if isinstance(label, list) else label])
                        for label, n in proof['weights']]
            assert weighted and all(type(n) is int and n > 0 for n, _ in weighted)
            assert sum(n * rhs for n, (rhs, _) in weighted) < 0
            assert all(sum(n * co(y, j) for n, (_, co) in weighted) >= 0 for y, j in types)
        else:
            den = proof['den']
            assert type(den) is int and den > 0
            support = [(tuple(y), sum(t < 16 for t in y), n) for y, n in proof['types']]
            assert all((y, j) in types and type(n) is int and n > 0 for y, j, n in support)
            for rhs, coefficient in table.values():
                assert sum(n * coefficient(y, j) for y, j, n in support) <= den * rhs
            survivors.append(key)
    assert set(data) == expected and len(expected) == 65 and len(survivors) == 12
    print('r=16 original unbranched inequalities: ' + ', '.join(survivors), flush=True)


def replay_regular_13(certificates):
    # These are the profiles before applying the incidence argument in Section 5.
    possible = {'0008/8', '0044/8'}
    keys = set()
    stats = Counter()
    for b, k in profiles():
        if k != 8:
            continue
        key = ''.join(map(str, b)) + '/8'
        if key in possible:
            assert sum(b) == 8 and all(t == 0 or t >= 3 for t in b)
            continue
        keys.add(key)
        verify_tree(13, b, k, 0, 0, certificates[key], {}, (), stats)
    assert len(keys) == 51 and set(certificates) == keys
    assert 2 * 12 - 16 > 4 and 52 % 12 == 4
    print(f'r=13 regular case: {len(keys)} excluded by counts; both remaining profiles excluded jointly by rerooting.', flush=True)


def replay(order, data, list_profiles=False):
    stats = Counter()
    expected = set()
    groups = Counter()
    surviving_keys = []
    for b, k in profiles():
        key = ''.join(map(str, b)) + '/' + str(k)
        if k == 8 and order >= 13:
            stats['degree theorem' if order >= 14 else 'regular theorem'] += 1
            continue
        if threshold_exclusion(order, b, k):
            stats['threshold'] += 1
            continue
        expected.add(key)
        proof = data[key]
        if 'witness' in proof:
            check_witness(order, b, k, proof, stats)
            groups[k] += 1
            surviving_keys.append(key)
        else:
            limits = [s for s, x, q in budgets(order, k)]
            verify_tree(order, b, k, min(limits), max(limits), proof, {}, (), stats)
            stats['certificate exclusions'] += 1
    assert set(data) == expected, (order, set(data) ^ expected)
    assert stats['degree theorem'] + stats['regular theorem'] + stats['threshold'] + stats['certificate exclusions'] + stats['survivors'] == 162
    if order >= 15:
        assert stats['survivors'] == 0
    print(f'r={order}: {dict(stats)}, survivors by k {dict(sorted(groups.items()))}', flush=True)
    if list_profiles:
        print(' '.join(surviving_keys) or 'No surviving profiles.', flush=True)


def check_arithmetic():
    floor = [max(j * (r // 4) + min(j, r % 4) - comb(j + 1, 2) for j in range(1, 5))
             for r in range(10, 17)]
    assert floor == [3, 3, 3, 4, 5, 6, 6]
    for r, expected in [(14, Fraction(40, 3)), (15, 15), (16, Fraction(50, 3))]:
        n, degree = 4 * r, 3 * (r - 1)
        assert 16 * degree > 11 * n
        bound = min(3 * (3 * degree - 2 * n),
                    Fraction(40 * degree - 25 * n, 12), Fraction(2 * (2 * degree - n), 3))
        assert bound == expected and bound > r - 1
    assert 15 * 19 - 15 * 17 == 2 * 15
    assert set(s for s, x, q in budgets(13, 8)) == {0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('orders', nargs='*', type=int)
    parser.add_argument('--data', type=Path, default=DATA)
    parser.add_argument('--list', action='store_true', help='Print every surviving profile at each order.')
    args = parser.parse_args()
    assert __debug__, 'Run without -O so every certificate assertion executes.'
    check_arithmetic()
    data = json.loads(args.data.read_text())
    for order in args.orders or range(10, 17):
        if order == 16:
            replay_original_16(data['original16'])
        if order == 13:
            replay_regular_13(data['regular13'])
        replay(order, data[str(order)], args.list)


if __name__ == '__main__':
    main()
