"""Exact replay for four-rows.md. Run with Python 3.10+ and its standard library."""

import json
from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement, product
from math import comb, prod
from pathlib import Path

from verify_extra_vertex import turan_floor


def profiles():
    for b in combinations_with_replacement(range(8), 4):
        for k in range(sum(b), 8):
            yield b, k


def row_floor(r, b, z, f):
    """Required nontarget edges on a row of size r-1-b and z exterior points."""
    if z == b + 1:
        return f
    return max(0, (r - 1) * (z - b - 1))


@cache
def row_cap(r, b, total, threshold):
    if threshold < 0:
        return 0
    for z in range(1, total + 1):
        available = z * threshold + comb(z, 2) - turan_floor(z, 4)
        if available < row_floor(r, b, z, r - 10):
            return z - 1
    return total


@cache
def thresholds(r, b, total):
    best = {}
    for threshold in range(-1, r - 1 - b):
        cap = row_cap(r, b, total, threshold)
        if cap < total:
            best[cap] = threshold
    return tuple(best.items())


def blocks_transversal(shape, misses, r=None):
    """Necessary coverage inequality. r=None uses only the order-independent cut."""
    if 0 in misses:
        return True
    total = prod(misses)
    bounds = []
    covered = 0
    for i, j in combinations(range(len(misses)), 2):
        area = misses[i] * misses[j]
        cut = misses[i] + misses[j]
        if r is not None:
            cut = min(cut, r - 1)
        upper = min(area, cut + shape[i] * shape[j])
        bounds.append(upper)
        covered += upper * (total // area)
    if r is not None and len(misses) == 4:
        # In lexicographic pair order, opposite pairs have indices summing to 5.
        covered -= sum(bounds[i] * bounds[5 - i] for i in range(3))
    return covered >= total


def threshold_exclusion(r, b, k):
    """Each witness found at r also excludes the same profile at every larger order."""
    exterior = 4 + sum(b)
    excess = k - sum(b)
    for choice in product(*(thresholds(r, d, exterior) for d in b)):
        unmarked = exterior - sum(cap for cap, _ in choice)
        if unmarked <= 0:
            continue
        max_roots = min(4, 2 + excess // unmarked)
        floors = [threshold + 1 for _, threshold in choice]
        possible = False
        for size in range(2, max_roots + 1):
            for rows in combinations(range(4), size):
                shape = tuple(b[i] for i in rows)
                misses = tuple(floors[i] for i in rows)
                if blocks_transversal(shape, misses):
                    possible = True
                    break
            if possible:
                break
        if not possible:
            return True
    return False


@cache
def budgets(r, k):
    """Finite branches have k>=5, hence a partition into independent quartets."""
    assert k >= 5 and (2 * r + 6) < 5 * (r - 4)
    max_surplus = (8 - k) * r // 2
    max_q = max(min(2 + s // 3, (8 - k) * r + k - 2 * s)
                for s in range(max_surplus + 1))
    f = r - 7 if r > 4 * (1 + max_surplus // 3) else r - 10
    return max_q, f


@cache
def miss_cost(r, b, exterior, f, threshold):
    minimum = [0]
    for z in range(1, exterior + 1):
        needed = row_floor(r, b, z, f) - comb(z, 2) + turan_floor(z, 4)
        from_subsets = [(z * minimum[u] + u - 1) // u for u in range(1, z)]
        minimum.append(max([0, needed] + from_subsets))
    return max(z * threshold - value for z, value in enumerate(minimum))


def possible_double(r, shape, misses, max_q, f, box):
    a, b = shape
    p, q = misses
    if p + q > r - 1:
        return False
    if p and q:
        if p + q == r - 1 and min(p, q) < f:
            return False
        if q > max_q + a + 2 or p > max_q + b + 2:
            return False
        if 2 * f > r - 1 and (a == 0 or b == 0):
            return False
    if box:
        t, u, present = box
        if present:
            union = t * u + p * q - min(t, p) * min(u, q)
            if union > min(r - 1, p + q) + a * b:
                return False
        elif p >= t and q >= u:
            return False
    return True


@cache
def possible_misses(r, shape, max_q, f, box):
    sizes = tuple(r - 1 - b for b in shape)
    ranges = [range(f if b == 0 else 0, s) for b, s in zip(shape, sizes)]
    min_total = sum(sizes) - r - max_q
    result = []
    for misses in product(*ranges):
        if sum(misses) < min_total:
            continue
        if len(shape) == 2 and not possible_double(r, shape, misses, max_q, f, box):
            continue
        if blocks_transversal(shape, misses, r):
            result.append(misses)
    return tuple(result)


def inequality(r, b, k, f, label):
    """Return the right side and a function evaluating one exterior vertex."""
    exterior = 4 + sum(b)
    if label == 'count-':
        return -exterior, lambda p, j: -1
    if label == 'arity+':
        return k - sum(b), lambda p, j: j - 2
    assert isinstance(label, list) and len(label) in (2, 3)
    tag, i = label[:2]
    assert type(i) is int and 0 <= i < 4
    if tag == 'root' and len(label) == 2:
        return -b[i] - 2, lambda p, j: -int(p[i] < r)
    if tag == 'long singleton' and len(label) == 2:
        assert b[i] == 0 and r >= 14
        return 1, lambda p, j: int(j == 2 and p[i] < r and 0 not in p)
    assert len(label) == 3 and type(label[2]) is int
    t = label[2]
    assert 0 <= t <= r - 1 - b[i]
    if tag == 'cap':
        return row_cap(r, b[i], exterior, t), lambda p, j: int(p[i] <= t)
    if tag == 'miss':
        return miss_cost(r, b[i], exterior, f, t), lambda p, j: max(0, t - p[i])
    raise ValueError(f'Unknown certificate inequality {label!r}')


def verify_node(r, b, k, proof, stats, box=None):
    if 'box' in proof:
        assert box is None and set(proof) == {'box', 'absent', 'present'}
        t, u = proof['box']
        assert type(t) is int and type(u) is int and t > 0 and u > 0
        stats['rectangle splits'] += 1
        verify_node(r, b, k, proof['absent'], stats, (t, u, False))
        verify_node(r, b, k, proof['present'], stats, (t, u, True))
        return
    assert set(proof) == {'weights'}
    max_q, f = budgets(r, k)
    rhs = 0
    terms = []
    for label, weight in proof['weights']:
        assert type(weight) is int and weight > 0
        bound, coefficient = inequality(r, b, k, f, label)
        rhs += weight * bound
        terms.append((weight, coefficient))
    assert rhs < 0, (r, b, k, rhs)
    stats['integer certificates'] += 1
    for size in range(2, min(4, 2 + k - sum(b)) + 1):
        for rows in combinations(range(4), size):
            shape = tuple(b[i] for i in rows)
            short_row_box = box if rows == (2, 3) else None
            for misses in possible_misses(r, shape, max_q, f, short_row_box):
                p = [r] * 4  # An unhit root never contributes a positive miss penalty.
                for row, value in zip(rows, misses):
                    p[row] = value
                value = sum(weight * coefficient(p, size) for weight, coefficient in terms)
                assert value >= 0, (r, b, k, box, p, value)
                stats['exterior vertex types checked'] += 1


def check_boundary_coloring():
    """Realize the equality pattern on 19 vertices in the order-16 branch."""
    # Vertices A, B and C have three cyclically indexed members each, D has two.
    # Translating a base matching gives three different colors.
    base = (
        ('A0D0', 'A1D1', 'B0C0'),
        ('B0D0', 'A0B1', 'A1C1'),
        ('B0D1', 'A0B2', 'A1C2'),
        ('C0D0', 'A0B0', 'B1C2'),
        ('C0D1', 'A0C2', 'B2C1'),
    )
    def vertex(group, index, shift):
        index = int(index)
        if group == 'D':
            return 9 + index
        return 3 * 'ABC'.index(group) + (index + shift) % 3

    edges = {}
    for i, matching in enumerate(base):
        for shift in range(3):
            endpoints = set()
            for g, a, h, b in matching:
                u, v = vertex(g, a, shift), vertex(h, b, shift)
                pair = tuple(sorted((u, v)))
                assert u != v and pair not in edges
                assert u not in endpoints and v not in endpoints
                edges[pair] = 1 + 3 * i + shift
                endpoints.update((u, v))
    assert set(edges) == {(u, v) for u, v in combinations(range(11), 2)
                          if u // 3 != v // 3}
    for subset in combinations(range(19), 17):
        colors = {edges.get(pair, 0) for pair in combinations(subset, 2)}
        assert colors == set(range(16))
    assert comb(11, 2) - turan_floor(11, 4) == 45 == 3 * 15 < 3 * 18
    print('Order-16 boundary: all 171 seventeen-sets in the 19-vertex coloring are balanced.')


def verify():
    assert __debug__, 'Run with assertions enabled.'
    cases = list(profiles())
    for b, k in cases:
        assert threshold_exclusion(28, b, k), (b, k)
    print(f'All {len(cases)} sorted row profiles excluded uniformly from order 28.')
    path = Path(__file__).with_name('four-row-certificates.json')
    proofs = json.loads(path.read_text())
    used = set()
    stats = Counter()
    for r in range(17, 28):
        for b, k in cases:
            if threshold_exclusion(r, b, k):
                stats['finite threshold exclusions'] += 1
                continue
            key = f"{r}/" + ''.join(map(str, b)) + f"/{k}"
            verify_node(r, b, k, proofs[key], stats)
            used.add(key)
    assert used == set(proofs)
    print(f'Orders 17 through 27: {len(used)} certified profiles.')
    for name, count in sorted(stats.items()):
        print(f'{name}: {count}')
    check_boundary_coloring()


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run with assertions enabled.')
    verify()
