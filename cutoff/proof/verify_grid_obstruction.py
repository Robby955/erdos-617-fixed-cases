"""Exact finite checks for grid-obstruction.md. Requires only Python 3.10+."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import ceil, comb
from random import Random


def permutation_tests(r: int, exhaustive: bool) -> tuple[int, dict]:
    cells = range(r*r)
    boards = [sum(1 << (i*r+j) for i, j in enumerate(p)) for p in permutations(range(r))]
    through = [sum(1 << i for i, board in enumerate(boards) if board & (1 << x)) for x in cells]
    edges = [(x, y) for x, y in combinations(cells, 2) if x//r != y//r and x%r != y%r]
    all_boards = (1 << len(boards))-1
    minima = {}
    rng = Random(617+r)
    if exhaustive:
        inputs = ((marks, blocked) for blocked in [(), *((e,) for e in edges)]
                  for marks in range(1 << (r*r)))
    else:
        def samples():
            for i in range(350):
                if i % 3 == 0:
                    marks = rng.getrandbits(r*r)
                elif i % 3 == 1:
                    marks = sum(1 << x for x in rng.sample(cells, rng.randint(r-2, r+3)))
                else:
                    marks = (1 << r)-1
                    for x in rng.sample(cells, rng.randrange(5)):
                        marks ^= 1 << x
                yield marks, rng.sample(edges, rng.randrange(2*r+1))
        inputs = samples()

    cases = 0
    for marks, blocked in inputs:
        free = all_boards
        degree = [0]*(r*r)
        for u, v in blocked:
            free &= ~(through[u] & through[v])
            degree[u] += 1
            degree[v] += 1
        without_marks = free
        with_one_mark = 0
        for x in cells:
            if marks & (1 << x):
                with_one_mark = (with_one_mark & ~through[x]) | (without_marks & through[x])
                without_marks &= ~through[x]
        demands = 0
        for x in cells:
            possible = without_marks | (with_one_mark if marks & (1 << x) else 0)
            if possible & through[x]:
                demands |= 1 << x
            else:
                assert (r-1-marks.bit_count())*(r-2) <= degree[x]*(r-2)+len(blocked)
        nmarks = marks.bit_count()
        if without_marks:
            assert demands.bit_count() >= r*r-nmarks-2*len(blocked)
        else:
            assert (demands & marks).bit_count() >= 2*r-nmarks-2*len(blocked)//(r-1)
            if len(blocked) <= r-2:
                assert nmarks >= r
                if nmarks == r:
                    assert demands & marks == marks
        state = nmarks, bool(without_marks)
        minima[state] = min(minima.get(state, r*r), demands.bit_count())
        cases += 1
    return cases, minima


def finite_three_color_case(minima: dict) -> int:
    options = [(marks, clean, count) for (marks, clean), count in minima.items()]
    best = min(sum(x[2] for x in case) for case in product(options, repeat=3)
               if sum(x[0] for x in case) == 9 and any(x[1] for x in case))
    assert best == 10
    return best


def arithmetic() -> None:
    for r in range(5, 121):
        for d in range(max(0, r-3), r+1):
            for m in range(1, d+1):
                holes, outside = r-m, d-m
                nonattacking = max(0, ceil(Fraction(d*(d-2*m+1), 2)))
                lower = max((r-d)*(r-1)+(1-Fraction(d-2, 3*(r-2)))*nonattacking,
                            holes*(r-1-outside))
                # At most r-3 full cliques leaves at least 2-outside defective rows.
                for singles in range(min(holes, 3)+1):
                    for pairs in range(min(max(0, 2-outside), 3-singles)+1):
                        obligations = singles+pairs
                        if not obligations:
                            continue
                        need = singles*(r-1-outside)+pairs*(r-2-outside)
                        numerator = need*(r-3)-2*comb(pairs, 2)*(r-4)
                        lower = max(lower, Fraction(numerator, r-4+obligations))
                assert ceil(lower) >= max(r-1, 2*r-7), (r, d, m, lower)
                if d < r:
                    assert ceil(lower) >= 3*r-12, (r, d, m, lower)

        for threshold, enough in ((r-4, r >= 17), (0, r >= 14)):
            floor_edges = r*comb(r, 2)+r-1
            excluded = min(2*threshold, threshold+2)
            exceptional = (r-1)*(r-2)**2-(r-2)*excluded+threshold
            margin = 2*exceptional+(r-2)*floor_edges-comb(r*r, 2)
            assert (margin > 0) == enough
            if r >= 6 and threshold == r-4:
                assert 2*margin == r**3-19*r*r+46*r-44
    for mask in range(16):
        crossing = [(i, j) for i, j in product(range(2), repeat=2) if mask & (1 << (2*i+j))]
        endpoints = len({i for i, _ in crossing})+len({j for _, j in crossing})
        assert endpoints <= len(crossing)+2
    for deviations in product(range(-3, 4), repeat=5):
        if sum(deviations):
            continue
        overshoot = sum(max(0, s) for s in deviations)
        added = sum(comb(5+s, 2)-comb(5, 2) for s in deviations if s > 0)
        assert 2*added-sum(s*s for s in deviations) <= 2*(5-1)*overshoot


def switch_one_edge(r: int) -> tuple[int, int]:
    cells = range(r*r)
    def color(v, w):
        y, x = divmod(v, r)
        yy, xx = divmod(w, r)
        if {v, w} == {0, 1}:
            return 1
        if x != xx:
            return ((yy-y)*pow((xx-x) % r, -1, r)) % r
        return int((x in (0, 1)) != (y == 0 or yy == 0))

    # Precompute exact labels for each pair. Check all old (r+1)-sets.
    labels = {(i, j): color(i, j) for i, j in combinations(cells, 2)}
    all_hues = set(range(r))
    for vertices in combinations(cells, r+1):
        assert {labels[e] for e in combinations(vertices, 2)} == all_hues
    edges = [p for p, a in labels.items() if a == 1]
    rows = [(v//r-v%r) % r for v in cells]
    cost = sum(rows[v] != rows[w] and v%r != w%r for v, w in edges)
    assert cost == 1
    if r == 3:
        # Any zero-cost placement preserves all slope-one full cliques as parallel lines.
        # Try every perpendicular ordering of these rows, fixing the first by symmetry.
        cols = list(permutations(range(r)))
        best = r*r
        for tail in product(cols, repeat=r-1):
            arrangement = [tuple(range(r)), *tail]
            count = sum(rows[v] != rows[w] and arrangement[rows[v]][v%r] != arrangement[rows[w]][w%r]
                        for v, w in edges)
            best = min(best, count)
        assert best == 1
    return comb(r*r, r+1), cost


def slope_lines(r: int) -> list:
    """Points on every finite-slope line for prime orders and the field of order 16."""
    def times16(a: int, b: int) -> int:
        value = 0
        while b:
            if b & 1:
                value ^= a
            b >>= 1
            a <<= 1
            if a & 16:
                a ^= 0b10011  # Reduce modulo x^4 + x + 1.
        return value

    if r == 16:
        return [[[(times16(a, x) ^ i)*r+x for x in range(r)] for i in range(r)] for a in range(r)]
    return [[[((a*x+i) % r)*r+x for x in range(r)] for i in range(r)] for a in range(r)]


def build_coloring(r: int, k: int, lines: list) -> list[bytearray]:
    """Point indices encode horizontal row first and vertical column second."""
    z = r*r
    label = [bytearray([255])*(z+1) for _ in range(z+1)]
    for a, parallel_class in enumerate(lines):
        for line in parallel_class:
            for v, w in combinations(line, 2):
                assert label[v][w] == 255
                label[v][w] = label[w][v] = a
    vertical = 0
    for x in range(r):
        for y, yy in combinations(range(r), 2):
            v, w = y*r+x, yy*r+x
            assert label[v][w] == 255
            if x < 2 and yy < k and yy-y in (1, k-1):
                a = 0
            else:
                a = 1+vertical % (r-1)
                vertical += 1
            label[v][w] = label[w][v] = a
    other = 0
    for v in range(z):
        y, x = divmod(v, r)
        if y < k and x >= 2:
            a = 0
        else:
            a = 1+other % (r-1)
            other += 1
        label[v][z] = label[z][v] = a
    return label


def verify_construction(r: int, k: int) -> tuple[int, int, int]:
    z = r*r
    lines = slope_lines(r)
    label = build_coloring(r, k, lines)
    counts = Counter(label[v][w] for v, w in combinations(range(z+1), 2))
    assert len(counts) == r and counts[0] == r*comb(r, 2)+k*r
    assert counts[0] < min(counts[a] for a in range(1, r))
    assert label[z].count(0) == k*(r-2)
    for a in range(r):
        for line in lines[a]:
            assert all(label[u][v] == a for u, v in combinations(line, 2))

    def check_sole_target(vertices, expected):
        assert len(set(vertices)) == len(vertices) == r+1
        actual = [tuple(sorted((u, v))) for u, v in combinations(vertices, 2) if label[u][v] == 0]
        assert actual == [tuple(sorted(expected))]

    certified = 0
    for row in range(r):
        for l, h in combinations(range(r), 2):
            pair = row*r+l, row*r+h
            verts = [*pair, *(i*r+2 for i in range(r) if i != row)]
            check_sole_target(verts, pair)
            certified += 1
    for i in range(k):
        j = (i+1) % k
        for col in (0, 1):
            pair = i*r+col, j*r+col
            verts = [z, *((j+h)%k*r+(col ^ (h % 2)) for h in range(k)),
                     *(y*r+2 for y in range(k, r))]
            check_sole_target(verts, pair)
            certified += 1
        for col in range(2, r):
            v = i*r+col
            path = [((i+h+1)%k)*r+h%2 for h in range(k-1)]
            check_sole_target([z, v, *path, *(y*r+2 for y in range(k, r))], (z, v))
            certified += 1
    assert certified == counts[0]

    natural_costs = []
    for y in range(z):
        row, col = divmod(y, r)
        degree = label[y].count(0)
        assert degree == (r+1 if row < k and col < 2 else r if row < k else r-1)
        if degree <= r:
            natural_costs.append(sum(label[z][u] == 0 and u//r != row and u%r != col
                                     for u in range(z)))
    minimum = (k-1)*(r-3)
    assert min(natural_costs) == minimum
    assert k*(r-2)-1-2*(r-1)+r-3 >= minimum

    demands = 0
    for b in range(1, r):
        assert label[z].count(b) <= r-2
        through = {point: i for i, line in enumerate(lines[b]) for point in line}
        for fixed in range(z):
            col = fixed % r
            intercept = through[fixed]
            rows = [i for i in range(r) if i != intercept]
            cols = [j for j in range(r) if j != col]
            for shift in range(r-1):
                reps = [fixed]
                for index, i in enumerate(rows):
                    x = cols[(index+shift) % (r-1)]
                    v = lines[b][i][x]
                    if label[z][v] == b:
                        break
                    reps.append(v)
                if len(reps) == r:
                    assert all(label[u][v] != b for u, v in combinations(reps, 2))
                    demands += 1
                    break
            else:
                raise AssertionError((r, k, b, fixed))
    assert demands == (r-1)*r*r
    return minimum, certified, demands


def common_neighbor_test() -> int:
    tested = 0
    for r in (3, 4):
        points = range(4)
        edges = list(combinations(points, 2))
        for coloring in product(range(r), repeat=len(edges)):
            labels = dict(zip(edges, coloring))
            demanding = {a for a in range(1, r)
                         if any(all(labels[e] != a for e in combinations(s, 2))
                                for s in combinations(points, r-1))}
            if len(demanding) > 1:
                continue
            c = next(iter(demanding), 1)
            for weights in ((1, 1, 1, 1), (1, 2, 3, 4), (3, 0, 2, 1)):
                norm = sum(w*w for w in weights)
                target = sum(2*weights[i]*weights[j] for (i, j), a in labels.items() if a == 0)
                added = sum(2*weights[i]*weights[j] for (i, j), a in labels.items() if a == c)
                assert target+added <= (r-3)*norm
                if not demanding:
                    assert (r-2)*target+sum(weights)**2 <= (r-2)**2*norm
                tested += 1
    assert tested
    return tested


def overlapping_witnesses() -> int:
    # In the target graph replace each point of a 5-cycle by a clique of size b.
    # The target independence number is two and every target clique has size at most 2b.
    tested = 0
    rng = Random(620)
    for b in (3, 5, 7):
        r = (5*b-1)//2
        n = 5*b
        for _ in range(10):
            masks = [[0]*n for _ in range(r)]
            for u, v in combinations(range(n), 2):
                a = 0 if (u//b-v//b) % 5 in (0, 1, 4) else rng.randrange(1, r)
                masks[a][u] |= 1 << v
                masks[a][v] |= 1 << u

            def independent(available, size, neighbors):
                if size == 0:
                    return 0
                while available.bit_count() >= size:
                    bit = available & -available
                    available ^= bit
                    tail = independent(available & ~neighbors[bit.bit_length()-1], size-1, neighbors)
                    if tail is not None:
                        return tail | bit
                return None

            witnesses = []
            for a in range(1, r):
                witness = independent((1 << n)-1, r+1, masks[a])
                if witness is None:
                    continue
                assert witness.bit_count() == r+1
                assert all(not (masks[a][v] & witness) for v in range(n) if witness & (1 << v))
                if any((witness & earlier).bit_count() >= 2 for earlier in witnesses):
                    tested += 1
                    break
                witnesses.append(witness)
            else:
                raise AssertionError("No overlapping witnesses in the labeled five-cycle construction")
    return tested


if __name__ == "__main__":
    cases, minima = permutation_tests(3, exhaustive=True)
    print(f"{cases:,} order-three boards. Minimum demand sum with a clean hue: "
          f"{finite_three_color_case(minima)}.")
    extra = sum(permutation_tests(r, exhaustive=False)[0] for r in range(4, 8))
    arithmetic()
    print(f"{extra:,} perturbed boards and all finite arithmetic checks passed.")
    switched = sum(switch_one_edge(r)[0] for r in (3, 5))
    print(f"{switched:,} old vertex sets checked in the squares requiring one exception.")
    for order in (11, 13, 16, 17, 19, 23):
        width = max(i for i in range(5, order//2+1) if i % 2)
        cost, edges, demands = verify_construction(order, width)
        print(f"r={order}, k={width}: attaining grid {cost}, critical edges {edges:,}, "
              f"explicit star demands {demands:,}.")
    print(f"{common_neighbor_test():,} weighted common-neighborhood checks passed.")
    print(f"{overlapping_witnesses()} fully labeled height-two cases yielded explicit double demands.")
