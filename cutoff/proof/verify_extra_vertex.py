"""Finite checks for extra-vertex.md. Run from the workspace with Python 3."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial
from random import Random


def check_six_point_graphs() -> int:
    """Check the single-hue stability estimates on every labeled six-point graph."""
    n, r = 6, 3
    edges = list(combinations(range(n), 2))
    incident = [sum(1 << i for i, pair in enumerate(edges) if v in pair) for v in range(n)]
    four_sets = [
        sum(1 << i for i, (a, b) in enumerate(edges) if a in subset and b in subset)
        for subset in combinations(range(n), r + 1)
    ]
    accepted = 0
    for graph in range(1 << len(edges)):
        if any(graph & mask == 0 for mask in four_sets):
            continue
        accepted += 1
        surplus = graph.bit_count() - r
        degree = [(graph & mask).bit_count() for mask in incident]
        isolates = degree.count(0)
        isolated_edges = sum(
            bool(graph & (1 << i)) and degree[a] == degree[b] == 1
            for i, (a, b) in enumerate(edges)
        )
        assert 0 <= isolates <= surplus
        assert max(degree) <= 1 + surplus
        assert sum(max(d - 1, 0) for d in degree) == 2 * surplus + isolates
        assert isolated_edges >= r - 5 * surplus
    return accepted


def double_cover_matching(neighbors: list[set[int]]) -> list[tuple[int, int]]:
    owner = [-1] * len(neighbors)

    def augment(u: int, seen: set[int]) -> bool:
        for v in sorted(neighbors[u]):
            if v in seen:
                continue
            seen.add(v)
            if owner[v] == -1 or augment(owner[v], seen):
                owner[v] = u
                return True
        return False

    for u in range(len(neighbors)):
        augment(u, set())
    return [(u, v) for v, u in enumerate(owner) if u != -1]


def check_window(r: int, d: int, slack: int) -> None:
    """Build labeled near-saturated examples and compute the sampler's true marginals."""
    core, outside = r - d, r + d
    owners = {}
    for hue in range(r - 1):
        edges = [(i, core + (i + hue - core) % outside) for i in range(core)]
        edges += [
            (core + (hue + j) % outside, core + (hue + 2 * d - 1 - j) % outside)
            for j in range(d)
        ]
        assert len({v for pair in edges for v in pair}) == 2 * r
        for edge in edges:
            key = tuple(sorted(edge))
            assert key not in owners
            owners[key] = hue
    extras = [edge for edge in combinations(range(core, 2 * r), 2) if edge not in owners]
    for edge in extras[:slack]:
        owners[edge] = 0
    assert comb(2 * r, 2) - len(owners) == r * r - slack
    assert min(Counter(owners.values()).values()) >= r
    # Every other hue retains its perfect matching, so its independence is at most r.
    # A target-independent set is a clique in these non-target edges. Its vertices
    # would all have non-target degree >= r. Only endpoints of added edges can do so.
    assert 2 * slack < r + 1

    neighbors = [set() for _ in range(outside)]
    for a, b in owners:
        if a >= core:
            neighbors[a - core].add(b - core)
            neighbors[b - core].add(a - core)
    senders = [sum((u, core + v) not in owners for u in range(core)) for v in range(outside)]
    overflow = sum(max(e - d - 1, 0) for e in senders)
    spread = sum(max(len(row) - 2 * d, 0) for row in neighbors)
    edges = sum(map(len, neighbors)) // 2
    assert edges >= d * (r - 1) and spread <= overflow + 3 * slack < 2 * d
    assert sum(d + 1 - e for e in senders) + edges - d * (r - 1) == 2 * d * (d + 1) + slack
    removed = 0
    for v, row in enumerate(neighbors):
        while len(row) > 2 * d:
            u = min(row)
            row.remove(u)
            neighbors[u].remove(v)
            removed += 1
    assert removed <= spread
    matching = double_cover_matching(neighbors)[: r - 2]
    assert len(matching) == r - 2

    t = Fraction(2 * r + 1, 2)
    p = 2 * (t - 1) / t**2
    outcomes = [(pair, p / 2) for pair in matching]
    loads = [Fraction() for _ in range(outside)]
    for (u, v), weight in outcomes:
        assert u != v and v in neighbors[u]
        loads[u] += weight
        loads[v] += weight
    left = 1 - (r - 2) * p / 2
    for v, load in enumerate(loads):
        extra = min(p - load, left)
        assert extra >= 0
        if extra:
            outcomes.append(((v,), extra))
            loads[v] += extra
            left -= extra
    assert left == 0 and max(loads) <= p
    core_loads = [Fraction() for _ in range(core)]
    mean_size = Fraction()
    mass = Fraction()
    for outcome, probability in outcomes:
        options = [u for u in range(core) if all((u, core + v) in owners for v in outcome)]
        assert options
        for u in options:
            core_loads[u] += probability / len(options)
        mass += probability
        mean_size += probability * (1 + len(outcome))
    assert mass == 1 and max(core_loads) <= p
    assert mean_size == 2 + (r - 2) * p / 2


def check_tangent() -> int:
    comparisons = 0
    for r in range(3, 201):
        t = Fraction(2 * r + 1, 2)
        p = 2 * (t - 1) / t**2
        q = (r - 2) * p / 2
        assert 0 < q < 1 and 3 * p >= 1 - q
        for d in range(1, (r - 6) // 6 + 1):
            assert 2 <= t / 4 and r - 3 * d - 2 >= 1 / p
        for n in (r * r, r * r + 1):
            mean_twice = Fraction(n * (n - 1), r)
            margin = (2 + q - r) * t**2 + (2 * t - 1) * (n - 2 * r) - mean_twice + 2 * r * r
            assert margin == Fraction(r, 4) + Fraction(3, 2)
        for m in range(int(t / 4) + 1):
            bound = 1 - m / t - m * max(m - 2, 0) / t**2
            assert bound >= 0 and 1 - p * m >= bound**2
            comparisons += 1
    return comparisons


def turan_floor(vertices: int, independence: int) -> int:
    size, larger = divmod(vertices, independence)
    return independence * comb(size, 2) + larger * size


def check_restricted_order() -> int:
    comparisons = 0
    for r in range(3, 91):
        for h in range(1, r // 2 + 1):
            for t in range(r):
                n = h * r + t
                remaining = comb(n, 2) - turan_floor(n, h) - (r - 1) * turan_floor(n, r)
                formula = r * (comb(h, 2) - t) + comb(t, 2) + h * t - turan_floor(t, h)
                assert remaining == formula <= r * comb(h, 2)
                comparisons += 1
    return comparisons


def cloned_square(r: int) -> list[list[int]]:
    """Return the symmetric hue matrix for a prime field and a clone of point 0."""
    points = [(x, y) for x in range(r) for y in range(r)]
    clone = len(points)
    labels = [[-1] * (clone + 1) for _ in range(clone + 1)]
    for i, (a, y) in enumerate(points):
        for j in range(i):
            b, z = points[j]
            if a == b:
                hue = (a * a + y + z) % r
            else:
                hue = (y - z) * pow((a - b) % r, -1, r) % r
            labels[i][j] = labels[j][i] = hue
    for i in range(1, clone):
        labels[clone][i] = labels[i][clone] = labels[0][i]
    labels[clone][0] = labels[0][clone] = 0
    return labels


def check_square_structure(labels: list[list[int]], r: int) -> None:
    clone = r * r
    edges = Counter(labels[a][b] for a, b in combinations(range(clone + 1), 2))
    assert len(edges) == r and set(edges.values()) == {r * (r * r + 1) // 2}
    assert Counter(labels[clone][:clone]) == Counter({i: r for i in range(r)})
    for hue in range(r):
        rows = [[x * r + (hue * x + y) % r for x in range(r)] for y in range(r)]
        assert all(labels[a][b] == hue for row in rows for a, b in combinations(row, 2))
        for left, right in combinations(rows, 2):
            assert sum(labels[a][b] == hue for a in left for b in right) <= 2
    for k in sorted({1, min(2, r - 2), max(1, int(r**0.5)), r - 2}):
        h = r * k
        holes = range(h)
        fixed = range(h, clone)
        inside = Counter(labels[a][b] for a, b in combinations(holes, 2))
        outside = Counter(labels[a][b] for a, b in combinations(fixed, 2))
        assert all(sum(labels[x][y] == hue for y in holes) == k for x in fixed for hue in range(r))
        for hue in range(r):
            expected = outside[hue] + Fraction((h + 1) * len(fixed) * k, h)
            expected += Fraction(comb(h + 1, 2) * inside[hue], comb(h, 2))
            assert expected == edges[hue]


def check_core_labels(labels: list[list[int]], r: int) -> None:
    """Count missing hues and repeated labels independently on the balanced square."""
    square = set(range(r * r))
    for hue in range(r):
        row = [x * r + (hue * x) % r for x in range(r)]
        for deficit in sorted({1, (r - 1) // 2, r - 2}):
            core = row[: r - deficit]
            outside = square.difference(core)
            n = len(outside)
            missing = [
                sum(all(labels[x][u] != other for u in core) for x in outside)
                for other in range(r) if other != hue
            ]
            assert max(missing) <= deficit * r
            repetitions = []
            for x in outside:
                counts = Counter(labels[x][u] for u in core)
                repetitions.append(counts[hue] + sum(k - 1 for j, k in counts.items() if j != hue))
            assert sum(missing) == (deficit - 1) * n + sum(repetitions)
            assert repetitions.count(0) >= deficit**2 + sum(max(a - 1, 0) for a in repetitions)
            full_n = n + 1
            assert (r - 1) * deficit * r - deficit * full_n == -deficit * (deficit + 1)


def recover_witness(labels: list[list[int]], r: int) -> list[int]:
    """Find a missing-color set with no coordinates or distinguished vertices."""
    n = len(labels)
    twins = [
        (a, b)
        for a, b in combinations(range(n), 2)
        if all(labels[a][v] == labels[b][v] for v in range(n) if v != a and v != b)
    ]
    assert len(twins) == 1
    a, b = twins[0]
    hue = labels[a][b]
    witness = [a, b] + [v for v in range(n) if v != a and v != b and labels[a][v] == hue]
    assert len(witness) == r + 1
    assert all(labels[x][y] == hue for x, y in combinations(witness, 2))
    return witness


def check_failures(labels: list[list[int]], r: int) -> tuple[int, int]:
    clone = r * r
    all_hues = (1 << r) - 1
    missing_counts = Counter()
    for subset in combinations(range(clone + 1), r + 1):
        seen = 0
        for a, b in combinations(subset, 2):
            seen |= 1 << labels[a][b]
            if seen == all_hues:
                break
        if seen != all_hues:
            assert subset[0] == 0 and subset[-1] == clone and seen & 1
            missing_counts[all_hues ^ seen] += 1
    count = sum(missing_counts.values())
    assert count > 0
    low = Fraction(r - 1, 2 * r) * r ** (r - 1)
    for hue in range(1, r):
        individual = sum(n for mask, n in missing_counts.items() if mask & (1 << hue))
        assert low <= individual <= r ** (r - 1)
    for a, b in combinations(range(1, r), 2):
        overlap = sum(n for mask, n in missing_counts.items() if mask & (1 << a) and mask & (1 << b))
        assert overlap <= factorial(r - 1)
    assert (r - 1) * low - comb(r - 1, 2) * factorial(r - 1) <= count <= (r - 1) * r ** (r - 1)
    return count, comb(clone + 1, r + 1)


def check_dense_sets(labels: list[list[int]], r: int) -> tuple[int, list[int]]:
    """Enumerate every 2r-set by DFS, counting its actual edges in every hue."""
    n, size = len(labels), 2 * r
    neighbors = [[sum(1 << u for u in range(v) if labels[v][u] == hue) for hue in range(r)] for v in range(n)]
    best = [0] * r
    total = 0

    def visit(start: int, left: int, chosen: int, counts: list[int]) -> None:
        nonlocal total
        for v in range(start, n - left + 1):
            weights = [count + (chosen & mask).bit_count() for count, mask in zip(counts, neighbors[v])]
            if left == 1:
                total += 1
                for hue, weight in enumerate(weights):
                    if weight > best[hue]:
                        best[hue] = weight
            else:
                visit(v + 1, left - 1, chosen | (1 << v), weights)

    visit(0, size, 0, [0] * r)
    assert total == comb(n, size) and max(best) <= r * r - r + 3
    return total, best


def check_affine_incidences() -> int:
    """Every choice of holes and one line per pure direction in the order-3 plane."""
    r = 3
    directions = (0, 1)
    checked = 0
    for b in range(r):
        for c in range(r):
            lines = [{x * r + (m * x + intercept) % r for x in range(r)} for m, intercept in zip(directions, (b, c))]
            for mask in range(1 << (r * r)):
                holes = {x for x in range(r * r) if mask & (1 << x)}
                incidence = sum(len(holes & line) for line in lines)
                assert len(holes) * (incidence + 2) >= incidence**2
                if all(len(holes & line) >= 2 for line in lines):
                    assert len(holes) * 3 >= 8
                checked += 1
    # Two and three revealed names in four holes induce the same ordered-pair law.
    short = Counter(permutations(range(4), 2))
    long = Counter(p[:2] for p in permutations(range(4), 3))
    assert all(long[p] == 2 * n for p, n in short.items())
    return checked


if __name__ == "__main__":
    print(f"{check_six_point_graphs()} six-point graphs passed among all 32,768 labeled graphs", flush=True)
    windows = [(r, d, slack) for r, d in [(33, 3), (49, 5), (64, 8), (81, 9)] for slack in (0, 1, d // 2)]
    for r, d, slack in sorted(set(windows)):
        check_window(r, d, slack)
    print(f"{len(set(windows))} labeled windows with exact sampler marginals and {check_tangent()} tangent checks", flush=True)
    print(f"{check_restricted_order():,} comparisons for the restricted-order bound", flush=True)
    for r in (3, 5, 7, 11, 17):
        labels = cloned_square(r)
        check_square_structure(labels, r)
        check_core_labels(labels, r)
        rng = Random(617 + r)
        vertices, hues = list(range(len(labels))), list(range(r))
        rng.shuffle(vertices)
        rng.shuffle(hues)
        blinded = [[-1 if a == b else hues[labels[a][b]] for b in vertices] for a in vertices]
        recover_witness(blinded, r)
        if r <= 5:
            failures, sets = check_failures(labels, r)
            windows, maxima = check_dense_sets(labels, r)
            print(f"r={r}: {failures:,} failing sets among {sets:,}, {windows:,} dense-set candidates, hue maxima {maxima}", flush=True)
    print(f"5 relabeled prime-field witnesses and {check_affine_incidences():,} point-line incidence checks", flush=True)
