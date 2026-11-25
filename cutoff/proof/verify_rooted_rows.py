"""Exact arithmetic and graph witnesses for rooted-rows.md. Run with Python 3."""

from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt

from verify_cutoff_refinement import check_sampling, check_shortfall, pairs


def check_cutoff() -> None:
    inv_r = F(1, 2**20)
    tau, star_cost = F(33, 200), F(81, 500)
    assert tau - F(1, 1024) - (F(1, 256) + inv_r) / 2 > star_cost
    assert star_cost * (F(1, 256) - inv_r) > F(1, 2048)
    assert 4 + (1 - 4*tau) / (2*star_cost) + F(1, 2) < 6
    lost, before, short, temporary_degree = F(1, 2), F(7, 8), F(1, 4), F(1, 16)
    initial_small = 6 / (1 - before)
    temporary_small = (1 / temporary_degree) / (short - 2*temporary_degree)
    pairs_chosen = (initial_small + temporary_small) / (1 - lost / (before - short))
    exceptions = pairs_chosen + (6 + lost*pairs_chosen) / lost + 512 + 1024
    assert pairs_chosen == 880 and exceptions == 3308
    mass = F(11, 2) + (1 - 4*tau) / (2*star_cost)
    assert mass == F(1061, 162)
    gamma, kappa = F(71, 500), F(1, 81)
    alpha, beta_sq = gamma / 4, kappa / 4
    x_sq = alpha**2 / beta_sq
    kernel_upper = 1/alpha + alpha / beta_sq * sum(
        (-x_sq)**j / (2*j + 1) for j in range(9)
    )
    assert kernel_upper < F(3841, 100)
    first_width, last_width = 2**20, 2**385
    assert exceptions < 4096
    upper = (1 + F(4096, first_width)) * (1 + F(1, first_width)) * mass * F(3841, 100)
    lower = 365 * F(693, 1000) - F(1, first_width)
    assert upper < F(25255, 100) < F(25294, 100) < lower
    assert 2**1578 < 2**38 * (last_width + 4097)**4 < 2**1579
    rho = F(1, 4*first_width)
    assert 1 - gamma*rho - F(1, 4) - F(1, 2) - tau - F(1, 12) > F(1, 1000)
    assert 4*1000**2 * (2*gamma*rho + inv_r**2) < 1
    check_shortfall()
    assert check_sampling() > F(1, 4096)


def check_color_identity() -> int:
    """For arbitrary signed part offsets, compare the two counts in (1)."""
    checked = 0
    for r in range(3, 32):
        for offset in range(-r, r + 1):
            for m in range(2*r + 1):
                # The common internal-pair term cancels. Negative lower bounds are allowed.
                expected = (r + offset)*m + pairs(m) - (r - 1)*(offset + m)
                assert expected == -(r - 1)*offset + (1 + offset)*m + pairs(m)
                checked += 1
    return checked


def check_root_weights() -> None:
    scale, low = F(5, 2), F(9, 10)
    mid = (scale + low)/2

    def g(x: F) -> F:
        return (x - 1)**2 / x

    assert (scale+1)*g(mid) == F(343, 340)
    assert (scale+1)*g(scale) > 2
    for den in range(1, 49):
        for num in range(1, 4 * den + 1):
            x = F(num, den)
            p, z = max(low-x, 0)/x, max(x-scale, 0)/x
            assert scale*(x-1)**2 - (low-x) == scale*(x - F(4, 5))**2
            assert p <= scale*g(x)
            assert max(0, scale-max(x, low))/x == scale/x - 1 - p + z
            assert int(x > mid) + int(x >= scale) + p - z - scale*g(x) <= g(x)


def root_mass_holds(adjacency: list[set[int]], roots: set[int], r: int) -> None:
    n = len(adjacency)
    assert n == r*r+1 and len(roots) == r
    assert all(not (adjacency[u] & roots) for u in roots)
    rows = {u: set() for u in roots}
    exterior = []
    for v, neighbors in enumerate(adjacency):
        support = (neighbors | {v}) & roots
        assert support
        if len(support) == 1:
            rows[next(iter(support))].add(v)
        else:
            exterior.append(len(support))
    assert all(all(v in adjacency[u] for u, v in combinations(row, 2)) for row in rows.values())
    assert all(len(row) <= r for row in rows.values())
    assert sum(r-len(row) for row in rows.values()) == len(exterior)-1
    assert 2*sum(t-1 for t in exterior) <= 5*(r-1)


def weighted_choice(candidates: list[tuple[int, ...]], adjacency: list[set[int]], r: int) -> set[int]:
    # Units of one tenth: this is exactly the positive-part weight in Section 3.
    w = [max(0, 25*(r+1)-max(10*(len(neighbors)+1), 9*(r+1))) for neighbors in adjacency]
    valid = [a for a in candidates if all(w[v] > 0 for v in a)]
    return set(max(valid, key=lambda a: (sum(w[v] for v in a), len(a))))


def check_small_root_graphs() -> tuple[int, int]:
    edges = list(combinations(range(5), 2))
    exhaustive = 0
    for mask in range(1 << len(edges)):
        adjacency = [set() for _ in range(5)]
        for i, (u, v) in enumerate(edges):
            if mask & (1 << i):
                adjacency[u].add(v)
                adjacency[v].add(u)
        if sum(map(len, adjacency)) > 10:
            continue
        if any(sum(v in adjacency[u] for u, v in combinations(triple, 2)) in (0, 3)
               for triple in combinations(range(5), 3)):
            continue
        independent = [()] + [(v,) for v in range(5)] + [(u, v) for u, v in edges if v not in adjacency[u]]
        root_mass_holds(adjacency, weighted_choice(independent, adjacency, 2), 2)
        exhaustive += 1
    assert exhaustive == 12

    # r-2 isolated clique components and the complement of a blown-up five-cycle.
    # In the latter all independent sets have size <= 2, and large target cliques
    # are unions of at most two nonconsecutive blocks.
    orders = range(3, 28)
    for r in orders:
        near, rem = divmod(2*r+1, 5)
        sizes = [near+(i < rem) for i in range(5)]
        assert all(sizes[i]+sizes[(i+2) % 5] <= r for i in range(5))
        block_of = [i for i, size in enumerate(sizes) for _ in range(size)]
        singleton_components = [tuple(range(2*r+1+j*r, 2*r+1+(j+1)*r)) for j in range(r-2)]
        adjacency = [set() for _ in range(r*r+1)]
        for vertices in [range(2*r+1), *singleton_components]:
            for u, v in combinations(vertices, 2):
                if v <= 2*r and (block_of[v]-block_of[u]) % 5 in (1, 4):
                    continue
                adjacency[u].add(v)
                adjacency[v].add(u)
        assert sum(map(len, adjacency)) <= r*(r*r+1)
        independent = [()] + [(v,) for v in range(2*r+1)]
        independent.extend((u, v) for u, v in combinations(range(2*r+1), 2) if v not in adjacency[u])
        roots = weighted_choice(independent, adjacency, r)
        for component in singleton_components:
            roots |= weighted_choice([()] + [(v,) for v in component], adjacency, r)
        root_mass_holds(adjacency, roots, r)
    return exhaustive, len(orders)


def check_order_19() -> None:
    r = 19
    n, cap, top = 362, F(88, 5), F(222, 5)
    assert (cap+top)/2 == 31
    constant, slope, inverse = F(791, 130), -F(73, 390), -F(4414, 195)
    for closed in range(1, n+1):
        weight = max(0, top - max(closed, cap))
        f = weight / F(closed)
        indicators = int(closed > 31) + int(closed >= 45)
        diff = (f-indicators-constant-slope*closed-inverse/closed)*390*closed
        if closed <= 17:
            factored = (closed-16)*(73*closed-1205)
        elif closed <= 31:
            factored = (closed-19)*(73*closed-1376)
        elif closed <= 44:
            factored = (closed-32)*(73*closed-817)
        else:
            factored = 73*closed**2-3153*closed+8828
        assert diff == factored and diff >= 0
        assert f >= top/20-1 - top*(closed-20)/400
    floor = constant*n + slope*20*n + inverse*r
    assert 2*n-(r+top)*(r-1)+floor == F(11, 65)
    limit = r*top-n-(top/20-1)*n
    assert limit == F(999, 25)
    max_excess = limit.numerator // limit.denominator
    assert max_excess == 39 and max_excess-1 == 2*r
    assert r-(max_excess-1)//3 == 7
    allowed = [(r-2-pairs(d+1))//(d+1) for d in range(7)]
    assert allowed == [17, 8, 4, 2, 1, 0, -1]
    for max_deficit, max_support in [(2, 2), (1, 3)]:
        for deficits in product(range(1, max_deficit+1), repeat=max_support):
            charge = sum(
                F(r-di-dj+di*dj, (allowed[di]+1)*(allowed[dj]+1)) for di, dj in combinations(deficits, 2)
            )
            assert charge < 1
    assert pairs(10) == 45


def check_affine_profiles() -> None:
    k = 2**20
    minimum_r = 1000 * 2**60
    donor_cut, donor_fraction = F(155, 100), F(321, 1000)
    center_fraction = F(12, 1000)
    assert (1 + 60*F(7, 10))/28 + F(1, 1000) < donor_cut
    assert donor_fraction * (F(1, 28)+F(1, 1000)) <= center_fraction
    assert 1+donor_fraction < 2*(1-F(1, 28)-F(1, 1000))
    assert (k+1)*max(center_fraction/(k+1), donor_cut/minimum_r) < F(71, 2000)
    assert (k+1)*(center_fraction**2/k + donor_fraction*donor_cut**2/minimum_r) < F(1, 324)

    m, r = 2**26, 80_530_636_807
    assert r % 2 and all(r % d for d in range(3, isqrt(r)+1, 2))
    t = r//26
    assert 1200*m < r < 2000*m and t < 2**33
    assert t*(1+33*F(7, 10)) < r-1
    assert F(r, m)*(F(1, 26)-F(1, 28)) > 2 and F(1, 28) > F(71, 2000)
    # Compute the exact number of unordered row pairs without expanding the square.
    diagonal = isqrt(t)
    ordered = 2*sum(t//i for i in range(1, diagonal+1)) - diagonal**2
    row_pairs = (ordered-diagonal)//2
    assert 2*row_pairs+diagonal == ordered and 2*row_pairs <= r-1
    for i in [1, diagonal, diagonal+1, m-1, m]:
        degree = t//i - int(i*i <= t)
        assert 28*i*degree >= r
    print(f"Actual harmonic square: prime {r:,}, {row_pairs:,} interacting row pairs.")


def check_actual_restoration() -> int:
    r, active = 59, 3
    counts = [(r+28*i-1)//(28*i) for i in range(1, active+1)]
    donors = set(range(active, active+8*r//25+1))
    cross = [set() for _ in range(r*r)]
    for i, cols in enumerate(counts):
        for col in range(cols):
            for donor in donors:
                u, v = i*r+col, donor*r+col
                cross[u].add(v)
                cross[v].add(u)
    # Vertical target edges are matchings between rows, so stage one is idle.
    alive = set(range(r*r))
    removed = []
    for u in range(r*r):
        if 4*len(cross[u] & alive) > r:
            alive.remove(u)
            removed.append(u)
    assert removed == [i*r+c for i, cols in enumerate(counts) for c in range(cols)]
    def full_cut(row: set[int]) -> int:
        return len(row)*(r-len(row)) + sum(len(cross[u]) for u in row)
    rows = [alive & set(range(i*r, (i+1)*r)) for i in range(r)]
    for u in removed:
        row = rows[u//r]
        full_degree = r-1+len(cross[u])
        old_cut, old_size = full_cut(row), len(row)
        assert full_degree <= 2*old_size
        row.add(u)
        assert full_cut(row)-old_cut == full_degree-2*old_size
    assert all(len(row) == r for row in rows)
    assert [full_cut(rows[i]) for i in range(active)] == [c*len(donors) for c in counts]
    assert all(full_cut(rows[i]) == sum(counts) for i in donors)
    return len(removed)


def check_star_extensions() -> int:
    """Enumerate the full extra star at the affine square of order three."""
    r = 3
    square = [(row, col) for row in range(r) for col in range(r)]
    color = {}
    vertical_other = 0
    for u, v in combinations(range(r*r), 2):
        i, c = square[u]
        j, d = square[v]
        if c != d:
            hue = ((j-i)*pow(d-c, -1, r)) % r
        elif {i, j} == {0, 1}:
            hue = 0
        else:
            hue = 1 + vertical_other % (r-1)
            vertical_other += 1
        color[u, v] = hue
    rows = [tuple(range(i*r, (i+1)*r)) for i in range(r)]
    for subset in combinations(range(r*r), r+1):
        assert len({color[e] for e in combinations(subset, 2)}) == r
    assert all(sum(hue == c for hue in color.values()) == 12 for c in range(r))
    count = 0
    for star in product(range(r), repeat=r*r):
        for row in rows:
            if sum(star[v] == 0 for v in row) >= 2:
                chosen = row
                break
        else:
            choices: list[int] = []
            for row in rows:
                choices.append(next(v for v in row if star[v] != 0 and
                                    all(color[u, v] != 0 for u in choices)))
            chosen = tuple(choices)
        used = {star[v] for v in chosen} | {color[e] for e in combinations(chosen, 2)}
        assert len(used) < r
        count += 1
    return count


if __name__ == "__main__":
    check_cutoff()
    identities = check_color_identity()
    check_root_weights()
    exhaustive, constructed = check_small_root_graphs()
    check_order_19()
    check_affine_profiles()
    restored = check_actual_restoration()
    extensions = check_star_extensions()
    print(f"{identities:,} star identities; row mass 1061/162; draft cutoff 2^1579.")
    print(f"Root lemma checked on {exhaustive} eligible five-vertex graphs and {constructed} larger graphs.")
    print(f"All 362 finite degree inequalities passed; incidence at most 39 and deficit at most 38.")
    print(f"Restored all {restored} marked points of the 59-color example.")
    print(f"Finite support bounds and all {extensions:,} labeled extensions of the three-color square passed.")
