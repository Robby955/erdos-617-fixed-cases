#!/usr/bin/env python3
"""Exact checks for overfull-core.md (Erdos 617).

Run:  python3 -B verify_overfull_core.py
Uses only the standard library. If the `cadical` solver is on PATH, the last
check also replays the order-three lower bound through search_one_colour.py.
"""
import itertools
import shutil
import subprocess
import sys
from fractions import Fraction as Fr
from math import comb


def p(m, parts):
    """Least edge count on m vertices with independence number <= parts."""
    q, s = divmod(m, parts)
    return parts * comb(q, 2) + s * q


def cap(m, r):
    return comb(m, 2) - (r - 1) * p(m, r)


def slack(r, s, x):
    """Pairs left on a set W with |W| = s*r + x, alpha_a(W) <= s, no a-K_r,
    after hue a and the other r-1 hues take their Brouwer minima."""
    n = s * r + x
    a_need = p(n, s) + n // s - 1
    c_need = p(n, r) + n // r - 1
    return comb(n, 2) - a_need - (r - 1) * c_need


def check(name, ok):
    print(('ok   ' if ok else 'FAIL ') + name)
    if not ok:
        sys.exit(1)


# --- Lemma 1 -------------------------------------------------------------
def slack_formula(r, s, x):
    return Fr(s * (r * (s - 3) + 2), 2) - x * (r - s) + comb(x, 2) - (1 if x == s else 0)


check('Lemma 1 closed form agrees with the direct count for 3 <= r < 120',
      all(slack(r, s, x) == slack_formula(r, s, x)
          for r in range(3, 120) for s in range(2, r) for x in range(1, s + 1)
          if s * r + x <= r * r + 1))
check('s = 2, x = 1: negative for every r >= 3 (checked to 2000)',
      all(slack(r, 2, 1) == 4 - 2 * r < 0 for r in range(3, 2001)))
check('s = 3, x = 1: equals 6 - r, negative exactly when r >= 7',
      all(slack(r, 3, 1) == 6 - r for r in range(4, 2001)))
check('s = 4: x = 3 gives 19 - r, x = 4 gives 25 - 2r',
      all(slack(r, 4, 3) == 19 - r and slack(r, 4, 4) == 25 - 2 * r for r in range(5, 2001)))
check('s = 4, x = 1: equals r + 8 (no exclusion from the count alone)',
      all(slack(r, 4, 1) == r + 8 for r in range(5, 2001)))

# --- core with h = 4 ------------------------------------------------------
def h4_window(r):
    n = 4 * r + 1
    upper = comb(n, 2) - (r - 1) * (p(n, r) + n // r - 1)      # other hues take their minima
    lower = -(-(n * r + r + 1) // 2)                           # min degree r, r+1 vertices of degree > r
    return lower, upper


check('h = 4 window: 2r^2+r+1 <= e_a(U) <= 2r^2+r+7 for 7 <= r <= 2000',
      all(h4_window(r) == (2 * r * r + r + 1, 2 * r * r + r + 7) for r in range(7, 2001)))

# --- Lemma 2 --------------------------------------------------------------
check('Lemma 2 count: at least h+1 core vertices have two neighbours in a maximum independent set',
      all((h * r + 1 - h) - h * (r - 2) == h + 1 for r in range(3, 300) for h in range(1, r + 1)))

# --- conditional arithmetic (Hypothesis A: core mean degree >= r + 2/h) -----
def k_allowed(r):
    mean = Fr(r * (r * r + 1), 2)
    out = []
    for k in range(0, r - 1):
        h = r - k
        if k * comb(r, 2) + Fr((h * r + 1) * (h * r + 2), 2 * h) <= mean:
            out.append(k)
    return out


check('Hypothesis A forces at least three full cliques (5 <= r <= 400)',
      all(min(k_allowed(r)) == 3 for r in range(5, 401)))


def slack_A(r, h):
    n = h * r + 1
    return comb(n, 2) - Fr(n * (n + 1), 2 * h) - (r - 1) * (p(n, r) + n // r - 1)


check('Hypothesis A excludes h = 3 for r >= 4 and h = 4 exactly for r >= 14',
      all(slack_A(r, 3) < 0 for r in range(4, 2001))
      and [r for r in range(5, 2001) if slack_A(r, 4) >= 0] == list(range(5, 14)))
check('Hypothesis A leaves h = 5 open (slack positive for 6 <= r <= 2000)',
      all(slack_A(r, 5) > 0 for r in range(6, 2001)))

# --- Section 4: identity (3), Lemma 4, Theorem 5, Corollary 6 ---------------
check('identity (3): pairs of U minus the Turan floors equal r*B(h) - (r-h)',
      all(comb(h * r + 1, 2) - (h * comb(r, 2) + r) - (r - 1) * p(h * r + 1, r)
          == r * comb(h, 2) - (r - h) for r in range(3, 200) for h in range(2, r)))
check('Brouwer minimum for another hue on U is surplus h-1',
      all((h * r + 1) // r - 1 == h - 1 for r in range(3, 200) for h in range(2, r)))


def theorem5_contradiction(r):
    n = 4 * r + 1
    upper = comb(n, 2) - (r - 1) * (p(n, r) + 3)             # e_a(U) at most this
    lower = -(-(n * r + r + 1) // 2)                         # Corollary 3
    some_hue_at_minimum = (upper - lower) < (r - 1)          # surplus beyond minima is spread over r-1 hues
    cliques = (r + 1) - 3                                    # Lemma 4 with eta = 3
    uncovered = n - 4 * cliques
    degree_sum = cliques * (4 * r + 2) + uncovered * r
    return some_hue_at_minimum and uncovered == 9 and degree_sum > 2 * upper


check('Theorem 5: h = 4 contradicts the window exactly for r >= 19 (checked 8 <= r <= 3000)',
      [r for r in range(8, 3001) if not theorem5_contradiction(r)] == list(range(8, 19)))


def corollary6(r):
    # h = 5, minimum degree r-2: X >= 2(r+1-eta) - 2(5(eta-1)+1), 2E_a = 4r + X
    eta_max = max(e for e in range(4, 200)
                  if (r - 1) * e <= 9 * r + 5 - Fr(4 * r + 2 * r + 10 - 12 * e, 2))
    X = 2 * r + 10 - 12 * eta_max
    E_a = Fr(4 * r + X, 2)
    left = 9 * r + 5 - E_a - 4 * (r - 1)
    return eta_max <= 6 and X >= 2 * r - 62 and left <= 2 * r + 40


check('Corollary 6: h = 5, r >= 50 gives excess >= 2r-62 and at most 2r+40 spare edges',
      all(corollary6(r) for r in range(50, 3001)))
check('Corollary 6 minima: p_r(5r+1) + 4 = 10r + 9',
      all(p(5 * r + 1, r) + 4 == 10 * r + 9 for r in range(6, 3001)))
check('with Hypothesis A exactly, h = 5 leaves capacity between 2r+8 and 2r+9',
      all(2 * r + 8 < slack_A(r, 5) < 2 * r + 9 for r in range(6, 3001)))

# --- Section 6: Proposition 7 and the least violation ------------------------
def prop7_top_case(r):
    q = (r - 1) * r + 1
    mean = Fr(r * (r * r + 1), 2)
    need = Fr(q * r + r + 1, 2)
    for t in range(0, r):
        d = r - 1 - t
        e_Y = mean - comb(d + 1, 2)                       # edges left after deleting N[v]
        if not e_Y * Fr(comb(q, 2), comb(q + t, 2)) < need:
            return False
    return True


check('Proposition 7: the averaging bound contradicts the edge count for every t (3 <= r <= 400)',
      all(prop7_top_case(r) for r in range(3, 401)))
check('Proposition 7: (r-1)(q-1) <= r^3 - r^2 + 2r, the inequality used for t >= 1',
      all((r - 1) * ((r - 1) * r) <= r ** 3 - r * r + 2 * r for r in range(3, 5001)))


def least_violation_compatible(r, s):
    # (r-2) eta <= r (s-3)(s+1)/2 + s - 1 together with eta >= s-1
    return (r - 2) * (s - 1) <= Fr(r * (s - 3) * (s + 1), 2) + s - 1


check('least violation: s = 4 incompatible exactly for r >= 19; s = 5 always compatible',
      [r for r in range(6, 2001) if least_violation_compatible(r, 4)] == list(range(6, 19))
      and all(least_violation_compatible(r, 5) for r in range(7, 2001)))


def s5_numbers(r):
    eta = max(e for e in range(4, 400) if (r - 2) * e <= Fr(r * 2 * 6, 2) + 4)
    X = 2 * (r + 1 - eta)
    E_a = Fr(4 * r + X, 2)
    spare = r * comb(5, 2) - (r - 5) - E_a - 4 * (r - 1)
    return eta <= 6 and X >= 2 * r - 10 and spare <= 2 * r + 14


check('least violation at s = 5, r >= 19: eta <= 6, X >= 2r-10, spare <= 2r+14',
      all(s5_numbers(r) for r in range(19, 2001)))

# --- Lemma 9: the order-five exception ---------------------------------------
C10 = {(0, 1): 0, (0, 2): 0, (0, 3): 0, (0, 4): 0, (0, 5): 0, (0, 6): 4, (0, 7): 1, (0, 8): 3, (0, 9): 2,
       (1, 2): 0, (1, 3): 0, (1, 4): 0, (1, 5): 0, (1, 6): 3, (1, 7): 2, (1, 8): 4, (1, 9): 1,
       (2, 3): 2, (2, 4): 4, (2, 5): 0, (2, 6): 0, (2, 7): 0, (2, 8): 1, (2, 9): 3,
       (3, 4): 0, (3, 5): 3, (3, 6): 1, (3, 7): 4, (3, 8): 0, (3, 9): 0,
       (4, 5): 1, (4, 6): 2, (4, 7): 3, (4, 8): 0, (4, 9): 0,
       (5, 6): 0, (5, 7): 0, (5, 8): 2, (5, 9): 4,
       (6, 7): 0, (6, 8): 0, (6, 9): 0, (7, 8): 0, (7, 9): 0, (8, 9): 0}
six_sets_ok = all(len({C10[p] for p in itertools.combinations(S, 2)}) == 5
                  for S in itertools.combinations(range(10), 6))
hue0 = {p for p, c in C10.items() if c == 0}
alpha2 = all(any(p in hue0 for p in itertools.combinations(S, 2)) for S in itertools.combinations(range(10), 3))
k5free = all(not all(p in hue0 for p in itertools.combinations(S, 2)) for S in itertools.combinations(range(10), 5))
check('Lemma 9 fails locally at r = 5: a balanced 5-coloring of K_10 with a 25-edge hue, independence 2, no K_5',
      len(C10) == 45 and six_sets_ok and len(hue0) == 25 and alpha2 and k5free)
check('Lemma 9: 4r/5 < r-1 exactly for r >= 6', [r for r in range(3, 100) if 4 * r < 5 * (r - 1)] == list(range(6, 100)))

# --- order ten from M(s), and the tight-case count ---------------------------
def x_cap(r, s):
    E_a = r * comb(s, 2) - (r - s) - (r - 1) * (s - 1)        # identity (3) with eta_c >= s-1
    return 2 * E_a - (s - 1) * r


def x_budget(r, s, t):
    mean = Fr(r * (r * r + 1), 2)
    e_R = mean - comb(r - t, 2) - (r - 1 - s) * comb(r, 2)    # least hue after N[v] and r-1-s cliques
    n = s * r + 1
    e_W = (e_R * Fr(comb(n, 2), comb(n + t, 2))).__floor__()  # some n-subset has at most this many edges
    return 2 * e_W - n * r


def survivors(r):
    return [s for s in range(4, r - 1)
            if s * r + 1 <= min(x_cap(r, s), max(x_budget(r, s, t) for t in range(r)))]


check('budget at t = 0 is r(r-s)', all(x_budget(r, s, 0) == r * (r - s) for r in range(5, 60) for s in range(1, r)))
check('degree >= r+1 in every violation closes r = 10; leaves s = 5 at r = 11, 12 and s = 5, 6 at r = 13, 14',
      survivors(10) == [] and survivors(11) == [5] and survivors(12) == [5]
      and survivors(13) == [5, 6] and survivors(14) == [5, 6])
check('cap on X equals r(s^2-4s+1)+4s-2; with M(s-1) it excludes s = 4 for r >= 5 and no s >= 5',
      all(x_cap(r, s) == r * (s * s - 4 * s + 1) + 4 * s - 2 for r in range(5, 200) for s in range(2, r))
      and all(4 * r + 1 > x_cap(r, 4) for r in range(5, 2000))
      and all(s * r + 1 <= x_cap(r, s) for r in range(7, 200) for s in range(5, r - 1)))
check('budget: t = 0 is the worst case; every stop with s >= r/2 closes (10 <= r < 120)',
      all(max(x_budget(r, s, t) for t in range(r)) == x_budget(r, s, 0) for r in range(10, 120) for s in range(1, r - 1))
      and all(s * r + 1 > x_budget(r, s, 0) for r in range(10, 120) for s in range((r + 1) // 2, r - 1)))
check('order ten: stops s = 5, 6, 7 close by budget from M(4), M(5), M(6); s = 5 by one unit',
      all(10 * s + 1 > x_budget(10, s, 0) for s in (5, 6, 7)) and 51 - x_budget(10, 5, 0) == 1)
check('tight case: -3sr - r + 6s + 4 + 2(s+1)(2r-5) = (s+3)r - 4s - 6',
      all(-3 * s * r - r + 6 * s + 4 + 2 * (s + 1) * (2 * r - 5) == (s + 3) * r - 4 * s - 6
          for r in range(3, 200) for s in range(1, r)))
check('tight case at exactly sr vertices: -3sr + 6s + 2s(2r-5) = s(r-4)',
      all(-3 * s * r + 6 * s + 2 * s * (2 * r - 5) == s * (r - 4) for r in range(3, 200) for s in range(1, r)))

# --- Theorem 10: a full clique on exactly three rows --------------------------
check('three rows: total degree excess plus twice the other surpluses is 3r',
      all(2 * comb(3 * r, 2) - 3 * r * r - 2 * (r - 1) * p(3 * r, r) == 3 * r
          for r in range(6, 2001)))
check('the regular complement exceeds the Goddard-Lyle threshold exactly from r = 11',
      all((10 * (r - 1) > 9 * r) == (r >= 11) for r in range(6, 2001)))
root_multiplicities = [
    (ij, jk, ki) for ij, jk, ki in itertools.product(range(4), repeat=3)
    if ij + ki == ij + jk == jk + ki == 2
]
check('three doubles incident twice at each root give exactly one double per pair',
      root_multiplicities == [(1, 1, 1)])
check('three disjoint rectangles at the tight triple leave six surplus edges',
      all(2 * (3 * comb(r - 1, 2) + 3 * (2 * r - 3)) - 3 * r * r == 3 * r - 12
          for r in range(6, 2001)))
check('other-hue degrees zero and one require at least five and three surplus edges',
      all((3 * r - 1) // (r - 1) == (3 * r - 2) // (r - 1) == 3
          and p(3 * r - 1, r - 1) + 2 - 3 * r == 5
          and p(3 * r - 2, r - 1) + 2 + 1 - 3 * r == 3 for r in range(6, 2001)))
check('two nonadjacent endpoints of low degree in a hue cost twice their combined shortfall',
      all((3 * r - 2 - j) // (r - 2) == 3
          and p(3 * r - 2 - j, r - 2) + 2 + j == 3 * r + 2 * (4 - j)
          for r in range(10, 2001) for j in range(3)))


def odd_cycle_cap(n, length):
    outside = n - length
    return length + 2 * outside + outside * outside // 4


check('a shortest odd cycle in the residual has length five, and its exterior is bipartite',
      all(odd_cycle_cap(2 * r - 1, 7) < (r - 1) ** 2
          and odd_cycle_cap(2 * r - 1, 5) == (r - 1) ** 2 + 1
          and odd_cycle_cap(2 * (r - 3), 5) < (r - 3) ** 2 - 1 for r in range(10, 2001)))


def replay_five_cycle_attachments(part_size):
    """Exhaust the cycle cuts for a balanced bipartite exterior of the given size."""
    singles = [1 << i for i in range(5)]
    independent_pairs = [singles[i] | singles[(i + 2) % 5] for i in range(5)]
    seen = set()
    count = 0
    for missing_edge in (False, True):
        # If one cross edge is missing, label its two endpoints 0 in their parts.
        choices = independent_pairs if missing_edge else independent_pairs + singles
        for left in itertools.product(choices, repeat=part_size):
            allowed = [
                [mask for mask in choices if all(
                    (missing_edge and i == j == 0) or not (mask & left_mask)
                    for i, left_mask in enumerate(left))]
                for j in range(part_size)
            ]
            for right in itertools.product(*allowed):
                attachments = left + right
                if sum(mask.bit_count() for mask in attachments) < 4 * part_size - 1 + missing_edge:
                    continue
                degrees = [2 + sum(bool(mask & bit) for mask in attachments) for bit in singles]
                if min(degrees[i] + degrees[(i + 1) % 5] for i in range(5)) > part_size + 5:
                    raise AssertionError((left, right, missing_edge))
                mixed = any(any(mask & bit for mask in left) and any(mask & bit for mask in right)
                            for bit in singles)
                seen.add((missing_edge, mixed))
                count += 1
    return count, seen


attachment_count, attachment_types = replay_five_cycle_attachments(3)
check(f'five-cycle pair bound on {attachment_count} labeled cuts, including a vertex meeting both parts',
      attachment_types == {(False, False), (True, False), (True, True)})
check('common-neighbor cap supplies two exterior edges and the final surplus bounds first conflict at eleven',
      all(2 * (2 * r - 2) - (r + 2) + 2 == 3 * r - 4
          and 2 * (3 * r - 4 - 2 * (r + 1)) - 1 == 2 * r - 13
          and (2 * r - 13 > (r + 6) // 2) == (r >= 11) for r in range(10, 2001))
      and (2 * 11 - 13, (11 + 6) // 2) == (9, 8)
      and list(range(2 * 10 - 13, (10 + 6) // 2 + 1)) == [7, 8])

# --- Proposition 13: tight sets ----------------------------------------------
def max_sum_binom(s):
    # largest sum of B(z_i) over s values 0 <= z_i <= s+1 with total 2(s+1)
    best = 0
    def rec(i, left, acc):
        nonlocal best
        if i == s:
            if left == 0:
                best = max(best, acc)
            return
        for z in range(min(s + 1, left) + 1):
            rec(i + 1, left - z, acc + comb(z, 2))
    rec(0, 2 * (s + 1), 0)
    return best


check('Proposition 13: max of sum B(z_i) is s(s+1) (2 <= s <= 7)',
      all(max_sum_binom(s) == s * (s + 1) for s in range(2, 8)))
check('Proposition 13: a*b <= r-1 with 1 <= a, b <= r-2 forces a+b <= r-1 (5 <= r <= 300)',
      all(a + b <= r - 1 for r in range(5, 301) for a in range(1, r - 1) for b in range(1, r - 1) if a * b <= r - 1))
check('Lemma 11 arithmetic: z(r-v) - (r-1)(z-v) = (r-1)v + z(1-v)',
      all(z * (r - v) - (r - 1) * (z - v) == (r - 1) * v + z * (1 - v)
          for r in range(3, 40) for v in range(0, r) for z in range(0, 2 * r)))
check('Lemma 12 arithmetic: (r-v)(r-w) - (r-1)(r-v-w) = r - v - w + v w',
      all((r - v) * (r - w) - (r - 1) * (r - v - w) == r - v - w + v * w
          for r in range(3, 60) for v in range(0, r) for w in range(0, r - v + 1)))
check('least violation: degree sum >= sr + s^2 - 4s + 2 on every maximum independent set contradicts eta >= s-1 for large r',
      all((s - 1) * (r - 1 - Fr(s * s - 4 * s + 2, 2)) > Fr(r * (s * (s - 1) - 2 - (s - 1) - (s * s - 4 * s + 2)), 2) + s
          for s in range(4, 12) for r in range(40 * s * s, 40 * s * s + 50)))

# --- Section 9: Proposition 15 and Theorem 14 --------------------------------
check('Section 9: a*b <= c <= 2r-5 with 1 <= a, b <= r-2 forces a+b <= r-1 (10 <= r <= 120)',
      all(a + b <= r - 1 for r in range(10, 121) for c in range(1, 2 * r - 4)
          for a in range(1, r - 1) for b in range(a, r - 1) if a * b <= c))


def G9(s, E):
    return 2 * E * (E + 1) * (E + 2) + (s + E) * (s + E + 1) + Fr(E * (s + E), 2)


def final_step_contradiction(r, s):
    e0 = s * s - 4 * s + 2
    for eta in range(s - 1, r + 2):
        E_a = Fr((s - 1) * r + e0 * max(0, r + 1 - eta), 2)
        if (r - 1) * eta <= r * comb(s, 2) - (r - s) - E_a:
            return False
    return True


check('Section 9: the last step is contradictory exactly from r = s^3-6s^2+14s-5 on (4 <= s <= 8)',
      all(not final_step_contradiction(s ** 3 - 6 * s * s + 14 * s - 6, s)
          and all(final_step_contradiction(r, s) for r in range(s ** 3 - 6 * s * s + 14 * s - 5, s ** 3 - 6 * s * s + 14 * s + 60))
          for s in range(4, 9)))
check('Section 9: thresholds 1 + G(s, s^2-4s-1): P(5) from 350, P(6) from 3833; above s^3 bound and E0^2+4',
      int(G9(5, 4)) + 2 == 350 and int(G9(6, 11)) + 2 == 3833
      and all(1 + G9(s, s * s - 4 * s - 1) > max(s ** 3 - 6 * s * s + 14 * s - 6, (s * s - 4 * s - 1) ** 2 + 4)
              for s in range(5, 40))
      and all(G9(s + 1, (s + 1) ** 2 - 4 * (s + 1) - 1) > G9(s, s * s - 4 * s - 1) for s in range(5, 40)))
check('Section 9: sum of B(z_i) <= V(V+1) + sigma V/2 when sum z_i = 2V+2+sigma and z_i <= V+1 (small cases)',
      all(max((sum(comb(z, 2) for z in zs) for zs in itertools.product(range(V + 2), repeat=3)
               if sum(zs) == 2 * V + 2 + sig), default=0) <= V * (V + 1) + Fr(sig * V, 2)
          for V in range(3, 8) for sig in range(0, 4)))


# --- Section 10: three rows at order ten -------------------------------------
def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def order_ten_heavy_pair_outcomes(r=10):
    """All (X, q(y), q(z)) that the accounting of Section 10 allows for a heavy pair.

    Each hue other than a gets a pair of shortfalls (D_c(y), D_c(z)) in {0,1,2}^2.
    In the hue of yz both ends have degree at least one.  Costs are the surplus
    lower bounds of Section 8: three and five for a single end short by one and
    two, 2(i+j) when both ends are short in a hue other than that of yz, and
    three when both ends are short in the hue of yz.
    """
    single = {1: 3, 2: 5}
    kinds = [(i, j) for i in range(3) for j in range(3)]

    def cost(i, j):
        if i == 0 and j == 0:
            return 0
        if i == 0 or j == 0:
            return single[i + j]
        return 2 * (i + j)

    outcomes = set()
    for own in ((0, 0), (1, 0), (0, 1), (1, 1)):
        own_cost = 0 if own == (0, 0) else 3
        for counts in compositions(r - 2, len(kinds)):
            Dy = own[0] + sum(n * k[0] for n, k in zip(counts, kinds))
            Dz = own[1] + sum(n * k[1] for n, k in zip(counts, kinds))
            least = own_cost + sum(n * cost(*k) for n, k in zip(counts, kinds))
            for sigma in range(least, 3 * r // 2 + 1):
                X = 3 * r - 2 * sigma
                for qy in range(Dy + 2):
                    for qz in range(Dz + 2):
                        # heavy pair: q(y)+q(z) >= r-4; at least r-2 triples avoid y, z
                        if qy + qz >= r - 4 and X >= qy + qz + (r - 2):
                            outcomes.add((X, qy, qz))
    return outcomes


check('Section 10: at r = 10 the regular graph has degree exactly 3n/5 and 2(2*18-30) = 12 >= 10',
      2 * (10 - 1) * 5 == 3 * 30 and 2 * (2 * 18 - 30) >= 10)
check('Section 10: join case, an independent part of size m <= 9 leaves a bipartite part with a class >= 10',
      all(5 * (18 - m) > 2 * (30 - m) and (30 - m + 1) // 2 >= 10 for m in range(10)))
check('Section 10: carried inequalities at r = 10 (15 < 18, 67 < 81, 43 < 48, parts 7+7, degree sum 12)',
      3 * 10 // 2 < 2 * 9 and 7 + 2 * 12 + 12 * 12 // 4 == 67 < 81 and 7 * 7 - 7 + 1 == 43 < 48
      and 6 * 8 == 48 and 8 + 2 == 10 and 4 + (2 + 7 - 1) == 12 and 2 * 18 - 12 + 2 - 20 == 6)
check('Section 10: surplus costs 5, 3 for one short end and 8-2j for two (r = 10)',
      [p(29 - j, 9) + 2 + j - 30 for j in (0, 1)] == [5, 3]
      and [p(28 - j, 8) + 2 + j - 30 for j in (0, 1, 2)] == [8, 6, 4])
check('Section 10: a heavy pair leaves only (X, q(y), q(z)) = (14,3,3), (14,4,2), (14,2,4), (16,3,3)',
      order_ten_heavy_pair_outcomes() == {(14, 3, 3), (14, 4, 2), (14, 2, 4), (16, 3, 3)})
check('Section 10: closing counts (X=14 leaves 20 zero vertices; X=16: 12+6 > 16, 3+8 > 10, 3+7 = 10)',
      30 - 2 - (14 - 6) == 20 and 12 + 6 > 16 and 3 + 8 > 16 - 6 and 3 + 7 == 16 - 6
      and 30 - 3 - 7 == 20)


# --- Section 11: the edge budget passes down the reduction --------------------
def passed_budget(r, s, t):
    """Lemma 17, part 1: W has sr+1 vertices and X(W) <= r(r-s); u has least degree
    r-1-t.  Returns the bound on X for the sparsest ((s-1)r+1)-subset of W - N[u]."""
    e_W = (r * (r - s) + r * (s * r + 1)) // 2
    e_rest = e_W - comb(r - t, 2)
    n = (s - 1) * r + 1
    e_sub = (Fr(e_rest) * Fr(comb(n, 2), comb(n + t, 2))).__floor__()
    return 2 * e_sub - n * r


def degree_r_drop(r):
    """Lemma 17, part 2: largest possible X(W') - X(W) over e <= C(r,2)-(r-1) and c >= r^2-r-2e."""
    return max((r * r - r) - 2 * e - 2 * max(0, r * r - r - 2 * e) for e in range(comb(r, 2) - (r - 1) + 1))


check('Lemma 17.1: the passed budget is r(r-s+1) at t = 0 and no larger for t >= 1 (6 <= r <= 40)',
      all(passed_budget(r, s, 0) == r * (r - s + 1)
          and max(passed_budget(r, s, t) for t in range(r)) == r * (r - s + 1)
          for r in range(6, 41) for s in range(2, r)))
check('Lemma 17.2: a vertex of degree exactly r lowers X by at least 2(r-1) (5 <= r <= 40)',
      all(degree_r_drop(r) == -2 * (r - 1) for r in range(5, 41)))
check('Corollary 19: order ten budgets 50, 40, 30, 20 give M(4;32), M(5;22), M(6;12), M(7;2), and sr+1 > r(r-s)',
      [10 * (10 - s) - 18 for s in (5, 6, 7, 8)] == [32, 22, 12, 2]
      and all(10 * s + 1 > 10 * (10 - s) for s in (5, 6, 7, 8))
      and all(x_budget(10, s, t) <= 10 * (10 - s) for s in range(1, 10) for t in range(10)))
check('Corollary 19: no-clique case, 81 of 91 vertices have X <= -84 and Lemma 17.1 at s = 9 passes 20',
      2 * ((Fr(460) * Fr(comb(81, 2), comb(91, 2))).__floor__()) - 810 == -84
      and passed_budget(10, 9, 0) == 20)
check('Corollary 20: four rows at order ten with X <= 32 force k <= 3 whatever the least surplus m',
      [(80 - 2 * max(24, 9 * m)) // (10 if m <= 2 else 10 - m) for m in range(5)] == [3, 3, 3, 3, 1]
      and [(s * 10 * (s - 2) - b + 1) // 2 for s, b in ((4, 32), (5, 22), (6, 12), (7, 2))] == [24, 64, 114, 174]
      and [(s * 100 + b) // 2 for s, b in ((5, 22), (6, 12), (7, 2))] == [261, 306, 351])

# --- one-hue witnesses ------------------------------------------------------
def analyse(n, r, edges):
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    e = [0] * (1 << n)
    alpha = 0
    worst = {}
    for S in range(1, 1 << n):
        low = (S & -S).bit_length() - 1
        rest = S & (S - 1)
        e[S] = e[rest] + bin(adj[low] & rest).count('1')
        m = bin(S).count('1')
        if e[S] == 0:
            alpha = max(alpha, m)
        if e[S] > worst.get(m, -1):
            worst[m] = e[S]
    caps_ok = all(worst[m] <= cap(m, r) for m in worst)
    return alpha, caps_ok


W3 = [(0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 6), (1, 7), (1, 8), (2, 4), (2, 7), (2, 9),
      (3, 5), (3, 7), (4, 6), (5, 8), (5, 9), (6, 8), (8, 9)]
alpha, caps_ok = analyse(10, 3, W3)
check('order 3: the 18-edge graph on 10 vertices has independence number 3 and meets every cap',
      len(W3) == 18 and alpha == 3 and caps_ok)

W4 = [(0, 4), (0, 5), (0, 6), (0, 7), (1, 5), (1, 8), (1, 9), (1, 10), (1, 11), (2, 8), (2, 9),
      (2, 10), (2, 12), (2, 13), (2, 14), (3, 8), (3, 10), (3, 12), (3, 15), (3, 16), (4, 6),
      (4, 7), (5, 9), (5, 11), (5, 12), (5, 13), (6, 7), (8, 10), (8, 16), (9, 12), (9, 15),
      (10, 11), (11, 13), (11, 14), (12, 15), (13, 14), (13, 16), (14, 15), (14, 16), (15, 16)]
alpha, caps_ok = analyse(17, 4, W4)
check('order 4: the 40-edge graph on 17 vertices has independence number 4 and meets every cap',
      len(W4) == 40 and alpha == 4 and caps_ok)

if shutil.which('cadical'):
    out = subprocess.run([sys.executable, '-B', 'search_one_colour.py', '--r', '3', '--n', '10',
                          '--h', '3', '--emax', '17', '--seconds', '120', '--tag', 'replay'],
                         capture_output=True, text=True).stdout
    check('order 3: no one-hue graph with independence number 3 and at most 17 edges (cadical)',
          'UNSAT' in out)
    # independence number <= 2 on 10 vertices already needs p_2(10) = 20 edges
    check('order 3: independence number <= 2 needs 20 edges by Turan', p(10, 2) == 20)
else:
    print('skip order-3 solver replay: cadical not found')

print('all checks passed')
