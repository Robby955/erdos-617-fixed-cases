#!/usr/bin/env python3
"""Order ten: exact replay of the edge ladder (Section 12 of overfull-core.md).

f(a, n) is a lower bound for the number of target edges on any n-vertex set
that has target independence at most a and no target clique of size 10,
inside a balanced 10-colouring.  inf means that no such set exists.

Inputs (all proved elsewhere in the note):
  N(1) = 9                      a clique has at most nine vertices
  N(2) = 19                     Lemma 9 (two rows)
  N(3) = 29                     Theorem 16 (three rows at order ten)
  N(4) = 40                     P(4) at order ten
  Turan and Brouwer             static floors
Rules used at a vertex x of least degree d, with U the non-neighbours:
  e(R) >= ceil(n d / 2)
  e(R) >= f(a-1, |U|) + rem(d)
  rem(d) = d(d+1)/2                         d <= 8
  rem(9) = 45 + max(1, tau - 1)             no K_10, transversal premium
  rem(10) = 55 + max(9, 2 tau - 6)          balance on N[x], two disjoint edges
  rem(d) = d(d+1)/2 + 9(d-9)                d >= 11, balance on N[x]
  tau >= |U| - N(a-2)                       when N(a-2) is known
Run:  python3 -B verify_order_ten_ladder.py          (add --rows to print every row of the key cells)
"""
import sys
from math import comb, inf

R = 10
N = {0: 0, 1: 9, 2: 19, 3: 29, 4: 40}


def ceil_div(a, b):
    return -((-a) // b)


def turan(m, a):
    q, x = divmod(m, a)
    return a * comb(q, 2) + x * q


def static_floor(a, m):
    """Turan, plus Brouwer when a cliques of size at most nine cannot cover."""
    if a == 0:
        return 0 if m == 0 else inf
    if a == 1:
        return comb(m, 2) if m <= 9 else inf
    base = turan(m, a)
    if m > 9 * a and m >= 2 * a + 1:
        base += m // a - 1
    return base


def rem(d, tau):
    if d <= 8:
        return d * (d + 1) // 2
    if d == 9:
        return 45 + max(1, tau - 1)
    if d == 10:
        return 55 + max(9, 2 * tau - 6)
    return d * (d + 1) // 2 + 9 * (d - 9)


def build(top_a=9, top_n=101):
    f = {}
    how = {}
    for a in range(0, top_a + 1):
        for n in range(0, top_n + 1):
            if a in N and n > N[a]:
                f[a, n] = inf
                how[a, n] = 'empty'
                continue
            best = static_floor(a, n)
            src = 'static'
            if best is inf:
                f[a, n] = inf
                how[a, n] = 'empty'
                continue
            # every (n-1)-subset has at least f(a, n-1) edges
            if n >= 3 and f.get((a, n - 1), 0) not in (inf,):
                avg = ceil_div(f[a, n - 1] * n, n - 2)
                if avg > best:
                    best, src = avg, 'average'
            if a >= 2 and n >= 1:
                rows = []
                for d in range(0, n):
                    u = n - 1 - d
                    resid = f[a - 1, u]
                    if resid is inf:
                        continue
                    tau = max(0, u - N[a - 2]) if (a - 2) in N else 0
                    rows.append((max(ceil_div(n * d, 2), resid + rem(d, tau)), d))
                if not rows:
                    f[a, n] = inf
                    how[a, n] = 'empty'
                    continue
                low, d = min(rows)
                if low > best:
                    best, src = low, 'least degree %d' % d
            f[a, n] = best
            how[a, n] = src
    return f, how


def main():
    f, how = build()
    show = [(2, 19), (3, 28), (3, 29), (4, 39), (4, 40), (4, 41), (5, 49), (5, 50), (5, 51),
            (6, 59), (6, 60), (6, 61), (7, 70), (7, 71), (8, 80), (8, 81), (9, 91)]
    for key in show:
        print('f%s >= %s   (%s)' % (key, f[key], how[key]))
    # Stops of Proposition 7 at order ten: a set of 10 s + 1 vertices with at most cap edges.
    caps = {s: (R * (R - s) + R * (R * s + 1)) // 2 for s in range(1, 10)}
    assert [caps[s] for s in (5, 6, 7, 8, 9)] == [280, 325, 370, 415, 460]
    ok = True
    for s in range(1, 10):
        need = caps[s] + 1
        got = f[s, R * s + 1]
        good = got >= need
        ok &= good
        print('stop s=%d: %d vertices, cap %d, floor %s  %s' % (s, R * s + 1, caps[s], got, 'ok' if good else 'FAIL'))
    assert ok
    # consequences in the notation of Section 11
    assert f[4, 40] >= 212 and f[5, 50] >= 262 and f[6, 60] >= 307 and f[7, 70] >= 352
    # sanity: the 28-vertex floor must not exceed the known 125- and 126-edge colourings
    assert f[3, 28] <= 125, f[3, 28]
    # the cells quoted in Section 12
    quoted = {(2, 19): 89, (3, 29): 143, (4, 39): 195, (4, 40): 212, (5, 49): 245, (5, 50): 264,
              (5, 51): 281, (6, 60): 312, (6, 61): 332, (7, 70): 358, (7, 71): 376,
              (8, 80): 404, (8, 81): 422, (9, 91): 468}
    assert all(f[k] == v for k, v in quoted.items()), {k: f[k] for k in quoted}
    if '--rows' in sys.argv:
        for a, n in sorted(quoted):
            if a < 3:
                continue
            for d in range(n):
                u = n - 1 - d
                resid = f[a - 1, u]
                if resid is inf:
                    continue
                tau = max(0, u - N[a - 2]) if (a - 2) in N else 0
                print('cell (%d,%d) degree %2d: residual (%d,%d) floor %s, tau %d, step %d, handshake %d, value %d'
                      % (a, n, d, a - 1, u, resid, tau, rem(d, tau), ceil_div(n * d, 2),
                         max(ceil_div(n * d, 2), resid + rem(d, tau))))
    # without the four-row input N(4) the stops s >= 5 still close, with the August values
    saved = N.pop(4)
    g, _ = build()
    N[4] = saved
    assert [g[s, R * s + 1] for s in (5, 6, 7, 8, 9)] == [281, 327, 373, 419, 465]
    print('order ten: every stop exceeds its cap')


if __name__ == '__main__':
    main()
