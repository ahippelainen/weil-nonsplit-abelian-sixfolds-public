"""Proposition 5.2, the relation (5.3), the identity (5.4), Tables 1 and 2, and the check sum_j c_j d_j = 28374 - 28368 = 6 after Proposition 5.2.

Reads subcovers.out (written by subcovers.g) and subcovers_double_cosets.out (written by subcovers_double_cosets.g) and checks in exact arithmetic: that the eleven pairs (H_j, psi_j) of Table 1 occur, with the vectors v_j of Table 2 and every entry of Table 1, including g(X_j) by the Riemann-Hurwitz formula and the exponents; the relation (5.3); the identity (5.4); the full pairing of the exponents of psi_j^t for every t in (Z/m_j)^*; and that the eleven pairs occur in the second enumeration with the same exponents and that the relation holds there.

GAP numbers the irreducible characters differently from run to run. Each enumeration is matched to the numbering of Table 2 through dim M_{rho_k}, with rho fixed, by the relabellings under which all eleven pairs of Table 1 occur; exactly one such relabelling is required, and it is then checked to respect the degrees and the values chi_{rho_k}(gamma_1) of Table 2.
"""
import collections
import itertools
import re
from fractions import Fraction
from math import gcd

# Table 1: j, c_j, |H_j|, m, r, g(Y_j), d, g(X_j), m' (None for the etale rows), exponents as (value, multiplicity).
TABLE1 = [
    (1, -1, 432, 6, 544, 989, 2520, 7015, 6, [(2, 270), (3, 4), (4, 270)]),
    (2, +1, 486, 6, 384, 913, 2208, 6241, 3, [(2, 192), (4, 192)]),
    (3, -1, 324, 6, 448, 1361, 3168, 9049, 6, [(2, 216), (3, 16), (4, 216)]),
    (4, +1, 288, 12, 654, 1537, 3726, 21043, 6, [(4, 324), (6, 6), (8, 324)]),
    (5, +1, 216, 24, 0, 2341, 4680, 56161, None, []),
    (6, +1, 144, 6, 336, 3397, 7128, 21043, 6, [(2, 162), (3, 12), (4, 162)]),
    (7, -1, 120, 24, 0, 4213, 8424, 101089, None, []),
    (8, +1, 108, 12, 0, 4681, 9360, 56161, None, []),
    (9, +1, 3888, 6, 160, 77, 312, 775, 6, [(2, 78), (3, 4), (4, 78)]),
    (10, -1, 72, 12, 672, 6793, 14256, 84169, 6, [(4, 324), (6, 24), (8, 324)]),
    (11, +1, 972, 6, 64, 449, 960, 2809, 6, [(2, 24), (3, 16), (4, 24)]),
]
# Table 2: k, dim rho_k, dim M_{rho_k}, chi_{rho_k}(gamma_1) = a + b zeta^2 as (a, b), and the row (v_1(rho_k), ..., v_11(rho_k)).
TABLE2 = [
    (1, 4, 6, (2, -1), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
    (2, 4, 42, (-1, 2), [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]),
    (3, 20, 102, (7, 7), [0, 0, 0, 0, 1, 1, 1, 1, 0, 2, 0]),
    (4, 20, 102, (1, -5), [0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0]),
    (5, 20, 138, (-5, -8), [2, 0, 0, 2, 1, 0, 1, 1, 0, 1, 0]),
    (6, 20, 174, (-5, 1), [0, 1, 1, 1, 0, 1, 1, 1, 0, 2, 0]),
    (7, 20, 174, (-8, -5), [2, 0, 1, 2, 1, 1, 1, 1, 0, 1, 0]),
    (8, 36, 162, (9, 0), [0, 0, 1, 0, 1, 1, 2, 2, 0, 2, 1]),
    (9, 36, 270, (0, 9), [0, 1, 0, 0, 1, 2, 2, 2, 1, 5, 0]),
    (10, 60, 342, (3, -6), [1, 0, 1, 1, 2, 2, 3, 3, 0, 4, 1]),
    (11, 60, 378, (3, 3), [0, 1, 1, 1, 1, 3, 3, 3, 0, 5, 0]),
    (12, 60, 450, (-6, 3), [1, 1, 1, 1, 2, 3, 3, 3, 0, 6, 1]),
    (13, 64, 384, (8, 8), [0, 1, 1, 0, 2, 3, 3, 4, 0, 6, 0]),
    (14, 80, 552, (-8, -8), [2, 1, 2, 3, 2, 3, 4, 5, 0, 6, 0]),
]
V = [[row[4][j] for row in TABLE2] for j in range(11)]
DEG = [row[1] for row in TABLE2]
DIMM = [row[2] for row in TABLE2]
CHI = [row[3] for row in TABLE2]
E_RHO = [1] + [0] * 13


def read_gap(path):
    txt = open(path).read().replace('\\\n', '')
    get = lambda name: eval(re.search(name + r':=(.*?);\n', txt, re.S).group(1))
    return {name: get(name) for name in ('rhopos', 'deg', 'dimM', 'chi1', 'pq', 'P')}


def identify(name, run, recs):
    """perm[k] is the position in this run of the representation in row k+1 of Table 2."""
    assert all(p == q and p + q == dM for (p, q), dM in zip(run['pq'], run['dimM']))
    cands = [[i for i in range(14) if run['dimM'][i] == DIMM[k]] for k in range(14)]
    found = []
    for perm in itertools.product(*cands):
        if len(set(perm)) == 14 and perm[0] == run['rhopos'] - 1 and all(
                any((x['size'], x['m'], x['r'], x['gY']) == t[2:6] and [x['v'][i] for i in perm] == v for x in recs)
                for t, v in zip(TABLE1, V)):
            found.append(perm)
    print(name, 'enumeration: relabellings through dim M, with rho fixed, under which all eleven pairs occur:', len(found))
    assert len(found) == 1
    perm = found[0]
    deg = [run['deg'][i] for i in perm]
    chi = [tuple(run['chi1'][i]) for i in perm]
    print(name, 'enumeration: position in this run of rows 1..14 of Table 2:', [i + 1 for i in perm])
    print(name, 'enumeration: degrees', deg, 'as in Table 2:', deg == DEG, '; chi(gamma_1) as (a, b), a + b zeta^2:', chi, 'as in Table 2:', chi == CHI)
    assert deg == DEG and chi == CHI
    return perm


def paired(ex, m):
    cnt = collections.Counter()
    for a, k in ex:
        cnt[a % m] += k
    return all(cnt[a] == cnt[(-a) % m] for a in cnt) and (m % 2 or cnt[m // 2] % 2 == 0)


run = read_gap('subcovers.out')
recs = []
bad = collections.Counter()
for (sz, idx, m, v, ex, gY, dimW, h10) in run['P']:
    a = [e for _, e in ex]; r = len(a)
    c = collections.Counter(x % m for x in a)
    if dimW != 2 * gY - 2 + r: bad['CW_vs_RH'] += 1
    if 2 * h10 != dimW: bad['unbalanced'] += 1
    if not paired(c.items(), m): bad['unpaired'] += 1
    if r % 2: bad['r_odd'] += 1
    if r == 0 and gY < 2: bad['etale_gY<2'] += 1
    if sum(Fraction(x % m, m) for x in a) != Fraction(r, 2): bad['sum<a/m>!=r/2'] += 1
    recs.append(dict(size=sz, m=m, v=v, r=r, gY=gY, dimW=dimW, exps=sorted(c.items())))
print('pairs (H,psi)', len(recs), 'violations', dict(bad))
print('orders', sorted(collections.Counter(x['m'] for x in recs).items()))
print('#pairs (H,psi)', len(recs), '#etale', sum(x['r'] == 0 for x in recs))
perm = identify('first', run, recs)
for x in recs:
    x['v'] = [x['v'][i] for i in perm]
PQ = [run['pq'][i] for i in perm]
print('Table 2 as identified (k, degree, dim M, chi(gamma_1)):', [(k + 1, run['deg'][i], run['dimM'][i], tuple(run['chi1'][i])) for k, i in enumerate(perm)])

tot = [sum(t[1] * V[j][k] for j, t in enumerate(TABLE1)) for k in range(14)]
print('sum c_j v_j =', tot, '== e_rho:', tot == E_RHO)
assert tot == E_RHO
rows = []; bad = []
for (j, c, H, m, r, gY, d, gXrec, mp, exps), v in zip(TABLE1, V):
    hits = [x for x in recs if (x['size'], x['m'], x['r'], x['gY'], x['v'], x['exps']) == (H, m, r, gY, v, exps)]
    if not hits:
        bad.append((j, 'not found')); continue
    x = hits[0]
    chk = {
        'd=sum v dimM (5.4)': d == sum(v[k] * DIMM[k] for k in range(14)) == x['dimW'],
        'd=2g-2+r (5.4)': d == 2 * gY - 2 + r,
        'r=sum exps': r == sum(k for _, k in exps),
        'balanced': 2 * sum(v[k] * PQ[k][0] for k in range(14)) == d,
        'paired(all t)': all(paired([(t * a, k) for a, k in exps], m) for t in range(1, m) if gcd(t, m) == 1),
        'sum<a/m>=r/2 all t': all(sum(Fraction((t * a) % m, m) * k for a, k in exps) == Fraction(r, 2) for t in range(1, m) if gcd(t, m) == 1),
        'r even': r % 2 == 0,
        'sum a = 0 mod m': sum(a * k for a, k in exps) % m == 0,
        'etale: gY>=2': r > 0 or gY >= 2,
        'ramified: m>=3 and r>=3': r == 0 or (m >= 3 and r >= 3),
    }
    g_ = 0
    for a, _ in exps: g_ = gcd(g_, a)
    chk["m' as recorded"] = (m // gcd(g_, m) if r else None) == mp
    # Riemann-Hurwitz for the connected cyclic cover X_j -> Y_j of degree m: a point with exponent a has gcd(a, m) preimages.
    gX = (m * (2 * gY - 2) + sum(k * (m - gcd(a, m)) for a, k in exps)) // 2 + 1
    chk['g(X) as recorded'] = gX == gXrec
    chk['d<=g(X)'] = d <= gX
    if not all(chk.values()): bad.append((j, [k for k, ok in chk.items() if not ok]))
    rows.append((j, c, H, m, r, gY, d, gX, mp, exps))
print('violations:', bad)
assert not bad and len(rows) == 11
npos = sum(row[6] for row in rows if row[1] == 1); nneg = sum(row[6] for row in rows if row[1] == -1)
print('sum c_j d_j = n_+ - n_- =', npos, '-', nneg, '=', npos - nneg, '; #(c_j = +1)', sum(row[1] == 1 for row in rows), '#(c_j = -1)', sum(row[1] == -1 for row in rows))
assert (npos, nneg, npos - nneg) == (28374, 28368, DIMM[0]) and sum(row[1] == 1 for row in rows) == 7
print("| j | c_j | |H_j| | m | r | g(Y_j) | d | g(X_j) | m' | exponents |")
for j, c, H, m, r, gY, d, gX, mp, exps in rows:
    exs = ', '.join(f'{a}:{k}' for a, k in exps) or 'etale'
    print(f'| {j} | {c:+d} | {H} | {m} | {r} | {gY} | {d} | {gX} | {mp if mp else "-"} | {exs} |')
print('#ramified', sum(row[4] > 0 for row in rows), '#etale', sum(row[4] == 0 for row in rows))
assert sum(row[4] > 0 for row in rows) == 8

run2 = read_gap('subcovers_double_cosets.out')
recs2 = [dict(size=H, m=m, v=v, exps=sorted((a, k) for a, k in ex), gY=gY, r=sum(k for _, k in ex)) for H, m, v, ex, gY in run2['P']]
print('second enumeration (11 orders): #pairs (H,psi)', len(recs2), 'orders', sorted(collections.Counter(x['m'] for x in recs2).items()), '#etale', sum(x['r'] == 0 for x in recs2))
perm2 = identify('second', run2, recs2)
for x in recs2:
    x['v'] = [x['v'][i] for i in perm2]
found = []
for (j, c, H, m, r, gY, d, gX, mp, exps), v in zip(TABLE1, V):
    hits = [x for x in recs2 if (x['size'], x['m'], x['r'], x['gY'], x['v']) == (H, m, r, gY, v)]
    assert hits, j
    found.append((c, hits[0]))
    print('  ', j, c, [H, m, r, gY], 'exps', hits[0]['exps'])
assert all(x['exps'] == t[9] for (_, x), t in zip(found, TABLE1))
tot2 = [sum(c * x['v'][k] for c, x in found) for k in range(14)]
print('sum c_j v_j = e_rho in the second enumeration:', tot2 == E_RHO, '; exponents as in the first enumeration:', all(x['exps'] == t[9] for (_, x), t in zip(found, TABLE1)))
assert tot2 == E_RHO

want = {t[2] for t in TABLE1}
old = collections.Counter(x['size'] for x in recs if x['size'] in want)
new = collections.Counter(x['size'] for x in recs2)
print('pairs per order, first vs second enumeration:', dict(old), dict(new), old == new)
assert old == new
