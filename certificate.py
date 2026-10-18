"""Proposition 6.8 and (6.9), as described in Appendix A (The rank certificate): the 9x9 minor of the limit matrix M* of Section 6.3 formed by the columns T_i at the six special points of P_0 other than the node of {1,2} and x_13, R_(6,7), R_(11,12) and Xi_k is a ball that excludes 0, so M* has rank 9.

Exact over K = Q(zeta^2), z = a + b*w with w = zeta^2, w^2 = -1 - w: the tuple, the joint eigenbases of the monodromies on P_0 and on the components of the trivial clusters with their dual bases, the local exponents, the coefficients of the series expansions, and Fix(gamma_3 gamma_4) cap (Im(gamma_3 - 1) + Im(gamma_4 - 1)) = 0 for both types of forms. In ball arithmetic at 320 bits: the values (p_j - p_i)^e (principal branch; arg = pi for negative reals, the value approached from the upper half-plane) and everything built from them: the 20x21 constraint matrices and the 18x18 minors that bound the dimension of the solution space by 3, the solutions, the expansions to order 3, the columns R, T and Xi, the 3x3 minor of the node columns, the relation vector k normalized at (8,9), and the 9x9 minor. The floating-point pivot searches only choose the minors; every minor used is certified in ball arithmetic.

Inputs from the text, not computed here: dim F^1 = 3 for both types of forms at the nodal fibre (Section 6.3), and that the node columns R of the trivial clusters satisfy one relation, by (6.6) and Lemma 6.4.
"""
import re
from fractions import Fraction as Fr

import numpy as np
from flint import acb, arb, acb_mat, ctx


class QZ:
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def __add__(self, o):
        return QZ(self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        return QZ(self.a - o.a, self.b - o.b)

    def __neg__(self):
        return QZ(-self.a, -self.b)

    def __mul__(self, o):
        # (a + b w)(c + d w) = ac + (ad + bc) w + bd w^2 = (ac - bd) + (ad + bc - bd) w
        a, b, c, d = self.a, self.b, o.a, o.b
        return QZ(a * c - b * d, a * d + b * c - b * d)

    def conj(self):  # w -> w^2 = -1 - w
        return QZ(self.a - self.b, -self.b)

    def norm(self):
        return (self * self.conj()).a

    def inv(self):
        n = self.norm()
        c = self.conj()
        return QZ(c.a / n, c.b / n)

    def __truediv__(self, o):
        return self * o.inv()

    def __eq__(self, o):
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def iszero(self):
        return self.a == 0 and self.b == 0

    def __repr__(self):
        return f"({self.a}+{self.b}w)"


ZERO, ONE, W = QZ(0), QZ(1), QZ(0, 1)
Z6 = -(W * W)  # e^{2 pi i/6}


def eye(n=4):
    return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]


def mmul(A, B):
    return [[sum((A[i][k] * B[k][j] for k in range(len(B))), ZERO) for j in range(len(B[0]))] for i in range(len(A))]


def msub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


def rref(A):
    A = [list(r) for r in A]
    m, n = len(A), len(A[0]) if A else 0
    piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, m) if not A[i][c].iszero()), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        iv = A[r][c].inv()
        A[r] = [x * iv for x in A[r]]
        for i in range(m):
            if i != r and not A[i][c].iszero():
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == m:
            break
    return A, piv


def colbasis(A):
    """independent columns of A (as column vectors = lists)."""
    _, piv = rref(A)
    return [[A[i][c] for i in range(len(A))] for c in piv]


def nullbasis(A, n):
    """basis of {x : A x = 0} in K^n (list of vectors)."""
    if not A:
        return [[ONE if i == j else ZERO for i in range(n)] for j in range(n)]
    R, piv = rref(A)
    free = [c for c in range(n) if c not in piv]
    out = []
    for f in free:
        x = [ZERO] * n
        x[f] = ONE
        for r, c in enumerate(piv):
            x[c] = -R[r][f]
        out.append(x)
    return out


def minv(A):
    n = len(A)
    aug = [list(A[i]) + [ONE if i == j else ZERO for j in range(n)] for i in range(n)]
    R, piv = rref(aug)
    assert piv[:n] == list(range(n))
    return [r[n:] for r in R]


def load_exact(path="tuple.g", name="gamma"):
    txt = open(path).read()
    body = txt[txt.index(name + " :="):]
    body = body[body.index("["): body.index("];") + 1]
    ents = re.findall(r"\((-?\d+)\+(-?\d+)\*E\(3\)\)/(\d+)", body)
    vals = [QZ(Fr(int(a), int(d)), Fr(int(b), int(d))) for a, b, d in ents]
    return [[[vals[16 * t + 4 * i + j] for j in range(4)] for i in range(4)] for t in range(len(vals) // 16)]


ctx.prec = 320
WB = acb(arb(-1) / 2, arb(3).sqrt() / 2)


def A(z):
    return acb(arb(z.a.numerator) / z.a.denominator) + acb(arb(z.b.numerator) / z.b.denominator) * WB


def R_(q):
    q = Fr(q)
    return acb(arb(q.numerator) / q.denominator)


def pw(d, e):
    if e == 0:
        return acb(1)
    if e.denominator == 1:
        return R_(d) ** int(e)
    return R_(d) ** (arb(e.numerator) / e.denominator)


def binom(c, e, N):
    out = [Fr(1)]
    for k in range(1, N + 1):
        out.append(out[-1] * (e - k + 1) / k * c)
    return out


def smul(a, b, N):
    return [sum((a[i] * b[k - i] for i in range(k + 1)), Fr(0)) for k in range(N + 1)]


def zpow(k):
    v = ONE
    for _ in range(k % 6):
        v = v * Z6
    return v


def char_frac(lam):
    for k in range(6):
        if zpow(k) == lam:
            return Fr(k, 6)
    raise ValueError(lam)


def order(M):
    P = M
    for o in range(1, 50):
        if P == eye():
            return o
        P = mmul(P, M)
    raise ValueError


def joint_eig(mats):
    blocks = [eye()]
    for M in mats:
        o = order(M)
        assert 6 % o == 0
        new = []
        for P in blocks:
            for k in range(6):
                if (k * o) % 6:
                    continue  # zpow(k) not an o-th root of unity
                Pr = [[ZERO] * 4 for _ in range(4)]
                Mk = eye()
                for j in range(o):
                    c = zpow(-k * j)
                    Pr = [[Pr[r][s] + c * Mk[r][s] for s in range(4)] for r in range(4)]
                    Mk = mmul(Mk, M)
                Pr = [[x * QZ(Fr(1, o)) for x in row] for row in Pr]
                Q = mmul(Pr, P)
                if any(not x.iszero() for row in Q for x in row):
                    new.append(Q)
        blocks = new
    cols = []
    for P in blocks:
        cols += colbasis(P)
    assert len(cols) == 4
    return [[cols[j][i] for j in range(4)] for i in range(4)]


def dualm(g):
    return transpose(minv(g))


class Comp:
    def __init__(self, pts, mons, isnode, extra=()):
        self.pts, self.mons, self.isnode = pts, mons, isnode
        self.V = joint_eig(list(mons) + list(extra))
        self.Vi = minv(self.V)
        self.VD = transpose(self.Vi)  # dual basis vectors as columns
        self.a = [self.chars(M) for M in mons]

    def chars(self, M):
        D = mmul(mmul(self.Vi, M), self.V)
        assert all(D[i][j].iszero() for i in range(4) for j in range(4) if i != j)
        return [char_frac(D[k][k]) for k in range(4)]

    def exps(self, dual):
        E = []
        for j in range(len(self.pts)):
            row = []
            for k in range(4):
                a = self.a[j][k]
                if dual:
                    a = (1 - a) % 1
                row.append(a - 1 if a > 0 else (Fr(-1) if self.isnode[j] else Fr(0)))
            E.append(row)
        return E


gs = load_exact()
cl = [(0, 1), (2, 3), (5, 6), (7, 8), (10, 11)]
xs = [Fr(x, 7) for x in (-13, -9, -5, -2, 1, 4, 8, 12)]
ys = {ci: (Fr(-3 - ci, 5), Fr(2 + ci, 7)) for ci in range(5)}
z0 = min(xs) - 1
lam = {0: acb(1), 2: acb(arb(2) / 3, arb(1) / 3), 3: acb(arb(-1) / 5, arb(2) / 5), 4: acb(arb(3) / 4, arb(-1) / 4)}
NS = 3

P = eye()
for g in gs:
    P = mmul(P, g)
assert P == eye()
starts = {c[0]: ci for ci, c in enumerate(cl)}
mons, isnode, node_of = [], [], {}
i = 0
while i < 13:
    if i in starts:
        node_of[starts[i]] = len(mons)
        mons.append(mmul(gs[i], gs[i + 1]))
        isnode.append(True)
        i += 2
    else:
        mons.append(gs[i])
        isnode.append(False)
        i += 1
for X in mons:
    for Y in mons:
        assert mmul(X, Y) == mmul(Y, X)
p0 = Comp(xs, mons, isnode)
comps, nonabelian = {}, []
for ci, (a, b) in enumerate(cl):
    ga, gb = gs[a], gs[b]
    if mmul(ga, gb) == mmul(gb, ga):
        hinv = minv(mmul(ga, gb))
        cp = Comp(list(ys[ci]), [ga, gb], [False, False], extra=[hinv])
        cp.ainf = cp.chars(hinv)
        comps[ci] = cp
    else:
        nonabelian.append(ci)
CLNAME = ["{%d,%d}" % (a + 1, b + 1) for a, b in cl]
print("trivial clusters", [CLNAME[ci] for ci in comps], "non-abelian cluster", [CLNAME[ci] for ci in nonabelian])
print("special points of P0, j = 0..7:", ["{1,2}", "{3,4}", "x5", "{6,7}", "{8,9}", "x10", "{11,12}", "x13"], "; ('R', j), ('T', j): node and residue columns at j; ('F', 0) = Xi_k")
assert sorted(comps) == [0, 2, 3, 4] and nonabelian == [1]


def basis_forms(c, dual):
    E = c.exps(dual)
    out = []
    for k in range(4):
        D = -2 - sum(E[j][k] for j in range(len(c.pts)))
        assert D.denominator == 1
        out += [(k, [E[j][k] for j in range(len(c.pts))], m) for m in range(int(D) + 1)]
    return out


def comp_forms(cp, dual):
    E = cp.exps(dual)
    out = []
    for k in range(4):
        c = cp.ainf[k]
        if dual:
            c = (1 - c) % 1
        bmin = c - 1 if c > 0 else Fr(-1)
        M = -E[0][k] - E[1][k] - 2 - bmin
        assert M.denominator == 1
        out += [(k, [E[0][k], E[1][k]], m) for m in range(int(M) + 1)]
    return out


def local_series(c, f, j, N=NS):
    k, es, m = f
    p = c.pts[j]
    c0 = acb(1)
    ser = [Fr(1)] + [Fr(0)] * N
    for i_, q in enumerate(c.pts):
        if i_ == j:
            continue
        c0 *= pw(p - q, es[i_])
        ser = smul(ser, binom(1 / (p - q), es[i_], N), N)
    if m:
        c0 *= pw(p - z0, Fr(m))
        ser = smul(ser, binom(1 / (p - z0), Fr(m), N), N)
    return es[j], [c0 * R_(s) for s in ser]


def comp_inf_series(c, f, N=NS):
    k, es, m = f
    beta = -sum(es) - m - 2
    ser = [Fr(-1)] + [Fr(0)] * N
    for i_, q in enumerate(c.pts):
        ser = smul(ser, binom(-q, es[i_], N), N)
    if m:
        ser = smul(ser, binom(-z0, Fr(m), N), N)
    return beta, [R_(s) for s in ser]


def allowance_ann(h, gens):
    """rows q (exact) with q.r = 0 <=> r in Fix(h) cap sum Im(g - 1)."""
    cols = []
    for g in gens:
        D = msub(g, eye())
        cols += [[D[r][c] for r in range(4)] for c in range(4)]
    M = [[cols[c][r] for c in range(len(cols))] for r in range(4)]
    im = colbasis(M)
    if not im:
        return eye()
    IM = [[im[c][r] for c in range(len(im))] for r in range(4)]
    HI = mmul(msub(h, eye()), IM)
    N = nullbasis(HI, len(im))
    Avecs = [[sum((IM[r][c] * v[c] for c in range(len(im))), ZERO) for r in range(4)] for v in N]
    if not Avecs:
        return eye()
    return nullbasis(Avecs, 4)


def pick_pivots(Mnp, r):
    """greedy column pivots (Gram-Schmidt) for a numeric complex matrix."""
    M = Mnp.copy()
    piv = []
    for _ in range(r):
        norms = np.linalg.norm(M, axis=0)
        norms[piv] = -1
        c = int(np.argmax(norms))
        piv.append(c)
        q = M[:, c] / np.linalg.norm(M[:, c])
        M = M - np.outer(q, q.conj() @ M)
    return piv


def tonp(rows):
    return np.array([[complex(float(x.real.mid()), float(x.imag.mid())) for x in r] for r in rows])


def build(dual):
    Vv = p0.VD if dual else p0.V
    unk = [('P0', f) for f in basis_forms(p0, dual)]
    for ci, cp in comps.items():
        unk += [(ci, f) for f in comp_forms(cp, dual)]
    cons = []
    for ci in range(len(cl)):
        j = node_of[ci]
        res = []
        for kind, f in unk:
            v = [acb(0)] * 4
            if kind == 'P0' and f[1][j] == -1:
                _, c = local_series(p0, f, j, 0)
                v = [c[0] * A(Vv[r][f[0]]) for r in range(4)]
            elif kind == ci:
                cp = comps[ci]
                LV = cp.VD if dual else cp.V
                beta, c = comp_inf_series(cp, f, 0)
                if beta == -1:
                    v = [c[0] * A(LV[r][f[0]]) for r in range(4)]
            res.append(v)
        if ci in comps:
            cons += [[res[u][r] for u in range(len(unk))] for r in range(4)]
        else:
            a, b = cl[ci]
            g = [gs[a], gs[b]]
            h = mmul(g[0], g[1])
            if dual:
                g, h = [dualm(x) for x in g], dualm(h)
            Q = allowance_ann(h, g)
            print("dual" if dual else "L   ", "Fix(gamma_3 gamma_4) cap (Im(gamma_3 - 1) + Im(gamma_4 - 1)) = 0, allowed residues 0 at the node of {3,4}:", len(Q) == 4)
            assert len(Q) == 4
            for q in Q:
                cons.append([sum((A(q[r]) * res[u][r] for r in range(4)), acb(0)) if unk[u][0] == 'P0' else acb(0)
                             for u in range(len(unk))])
    nu = len(unk)
    rk = nu - 3  # dim F^1 = 3 (Section 6.3)
    Cn = tonp(cons)
    print("nan entries", np.isnan(Cn).sum(), "shape", Cn.shape, "maxabs", np.nanmax(np.abs(Cn)))
    sv = np.linalg.svd(Cn, compute_uv=False)
    print("dual" if dual else "L   ", "unknowns", nu, "constraints", len(cons), "numeric sv around rank:", sv[rk - 1], sv[rk] if rk < len(sv) else 0.0)
    assert (nu, len(cons), rk) == (21, 20, 18)
    pc = pick_pivots(Cn, rk)
    pr = pick_pivots(Cn[:, pc].T.copy(), rk)
    free = [u for u in range(nu) if u not in pc]
    Csub = acb_mat([[cons[r][c] for c in pc] for r in pr])
    d = Csub.det()
    assert not d.contains(0), "pivot minor not certified"
    basis = []
    for f in free:
        rhs = acb_mat([[-cons[r][f]] for r in pr])
        x = Csub.solve(rhs)
        coef = [acb(0)] * nu
        coef[f] = acb(1)
        for t, c in enumerate(pc):
            coef[c] = x[t, 0]
        basis.append(coef)
    data = []
    for coef in basis:
        loc = {}
        for j in range(len(p0.pts)):
            lines = {}
            for (kind, f), cf in zip(unk, coef):
                if kind != 'P0' or (cf.real == 0 and cf.imag == 0):
                    continue
                e, c = local_series(p0, f, j)
                lines.setdefault(f[0], [e, [acb(0)] * (NS + 1)])
                lines[f[0]][1] = [x_ + cf * y_ for x_, y_ in zip(lines[f[0]][1], c)]
            loc[('P0', j)] = lines
        for ci, cp in comps.items():
            lines = {}
            for (kind, f), cf in zip(unk, coef):
                if kind != ci or (cf.real == 0 and cf.imag == 0):
                    continue
                beta, c = comp_inf_series(cp, f)
                lines.setdefault(f[0], [beta, [acb(0)] * (NS + 1)])
                lines[f[0]][1] = [x_ + cf * y_ for x_, y_ in zip(lines[f[0]][1], c)]
            loc[('comp', ci)] = lines
        data.append(loc)
    return data


def vec_at(loc, key, beta, dual):
    if key[0] == 'P0':
        Vv = p0.VD if dual else p0.V
    else:
        cp = comps[key[1]]
        Vv = cp.VD if dual else cp.V
    out = [acb(0)] * 4
    for k, (e, c) in loc[key].items():
        d = beta - e
        if d.denominator == 1 and 0 <= d <= NS:
            out = [out[r] + c[int(d)] * A(Vv[r][k]) for r in range(4)]
    return out


def dot(u, v):
    return sum((a * b for a, b in zip(u, v)), acb(0))


F, G = build(False), build(True)
rows = [(a, b) for a in range(3) for b in range(3)]
cols, names = [], []
for j in range(8):
    Rc, Tc = [], []
    for a, b in rows:
        la, lb = F[a][('P0', j)], G[b][('P0', j)]
        rr, tt = acb(0), acb(0)
        for k in set(la) & set(lb):
            e1, c1 = la[k]
            e2, c2 = lb[k]
            s = e1 + e2
            if s == -2:
                rr += c1[0] * c2[0]
                tt += c1[0] * c2[1] + c1[1] * c2[0]
            elif s == -1:
                tt += c1[0] * c2[0]
        Rc.append(rr)
        Tc.append(tt)
    if isnode[j]:
        cols.append(Rc)
        names.append(('R', j))
    cols.append(Tc)
    names.append(('T', j))
Ecol = {}
for ci in comps:
    j = node_of[ci]
    m = order(mons[j])
    bs = Fr(1, m) - 1
    Ecol[ci] = [dot(vec_at(F[a], ('P0', j), bs, False), vec_at(G[b], ('comp', ci), bs, True)) +
                dot(vec_at(F[a], ('comp', ci), bs, False), vec_at(G[b], ('P0', j), bs, True)) for a, b in rows]
# The node columns R of the trivial clusters have rank at most 3 by (6.6) and Lemma 6.4; the certified 3x3 minor makes it exactly 3, so the relation is unique up to scale.
triv = sorted(comps)
Rex = [cols[names.index(('R', node_of[ci]))] for ci in triv]
Rnp = tonp([[Rex[t][i] for t in range(len(triv))] for i in range(9)])
print("numeric sv of the node columns R of the trivial clusters:", np.linalg.svd(Rnp, compute_uv=False))
pc = pick_pivots(Rnp, 3)
dep = [t for t in range(len(triv)) if t not in pc][0]
pr = pick_pivots(Rnp[:, pc].T.copy(), 3)
Msub = acb_mat([[Rex[t][i] for t in pc] for i in pr])
print("3x3 minor of the node columns R of the trivial clusters:", Msub.det())
assert not Msub.det().contains(0)
x = Msub.solve(acb_mat([[-Rex[dep][i]] for i in pr]))
c = {triv[dep]: acb(1)}
for s, t in enumerate(pc):
    c[triv[t]] = x[s, 0]
Fcol = [sum((c[ci] * lam[ci] * Ecol[ci][i] for ci in triv), acb(0)) for i in range(9)]
allc = cols + [Fcol]
allnames = names + [('F', 0)]
Mnp = tonp([[allc[t][i] for t in range(len(allc))] for i in range(9)])
print("numeric sv full:", np.linalg.svd(Mnp, compute_uv=False))
sel = pick_pivots(Mnp, 9)
M9 = acb_mat([[allc[t][i] for t in sel] for i in range(9)])
det = M9.det()
print("selected columns:", [allnames[t] for t in sel])
chosen = {allnames[t] for t in sel}
# M* has node columns R only for the trivial clusters other than {8,9}; Proposition 6.8 names the nine columns.
assert ('R', node_of[3]) not in chosen and ('R', node_of[1]) not in chosen
assert chosen == {('T', j) for j in range(1, 7)} | {('R', node_of[2]), ('R', node_of[4]), ('F', 0)}
print("det of 9x9 minor:", det)
print("CERTIFIED rank >= 9:", not det.contains(0))
assert not det.contains(0)
# (6.9) quotes the decimal balls printed above, which contain the computed ball.
(re_, rr), (im_, ri) = [(float(m), float(r)) for m, r in re.findall(r'\[(\S+) \+/- ([^\]]+)\]', str(det))]
print("printed radii of the real and imaginary parts:", rr, ri, "; modulus of the error below 6e-106:", (rr * rr + ri * ri) ** 0.5 < 6e-106)
assert 2.6207710e-29 <= re_ < 2.6207711e-29 and -2.9287923e-29 < im_ <= -2.9287922e-29
assert rr < 3.7e-106 and ri < 4.6e-106 and (rr * rr + ri * ri) ** 0.5 < 6e-106
cc = [c[ci] for ci in triv]
print("k for nodes (1,2),(6,7),(8,9),(11,12), normalized at (8,9):", [str(z) for z in cc][:4])
assert triv == [0, 2, 3, 4] and triv[dep] == 3
for z, target in zip(cc, (0, -1, 1, 0)):
    assert z.contains(target) and float(z.real.rad()) < 2e-82 and float(z.imag.rad()) < 2e-82
