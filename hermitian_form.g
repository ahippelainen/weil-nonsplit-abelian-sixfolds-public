# Proposition 3.2 and Appendix A (The determinant): the commutant of the tuple gamma of Appendix B consists of scalars; the parabolic cocycles form a space of dimension 10, the coboundaries one of dimension 4, and H^1_par, a K-structure on M_{rho^vee} (Section 2.4), has dimension 6; for 67 braids, each checked to fix gamma, the matrices on H^1_par are all different from 1, and the sesquilinear forms invariant under them form a space of dimension 1 over K, spanned by a Hermitian form of signature (3,3) and determinant -128 = -2 * 8^2.
Read("tuple.g");
T := gamma; r := Length(T); n := 4; I4 := IdentityMat(n);
Print("product=1: ", Product(T) = I4, "\n");
G := Group(T);
Print("|<T>| = ", Size(G), "\n");
# absolute irreducibility: commutant of the tuple is scalars
eqs := [];
for g in T do
  for i in [1..n] do for j in [1..n] do
    v := List([1..n^2], k -> 0*E(3));
    for a in [1..n] do
      v[(i-1)*n+a] := v[(i-1)*n+a] + g[a][j];   # (X g)_{ij} = sum_a X_{ia} g_{aj}
      v[(a-1)*n+j] := v[(a-1)*n+j] - g[i][a];   # (g X)_{ij} = sum_a g_{ia} X_{aj}
    od;
    Add(eqs, v);
  od; od;
od;
Print("commutant dim = ", n^2 - RankMat(eqs), "\n");
Assert(0, n^2 - RankMat(eqs) = 1);
cls := ConjugacyClasses(G);
Print("per entry [order, |class|, rk(g-1), det]: ",
  List(T, x -> [Order(x), Size(First(cls, c -> x in c)), RankMat(x - I4), DeterminantMat(x)]), "\n");
Print("reflections in G: ", Sum(Filtered(cls, c -> RankMat(Representative(c) - I4) = 1), Size), "\n");

# parabolic cocycles u = (u_1..u_r), u_i in Im(g_i - 1), sum_i g_1..g_{i-1} u_i = 0
pref := [I4]; for i in [1..r-1] do Add(pref, pref[i]*T[i]); od;
ims := List(T, g -> BaseMat(TransposedMat(g - I4)));   # basis of column space as rows
params := [];
for i in [1..r] do for b in ims[i] do
  v := List([1..n*r], k -> 0*E(3)); v{[(i-1)*n+1..i*n]} := b; Add(params, v);
od; od;
cond := List(params, p -> Sum([1..r], i -> pref[i]*p{[(i-1)*n+1..i*n]}));
ns := NullspaceMat(cond);
Zc := List(ns, c -> c*params);
B := List(IdentityMat(n), e -> Concatenation(List(T, g -> (g - I4)*e)));
Print("dim Zpar = ", Length(Zc), "  dim B = ", RankMat(B), "\n");
Assert(0, Length(Zc) = 10 and RankMat(B) = 4);
Bb := BaseMat(B); H1 := [];
for z in Zc do if RankMat(Concatenation(Bb, H1, [z])) > Length(Bb) + Length(H1) then Add(H1, z); fi; od;
d := Length(H1); Print("dim H1par = ", d, "\n");
Assert(0, d = 6);
full := Concatenation(H1, Bb);
coords := function(z) return SolutionMat(full, z){[1..d]}; end;

Sg := function(st, j, s)  # st = [tuple, cocycles]; braid generator sigma_j^{s}, s = +-1
  local t, a, b, nc, u, nc0, nc1;
  t := ShallowCopy(st[1]); a := t[j]; b := t[j+1];
  nc := [];
  for u in st[2] do
    u := ShallowCopy(u);
    if s = 1 then
      nc0 := u{[(j-1)*n+1..j*n]} + a*u{[j*n+1..(j+1)*n]} - a*b*a^-1*u{[(j-1)*n+1..j*n]};
      nc1 := u{[(j-1)*n+1..j*n]};
    else
      nc0 := u{[j*n+1..(j+1)*n]};
      nc1 := -b^-1*u{[j*n+1..(j+1)*n]} + b^-1*(u{[(j-1)*n+1..j*n]} + a*u{[j*n+1..(j+1)*n]});
    fi;
    u{[(j-1)*n+1..j*n]} := nc0; u{[j*n+1..(j+1)*n]} := nc1; Add(nc, u);
  od;
  if s = 1 then t[j] := a*b*a^-1; t[j+1] := a; else t[j] := b; t[j+1] := b^-1*a*b; fi;
  return [t, nc];
end;

mats := [];
Reset(GlobalMersenneTwister, 17);
trial := 0;
while Number(mats, A -> A <> IdentityMat(d)) < 80 and trial < 600 do
  trial := trial + 1;
  st := [T, H1];
  w := List([1..Random([10..40])], k -> [Random([1..r-1]), Random([1,-1])]);
  for m in w do st := Sg(st, m[1], m[2]); od;
  j := Random([1..r-1]); k := 0; st2 := st;
  repeat st2 := Sg(st2, j, 1); k := k + 1; until st2[1]{[j,j+1]} = st[1]{[j,j+1]};
  st := st2;
  for m in Reversed(w) do st := Sg(st, m[1], -m[2]); od;
  if st[1] <> T then Error("tuple not restored"); fi;
  A := TransposedMat(List(st[2], coords));   # columns = images of basis
  if A <> IdentityMat(d) then Add(mats, A); fi;
od;
Print("trials ", trial, "\n");
Print("monodromy matrices: ", Length(mats), ", nontrivial: ", Number(mats, A -> A <> IdentityMat(d)), "\n");
Assert(0, Length(mats) = 67 and ForAll(mats, A -> A <> IdentityMat(d)));
# sesquilinear invariant forms: A^* H A = H
cc := x -> GaloisCyc(x, -1);
star := A -> TransposedMat(List(A, row -> List(row, cc)));
eqs := [];
for A in mats do
  As := star(A);
  for i in [1..d] do for j in [1..d] do
    v := List([1..d^2], k -> 0*E(3));
    for a in [1..d] do for b in [1..d] do
      v[(a-1)*d+b] := v[(a-1)*d+b] + As[i][a]*A[b][j];
    od; od;
    v[(i-1)*d+j] := v[(i-1)*d+j] - 1;
    Add(eqs, v);
  od; od;
od;
sol := NullspaceMat(TransposedMat(eqs));
Print("dim invariant sesquilinear forms = ", Length(sol), "\n");
Assert(0, Length(sol) = 1);
H0 := List([1..d], i -> sol[1]{[(i-1)*d+1..i*d]});
if star(H0) + H0 <> 0*H0 then H := H0 + star(H0); else H := (E(3)-E(3)^2)*H0; fi;
Print("H Hermitian: ", star(H) = H, "\n");
dt := DeterminantMat(H); Print("det H = ", dt, "\n");
Assert(0, star(H) = H and dt = -128);
# signature by exact symmetric Gaussian elimination
M := List(H, ShallowCopy); sig := [0,0];
for i in [1..d] do
  if M[i][i] = 0 then
    p := First([i+1..d], j -> M[j][j] <> 0);
    if p <> fail then
      tmp := M[i]; M[i] := M[p]; M[p] := tmp;
      for row in M do tmp := row[i]; row[i] := row[p]; row[p] := tmp; od;
    else
      p := First([i+1..d], j -> M[j][i] <> 0);
      M[i] := M[i] + M[p]; for row in M do row[i] := row[i] + row[p]; od;
      if M[i][i] = 0 then  # try the other combination
        M[i] := M[i] + (E(3)-1)*M[p]; for row in M do row[i] := row[i] + cc(E(3)-1)*row[p]; od;
      fi;
    fi;
  fi;
  piv := M[i][i];
  if piv > 0 then sig[1] := sig[1]+1; else sig[2] := sig[2]+1; fi;
  for j in [i+1..d] do
    f := M[j][i]/piv;
    M[j] := M[j] - f*M[i];
    for row in M do row[j] := row[j] - cc(f)*row[i]; od;
  od;
od;
Print("signature (p,q) = ", sig, "\n");
Assert(0, sig = [3, 3]);
nd := -dt; Print("-det = ", nd, " factors ", Collected(Factors(NumeratorRat(nd)*DenominatorRat(nd))), "\n");
QUIT;
