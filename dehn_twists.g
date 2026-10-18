# Equation (6.6), Section 6.2 and Appendix A (The Dehn twists), in exact arithmetic: for each of the five clusters {j,j+1} of the tuple gamma of Appendix B, the smallest power sigma_j^k that fixes gamma, its matrix A on H^1_par and N = A^o - 1 for the smallest o >= 1 with (A^o - 1)^2 = 0; for the four trivial clusters k = 2, o = 1 and N has rank 1, and the four N span a space of dimension 3 over K with the single relation N_(6,7) = N_(8,9).
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
Bb := BaseMat(B); H1 := [];
for z in Zc do if RankMat(Concatenation(Bb, H1, [z])) > Length(Bb) + Length(H1) then Add(H1, z); fi; od;
d := Length(H1); Print("dim H1par = ", d, "\n");
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

Ns := [];
Ks := []; Os := []; Ranks := [];
for c in clusters do
  j := c[1]; st := [T, H1]; k := 0;
  repeat st := Sg(st, j, 1); k := k + 1; until st[1] = T;
  A := TransposedMat(List(st[2], coords));
  o := 1; while not IsZero((A^o - IdentityMat(d))^2) do o := o + 1; if o > 100 then Error("no unipotent power"); fi; od;
  Nn := A^o - IdentityMat(d);
  Print("cluster ", c, ": sigma^", k, " restores tuple; o = ", o, "; rank N = ", RankMat(Nn), "\n");
  Add(Ks, k); Add(Os, o); Add(Ranks, RankMat(Nn));
  if RankMat(Nn) > 0 then Add(Ns, Flat(Nn)); fi;
od;
Assert(0, Ks{[1,3,4,5]} = [2,2,2,2] and Os{[1,3,4,5]} = [1,1,1,1] and Ranks{[1,3,4,5]} = [1,1,1,1] and Length(Ns) = 4);
Print("exact span{N} = ", RankMat(Ns), "\n");
rel := NullspaceMat(Ns); Print("relation among N of clusters (1,2),(6,7),(8,9),(11,12): ", rel, "\n");
Assert(0, RankMat(Ns) = 3 and Length(rel) = 1 and rel[1][1] = 0 and rel[1][4] = 0 and rel[1][2] = -rel[1][3] and rel[1][2] <> 0);
QUIT;
