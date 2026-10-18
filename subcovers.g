# Section 5.1, Table 2 and Appendix A (The characters, The subcovers): Z(G) is cyclic of order 6, and exactly fourteen irreducible characters have the central character chi_rho of rho; their degrees, dim M by (2.2), the two numbers (2.3) and chi(gamma_1) = a + b zeta^2, written as [a, b]. Then all pairs (H, psi), H >= Z(G) up to conjugacy and psi linear with psi|Z(G) = chi_rho, each with |H|, [G:H], m = ord psi, v_{H,psi} (14 multiplicities), the exponents at the branch points of X = C/ker psi -> Y = C/H, g(Y) by Riemann-Hurwitz from the coset action, dim W_{H,psi} and its h^{1,0}. Written to subcovers.out, which relation.py reads.
Read("tuple.g"); T := gamma; r := Length(T);
Gm := Group(T); iso := IsomorphismPermGroup(Gm); G := Image(iso);
Tg := List(T, x -> Image(iso, x));
Print("prod=1: ", Product(Tg) = One(G), " |G|=", Size(G), "\n");
Assert(0, Product(Tg) = One(G) and Size(G) = 155520);
ZZ := Centre(G);
Print("Z(G): order ", Size(ZZ), ", cyclic ", IsCyclic(ZZ), "\n");
Assert(0, Size(ZZ) = 6 and IsCyclic(ZZ));
z0 := First(Elements(ZZ), z -> Order(z) = 6);
lamOf := z -> PreImagesRepresentative(iso, z)[1][1];
lam := lamOf(z0);
ct := CharacterTable(G); irr := Irr(ct);
chirho := ClassFunction(ct, List(ConjugacyClasses(ct), c -> TraceMat(PreImagesRepresentative(iso, Representative(c)))));
irho := Position(irr, chirho);
same := Filtered([1..Length(irr)], i -> z0^irr[i] = lam * irr[i][1]);
Print("index of rho ", irho, " ; #irreducibles with central character chi_rho ", Length(same), " degrees ", List(same, i -> irr[i][1]), "\n");
Assert(0, Length(same) = 14 and irho in same);
eig := function(chi, g) local e; e := Order(g);
  return List([0..e-1], a -> Sum([0..e-1], k -> (g^k)^chi * E(e)^(-a*k)) / e); end;
CW := function(chi) local d, p, q, g, e, N, a;
  d := chi[1]; p := -d; q := -d;
  for g in Tg do e := Order(g); N := eig(chi, g);
    for a in [1..e-1] do p := p + N[a+1]*a/e; q := q + N[a+1]*(1 - a/e); od; od;
  return [p, q]; end;
pq := List(same, i -> CW(irr[i]));
Print("CW (p,q) per rho': ", pq, "\n");
dimM := List(same, i -> (r-2)*irr[i][1] - Sum(Tg, g -> eig(irr[i], g)[1]));
Print("dim M by (2.2): ", dimM, "\n");
Assert(0, ForAll([1..14], k -> pq[k][1] = pq[k][2] and pq[k][1] + pq[k][2] = dimM[k]));
Kab := x -> [x - (x - GaloisCyc(x, -1))/(E(3) - E(3)^2)*E(3), (x - GaloisCyc(x, -1))/(E(3) - E(3)^2)];
chi1 := List(same, i -> Kab(Tg[1]^irr[i]));
Print("chi(gamma_1) as [a, b], a + b zeta^2: ", chi1, "\n");
Assert(0, ForAll(Flat(chi1), IsRat));
nat := NaturalHomomorphismByNormalSubgroup(G, ZZ);
reps := List(ConjugacyClassesSubgroups(Image(nat)), Representative);
Print("#classes of subgroups H >= Z(G): ", Length(reps), "\n");
# bind the globals that functions inside the loop refer to, so that GAP does not warn about unbound globals
H := 0; m := 0; psi := 0; ctH := 0; v := 0;
out := [];
for Hb in reps do
  H := PreImage(nat, Hb);
  n := Index(G, H);
  act := FactorCosetAction(G, H);   # right cosets, point 1 = H
  pts := [1..n];
  stabs := []; ramsum := 0;
  for i in [1..r] do
    cyc := Cycles(Image(act, Tg[i]), pts);
    ramsum := ramsum + Sum(cyc, c -> Length(c) - 1);
    for c in cyc do
      x := RepresentativeAction(Image(act), 1, c[1]);
      x := PreImagesRepresentative(act, x);
      h := x * Tg[i]^Length(c) * x^-1;
      if not h in H then Error("stabilizer element not in H"); fi;
      Add(stabs, [i, h]);
    od;
  od;
  gY := 1 - n + ramsum/2;
  ctH := CharacterTable(H);
  lin := Filtered(Irr(ctH), c -> c[1] = 1 and ForAll(GeneratorsOfGroup(ZZ), z -> z^c = lamOf(z)));
  for psi in lin do
    m := Order(psi);
    ex := List(stabs, ih -> [ih[1], First([0..m-1], a -> E(m)^a = ih[2]^psi)]);
    v := List(same, i -> ScalarProduct(ctH, RestrictedClassFunction(irr[i], H), psi));
    dimW := Sum([1..Length(same)], j -> v[j]*(pq[j][1] + pq[j][2]));
    h10 := Sum([1..Length(same)], j -> v[j]*pq[j][1]);
    Add(out, [Size(H), Index(G,H), m, v, Filtered(ex, p -> p[2] <> 0), gY, dimW, h10]);
  od;
od;
PrintTo("subcovers.out", "rhopos:=", Position(same, irho), ";\ndeg:=", List(same, i -> irr[i][1]), ";\ndimM:=", dimM, ";\nchi1:=", chi1, ";\npq:=", pq, ";\nP:=", out, ";\n");
Print("#pairs (H,psi) ", Length(out), "\n");
QUIT;
