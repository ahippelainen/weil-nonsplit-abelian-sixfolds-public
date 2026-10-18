# Appendix A (The subcovers), second enumeration: the pairs (H, psi), H >= Z(G) up to conjugacy and psi linear with psi|Z(G) = chi_rho, with |H| among the eleven orders of Table 1, computed in another way than in subcovers.g: psi from the abelianization of H, v_{H,psi} from explicit class sums, the exponents and g(C/H) from the double cosets H\G/<gamma_i>. Also the degrees, dim M by (2.2), the two numbers (2.3) and chi(gamma_1) of the fourteen irreducible characters with central character chi_rho; relation.py identifies this run's numbering with that of Table 2 through dim M and checks the identification against the degrees and chi(gamma_1). Written to subcovers_double_cosets.out, which relation.py reads.
Read("tuple.g"); T := gamma; r := Length(T);
Gm := Group(T); iso := IsomorphismPermGroup(Gm); G := Image(iso);
Tg := List(T, x -> Image(iso, x));
Print("prod=1: ", Product(Tg) = One(G), " |G|=", Size(G), "\n");
ZZ := Centre(G); z0 := First(Elements(ZZ), z -> Order(z) = 6);
lam := PreImagesRepresentative(iso, z0)[1][1];
ct := CharacterTable(G); irr := Irr(ct);
chirho := ClassFunction(ct, List(ConjugacyClasses(ct), c -> TraceMat(PreImagesRepresentative(iso, Representative(c)))));
same := Filtered([1..Length(irr)], i -> z0^irr[i] = lam * irr[i][1]);
irho := Position(same, Position(irr, chirho));
Assert(0, Length(same) = 14 and irho <> fail);
CWp := function(chi) local p, q, g, e, a, N;
  p := -chi[1]; q := -chi[1];
  for g in Tg do e := Order(g);
    for a in [1..e-1] do
      N := Sum([0..e-1], k -> (g^k)^chi * E(e)^(-a*k)) / e;
      p := p + N*a/e; q := q + N*(1 - a/e);
    od;
  od; return [p, q]; end;
pq := List(same, i -> CWp(irr[i]));
dimM := List(same, i -> (r-2)*irr[i][1] - Sum(Tg, g -> Sum([0..Order(g)-1], k -> (g^k)^irr[i]) / Order(g)));
Kab := x -> [x - (x - GaloisCyc(x, -1))/(E(3) - E(3)^2)*E(3), (x - GaloisCyc(x, -1))/(E(3) - E(3)^2)];
chi1 := List(same, i -> Kab(Tg[1]^irr[i]));
Assert(0, ForAll(Flat(chi1), IsRat));
nat := NaturalHomomorphismByNormalSubgroup(G, ZZ);
reps := List(ConjugacyClassesSubgroups(Image(nat)), Representative);
# bind the globals that functions inside the loop refer to, so that GAP does not warn about unbound globals
H := 0; al := 0; A := 0; coords := 0; ords := 0; i := 0; x := 0; creps := 0; csz := 0; fus := 0; pc := 0; psv := 0; psi := 0; m := 0;
out := [];
SIZES := [432, 486, 324, 288, 216, 144, 120, 108, 3888, 72, 972];
for Hb in reps do
  if not 6*Size(Hb) in SIZES then continue; fi;
  H := PreImage(nat, Hb); n := Index(G, H);
  al := MaximalAbelianQuotient(H); A := Image(al);
  gens := IndependentGeneratorsOfAbelianGroup(A); ords := List(gens, Order);
  coords := k -> IndependentGeneratorExponents(A, Image(al, k));
  ctH := CharacterTable(H); clH := ConjugacyClasses(ctH); fus := FusionConjugacyClasses(ctH, ct);
  creps := List(clH, Representative); csz := List(clH, Size);
  ccr := List(creps, coords);
  loc := []; ramsum := 0;
  for i in [1..r] do
    Ci := Group(Tg[i]); e := Order(Tg[i]);
    for dc in DoubleCosets(G, H, Ci) do
      x := Representative(dc);
      l := First([1..e], l -> x * Tg[i]^l * x^-1 in H);
      if l <> Size(dc)/Size(H) then Error("orbit length"); fi;
      ramsum := ramsum + l - 1;
      Add(loc, [i, x * Tg[i]^l * x^-1]);
    od;
  od;
  gY := 1 - n + ramsum/2;
  zc := coords(z0);
  for ex in Cartesian(List(ords, o -> [0..o-1])) do
    psv := cc -> Product([1..Length(ords)], j -> E(ords[j])^(ex[j]*cc[j]));
    psi := k -> psv(coords(k));
    if psi(z0) <> lam then continue; fi;
    m := Lcm(List([1..Length(ords)], j -> ords[j] / Gcd(ords[j], ex[j])));
    pc := List(ccr, cc -> ComplexConjugate(psv(cc)));
    v := List(same, i -> Sum([1..Length(creps)], c -> csz[c] * irr[i][fus[c]] * pc[c]) / Size(H));
    exps := List(loc, ih -> First([0..m-1], a -> E(m)^a = psi(ih[2])));
    exps := Filtered(exps, a -> a <> 0);
    Add(out, [Size(H), m, v, Collected(exps), gY]);
  od;
od;
PrintTo("subcovers_double_cosets.out",
  "rhopos:=", irho, ";\ndeg:=", List(same, i -> irr[i][1]), ";\ndimM:=", dimM, ";\nchi1:=", chi1, ";\npq:=", pq, ";\nP:=", out, ";\n");
Print("#pairs (H,psi) ", Length(out), " index of rho ", irho, "\n");
QUIT;
