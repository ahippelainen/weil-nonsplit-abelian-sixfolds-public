# Section 3 and Appendix A (The group and the tuple): G32, built from four reflections of order 3, has order 155520; the tuple gamma of Appendix B lies in it, generates it and has product 1; gamma_1, ..., gamma_12 are reflections of order 3 in the two conjugacy classes of size 40, of determinant zeta^2 = E(3) exactly for i in {2,3,4,7,8,12}, and gamma_13 is an involution of determinant 1 with rk(gamma_13 - 1) = 2 in the class of size 90.
Read("tuple.g");
Refl := function(a, z)   # r = I + (z-1) a a^* / (a^* a)
  local n, ab, i, j, M, nrm;
  n := Length(a); ab := List(a, x -> GaloisCyc(x, -1));
  nrm := a*ab;
  M := List([1..n], i -> List([1..n], j -> (z-1)*a[i]*ab[j]/nrm));
  return IdentityMat(n) + M;
end;
w := E(3); s3 := E(3)-E(3)^2;  # sqrt(-3)
ip := function(a,b) return a*List(b, x->GaloisCyc(x,-1)); end;
c2 := function(a,b) local x; x := ip(a,b); return x*GaloisCyc(x,-1)/(ip(a,a)*ip(b,b)); end;
A1 := [1,0,0,0]; A2 := [1,1,1,0]; A3 := [0,1,s3,0];
ents := [0,1,-1,w,-w,w^2,-w^2,s3,-s3];
A4 := First(Tuples(ents,4), a -> a[4]<>0 and ip(a,A1)=0 and ip(a,A2)=0 and c2(a,A3)=1/3);
Print("A4 ", A4, "\n");
gens := List([A1,A2,A3,A4], a -> Refl(a, w));
Assert(0, ForAll(gens, g -> Order(g) = 3 and RankMat(g - g^0) = 1));
G32 := Group(gens);
Print("|G32| = ", Size(G32), "\n");
Assert(0, Size(G32) = 155520);
cls := ConjugacyClasses(G32);
Print("product = 1: ", Product(gamma) = gamma[1]^0, "\n");
Print("all in G32: ", ForAll(gamma, x -> x in G32), "  |<tuple>| = ", Size(Group(gamma)), "\n");
Assert(0, Product(gamma) = gamma[1]^0 and ForAll(gamma, x -> x in G32) and Size(Group(gamma)) = 155520);
Print("class sizes/orders/rank(g-1)/det: ", Collected(List(gamma, x -> [Order(x), Size(First(cls, c -> x in c)), RankMat(x - x^0), DeterminantMat(x)])), "\n");
data := List(gamma, x -> [Order(x), RankMat(x - x^0), DeterminantMat(x), PositionProperty(cls, c -> x in c)]);
Print("per entry [order, rk(g-1), det, class size]: ", List(data, e -> [e[1], e[2], e[3], Size(cls[e[4]])]), "\n");
Assert(0, ForAll([1..12], i -> data[i]{[1,2]} = [3, 1] and Size(cls[data[i][4]]) = 40));
Assert(0, Filtered([1..12], i -> data[i][3] = E(3)) = [2,3,4,7,8,12] and ForAll([1..12], i -> data[i][3] in [E(3), E(3)^2]));
Assert(0, Length(Set(data{[1..12]}, e -> e[4])) = 2 and ForAll([1..12], i -> ForAll([1..12], j -> (data[i][4] = data[j][4]) = (data[i][3] = data[j][3]))));
Assert(0, data[13]{[1,2,3]} = [2, 2, 1] and Size(cls[data[13][4]]) = 90);
QUIT;
