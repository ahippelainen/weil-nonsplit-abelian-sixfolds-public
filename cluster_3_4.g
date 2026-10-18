# Sections 6.1 and 6.3 and Appendix A, for the tuple gamma of Appendix B: gamma_1 gamma_2 = gamma_6 gamma_7 = gamma_8 gamma_9 = gamma_11 gamma_12 = 1, gamma_3 and gamma_4 do not commute and gamma_3 gamma_4 has order 6, and the eight monodromies on P_0 commute; on the component of the cluster {3,4}, rk(g_3 - 1) = rk(g_4 - 1) = 1 and dim Fix<g_3, g_4> = 2 both for g_i = gamma_i and for the inverse transposes, so that the cocycles modulo coboundaries vanish; and Fix(gamma_3 gamma_4) cap (Im(gamma_3 - 1) + Im(gamma_4 - 1)) = 0, also for the inverse transposes.
Read("tuple.g");
t := gamma; n := Length(t); I4 := IdentityMat(4, CF(3));
Print("n=", n, " product=1: ", Product(t) = I4, "\n");
G := Group(t); Print("|G|=", Size(G), "\n");
Print("rank(g-1): ", List(t, g -> RankMat(g - I4)), " orders ", List(t, Order), "\n");
for c in clusters do Print(c, " prod order ", Order(t[c[1]]*t[c[2]]), " commute ", t[c[1]]*t[c[2]] = t[c[2]]*t[c[1]], "\n"); od;
Assert(0, ForAll([1,6,8,11], i -> t[i]*t[i+1] = I4) and Order(t[3]*t[4]) = 6 and t[3]*t[4] <> t[4]*t[3]);
mP0 := [t[1]*t[2], t[3]*t[4], t[5], t[6]*t[7], t[8]*t[9], t[10], t[11]*t[12], t[13]];
Print("P0 monodromies commute: ", ForAll(mP0, a -> ForAll(mP0, b -> a*b = b*a)), " P0 product=1 ", Product(mP0) = I4, "\n");
Assert(0, ForAll(mP0, a -> ForAll(mP0, b -> a*b = b*a)));
g3 := t[3]; g4 := t[4]; h := g3*g4;
d := g -> TransposedMat(g^-1);
for side in [["gamma", g3, g4], ["inverse transpose", d(g3), d(g4)]] do
  ra := RankMat(side[2] - I4); rb := RankMat(side[3] - I4);
  fab := 4 - RankMat(Concatenation(side[2] - I4, side[3] - I4));
  Print(side[1], ": rk(g3-1), rk(g4-1), dim Fix<g3,g4> = ", [ra, rb, fab], "; cocycles mod coboundaries: ", ra + rb - (4 - fab), "\n");
  Assert(0, [ra, rb, fab] = [1, 1, 2] and ra + rb - (4 - fab) = 0);
od;
B3 := BaseMat(TransposedMat(g3 - I4)); B4 := BaseMat(TransposedMat(g4 - I4));
Imsum := BaseMat(Concatenation(B3, B4));
Fh := NullspaceMat(TransposedMat(h - I4));
Print("dim Fix(h)=", Length(Fh), " dim Imsum=", Length(Imsum), " dim intersection=", Length(SumIntersectionMat(Fh, Imsum)[2]), "\n");
Fhd := NullspaceMat(TransposedMat(d(h) - I4)); Imd := BaseMat(Concatenation(TransposedMat(d(g3)-I4), TransposedMat(d(g4)-I4)));
Print("inverse transpose: dim intersection=", Length(SumIntersectionMat(Fhd, Imd)[2]), "\n");
Assert(0, Length(SumIntersectionMat(Fh, Imsum)[2]) = 0 and Length(SumIntersectionMat(Fhd, Imd)[2]) = 0);
QUIT;
