intrinsic Genus(sigma::SeqEnum);
  {Compute genus from permutation triple}
  d := Degree(Parent(sigma[1]));
  // Riemann-Hurwitz formula
  g2 := -2*d + &+[&+[ e[2]*(e[1]-1) : e in CycleStructure(sigma[i])] : i in [1..3]];
  assert g2 mod 2 eq 0;
  g := (g2+2) div 2;
  return g;
end intrinsic;


/*B<i,j,ij> := QuaternionAlgebra(Rationals(),-3,2);
intrinsic OmodN(O::AlgQuatOrd,N::RngIntElt) //matmodq(u::AlgQuatElt);

  B<i,j,ij> := QuaternionAlgebra(Rationals(),-3,2);
  assert Discriminant(O) eq 6;
  assert Algebra(O) eq B;

  K<omega> := NumberField(Polynomial([1,1,1]));
  barK := hom<K -> K | Trace(K.1)-K.1>;
  s3 := 1+2*omega;
  S := Integers(K);

  p := 2;
  N := 2;
  SmodN, modN := quo<S | N>;
  bar := map<SmodN -> SmodN | x :-> modq(Trace(x@@modN)) - x>;
  OmodNx := sub<GL(2,SmodN) | [[[a,b],[2*bar(b),bar(a)]] : a,b in SmodN | IsUnit(a) ]>;

  // returns image in Omodqx;
  M2K := MatrixRing(K,2);
  mati := M2K![[s3,0],[0,barK(s3)]];
  matj := M2K![[0,1],[2,0]];
  useq := Eltseq(B!u);
  uK := Eltseq(useq[1]+useq[2]*mati+useq[3]*matj+useq[4]*mati*matj);
  return Omodqx![[modq(uK[1]),modq(uK[2])],[modq(uK[3]),modq(uK[4])]];
end intrinsic;*/

K<omega> := NumberField(Polynomial([1,1,1]));
barK := hom<K -> K | Trace(K.1)-K.1>;
s3 := 1+2*omega;
S := Integers(K);

p := 2;
q := 2;
Smodq, modq := quo<S | q>;
bar := map<Smodq -> Smodq | x :-> modq(Trace(x@@modq)) - x>;
Omodqx := sub<GL(2,Smodq) | [[[a,b],[2*bar(b),bar(a)]] : a,b in Smodq | IsUnit(a)]>;

B<i,j,ij> := QuaternionAlgebra(Rationals(),-3,2);
matmodq := function(u);
  // returns image in Oqx;
  M2K := MatrixRing(K,2);
  mati := M2K![[s3,0],[0,barK(s3)]];
  matj := M2K![[0,1],[2,0]];
  useq := Eltseq(B!u);
  uK := Eltseq(useq[1]+useq[2]*mati+useq[3]*matj+useq[4]*mati*matj);
  return Omodqx![[modq(uK[1]),modq(uK[2])],[modq(uK[3]),modq(uK[4])]];
end function;



mu := i*(2+j); assert mu^2 eq -6;
muj := mu*j/2;
matmuj := matmodq(muj);
AutmuO := AbelianGroup([2,2]);   // (1,0) = j, (0,1) = muj, (1,1) = mu
thetaj := hom<Omodqx -> Omodqx | 
             [[[bar((Omodqx.i)[1,1]),bar((Omodqx.i)[1,2])],[bar((Omodqx.i)[2,1]),bar((Omodqx.i)[2,2])]]
              : i in [1..#Generators(Omodqx)]]>;
thetamuj := hom<Omodqx -> Omodqx | [Omodqx.i^matmuj : i in [1..#Generators(Omodqx)]]>;
AutOmodqx := AutomorphismGroup(Omodqx);
theta := hom<AutmuO -> AutOmodqx | [AutOmodqx | thetaj,thetamuj]>;
G,iotaOmodqx,iotaAutmuO,proj := SemidirectProduct(Omodqx,AutmuO,theta);

omegaO := Eltseq(K!S.2)[1] + Eltseq(K!S.2)[2]*(-1+i)/2;
O := QuaternionOrder([1,omegaO,j,omegaO*j]);
delta2 := mu;
delta4 := 1 - i + 1/2*j - 1/2*ij;
delta6 := Conjugate(delta2*delta4);
eps := 1+j;
assert IsScalar(delta2*delta4*delta6) and IsScalar(delta2^2) and IsScalar(delta4^4) and IsScalar(delta6^6);

g2 := iotaAutmuO(AutmuO![1,1]);
g4 := iotaOmodqx(matmodq(delta4/j))*iotaAutmuO(AutmuO![1,0]);
g6 := iotaOmodqx(matmodq(delta6/(mu*j)))*iotaAutmuO(AutmuO![0,1]);
eps := iotaOmodqx(matmodq(eps));
G1 := sub<G | [g2,g4,g6,eps]>;

Gamma1, m1 := Group(FuchsianGroup(O));
// [piH(matmodq(Quaternion(m1(Gamma1.i)))) : i in [1..3]];

GL4red := function(g);
  nu := proj(g);
  alpha := (iotaAutmuO(nu)^-1*g)@@iotaOmodqx;
  assert iotaAutmuO(nu)*iotaOmodqx(alpha) eq g;

  a := alpha[1,1];
  assert alpha[2,2] eq bar(a);
  b := alpha[1,2];
  assert alpha[2,1] eq 2*bar(b);
  aSseq := Eltseq(S!(a@@modq));
  bSseq := Eltseq(S!(b@@modq));
  alphap := aSseq[1] + aSseq[2]*omegaO + (bSseq[1]+bSseq[2]*omegaO)*j;
  assert matmodq(alphap) eq alpha;
  alpha := alphap;
  
  nuseq := Eltseq(nu);
  if nuseq eq [0,0] then 
    nu := B!1;
  elif nuseq eq [1,0] then
    nu := j;
  elif nuseq eq [0,1] then
    nu := mu*j;
  else
    assert nuseq eq [1,1];
    nu := mu;
  end if;
  
  rowv := function(s);
    es := Eltseq(B!s);
    return Eltseq(modq(es[1]+es[2]*s3)) cat Eltseq(modq(es[3]+es[4]*s3));
  end function;
  return Matrix(Integers(q),[rowv(alpha),rowv(nu^(-1)*omegaO*nu*alpha),
                rowv(nu^(-1)*j*nu*alpha),rowv(nu^(-1)*(omegaO*j)*nu*alpha)]);
end function;

for i := 1 to 100 do
  g := Random(G); h := Random(G);
  assert GL4red(g*h) eq GL4red(g)*GL4red(h);
end for;

Uq, mq := UnitGroup(Integers(q));

print "#H | Index | #H meet O/N | Deg(L) | Genus | Torsion \n";
for Hrec in Subgroups(G) do
  // still have to think about a conjugate under Aut_mu(O)
  H := Hrec`subgroup;
  // if sub<Uq | [Determinant(GL4red(h))@@mq : h in Generators(H)]> ne Uq then continue; end if;    
  T := CosetTable(G,H);
  piH := CosetTableToRepresentation(G,T);
  sigma := [piH(g2),piH(g4),piH(g6)];
  fixsub := &meet[Kernel(GL4red(h)-1) : h in {Id(H)} join Generators(H)];
  abinvs := [];
  for i := 1 to Rank(fixsub) do
    j := 1; while (fixsub.i)[j] eq 0 do j +:= 1; end while;
    Append(~abinvs, q/Integers()!(fixsub.i)[j]);
  end for;
  // if 4 in abinvs then 
    print #H, Index(G,H), #(iotaOmodqx(Omodqx) meet H), #proj(H), Genus(sigma), abinvs, sprint(sigma);
  // end if;
end for;


/*
for a,b,c,d in [-10..10] do
del := a+b*(1+i)/2+c*j+d*(1+i)/2*j;
if del^4 eq -4 and IsScalar((mu*del)^6) and not IsScalar((mu*del)^3) and not IsScalar((mu*del)^2) then
print del;
end if;
end for;
*/
