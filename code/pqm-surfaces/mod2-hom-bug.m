Rx<x>:=PolynomialRing(Rationals());
//this one actually works
f:=-x^5+4*x^4-10*x^3+8*x^2-2*x;
prec:=30;
CC:=ComplexField(prec);
//f:= 3*x^5 + 3*x^4 - 4*x^3 + 3*x - 1;this returns a map which is not a hom
X:=HyperellipticCurve(f);
N:=2;
  
endos:=HeuristicEndomorphismRepresentation( X : CC:=true);
endosM2:=[ ChangeRing(m[1],CC) : m in endos ];
endosM4:=[ ChangeRing(m[2],Rationals()) : m in endos ]; 
Bmat:=MatrixAlgebra< Rationals(), 4 | endosM4 >;
tr, B, maptoB := IsQuaternionAlgebra(Bmat);
Obasis:=[ maptoB(b) : b in endosM4 ];
O:=QuaternionOrder(Obasis);


tr,mu:=HasPolarizedElementOfDegree(O,1);

perm_rep:=EnhancedPermutationRepresentationMod2(O,mu);

D4subs := [ sub`subgroup : sub in Subgroups(Codomain(perm_rep)) | GroupName(sub`subgroup) eq "D4" ];
D4enh := [ [ Inverse(perm_rep)(a) : a in sub ] : sub in D4subs ];

Omod2:=quo(O,2);
Oenh:=EnhancedSemidirectProduct(O : N:=2);
Omod2_elements := Setseq(Set(quo(O,2)));
Omod2_units := [ a : a in Omod2_elements | IsUnit(a) ];

GalM,mapM,rho2 :=EnhancedRepresentationMod2PQM(X);
rho2_image := [ rho2(a) : a in GalM ];

for unit in Omod2_units do 
  unit_enh := Oenh!<1,unit>;
  Set([ unit_enh^-1*a*unit_enh : a in rho2_image ]) eq Set(D4enh[1]);
end for;