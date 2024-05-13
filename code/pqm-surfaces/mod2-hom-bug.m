Rx<x>:=PolynomialRing(Rationals());
//f:=-x^5+4*x^4-10*x^3+8*x^2-2*x; //this one actually works
f:= 3*x^5 + 3*x^4 - 4*x^3 + 3*x - 1; //this returns a map which is not a hom
f := 2*x^6+9*x^5+6*x^4+2*x^3-6*x-4; //this one doesn't have a rational root.
prec:=30;
CC:=ComplexField(prec);
X:=HyperellipticCurve(f);
N:=2;
GalM,map2,f2:=Mod2GaloisMapPQM(X);
f2;

GalM,mapM,rho2,O :=EnhancedRepresentationMod2PQM(X);
  
QA2:=SplittingField(f);
L:=HeuristicEndomorphismFieldOfDefinition(X);
assert Degree(L) eq 4;
assert IsSubfield(L,QA2);

M:=Domain(mapM(GalM.1));
JM:=Jacobian(ChangeRing(X,M));
T2,J2:=TwoTorsionSubgroup(JM);

assert IsMaximal(O);
tr,mu:=HasPolarizedElementOfDegree(O,1);

perm_rep:=EnhancedPermutationRepresentationMod2(O,mu);

//list the subgroups of the semidirect product isomorphic to D4 up to conjugation
D4subs := [ sub`subgroup : sub in Subgroups(Codomain(perm_rep)) | GroupName(sub`subgroup) eq "D4" ];
D4enh := [ [ Inverse(perm_rep)(a) : a in sub ] : sub in D4subs ];
D4enh := [ sub : sub in D4enh | #Set([a`element[1] : a in sub]) eq 4 ];

rho2_image := [ rho2(a) : a in GalM ];
exists(e){ [a,b] : a,b in rho2_image | a*b notin rho2_image };

Omod2_elements := Setseq(Set(quo(O,2)));
Omod2_units := [ a : a in Omod2_elements | IsUnit(a) ];
Oenh:=Codomain(rho2);


//Let's see
for subgrp in D4enh do 
  for unit in Omod2_units do 
    unit_enh := Oenh!<1,unit>;
    U:=Universe(Set(subgrp));
    item:=ChangeUniverse(Set([ unit_enh^-1*a*unit_enh : a in rho2_image ]),U);
    if item eq Set(subgrp) then 
      conj_elt:=unit_enh;
      D4grp := subgrp;
      conj_elt;
      D4grp;
    end if;
  end for;
end for;

// conj_elt^-1*rho2*conj_elt = D4grp which is true for the example that works


