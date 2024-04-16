Rx<x>:=PolynomialRing(Rationals());
//f:=-x^5+4*x^4-10*x^3+8*x^2-2*x; //this one actually works
prec:=30;
CC:=ComplexField(prec);
f:= 3*x^5 + 3*x^4 - 4*x^3 + 3*x - 1; //this returns a map which is not a hom
X:=HyperellipticCurve(f);
N:=2;
  
QA2:=SplittingField(f);
L:=HeuristicEndomorphismFieldOfDefinition(X);
assert Degree(L) eq 4;
assert IsSubfield(L,QA2);

GalM,mapM,rho2,O :=EnhancedRepresentationMod2PQM(X);
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


Rx<x>:=PolynomialRing(Rationals());
f:= 3*x^5 + 3*x^4 - 4*x^3 + 3*x - 1;
XR:=RiemannSurface(f,2 : Precision:=prec);
//We change the base point
oldbasepoint := XR`BasePoint;
XR`BasePoint := XR![-1,0];
//The Abel Jacobi should give the 0 element but it doesn't because its the minus of the output with the old basepoint
AbelJacobi(XR![-1,0]); 
assert AbelJacobi(XR![-1,0]) eq -AbelJacobi(XR![-1,0], oldbasepoint); 
//We have to the specify the new base point still 
AbelJacobi(XR![-1,0],XR`BasePoint); 