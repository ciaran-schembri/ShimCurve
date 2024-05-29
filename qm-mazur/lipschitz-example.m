

 
//t:=27; //smaller image
t:=19; //image has size 48, enhanced rep is a hom!

Rx<x>:=PolynomialRing(Rationals());
f:=x^5 + 8*x^4 + t*x^3 + 16*x^2-4*x;


prec:=30;
CC:=ComplexField(prec);
X:=HyperellipticCurve(f);
TwoTorsionSubgroup(Jacobian(X));

GalM,mapM,rho2,O :=EnhancedRepresentationMod2PQM(X : prec:=prec);

tr,mu:=HasPolarizedElementOfDegree(O,1);
//create the permutation representation so we can work with the semidirect product as a group
perm_rep:=EnhancedPermutationRepresentationMod2(O,mu);

rho2_image := [ rho2(a) : a in GalM ];
rho2_image_GL4 := [ GL(4,2)!EnhancedElementInGL4modN(a,2) : a in rho2_image ];
rho2_image_GL4elts:= Set(rho2_image_GL4);  //size is 24 since map to GL4 not injective for N=2
rho2_image_GL4grp := sub< GL(4,2) | rho2_image_GL4 >;

//check with Mod2EnhancedImage();
mod2rep:=mod2Galoisimage(X);
mod2rep_elts:=Set([ GL(4,2)!a : a in mod2rep ]);

assert GroupName(rho2_image_GL4grp) eq GroupName(mod2rep);
IsGLConjugate(mod2rep,rho2_image_GL4grp); //true

Oenh_elts:=[ Inverse(perm_rep)(a) : a in Codomain(perm_rep) ];
for elt in Oenh_elts do 
    rho2_image_GL4 := [ EnhancedElementInGL4modN(elt*a*elt^-1,2) : a in rho2_image ];
    rho2_image_GL4elts := Set(rho2_image_GL4);  //size is 24 since map to GL4 not injective for N=2
    if mod2rep_elts eq rho2_image_GL4elts then 
        elt;
    end if;
end for;



//create the permutation representation so we can work with the semidirect product as a group
perm_rep:=EnhancedPermutationRepresentationMod2(O,mu);









//list the subgroups of the semidirect product with size 48 and autmuO part of size 12 up to conjugation
G48list := [ sub`subgroup : sub in Subgroups(Codomain(perm_rep)) | #sub`subgroup eq 48 ];
G48enhlist := [ [ Inverse(perm_rep)(a) : a in sub ] : sub in G48list ];
G48enhlist := [ sub : sub in G48enhlist | #Set([a`element[1] : a in sub]) eq 12 ];

rho2_image := [ rho2(a) : a in GalM ];

Omod2_elements := Setseq(Set(quo(O,2)));
Omod2_units := [ a : a in Omod2_elements | IsUnit(a) ];
Oenh:=Codomain(rho2);





N:=2;
GalM,map2,f2:=Mod2GaloisMapPQM(X);
GalM;
f2;


L:=OptimizedRepresentation(HeuristicEndomorphismFieldOfDefinition(C));
assert GroupName(GaloisGroup(L)) eq "D6";

QA2:=OptimizedRepresentation(SplittingField(f));
assert GroupName(GaloisGroup(QA2)) eq "S4";

LA2:=AbsoluteField(Compositum(L,QA2));
assert Degree(LA2) eq 48;
LandQA2:=L meet QA2;
assert GroupName(GaloisGroup(LandQA2)) eq "S3";

assert IsSubfield(L,QA2) eq false; 



////////////////////////////////
//this finds the mod 2 image by showing it's conjugate to a particular subgroup of the enhanced semidirect product
B<i,j>:=QuaternionAlgebra< Rationals() | -1,3 >;
O:=QuaternionOrder([1,i,j,i*j]);

mu:=(3*i+j-i*j)/6;
z6:=B!(1/2+3*mu);
chi:=B!(i-i*j);

//AutmuO:=[ (1+z6)^l*chi^k : l in [0..5], k in [0..1] ];
//AutmuO:=Setseq(Set(AutmuO));

//ker:= [ [l,k] : l in [0..5], k in [0..1] | GL(4,ResidueClassRing(2))!1 eq NormalizingElementToGL4modN((1+z6)^l*chi^k,O,2) ];

AutmuO:=Aut(O,mu);

G, ONxinGL4, Ahom := EnhancedImageGL4(AutmuO,O,2);
Gelts := [g : g in G];
subs:=Subgroups(G);


mod2rep:=mod2Galoisimage(C);


Ocirc:=EnhancedSemidirectProduct(O);
EnhancedElementInGL4(Ocirc!<B!1,O!1>);
m1:=EnhancedElementInGL4modN(Ocirc!<B!(1+z6),O!i>, 2);
m2:=EnhancedElementInGL4modN(Ocirc!<B!(1+z6),O!j>, 2);
m3:=EnhancedElementInGL4modN(Ocirc!<B!(chi),O!i>, 2);
m4:=EnhancedElementInGL4modN(Ocirc!<B!(chi),O!j>, 2);


matrix_gens:=[ ChangeRing(a,GF(2)) : a in [m1,m2,m3,m4] ];

HH:=sub< GL(4,GF(2)) | matrix_gens >;
IsGLConjugate(mod2rep,HH);


Hmods:=[ H : H in subs | H`order eq 24 ];
Hmods_subgroup:=[ ChangeRing(H`subgroup,GF(2)) : H in Hmods ];
[ FixedSubspace(H`subgroup) : H in Hmods ];

assert IsGLConjugate(mod2rep,Hmods_subgroup[2]);
assert not(IsGLConjugate(mod2rep,Hmods_subgroup[1]));
assert not(IsGLConjugate(mod2rep,Hmods_subgroup[3]));

Hcorrect:=Hmods_subgroup[2];

basis := Basis(O);
Hi := UnitGroupToGL4modN(basis[2], 2);
Hj := UnitGroupToGL4modN(basis[3], 2);
Hij := UnitGroupToGL4modN(basis[4], 2);

Hi in Hcorrect;
Hj in Hcorrect;
Hij in Hcorrect;

inHenhanced := [GL4ToPair(x, O, Ahom) : x in Hcorrect];






///////////////////////////////////////////////////
//This uses Shiva's code to compute the mod 4 image.

//G4:=find_mod4image(C);
H4:=MatrixGroup<4, IntegerRing(4) |
Matrix(IntegerRing(4), 4, 4, [ 0, 2, 2, 1, 2, 1, 2, 2, 2, 2, 3, 0, 1, 0, 2, 0 ]),
Matrix(IntegerRing(4), 4, 4, [ 2, 2, 0, 3, 0, 3, 1, 3, 2, 0, 1, 0, 1, 2, 3, 1 ]),
Matrix(IntegerRing(4), 4, 4, [ 0, 2, 0, 1, 0, 3, 2, 0, 2, 3, 1, 2, 3, 2, 0, 0 ]),
Matrix(IntegerRing(4), 4, 4, [ 3, 2, 1, 1, 3, 2, 2, 3, 3, 1, 0, 0, 3, 3, 3, 3 ]),
Matrix(IntegerRing(4), 4, 4, [ 1, 2, 0, 2, 0, 1, 0, 0, 0, 2, 1, 2, 2, 0, 0, 1 ]),
Matrix(IntegerRing(4), 4, 4, [ 1, 2, 0, 0, 0, 3, 0, 0, 0, 0, 3, 2, 0, 0, 0, 1 ]),
Matrix(IntegerRing(4), 4, 4, [ 1, 0, 2, 0, 2, 1, 0, 2, 2, 0, 1, 0, 0, 2, 2, 1 ]),
ScalarMatrix(IntegerRing(4), 4, 3),
Matrix(IntegerRing(4), 4, 4, [ 1, 2, 0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 2, 0, 1 ]) >;


H4transpose:=MatrixGroup< 4, IntegerRing(4) | [Transpose(A) : A in Generators(H4)] >;
FixedSubspace(H4transpose); //(Z/2)



