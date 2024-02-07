
function createHash(Gelts)
    ret := AssociativeArray();
    for e in Gelts do
	ret[e`GL4] := e`enhanced;
    end for;
    return ret;
end function;

function getEnhancedElt(h : Hash := AssociativeArray())
    if IsEmpty(Keys(Hash)) then
	Error("Not implemented without specifying hash table!");
    end if;
    return Hash[h];
end function;

function getDeterminantImage(H : Hash := AssociativeArray())
    gens := [H.i : i in [1..Ngens(H)]];
    images := [];
    for g in gens do
	e := getEnhancedElt(g : Hash := Hash);
	Append(~images, [[Norm(e)]]);
    end for;
    N := Modulus(BaseRing(H));
    return sub<GL(1,Integers(N)) | images>; 
end function;

intrinsic EnumerateGerbiestSurjectiveH(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt) -> SeqEnum
{return all of the enhanced subgroups which contain the entire kernel (maximal size of gerbe, hence gerbisest), and having surjective reduced norm, in a list with each one being a record (rethink it).}
   
  assert N gt 2;
  AutFull:=Aut(O,mu);
  assert MapIsHomomorphism(AutFull : injective:=true);

  G,Gelts:=EnhancedImageGL4(AutFull,O,N);
  
  assert -G!1 in G;

  subs:=Subgroups(G);
  
  surjH := [H : H in subs | getDeterminantImage(H`subgroup : Hash := createHash(Gelts)) eq GL(1,Integers(N))];
  
  NBOplusgens_enhanced:=NormalizerPlusGeneratorsEnhanced(O,mu);
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens_enhanced ]; 
  G1plus:=sub< G | NBOplusgensGL4 >;
  assert #G/#G1plus eq 2;
  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  KGlist:=[ EnhancedElementInGL4modN(k,N) : k in K ];
  KG:=sub< G1plus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;
  assert #KG eq #K;
  
  return [H : H in surjH | KG subset H`subgroup];
  
end intrinsic;


intrinsic EnumerateH(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {return all of the enhanced subgroups in a list with each one being a record}
  if write eq true then 
    assert verbose eq true;
    assert minimal eq false;
  end if;
  assert N gt 2;
  B:=QuaternionAlgebra(O);
  BxmodQx:=QuaternionAlgebraModuloScalars(B);
  OmodN:=quo(O,N);
  possible_tors:=[   [3], [2,3], [3,3], [4], [2,4], [2,2,2], [2,2,3],[3,4],[4,4], [2,2,4],[2,3,3] ];
  D:=Discriminant(B);
  del:=DegreeOfPolarizedElement(O,mu);

  //mu:=PolarizedElementOfDegree(O,1);
  AutFull:=Aut(O,mu);
  assert MapIsHomomorphism(AutFull : injective:=true);

  RF := recformat< n : Integers(),
    subgroup,
    genus,
    order,
    index,
    fixedsubspace,
    generators,
    split,
    endomorphism_representation,
    AutmuO_norms,
    ramification_data
    >
    ;

  NBOplusgens_enhanced:=NormalizerPlusGeneratorsEnhanced(O,mu);
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens_enhanced ]; 

  G,Gelts:=EnhancedImageGL4(AutFull,O,N);
  assert -G!1 in G;
  G1plus:=sub< G | NBOplusgensGL4 >;
  assert #G/#G1plus eq 2;
  GO:= G meet sub< GL(4,ResidueClassRing(N)) | UnitGroup(O,N) >;
  //assert #G/4 eq #GO; //if twisting

  ZmodN:=ResidueClassRing(N);
  Autmuimage:=[AutFull(c) : c in Domain(AutFull) ];

  elliptic_elements_enhanced:=EnhancedEllipticElements(O,mu);
  assert forall(u){ <u,v> : u,v in elliptic_elements_enhanced | 
  EnhancedElementInGL4modN(u,N)*EnhancedElementInGL4modN(v,N) eq EnhancedElementInGL4modN(u*v,N) };
  elliptic_eltsGL4:= [ EnhancedElementInGL4modN(e,N) : e in elliptic_elements_enhanced ];
  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  KGlist:=[ EnhancedElementInGL4modN(k,N) : k in K ];
  KG:=sub< G1plus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;
  assert #KG eq #K;

  G1plusmodKG,Gmap:= quo< G1plus | KG >;

  minimal_subs_init:=<>;
  subs:=Subgroups(G);

  for H in subs do
    Hgp:=H`subgroup;
    fixedspace:=FixedSubspace(Hgp);

    gens:=Generators(Hgp);

    order:=H`order;
    //index:=Order(G)/order;

    H1plus := sub< G1plus | Hgp meet G1plus >;
    H1plusKG:= sub< G1plus | H1plus, KG >;
    H1plusKGmodKG:= quo< H1plusKG | KG >;

    H1plusquo:=Gmap(H1plus);
    if not IsIsomorphic(H1plusquo,H1plusKGmodKG) then 
      break;
    end if;

    index:=#G1plusmodKG/#H1plusquo;

    T:=CosetTable(G1plusmodKG,H1plusquo);
    piH:=CosetTableToRepresentation(G1plusmodKG,T);
    //piH := EnhancedCosetRepresentation(G,Hgp,Gammastar_plus);
    sigma := [ piH(Gmap(v)) : v in elliptic_eltsGL4 ];
    assert &*(sigma) eq Id(Parent(sigma[1]));
    genus:=EnhancedGenus(sigma);

    Henh:=[ g`enhanced : g in Gelts | g`GL4 in Hgp ];
    Hautmus:= Setseq(Set([ h`element[1] : h in Henh ]));
    rho_end_norms:= Set([ Abs(SquarefreeFactorization(Integers()!Norm((w`element)[1]`element))) : w in Henh ]);
    rho_end:= sub< GL(4,ZmodN) | [ NormalizingElementToGL4modN(w`element[1],O,N) : w in Henh ] >;
    // rho_end_size:=Integers()!#Hgp/(#(GO meet Hgp));

    is_split:=true;
    for w in Hautmus do 
      if <w,OmodN!(O!1)> notin Henh then 
        is_split := false;
      end if;
    end for;

    HGL4gens:=Generators(Hgp);
    Henhgens:=< g`enhanced : g in Gelts | g`GL4 in HGL4gens >;

    s := rec< RF | >;
    s`subgroup:=Hgp;
    s`genus:=genus;
    s`order:=order;
    s`index:=index;
    s`fixedsubspace:=PrimaryAbelianInvariants(fixedspace);
    s`endomorphism_representation:=GroupName(rho_end);
    s`AutmuO_norms:=rho_end_norms;
    s`split:=is_split;
    s`generators:=Henhgens;
    s`ramification_data:=sigma;

    if PQMtorsion eq true then 
      if s`endomorphism_representation ne "C1" and s`fixedsubspace in possible_tors then
        if lowgenus eq true then  
          if genus le 1 then 
            Append(~minimal_subs_init,s);
          end if;
        else 
          Append(~minimal_subs_init,s);
        end if;
      end if;
    else 
      if lowgenus eq true then  
        if genus le 1 then 
          Append(~minimal_subs_init,s);
        end if;
      else 
        Append(~minimal_subs_init,s);
      end if;
    end if;
  end for;

  if minimal eq false then 
    if verbose eq true then 
      printf "Quaternion algebra of discriminant %o with presentation\n",Discriminant(O);
      print B : Magma;
      printf "Basis of O is %o\n", Basis(O);
      printf "Level N = %o\n", N;
      printf "Polarized Element \\mu=%o of degree %o and norm %o\n", mu, DegreeOfPolarizedElement(O,mu),Norm(mu);
      print "Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data \n";
      for s in minimal_subs_init do 
        printf "%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o \n", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, s`generators, Sprint(s`ramification_data : oneline:=true);
      end for;
      if write eq true then 
        filename:=Sprintf("ShimCurve/data/genera-tables/genera-D%o-deg%o-N%o.m",D,del,N);
        Write(filename,Sprintf("%m;",B));
        Write(filename,Sprintf("%o;",Basis(O)));
        Write(filename,Sprintf("%o;",N));
        Write(filename,Sprintf("%o;",Eltseq(O!mu)));
        //Write(filename,Sprintf("Discriminant %o",Discriminant(O)));
        //Write(filename,Sprintf("Basis of O is %o", Basis(O)));
        //Write(filename,Sprintf("Level N = %o", N));
        Write(filename,Sprintf("Polarized Element \\mu=%o of degree %o and norm %o", mu, DegreeOfPolarizedElement(O,mu),Norm(mu)));
        Write(filename,"Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data");

        for s in minimal_subs_init do 
          gens_readable:=[ Sprintf("< %o, %o >", g`element[1], Eltseq((g`element[2])`element)) : g in s`generators ];
          gens_readable;
          Write(filename,Sprintf("%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o ? %o", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, gens_readable, Sprint(s`ramification_data : oneline:=true)));
        end for;
      end if;
    end if;
    return minimal_subs_init;
  else 
    minimal_subs:=<>;
    for s in minimal_subs_init do  
      F:=s`subgroup;
      tors:=s`fixedsubspace;
      //endorep:=s`endomorphism_representation;
      //AL:=s`atkin_lehners;
      if exists(e){ N : N in minimal_subs_init | F subset N`subgroup and 
        tors eq N`fixedsubspace and F ne N`subgroup }
        //or exists(e){ N : N in minimal_subs_init | IsGLConjugate(F,N`subgroup) } 
        then 
        ;
      else 
        Append(~minimal_subs,s);
      end if;
    end for;
    if verbose eq true then
      printf "Quaternion algebra of discriminant %o with presentation\n",Discriminant(O);
      print B : Magma;
      printf "Basis of O is %o\n", Basis(O);
      printf "Level N = %o\n", N;
      printf "Polarized Element \\mu=%o of degree %o and norm %o\n", mu, DegreeOfPolarizedElement(O,mu),Norm(mu);
      print "Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data\n";
      for s in minimal_subs do 
        printf "%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o \n", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, Sprint(s`generators), Sprint(s`ramification_data : oneline:=true);
      end for;
    end if;
    return minimal_subs;
  end if;

end intrinsic;


intrinsic EnumerateH(B::AlgQuat,mu::AlgQuatOrdElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  return EnumerateH(MaximalOrder(B),mu,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
end intrinsic;

intrinsic EnumerateH(O::AlgQuatOrd,del::RngIntElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  if HasPolarizedElementOfDegree(O,del) then 
    tr,mu:=HasPolarizedElementOfDegree(O,del);
    return EnumerateH(O,mu,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
  else 
    printf "No polarization of degree %o\n", del;
    return "";
  end if;
end intrinsic;

intrinsic EnumerateH(B::AlgQuat,del::RngIntElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  O:=MaximalOrder(B);
  return EnumerateH(O,del,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
end intrinsic;

intrinsic EnumerateH(D::RngIntElt,del::RngIntElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  B:=QuaternionAlgebra(D);
  O:=MaximalOrder(B);
  return EnumerateH(O,del,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
end intrinsic;




intrinsic Print(elt::AlgQuatOrdResElt)
{.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(OmodN::AlgQuatOrdRes)
{.}
  printf "Quotient of %o by %o", OmodN`quaternionorder, OmodN`quaternionideal;
end intrinsic;

intrinsic Print(elt::AlgQuatProjElt)
{.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(BxmodFx::AlgQuatProj)
{.}
  printf "Quotient by scalars of %o", BxmodFx`quaternionalgebra;
end intrinsic;





