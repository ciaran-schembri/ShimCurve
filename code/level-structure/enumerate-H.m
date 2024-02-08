
function createHash(Gelts)
    ret := AssociativeArray();
    for e in Gelts do
	ret[e`GL4] := e`enhanced;
    end for;
    return ret;
end function;

function createInverseHash(Gelts)
    ret := AssociativeArray();
    for e in Gelts do
	ret[e`enhanced] := e`GL4;
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

// !!!! TODO - This is highly inefficient (p^4 inefficient) !!!! replace by something sensible
function getKernelOfReduction(OmodN, p, inv_hash, G)
    N := Modulus(OmodN);
    assert(N mod (N div p) eq 0);
    if (p eq N) then
	return sub< G | [x : x in UnitGroup(OmodN)]>;
    end if;
    param := CartesianPower([0..p - 1],4);
    ker_p := [1+(N div p)*O![y : y in TupleToList(x)] : x in param];
    assert &and[IsUnit(y) : y in ker_p];
    GG := Universe(Keys(inv_hash));
    return sub<G|[inv_hash[GG!<1,x>] : x in ker_p]>;
end function;

function getAllReductionKernels(OmodN, inv_hash, G)
    N := Modulus(OmodN);
    ker_reds := AssociativeArray();
    for p in PrimeDivisors(N) do
	ker_p := getKernelOfReduction(OmodN, p, inv_hash, G);
	ker_reds[p] := ker_p;
    end for;
    return ker_reds;
end function;

intrinsic GetG1plus(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt,G::GrpMat) -> GrpMat
{Returns G1plus given G.}
    NBOplusgens_enhanced:=NormalizerPlusGeneratorsEnhanced(O,mu);
    NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens_enhanced ]; 
    G1plus:=sub< G | NBOplusgensGL4 >;
    assert #G/#G1plus eq 2;
    return G1plus;
end intrinsic;

intrinsic GetKernelAsSubgroup(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt,G1plus::GrpMat) -> GrpMat
{Returns the kernel of the semidirect to normalizer map, as a subgroup of G.}
    K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
    KGlist:=[ EnhancedElementInGL4modN(k,N) : k in K ];
    KG:=sub< G1plus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;
    assert #KG eq #K;
    return KG;
end intrinsic;

intrinsic EnumerateGerbiestSurjectiveH(OmodN::AlgQuatOrdRes, G::GrpMat, Gelts::SeqEnum[Rec], KG::GrpMat) -> SeqEnum[Rec]
{return all of the enhanced subgroups which contain the entire kernel (maximal size of gerbe, hence gerbisest), and having surjective reduced norm, in a list with each one being a record (rethink it).}
   
  subs:=Subgroups(G);
  N := Modulus(BaseRing(G));
  surjH := [H : H in subs | getDeterminantImage(H`subgroup : Hash := createHash(Gelts)) eq GL(1,Integers(N))];
  surj_gerby_H := [H : H in surjH | KG subset H`subgroup];
  inv_hash := createInverseHash(Gelts);

  ker_reds := getAllReductionKernels(OmodN, inv_hash, G);
  prime_kernels_in_H := [[] : H in surj_gerby_H];
  // !!!! TODO !!! Might be more efficient to get all subgroups containing a kernel of reduction every time
  for p in Keys(ker_reds) do
      for i->H in surj_gerby_H do
	  if ker_reds[p] subset H`subgroup then
	      Append(~prime_kernels_in_H[i], p);
	  end if;
      end for;
  end for;
  
  return surj_gerby_H, prime_kernels_in_H;
end intrinsic;

intrinsic EnumerateGerbiestSurjectiveH(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt : prime_kernel := []) -> SeqEnum[Rec]
{return all of the enhanced subgroups which contain the entire kernel (maximal size of gerbe, hence gerbisest), and having surjective reduced norm, in a list with each one being a record (rethink it).}

  assert N gt 2;
  AutFull:=Aut(O,mu);
  assert MapIsHomomorphism(AutFull : injective:=true);

  G,Gelts:=EnhancedImageGL4(AutFull,O,N);
  
  assert -G!1 in G;

  G1plus := GetG1plus(O, mu, N, G);
  
  KG := GetKernelAsSubgroup(O, mu, N, G1plus);
  
  subs, prime_kernels := EnumerateGerbiestSurjectiveH(quo(O,N), G, Gelts, KG);
  
  // For now, we simply return the subgroups that have minimal level N
  return [subs[i] : i in [1..#subs] | prime_kernels[i] eq prime_kernel];
  
end intrinsic;

intrinsic EllipticElementsGL4(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt) -> SeqEnum
{return the elliptic elements of the associated Shimura curve as elements in GL4(Z/NZ).}
    elliptic_elements_enhanced:=EnhancedEllipticElements(O,mu);
    assert forall(u){ <u,v> : u,v in elliptic_elements_enhanced | 
		      EnhancedElementInGL4modN(u,N)*EnhancedElementInGL4modN(v,N) eq EnhancedElementInGL4modN(u*v,N) };
    elliptic_eltsGL4:= [ EnhancedElementInGL4modN(e,N) : e in elliptic_elements_enhanced ];
    return elliptic_eltsGL4;
end intrinsic;

function Base26Encode(n)
    strip := "abcdefghijklmnopqrstuvwxyz";
    assert n gt 0;
    x := n - 1;
    s := "";
    repeat
	digit := x mod 26;
	s cat:= strip[digit+1];
	x div:= 26;
    until x eq 0;
    return Reverse(s);
end function;

intrinsic GetH1plusquo(H::GrpMat[RngIntRes], G1plus::GrpMat[RngIntRes], KG::GrpMat[RngIntRes], G1plusmodKG::GrpPerm, Gmap::Map[GrpMat[RngIntRes], GrpPerm]) -> GrpPerm
{}
    H1plus := sub< G1plus | H meet G1plus >;
    H1plusKG:= sub< G1plus | H1plus, KG >;
    H1plusKGmodKG:= quo< H1plusKG | KG >;

    H1plusquo:=Gmap(H1plus);
    if not IsIsomorphic(H1plusquo,H1plusKGmodKG) then 
	Error("This should not happen, something is not right - maybe this subgroup is not coarsest?");
    end if;
    return H1plusquo;
end intrinsic;

intrinsic FuchsianIndex(G1plusmodKG::GrpPerm, H1plusquo::GrpPerm) -> RngIntElt
{Returns the index of H as a fuchsian group acting on the upper half plane.}

    fuchsian_index:=#G1plusmodKG/#H1plusquo;
    
    return fuchsian_index;
end intrinsic;

intrinsic RamificationData(G1plusmodKG::GrpPerm, H1plusquo::GrpPerm, Gmap::Map[GrpMat[RngIntRes], GrpPerm], ells::SeqEnum[GrpMatElt[RngIntRes]]) -> SeqEnum[GrpPermElt]
{return the genus of the Shimura curve corresponding to H.}
    
    T:=CosetTable(G1plusmodKG,H1plusquo);
    piH:=CosetTableToRepresentation(G1plusmodKG,T);
    
    sigma := [ piH(Gmap(v)) : v in ells ];
    assert &*(sigma) eq Id(Parent(sigma[1]));
    
    return sigma;
end intrinsic;

GP_SHIM_RF := recformat< level : Integers(),
			 subgroup,
			 genus,
			 order,
			 index,
			 fuchsian_index,
			 torsion,
			 generators,
			 is_split,
			 galEnd,
			 autmuO_norms,
			 ram_data_elts,
			 discB,
			 discO,
			 deg_mu,
			 order_label,
			 mu_label,
			 label,
			 coarse_label
		       >;

function createRecord(H, G1plus, KG, ells, Gelts, O, N, OmodN, G, mu, level)
    s := rec< GP_SHIM_RF | >;
    Hgp:=H`subgroup;
    fixedspace:=FixedSubspace(Hgp);
    order:=H`order;
    
    G1plusmodKG,Gmap:= quo< G1plus | KG >;

    H1plusquo := GetH1plusquo(Hgp, G1plus, KG, G1plusmodKG, Gmap);

    fuchsian_index:=FuchsianIndex(G1plusmodKG, H1plusquo);
    sigma := RamificationData(G1plusmodKG, H1plusquo, Gmap, ells);
    genus := EnhancedGenus(sigma);

    Henh:=[ g`enhanced : g in Gelts | g`GL4 in Hgp ];
    Hautmus:= Setseq(Set([ h`element[1] : h in Henh ]));
    rho_end_norms:= Set([ Abs(SquarefreeFactorization(Integers()!Norm((w`element)[1]`element))) : w in Henh ]);
    ZmodN := Integers(N);
    rho_end:= sub< GL(4,ZmodN) | [ NormalizingElementToGL4modN(w`element[1],O,N) : w in Henh ] >;

    is_split:=true;
    for w in Hautmus do 
	if <w,OmodN!(O!1)> notin Henh then 
	    is_split := false;
	end if;
    end for;

    HGL4gens:=Generators(Hgp);
    Henhgens:=< g`enhanced : g in Gelts | g`GL4 in HGL4gens >;

    s`subgroup:=Hgp;
    s`level := level;
    s`genus:=genus;
    s`order:=order;
    s`index:=Order(G) div order;
    s`fuchsian_index:=fuchsian_index;
    s`torsion:=PrimaryAbelianInvariants(fixedspace);
    s`galEnd:=GroupName(rho_end);
    s`autmuO_norms:=rho_end_norms;
    s`is_split:=is_split;
    s`generators:=Henhgens;
    s`ram_data_elts:=sigma;
    s`discO := Discriminant(O);
    s`discB := Discriminant(Algebra(O));
    if IsMaximal(O) then 
	s`order_label := Sprintf("%o", s`discO);
    elif IsEichler(O) then
	s`order_label := Sprintf("%o.%o", s`discB, s`discO);
    else
	Error("Not implemented for non-Eichler orders at the moment");
    end if;
    s`deg_mu := Integers()!Norm(mu) div Discriminant(O);
    s`mu_label := Sprintf("%o.%o", s`order_label, s`deg_mu);
    s`coarse_label := Sprintf("%o.%o.%o", s`level, s`index, s`genus);
    
    return s;
end function;

procedure updateLabels(~subs, G)
    labels := {s`coarse_label : s in subs};
    for label in labels do
	label_subs := [i : i in [1..#subs] | subs[i]`coarse_label eq label];
	perm_chars := [<Eltseq(PermutationCharacter(G,subs[i]`subgroup)),i> : i in label_subs];
	perm_chars_sorted := Sort(perm_chars);
	n := 0;
	idx := 0;
	prev_char := [];
	tiebreaker := 0;
	while idx lt #perm_chars do 
	    idx +:= 1;
	    perm_char := perm_chars_sorted[idx][1];
	    if (perm_char ne prev_char) then 
		n +:= 1; 
		tiebreaker := 0;
	    else
		tiebreaker +:= 1;
	    end if;
	    class := Base26Encode(n);
	    sub_idx := perm_chars_sorted[idx][2];
	    subs[sub_idx]`coarse_label cat:= Sprintf(".%o.%o", class, tiebreaker+1);
	end while;
    end for;
    for i in [1..#subs] do
	subs[i]`label := Sprintf("%o.%o", subs[i]`mu_label, subs[i]`coarse_label);
    end for;
end procedure;

intrinsic GenerateDataForGerbiestSurjectiveH(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt) -> SeqEnum[Rec]
{Returns a list of records, each representing a line to be added to the database gps_shimura_test.}

   level := N;
   if N le 2 then
       N := 3*N;
       prime_kernel := [3];
   else
       prime_kernel := [];
   end if;
   assert N gt 2;
   OmodN := quo(O,N);
   AutFull:=Aut(O,mu);
   assert MapIsHomomorphism(AutFull : injective:=true);
   
   G,Gelts:=EnhancedImageGL4(AutFull,O,N);
  
   assert -G!1 in G;
   
   G1plus := GetG1plus(O, mu, N, G);
  
   KG := GetKernelAsSubgroup(O, mu, N, G1plus);
   
   subs, prime_kernels := EnumerateGerbiestSurjectiveH(OmodN, G, Gelts, KG);
  
   subs := [subs[i] : i in [1..#subs] | prime_kernels[i] eq prime_kernel];
   
   ells := EllipticElementsGL4(O, mu, N);
    
   ret_subs := [createRecord(H, G1plus, KG, ells, Gelts, O, N, OmodN, G, mu, level) : H in subs];
	  
   updateLabels(~ret_subs, G);
       
   return ret_subs;
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
    torsion,
    generators,
    is_split,
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





