




intrinsic EnumerateH(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false, profile:=false) -> Any
  {return all of the enhanced subgroups in a list with each one being a record}
  t0 := Cputime();
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
  //if profile then print "Setup", Cputime() - t0; end if;
  t0 := Cputime();

  //mu:=PolarizedElementOfDegree(O,1);
  AutFull:=Aut(O,mu);
  if profile then print "Aut(O,mu)", Cputime() - t0; t0 := Cputime(); end if;

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
  if profile then print "NBOplusgens_enhanced", Cputime() - t0; t0 := Cputime(); end if;
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens_enhanced ];
  //if profile then print "NBOplusgensGL4", Cputime() - t0; end if;
  t0 := Cputime();

  G, ONxinGL4, Ahom := EnhancedImageGL4(AutFull,O,N);
  //print "Group:", GroupToString(G : use_id:=false);
  if profile then print "EnhancedImageGL4", Cputime() - t0; t0 := Cputime(); end if;
  assert -G!1 in G;
  G1plus:=sub< G | NBOplusgensGL4 >;
  if profile then print "G1plus", Cputime() - t0; t0 := Cputime(); end if;
  assert #G/#G1plus eq 2;
  GO:= G meet sub< GL(4,ResidueClassRing(N)) | UnitGroup(O,N) >;
  if profile then print "GO", Cputime() - t0; t0 := Cputime(); end if;
  //assert #G/4 eq #GO; //if twisting

  ZmodN:=ResidueClassRing(N);

  elliptic_elements_enhanced:=EnhancedEllipticElements(O,mu);
  if profile then print "elliptic_elements_enhanced", Cputime() - t0; t0 := Cputime(); end if;
  //assert forall(u){ <u,v> : u,v in elliptic_elements_enhanced |
  //EnhancedElementInGL4modN(u,N)*EnhancedElementInGL4modN(v,N) eq EnhancedElementInGL4modN(u*v,N) };
  //if profile then print "assertion", Cputime() - t0; t0 := Cputime(); end if;
  elliptic_eltsGL4:= [ EnhancedElementInGL4modN(e,N) : e in elliptic_elements_enhanced ];
  //if profile then print "elliptic_eltsGL4", Cputime() - t0; end if;
  t0 := Cputime();
  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  if profile then print "K", Cputime() - t0; t0 := Cputime(); end if;
  KGlist:=[ EnhancedElementInGL4modN(k,N) : k in K ];
  KG:=sub< G1plus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;
  assert #KG eq #K;

  G1plusmodKG,Gmap:= quo< G1plus | KG >;

  minimal_subs_init:=<>;
  //if profile then print "G1plusmodKG", Cputime() - t0; end if;
  t0 := Cputime();
  subs:=Subgroups(G);
  if profile then print "Subgroups(G)", Cputime() - t0; t0 := Cputime(); end if;

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
    //if not IsIsomorphic(H1plusquo,H1plusKGmodKG) then 
    //  break;
    //end if;

    index:=#G1plusmodKG/#H1plusquo;

    T:=CosetTable(G1plusmodKG,H1plusquo);
    piH:=CosetTableToRepresentation(G1plusmodKG,T);
    //piH := EnhancedCosetRepresentation(G,Hgp,Gammastar_plus);
    sigma := [ piH(Gmap(v)) : v in elliptic_eltsGL4 ];
    assert &*(sigma) eq Id(Parent(sigma[1]));
    genus:=EnhancedGenus(sigma);

    is_split := (order eq #(Hgp meet Image(Ahom)) * #(Hgp meet ONxinGL4));
    Henhgens := [GL4ToPair(Hgp.i, O, Ahom) : i in [1..NumberOfGenerators(Hgp)]];
    aut_mu_norms := [Abs(SquarefreeFactorization(Integers()!Norm(AutFull(pair[1])`element))) : pair in Henhgens];
    rho_end := sub<GL(4,ZmodN)|[Ahom(pair[1]) : pair in Henhgens]>;

    s := rec< RF | >;
    s`subgroup:=Hgp;
    s`genus:=genus;
    s`order:=order;
    s`index:=index;
    s`fixedsubspace:=PrimaryAbelianInvariants(fixedspace);
    s`endomorphism_representation:=GroupName(rho_end);
    s`AutmuO_norms:=aut_mu_norms;
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

  if profile then print "Subloop", Cputime() - t0; t0 := Cputime(); end if;
  if minimal eq false then 
    if verbose eq true then 
      printf "Quaternion algebra of discriminant %o with presentation\n",Discriminant(O);
      print B : Magma;
      printf "Basis of O is %o\n", Basis(O);
      printf "Level N = %o\n", N;
      printf "Polarized Element \\mu=%o of degree %o and norm %o\n", mu, DegreeOfPolarizedElement(O,mu),Norm(mu);
      print "Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data \n";
      for s in minimal_subs_init do 
        printf "%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o \n", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, s`generators, sprint(s`ramification_data);
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
          gens_readable:=[ Sprintf("<%o, %o>", g[1], Eltseq(g[2])) : g in s`generators ];
          //gens_readable;
          Write(filename,Sprintf("%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o ? %o", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, gens_readable, sprint(s`ramification_data)));
        end for;
      end if;
    end if;
    if profile then print "Minimal", Cputime() - t0; t0 := Cputime(); end if;
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
        printf "%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o \n", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, sprint(s`generators), sprint(s`ramification_data);
      end for;
    end if;
    if profile then print "Nonminimal", Cputime() - t0; t0 := Cputime(); end if;
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





