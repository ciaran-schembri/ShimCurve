
intrinsic Aut(O::AlgQuatOrd,mu::AlgQuatElt) -> Any
  {return Autmu(O). It will be a map from a subgroup of D_n to where the codomain 
  is Autmu(O)}

  assert IsScalar(mu^2);
  tr,eta:=IsScalar(mu^2);
  disc:=Discriminant(O);
  Rx<x>:=PolynomialRing(Rationals());
  sqeta,c:=SquarefreeFactorization(eta);
  Em<v>:=NumberField(x^2-sqeta);
  //Rm:=Order([1,v]);
  cyc,Czeta,zeta:=IsCyclotomic(Em);
  //Zzeta:=Integers(Czeta);

  B:=QuaternionAlgebra(O);
  BxmodQx:=QuaternionAlgebraModuloScalars(B);

  if cyc eq true then  
    //sqeta,c:=SquarefreeFactorization(eta);
    assert sqeta in {-1,-3};
    if sqeta eq -1 then 
      cyc_order:=4;
      zeta_n := mu/c;
    elif sqeta eq -3 then 
      cyc_order:=6;
      zeta_n := ((mu/c)+1)/2;
    end if;
    a:=B!zeta_n+1;
  else 
    cyc_order:=2;
    a:=B!mu;
  end if;

  if IsTwisting(O,mu) then
    tr,muchi:=IsTwisting(O,mu);
    b:=B!(muchi[2]);
    if cyc eq true then 
      Dn:=DihedralGroup(cyc_order);
    else 
      Dn:=Group("C2^2");
    end if;
    Dngens:=Generators(Dn);
    assert #Dngens eq 2;
    assert Order(Dn.1) eq #Dn/2;
    assert Order(Dn.2) eq 2;
    elts:= [ <Dn.1^l*Dn.2^k, BxmodQx!(a^l*b^k)> : l in [0..cyc_order-1], k in [0..1] ];
    grp_map:=map< Dn -> BxmodQx | elts >;
  else 
    if cyc eq true then 
      Cn:=CyclicGroup(cyc_order);
    else 
      Cn:=CyclicGroup(2);
    end if;
    elts:= [ <Cn.1^k,BxmodQx!(a^k)> : k in [0..#Cn-1] ];
    grp_map:=map< Cn -> BxmodQx | elts >;
  end if;
  
  assert MapIsHomomorphism(grp_map);
  return grp_map, [ grp_map(a) : a in Domain(grp_map) ];
end intrinsic;


intrinsic Aut(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> Any
  {return Autmu(O). It will be a map from D_n to  where the codomain 
  is Autmu(O)}
  B:=QuaternionAlgebra(O);
  return Aut(O,B!mu);
end intrinsic;
