/* This software is governed by the CeCILL license under French law and abiding
 * by the rules of distribution of free software.  You can use, modify or
 * redistribute the software under the terms of the CeCILL license as
 * circulated by CEA, CNRS and INRIA at the following URL
 * 
 *     www.cecill.info
 * 
 *  Author: Pierre Lairez (2014)
 *
 **/



/*****************
 * Interpolation
 */

// ys : tous de même taille
intrinsic HigherOrderInterpolation( xs :: [], ys :: [[]] ) -> RngUPolElt
  {}

  A<t> := PolynomialRing(Universe(ys[1]));
  R := A ! Interpolation( xs, [ y[1] : y in ys ] );

  if #ys[1] eq 1 then
    return R;
  elif #ys[1] eq 2 then
    L := &*[ t - x : x in xs ];
    dL := Derivative(L);
    dR := Derivative(R);
    ys0 := [ (ys[i,2] - Evaluate(dR, xs[i]))/Evaluate(dL, xs[i]) : i in [1..#xs] ];
    return L*Interpolation( xs, ys0 ) + R;
  else
    error "Not implemented.";
  end if;
end intrinsic;


intrinsic PadeHermite( Lf, type ) -> []
  {}

  R<t> := Universe(Lf);
  M := RSpace(R, #type);
  deg := func< m | Maximum([Degree(m[i])-type[i] : i in [1..#type]]) >;
  
  Q := [ M.i : i in [1 .. #Lf]];
  T := Lf;

  for s := 0 to &+type + #Lf - 1 do
    k := 0;
    for i in [1..#Lf] do
      if Valuation(T[i]) eq s
        and ( k eq 0 or deg(Q[i]) lt deg(Q[k]) ) then
        k := i;
      end if;
    end for; 

    if k ne 0 then
      c := Coefficient(T[k], s);
      assert c ne 0;
      for i := 1 to #Lf do
        if i ne k then
          l := Coefficient(T[i], s);
          Q[i] -:= l/c*Q[k];
          T[i] -:= l/c*T[k];
        end if;
      end for;
      Q[k] *:= t;
      T[k] *:= t;
    end if;
  end for;

  _, k := Minimum( [deg(Q[i]) : i in [1..#Lf]] );

  return Eltseq(Q[k]);
end intrinsic;


intrinsic RatInterp(xs :: [], ys :: []) -> FldFunRatElt
  {}

  R<t> := PolynomialRing(Universe(xs));

  if ISA(Type(ys[1]), SeqEnum) then
    L := R ! HigherOrderInterpolation(xs, ys);
    m := (&*[ t - x : x in xs ])^#ys[1];
    d := Floor(#xs*#ys[1] / 2);
  else
    L := R ! Interpolation(xs, ys);
    m := &*[ t - x : x in xs ];
    d := Floor(#xs / 2);
  end if;

  ph := PadeHermite([R!-1, L, m], [d, d, d]);

  return ph[1]/ph[2];
end intrinsic;


intrinsic Deconstruct( a ) -> < >
  {}

  if ISA(Type(a), SeqEnum) then
    L := [ Deconstruct(p) : p in a ];
    return <&cat[ d[1] : d in L ], < "seq", [ <#d[1], d[2]> : d in L ] > >;
  elif ISA(Type(a), Mtrx) then
    p := Deconstruct(Eltseq(a));
    return < p[1], < "mtrx", NumberOfRows(a), NumberOfColumns(a), p[2] > >;
  elif ISA(Type(a), RngUPolElt) then
    p := Deconstruct(Coefficients(a));
    return <p[1], < "upol", p[2] >>;
  elif ISA(Type(a), RngMPolElt) then
    p := Deconstruct(Coefficients(a));
    return <p[1], < "mpol", p[2],  Rank(Parent(a)), MonomialOrder(Parent(a)), [ Exponents(m) : m in Monomials(a) ] >>;
  elif ISA(Type(a), FldFunRatUElt) then
    p := Deconstruct( [ Denominator(a), Numerator(a) ] );
    return < p[1], < "ratu", p[2] >>;
  elif ISA(Type(a), List) then
    L := [ Deconstruct(p) : p in a ];
    return <&cat[ d[1] : d in L ], < "list", [ <#d[1], d[2]> : d in L ] >>;
  else
    return < [a], < "self" >> ;
  end if;
end intrinsic;


intrinsic Rebuild( a, b ) -> Any
  {}

  case b[1] :
  when "seq":
    L := [];
    acc := 0;
    for i in [1..#b[2]] do
      Append(~L, Rebuild( a[acc+1..acc+b[2,i,1]], b[2,i,2]));
      acc +:= b[2,i,1];
    end for;
    return L;
  when "list":
    L := [* *];
    acc := 0;
    for i in [1..#b[2]] do
      Append(~L, Rebuild( a[acc+1..acc+b[2,i,1]], b[2,i,2]));
      acc +:= b[2,i,1];
    end for;
    return L;
  when "mtrx":
    L := Rebuild(a, b[4]);
    return Matrix(Universe(L), b[2], b[3], L);
  when "upol":
    L := Rebuild(a, b[2]);
    if #L gt 0 then
      return Polynomial( L );
    else
      return 0;
    end if;
  when "mpol":
    L := Rebuild(a, b[4]);
    if #L gt 0 then
      R := PolynomialRing(Universe(L), b[2], b[3]);
      ms := [ Monomial(R, e) : e in b[4] ];
      return Polynomial( L, ms );
    else
      return 0;
    end if;
  when "ratu":
    L := Rebuild(a, b[2]);
    return L[2]/L[1];
  when "self":
    return a[1];
  else
    error "Bad format.";
  end case;
end intrinsic;


RHfmt := recformat< vals, recons, tests, candidate, num, points, rand >;
intrinsic RHnew() -> Rec
  {}

  return rec< RHfmt | vals := AssociativeArray(), recons := AssociativeArray(), tests := AssociativeArray(), rand := AssociativeArray(), num := 0, points := {} >;
end intrinsic;

procedure AppendToVal(~aa, key, val)
  if IsDefined(aa, key) then
    Append(~aa[key], val);
  else
    aa[key] := [* val *];
  end if;
end procedure;

intrinsic RHAddRat(~H, val, point : xkey := false)
  {}

  L, S := Explode(Deconstruct(val));
  key := <S, xkey>;
  Include(~H`points, point);
  
  if IsDefined(H`rand, key) then
    rand := H`rand[key];
  else
    rand := [ Random(10000) : p in L ];
    H`rand[key] := rand;
  end if;

  if Characteristic(Universe(L)) eq 0 then
    Kev := GF(4194301);
    test := &+[ Kev ! rand[i]*L[i] : i in [1..#L] ];
  else
    test := &+[ rand[i]*L[i] : i in [1..#L] ];
    Kev := Universe(L);
  end if;

  AppendToVal(~H`vals, key, <L, point>);
  AppendToVal(~H`tests, key, <test, point>);

  all := H`tests[key];
  points := [ v[2] : v in all ];
  
  recon := RatInterp(ChangeUniverse(points, Kev), [ v[1] : v in all ] );

  if IsDefined(H`recons, key) and H`recons[key] eq recon then
    if H`num gt -1 then
      all := H`vals[key];
      vprintf User2 : "Rational reconstruction of %o elements...", #L;
      den := Denominator(recon);
      evden := [ Evaluate(den, p) : p in points ];
      //cand := [ RatInterp( points, [ all[i, 1, j] : i in [1..#points] ] ) : j in [1..#L] ];
      cand := [ Interpolation( points, [ evden[i]*all[i, 1, j] : i in [1..#points] ] )/den : j in [1..#L] ];

      if Maximum([Degree(p) : p in cand]) gt 2/3*#points then
        // Bad luck: the sampling is not good.
        // This happens so rarely that we just throw away everything.
        H := RHnew();
      end if;

      H`candidate := Rebuild(cand, S);
    else
      H`num +:= 1;
    end if;
  end if;

  H`recons[key] := recon;

end intrinsic;

intrinsic RHAddMod(~H, val, point : xkey := false)
  {}

  L, S := Explode(Deconstruct(val));
  key := <S, xkey>;
  Include(~H`points, point);
  
  Li := ChangeUniverse(L, Integers());

  if IsDefined(H`vals, key) then
    sofar, modulo := Explode(H`vals[key]);
    nval := <
      [ ChineseRemainderTheorem([sofar[i], Li[i]], [modulo, point]) : i in [1..#L] ],
      modulo*point >;
  else
    nval := < Li, point >;
  end if;
  H`vals[key] := nval;

  Lm := ChangeUniverse(nval[1], ResidueClassRing(nval[2]));
  rec := [ RationalReconstruction(x) : x in Lm ];
  if forall{x : x in rec | x} then
    Lm := [ a where _, a is RationalReconstruction(x) : x in Lm ];
    if IsDefined(H`recons, key) and H`recons[key] eq Lm then
      H`candidate := Rebuild(Lm, S);
    end if;
    H`recons[key] := Lm;
  end if;

  vprintf User2 : "%o percents of coefficients reconstructed (%o/%o). \n", Floor(100*done/#rec), done, #rec where done is #[ x : x in rec | x ];
end intrinsic;
  



