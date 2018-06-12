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


intrinsic DenomRatInterp(xs :: [], ys :: []) -> FldFunRatElt
          {}

  if Characteristic(Universe(ys)) ne 0 then
    return Denominator(RatInterp(xs, ys));
  end if;

  RH := RHnew();
  prime_counter := 0;
  IndentPush();
  while not assigned RH`candidate do
      modulo := RandomPrime(23);
      if modulo in RH`points then continue; end if;
      prime_counter +:= 1;

      vprintf User2 : "Computing denominator modulo prime number %o (%o).\n  ", prime_counter, modulo;

      Kev := GF(modulo);

      try
          xsev := ChangeUniverse(xs, Kev);
          ysev := ChangeUniverse(ys, Kev);
          cand := Denominator(RatInterp(xsev, ysev));
          RHAddMod(~RH, cand, modulo);
      catch e
          vprintf User2 : "Reduction modulo a bad prime";
      end try;

  end while;
  IndentPop();

  return RH`candidate;

end intrinsic;


intrinsic PolInterp(xs :: [], ys :: []) -> Any
          {}

   if Characteristic(Universe(ys)) ne 0 then
       return Interpolation(xs, ys);
   end if;

   RH := RHnew();
   IndentPush();
   while not assigned RH`candidate do
      modulo := RandomPrime(50);
      if modulo in RH`points then continue; end if;
      Kev := GF(modulo);
      xsev := ChangeUniverse(xs, Kev);
      ysev := ChangeUniverse(ys, Kev);
      vprintf User2 : ".";
      cand := Interpolation(xsev, ysev);
      RHAddMod(~RH, cand, modulo);
   end while;
   IndentPop();

   return RH`candidate;
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

intrinsic RHAddRat(~H, val, point : xkey := false, denom := true)
  {}

  L, S := Explode(Deconstruct(val));
  key := <S, xkey>;
  Include(~H`points, point);

  rand := [];
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

  // We don't always try to reconstruct.
  if not Floor(Sqrt(#H`points))^2 eq #H`points and not Floor(Sqrt(3*#H`points))^2 eq 3*#H`points  then
      return;
  end if;

  vprintf User2 : "Testing reconstruction... ";


  points := [ v[2] : v in all ];

  recon := RatInterp(ChangeUniverse(points, Kev), [ v[1] : v in all ] );

  if IsDefined(H`recons, key) and H`recons[key] eq recon then
    if H`num gt -1 then
      all := H`vals[key];
      vprintf User2 : "Rational reconstruction of %o elements... ", #L;

      cand := [];
      den := 0;
      if Characteristic(Universe(L)) eq 0 then
          vprintf User2 : "Reconstructing denominator... ";
          vtime User2 : den := DenomRatInterp(points, [ &+[ all[i,1,j]*rand[j] : j in [1..#L] ] : i in [1..#points] ]);
      else
          den := Denominator(recon);
      end if;

      vprintf User2 : "Reconstructing numerators... ";
      evden := [ Evaluate(den, p) : p in points ];

      for j in [1..#L] do
          vprintf User2 : "%o/%o ", j, #L;
          Append(~cand, Interpolation( points, [ evden[i]*all[i, 1, j] : i in [1..#points] ] ));
      end for;

      if Maximum([Degree(p) : p in cand]) gt 2/3*#points then
            // Bad luck: the sampling is not good.
            // This happens so rarely that we just throw away everything.
            H := RHnew();
      end if;
      if denom then
          H`candidate := [* Rebuild(cand, S), den *];
      else
          H`candidate := Rebuild([p/den : p in cand], S);
      end if;
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

  // We don't always try to reconstruct.
  if #H`points gt 10 and not Floor(Sqrt(#H`points-5))^2 eq #H`points - 5  then
      return;
  end if;

  Lm := ChangeUniverse(nval[1], ResidueClassRing(nval[2]));
  rec := [ RationalReconstruction(x) : x in Lm ];
  if forall{x : x in rec | x} then
    Lm := [ a where _, a is RationalReconstruction(x) : x in Lm ];
    if IsDefined(H`recons, key) and H`recons[key] eq Lm then
      H`candidate := Rebuild(Lm, S);
    end if;
    H`recons[key] := Lm;
  end if;

  vprintf User2 : "%o percents of coefficients reconstructed (%o/%o). \n", Floor(100*(1+done)/(1+#rec)), done, #rec where done is #[ x : x in rec | x ];
end intrinsic;
  



