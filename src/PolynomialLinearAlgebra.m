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


procedure RemoveTrailingZeros( ~L )
  while 0 lt #L and L[#L] eq Zero(Universe(L)) do
    Prune(~L);
  end while;
end procedure;

// input : M an echelonized matrix
// output : list of indices of first non-zero entries of the rows
function RankProfile( M )
  p := [];
  i := 1;
  for j := 1 to NumberOfColumns(M) do
    if i le NumberOfRows(M) and M[i, j] ne 0 then
      i +:= 1;
      Append(~p, j);
    end if;
  end for;

  return p;
end function;



intrinsic Linearize( L :: [] : pre := 0, post := 0 ) -> Mtrx, []
  {Return coefficients M and monomials V such that M.V = L.
  Optional parameters pre and post add extra columns.}

  require pre le #L : "pre must be lt #L";
  require post le #L : "post must be lt #L";

  A := CoefficientRing(Universe(L));
  M := Setseq(&join[ Seqset(Monomials(p)) : p in L ]); // FIXME Redondance avec H
  Sort(~M);
  Reverse(~M);

  H := AssociativeArray();
  for i := 1 to #M do
    H[M[i]] := i;
  end for;

  mat := ZeroMatrix(A, #L, pre+#M+post);

  for i := 1 to #L do
    c, m := CoefficientsAndMonomials(L[i]);
    for j := 1 to #m do
      mat[i, pre+H[m[j]]] := c[j];
    end for;
  end for;

  for i := 1 to pre do
    mat[i,i] := 1;
  end for;

  m := pre+#M;
  for i := 1 to post do
    mat[i, m + i] := 1;
  end for;

  return mat, M;
end intrinsic;


intrinsic EchelonForm( L :: [ RngMPolElt ]  ) -> []
  { Reduced row echelon form for multivariate polynomials. }

  if #L gt 0 then
    mat, V := Linearize(L);
    vprintf User1 : "Reducing a %o by %o matrix over %m... ", NumberOfRows(mat), NumberOfColumns(mat), BaseRing(mat);
    vtime User1 : mat := EchelonForm(mat);
    L0 := [ Polynomial(l, V) : l in RowSequence(mat) ];
    RemoveTrailingZeros(~L0);
    return L0;
  else
    return L;
  end if;
end intrinsic;


intrinsic EchelonForm( L :: [ ModMPolElt ] ) -> []
  { Reduced row echelon form for modules multivariate polynomials with POT order. }

  if #L gt 0 then
    IndentPush();
    Ls := [ [ p[i] : p in L ] : i in [1..Rank(Universe(L))] ];
    mats := < >; Vs := [];
    for i := 1 to #Ls do
      mat, V := Linearize(Ls[i]);
      Append(~mats, mat);
      Append(~Vs, V);
    end for;

    mat := HorizontalJoin(mats);
    vprintf User1 : "Reducing a %o by %o matrix over %m... ", NumberOfRows(mat), NumberOfColumns(mat), BaseRing(mat);
    vtime User1 : mat := EchelonForm(mat);

    indices := [];
    acc := 1;
    rs := [];
    for i := 1 to #Vs do
      Append(~rs, RowSequence(Submatrix(mat, 1, acc, #L, #Vs[i])));
      acc +:= #Vs[i];
    end for;

    L0 := [ Universe(L) | [ Polynomial( rs[i,j], Vs[i] ) : i in [1..#Ls] ] : j in [1..#L] ];

    RemoveTrailingZeros(~L0);

    IndentPop();
    return L0;
  else
    return L;
  end if;
end intrinsic;


intrinsic LinNormalForm( L :: [ ], M :: [ ], echelon :: BoolElt ) -> []
  { Reduces the elements of L modulo the elements of M. If echelon is true, then, it echelonizes the result. }

  mat, V := Linearize(L cat M : pre := #L);
  mat := EchelonForm(mat);
  mat := Submatrix(mat, 1, #L+1, #L, #V);

  if echelon then
    mat := EchelonForm(mat);
    L0 := [ Polynomial(l, V) : l in RowSequence(mat) ];
    RemoveTrailingZeros(~L0);
    return L0;
  else
    return [ Polynomial(l, V) : l in RowSequence(mat) ];
  end if;
end intrinsic;


intrinsic RelationsMatrix( L :: [] ) -> Mtrx
  {}

  mat, V := Linearize(L : post := #L);
  mat := EchelonForm(mat);
  rk := #[ j : j in RankProfile(mat) | j le #V ];
  return Submatrix(mat, rk+1, #V+1, #L - rk, #L);
end intrinsic;


intrinsic RowSpaceMatrix( L :: [] ) -> [], Mtrx
  {}

  mat, V := Linearize(L : post := #L);
  mat := EchelonForm(mat);
  rk := #[ j : j in RankProfile(mat) | j le #V ];
  matp := Submatrix(mat, 1, 1, rk, #V);
  return [ Polynomial(l, V) : l in RowSequence(mat) ], Submatrix(mat, 1, #V+1, rk, #L);
end intrinsic;



intrinsic EchelonForm_p( L0 :: [] ) -> []
  {The same as EchelonForm but without polynomials to matrices conversion.}

  L := L0;
  for i := 1 to #L do
    Sort(~L);
    Reverse(~L);

    while #L gt 0 and L[#L] eq 0 do
      Prune(~L);
    end while;

    if i gt #L then
      break;
    end if;

    L[i] /:= LeadingCoefficient(L[i]);
    m := LeadingMonomial(L[i]);

    for k := 1 to i-1 do
      L[k] -:= MonomialCoefficient(L[k], m)*L[i];
    end for;

    k := i+1;
    while k le #L and LeadingMonomial(L[k]) ge m do
      L[k] -:= MonomialCoefficient(L[k], m)*L[i];
      k +:= 1;
    end while;
  end for;

  return L;
end intrinsic;


// M doit déjà être sous forme échelon (réduite ou non)
intrinsic LinNormalForm_p( L0 :: [ RngMPolElt ], M :: [ RngMPolElt ], reduce :: BoolElt ) -> []
  {The same as LinNormalForm but without polynomials to matrices conversion.}

  L := L0;
  for j := 1 to #M do
    m := LeadingMonomial(M[j]);
    for i := 1 to #L do
      c := MonomialCoefficient(L[i], m);
      L[i] -:= c*M[j];
    end for;
  end for;

  if reduce then
    L := EchelonForm_p(L);
  end if;

  return L;

end intrinsic;


// M doit déjà être sous forme échelon (réduite ou non)
intrinsic LinNormalForm_p( L0 :: [ ModMPolElt ], M :: [ ModMPolElt ], reduce :: BoolElt ) -> []
  {The same as LinNormalForm but without polynomials to matrices conversion.}

  L := L0;
  for j := 1 to #M do
    m, k := Maximum(Eltseq(LeadingMonomial(M[j])));
    //m := LeadingMonomial(M[j]);
    // HACK parce que MonomialCoefficient(u*M.2,  u*M.1) donne 1...
    for i := 1 to #L do
      c := MonomialCoefficient(L[i][k], m);
      L[i] -:= c*M[j];
    end for;
  end for;

  if reduce then
    L := EchelonForm_p(L);
  end if;

  return L;

end intrinsic;


intrinsic RelationsMatrix_p( L0 :: [] ) -> Mtrx
  {}

  L := L0;

  indices := [ i : i in [1..#L] | L[i] ne 0];
  rels := IdentityMatrix(CoefficientRing(Universe(L0)), #L) ;

  for i := 1 to #L do
    if #indices eq 0 then
      break;
    end if;

    m, j := Maximum( [ LeadingMonomial(L[j]) : j in indices ] );
    c0 := LeadingCoefficient(L[indices[j]]);
    for k := j+1 to #indices do
      c := MonomialCoefficient(L[indices[k]], m);
      L[indices[k]] -:= c/c0*L[indices[j]];
      AddRow(~rels, -c/c0, indices[j], indices[k]);
    end for;

    Exclude(~indices, indices[j]);

    indices := [ i : i in indices | L[i] ne 0 ];

  end for;


  zeroes := [ i : i in [1..#L] | L[i] eq 0];

  rels := Submatrix(rels, zeroes, [1..#L0]);
  rels := EchelonForm(rels);

  return rels;

end intrinsic;





//////////////////////// CYCLIC EQUATION




MDer := func< m | Matrix(BaseRing(m), NumberOfRows(m), NumberOfColumns(m), [Derivative(p) : p in Eltseq(m)]) >;


function LeftKernelInterp(M)

    Kt<t> := BaseRing(M);
    K := CoefficientRing(Kt);

    RH := RHnew();
    ipoint := 100;

    while not assigned RH`candidate do
        if Characteristic(K) eq 0 then
            ipoint := K ! ipoint + 1;
        else
            ipoint := Random(K);
        end if;
        ev := hom<Kt -> K | ipoint>;
        if ipoint in RH`points then continue; end if;

        ker := Basis(NullSpace(ChangeRing(M, ev)));
        RHAddRat(~RH, ker, ipoint : denom := true);

    end while;

    return RH`candidate[1];

end function;

// Old version
intrinsic CyclicEquation(M :: Mtrx, v, den : theta := false) -> Any
  {}

  n := NumberOfRows(M);

  Kt<t> := BaseRing(M);
  Krat := Parent(1/t);
  K0 := CoefficientRing(Kt);

  if Characteristic(K0) eq 0 then
      Kev := GF(RandomPrime(23));
  else
      Kev := K0;
  end if;

  ev := hom< Kt -> Kev | Random(Kev) >;

  A := [v]; Aev := ChangeRing(v, ev);
  u := v;
  counter := 0;
  vprint User2: "Trying order... ";
  repeat
      vprintf User2: "%o... ", counter+1;
      vtime User2 : v := den*MDer(v)-counter*Derivative(den)*v+M*v;
      // v := u/den^(counter+1);
      if theta then v *:= t; end if;
      Append(~A, v);
      Aev := HorizontalJoin(ChangeRing(v, ev), Aev);
      counter +:= 1;
  until Rank(Aev) lt #A;

  vprintf User2: "OK. \n";

  m := Transpose(HorizontalJoin(Reverse(A)));
  ker := LeftKernelInterp(m);


  ret := Reverse(Eltseq(ker[1]));
  return [ret[k]*den^(k-1) : k in [1..#ret]];
end intrinsic;


function mapFun(fun, S)
    m:=NumberOfRows(S);
    n:=NumberOfColumns(S);
    return Matrix(m, n, [[fun(S[i,j]) : j in [1..n]] : i in [1..m]]);
end function;


// Faster version
// May be buggy though
// input : M a matrix with coefficients in k(t)
//         v a vector with coefficients in k(t)
//      M represents a connection D on the space k(t)^n
// output : the minimal operator L(t, D) such that L(v) = 0
intrinsic CyclicEquation2(M :: Mtrx, v : theta := false) -> Any
  {Returns the minimum annihilating differential operator.}

  n := NumberOfRows(M);

  if v eq 0 then
    return [ CoefficientRing(Parent(v)) | 1];
  end if;

  Kt<t> := BaseRing(M);
  K0 := CoefficientRing(Kt);
  if Characteristic(K0) eq 0 then
    error "Not implemented, use with care";
  end if;
  ipoint :=  Random(K0);
  ev := hom< Kt -> K0 | 0  >;
  shift := hom< Kt -> Kt | t + ipoint >;
  ishift := hom< Kt -> Kt | t - ipoint >;


  M := ChangeRing(M, shift);
  v := ChangeRing(v, shift);

  A := [v]; Aev := ChangeRing(v, ev);
  counter := 1;
  vprintf User2 : "order... ";
  repeat
    vprintf User2 : "%o... ", #A;
    v := MDer(v) + M*v;
    if theta then v *:= (Kt.1 + ipoint) ; end if;
    Append(~A, v);
    Aev := HorizontalJoin(ChangeRing(v, ev), Aev);
    counter +:= 1;
  until Rank(Aev) lt #A;
  vprintf User2 : "ok\.  ";

  rp := RankProfile(EchelonForm(Transpose(Aev)));
  M := Submatrix(HorizontalJoin(Prune(A)), rp, [1..#A-1]);
  v := Submatrix(v, rp, [1]);

  den := LCM([Denominator(p) : p in Eltseq(M) cat Eltseq(v)]);
  Mpol := mapFun(func<x | Numerator(x*den)>, M);
  vpol := mapFun(func<x | Numerator(x*den)>, v);

  storjsol := SolveByStorjohann(Mpol, vpol);

  // Check does not pass, see bug/bugs
  //error Error([*storjsol, vpol, Mpol*]);
  vprintf User2 : "Checking... ";
  assert Mpol*ClearDenominator(storjsol) eq Denominator(storjsol)*vpol;
  vprintf User2 : "Check ok.  ";
  ////////////

  sol := Eltseq(-SolveByStorjohann(Mpol, vpol));
  sol := [ ishift(Numerator(p))/ishift(Denominator(p)) : p in sol ];

  return Append(sol,1);
end intrinsic;
