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


//AttachSpec("PFdev.spec");

/******************
 * Calcul de la connection de Gauss-Manin
 */

RKGMfmt := recformat< basis, ebasis, proj, gm >;
RKprof := recformat< tsyzlm, syzlm >;


// Calcul en évaluation.
intrinsic GaussManin(f, r, L : modulo := 0, variant := {}, prof := rec< RKprof | > ) -> Rec, Rec
  {}

  IndentPush();

  A := Parent(f);
  K := CoefficientRing(A);
  dim := Rank(A);

  ipoint := 100;
  if modulo eq 0 then
      Kev := CoefficientRing(K);
  else
    Kev := GF(modulo);
  end if;

  B := PolynomialRing(Kev, dim, "grevlex");
  ft := Polynomial( [ Derivative(c) : c in Coefficients(f) ], Monomials(f) );
  //if "theta" in variant then ft *:= K.1; end if;

  RH := RHnew();
  basis := [];
  profile := prof;

  rtoosmall := 0;

  point_counter := 0;
  while not assigned RH`candidate do
    if modulo eq 0 then
        ipoint := Kev ! ( ipoint + 1 );
    else
        ipoint := Random(Kev);
    end if;
    if ipoint in RH`points then continue; end if;
    point_counter +:= 1;

    vprintf User2 : "Computing connexion at point number %o (%o)... ", point_counter, ipoint ;
    vtime User2 :  if true then

    evc := hom< K -> Kev | ipoint >;
    ev := hom< A -> B | evc, [B.i : i in [1..dim]] >;

    U := InitRK(ev(f) : variant := variant, prof := profile, r := r);

    try
      ComputeGM(~U, ev(ft), [ev(p) : p in L], ~gm);

      if #basis ne #gm`basis then
        vprintf User2 : "Found %o independent integrals. \n", #gm`basis;
        basis := gm`basis;
      end if;

      ComputeProfile(~U);
      profile := U`prof;
      RHAddRat(~RH, [* gm`gm, gm`proj *], ipoint : xkey := gm`ebasis );
    catch e
      if e`Object eq "r_toosmall" then
        rtoosmall +:= 1;
        if rtoosmall ge 3 then
          vprintf User2 : "r is too small, raising error";
          error Error("r_toosmall");
        end if;
      else
        error e;
      end if;
    end try;

    end if; //vtime
  end while;

  IndentPop();

  ret := rec< RKGMfmt | ebasis := gm`ebasis, gm := RH`candidate[1], proj := RH`candidate[2] >;

  return ret, profile;
end intrinsic;

/*
intrinsic GaussManinSys(f, r, L : modulo := 0, modsize := 23, variant := {}, prof := rec< RKprof | > ) -> Any, Any, Any
  {}

  if modulo gt 0 then
      return GaussManin(f, r, L : modulo := modulo, variant := variant, prof := prof);
  end if;

  RH := RHnew();
  profile := prof;
  prime_counter := 0;
  rtoosmall := 0;
  ebasis := 0;

  IndentPush();
  while not assigned RH`candidate do
    modp := RandomPrime(modsize);
    if modp in RH`points then continue; end if;
    prime_counter +:= 1;

    vprintf User2 : "Computing Gauss-Manin connection modulo prime number %o (%o)...  ", prime_counter, modp;

    try
      vtime User2 : rec, profile := GaussManin(f, r, L : modulo := modp, variant := variant, prof := profile);

      RHAddMod(~RH, [* rec`gm, rec`proj *], modp : xkey := rec`ebasis);
      ebasis := rec`ebasis;
    catch e
      vprintf User2 : e`Object;
      if e`Object eq "r_toosmall" then
        rtoosmall +:= 1;
        if rtoosmall ge 3 then
          vprintf User2 : "r is too small, raising error";
          error Error("r_toosmall");
        end if;
      else
        error e;
      end if;
    end try;

  end while;
  IndentPop();

  return ebasis, RH`candidate[1], RH`candidate[2];
end intrinsic;
*/

/***********************
 * Linear homotopies
 */



intrinsic
    GaussManinLin(f0, f1, basis : r := 1, variant := {}) -> Any, Any {}

    RH := RHnew();

    ipoint := CoefficientRing(Parent(f0)) ! 100;
    point_counter := 0;

    IndentPush();
    while not assigned RH`candidate do
        ipoint +:= 1;
        point_counter +:= 1;
        vprintf User2 : "Computing connexion at point number %o (%o)... ", point_counter, ipoint ;

      //try
        U := InitRK((1-ipoint)*f0 + ipoint*f1 : variant := variant, r := r);
        vtime User2 : ComputeGM(~U, f1-f0, basis, ~gm);

        mat := gm`proj^(-1)*gm`gm*gm`proj;

        RHAddRat(~RH, mat, ipoint : xkey := gm`ebasis);
      /*catch e
          if e`Object eq "r_toosmall" then
              rtoosmall +:= 1;
              if rtoosmall ge 9 then
                  vprintf User2 : "r is too small, raising error";
                  error Error("r_toosmall");
              end if;
          else
              error e;
          end if;
      end try;*/
    end while;
    IndentPop();

    return RH`candidate;

end intrinsic;


/********************
 * Calcul des équations de Picard-Fuchs
 */

// Integration par rapport à la première variable.
intrinsic PicardFuchs(R, r : modsize := 23, name := "t", variant := {}, prof := rec< RKprof | >) -> Any
  {}

  RH := RHnew();
  profile := prof;
  prime_counter := 0;
  rtoosmall := 0;

  IndentPush();
  while not assigned RH`candidate do
    modulo := RandomPrime(modsize);
    if modulo in RH`points then continue; end if;
    prime_counter +:= 1;

    vprintf User2 : "Computing Picard-Fuchs equation modulo prime number %o (%o).\n  ", prime_counter, modulo;

    try
      vtime User2 : rec, profile := GaussManin(R[1], r, [ R[2] ] : modulo := modulo, variant := variant, prof := profile);
      vprintf User2 : "Computing linear relation... ";

      vtime User2 : deq := CyclicEquation(rec`gm, rec`proj : theta := "theta" in variant);
      vprintf User2 : "Found an equation of order %o and degree %o.\n", #deq-1, Maximum([Maximum([Degree(Numerator(p)), Degree(Denominator(p))]) : p in deq]);

      RHAddMod(~RH, deq, modulo);
    catch e
      vprintf User2 : e`Object;
      if e`Object eq "r_toosmall" then
        rtoosmall +:= 1;
        if rtoosmall ge 3 then
          vprintf User2 : "r is too small, raising error";
          error Error("r_toosmall");
        end if;
      else
        error e;
      end if;
    end try;

  end while;
  IndentPop();

  return RH`candidate, profile;
end intrinsic;

//////////////////////////
/// Heuristiques

function minimize_degree(f : rounds := 3, concurrent := 10)
  A := Parent(f);
  //A := Parent(Denominator(f));
  prod := &* [A.i : i in [1..Rank(A)]] ;

  L := { <f*prod, ScalarMatrix(Integers(), Rank(A), 1)> };
  current := Degree(Denominator(f));
  start := current;
  vprintf User2 : "Degree minimisation : from %o to  ", current;

  counter := 0;
  while counter le rounds do
    vprintf User2 : ".";
    L0 := {
      < Evaluate(Numerator(h[1]), i, 1/A.i)/Evaluate(Denominator(h[1]), i, 1/A.i), MultiplyRow(h[2], -1, i) >
      : i in [1..Rank(A)], h in L } join {
      < Evaluate(Numerator(h[1]), i, A.i*(A.j)^e)/Evaluate(Denominator(h[1]), i, A.i*(A.j)^e), AddRow(h[2], e, j, i) >
      : i, j in [1..Rank(A)], e in [-1,1], h in L | i ne j };

    min := Minimum([Degree(Denominator(h[1]/prod)): h in L0]);
    if current le min then
      counter +:= 1;
    end if;
    if min lt current then
      vprintf User2 : "%o", min;
    end if;
    if min le current then
      L := { h : h in L0 | Degree(Denominator(h[1]/prod)) le min };
      L := RandomSubset(L, Minimum(#L, concurrent));
      current := min;
    end if;
  end while;

  vprintf User2 : "%o\n", current;

  if current eq start then
    return f, ScalarMatrix(Integers(), Rank(A), 1);
  else
    pick := Random(L);
    return pick[1]/prod, pick[2];
  end if;
end function;

function prepare_fraction(R)
  F := Parent(R);
  n := Rank(F);
  Ph := PolynomialRing( CoefficientRing(F), n+1, "grevlex" );
  Fh := Parent(Ph.1/Ph.2);
  Rh := 1/(Fh.(n+1) ^ (n+1)) * (hom< F -> Fh | [ Fh.i/Fh.(n+1) : i in [1..n] ] >(R));

  f := Denominator(Rh);

  den := LCM([Denominator(p) : p in Coefficients(f)]);
  facts := SquarefreeFactorization(f);
  fsf := &*[ ClearDenominators(p[1]) : p in facts ];         // Notre numérateur sans carré.
  deg := Maximum([ p[2] : p in facts ]);

  vprintf User2 : "The square-free part of the denominator has degree %o.", Degree(fsf);

  return <fsf, Numerator( fsf^deg*Rh )>;
end function;

function easy_order(R)  // This is very questionable
  L := Monomials(Polynomial([Derivative(p) : p in Coefficients(R[1])], Monomials(R[1])));
  _, k := Minimum([ Sort(Exponents(p)) : p in Monomials(Polynomial([Derivative(p) : p in Coefficients(R[1])], Monomials(R[1])))]);

  vars := [Parent(R[1]).i : i in [1..Rank(Parent(R[1]))]];
  exp := [ &+[ Exponents(p)[i] : p in L] : i in [1..#vars] ];//Exponents(L[k]);
  ParallelSort(~exp, ~vars);

  perm := hom< Parent(R[1]) -> Parent(R[1]) | Reverse(vars) >;
  return < perm(R[1]), perm(R[2])>;
end function;

function random_order(R)
  vars := [Parent(R[1]).i : i in [1..Rank(Parent(R[1]))]];
  exp := [Random(1000) : v in vars];
  ParallelSort(~exp, ~vars);

  perm := hom< Parent(R[1]) -> Parent(R[1]) | Reverse(vars) >;
  return < perm(R[1]), perm(R[2])>;
end function;


intrinsic Periods(f : r := 1, variant := {}, onlyprep := false) -> Any
  {f a rational function. The first variable is the parameter. Outputs an
  annihilating operator of the periods.}

  A := Parent(f);
  Kt<t> := FunctionField(CoefficientRing(A));
  B<[u]> := FunctionField(Kt, Rank(A)-1);
  chvar := [B ! Kt.1] cat [ B.i : i in [1..Rank(B)] ];
  g := Evaluate(Numerator(f), chvar) / Evaluate(Denominator(f), chvar);

  vprintf User2 : "Integrating %o", g;
  if "mindeg" in variant then
    g, mat := minimize_degree(g);
    vprintf User2 : "Integrating %o \n", g;
    vprintf User2 : "Change of variables:\n %o \n", mat;
  end if;

  R := prepare_fraction(g);
  if "randord" in variant then
    // Extremely questionable
    R := easy_order(easy_order(random_order(prepare_fraction(g))));
  end if;

  if onlyprep then
    return R;
  end if;

  repeat
    try
      deq := PicardFuchs(R, r : variant := variant);
    catch e
      if e`Object eq "r_toosmall" then
        vprintf User2 : "Increasing r";
        r +:= 1;
      else
        error e`Object;
      end if;
    end try;
  until assigned deq;

  dop<D> := PolynomialRing(Universe(deq));
  return dop ! deq;
end intrinsic;

intrinsic LaurentSequence(f : r := 1, variant := {}, onlyprep := false) -> Any
  {f a Laurent polynomial. (But after all, this is not checked.) Outputs an
  annihilating operator of the generating function of c.t.(f^n).}

  A := Parent(f);
  B := FunctionField(CoefficientRing(A), Rank(A)+1);
  chvar :=  [ B.i : i in [2..Rank(B)] ];
  ft := 1/(1-(B.1)*( Evaluate(Numerator(f), chvar)/Evaluate(Denominator(f), chvar))) / &*chvar ;

  return Periods(ft : r := r, variant := variant, onlyprep := onlyprep);
end intrinsic;

intrinsic Diagonal(f : r := 1, variant := {}, onlyprep := false) -> Any
  {f a rational function. Outputs an annihilating operator of its diagonal.}

  A := Parent(f);
  vars := [ A.i : i in [2..Rank(A)] ];
  chvar := [ A.1/&*vars ] cat vars;

  ft := Evaluate(Numerator(f), chvar) / Evaluate(Denominator(f), chvar) / &*vars;

  return Periods(ft : r := r, variant := variant, onlyprep := onlyprep);
end intrinsic;
