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


// log channel : User1

/***********************
 * Fonctions pour extraire des bases en degré fixé
 */


// Il faudrait faire un peu de mémoïsation
//( a :: RngMPolElt, B :: [RngMPolElt], vars :: [RngMPolElt], deg :: RngIntElt )
// Renvoie l'ensemble des monômes de degré deg, produit de a par un monôme en
// vars mais pas divisible par l'un des monômes de B.
function DiffStairs( a, B, vars, deg ) 
  if deg lt Degree(a) then
    return { Parent(a) | };
  elif deg eq Degree(a) then
    return { NormalForm(a, B) } diff { Zero(Parent(a)) };
  end if;

  r := DiffStairs(a, B, vars, deg-1);
  ret := { v*e : v in vars, e in r };
  ret := Set(NormalForm(ret, B)) diff { Zero(Parent(a)) };
  return ret;
end function;

// Renvoie l'ensemble des monômes de degré deg multiples de l'un des monômes de
// A mais pas divisible par l'un des monômes de B.
function BasisAtDegree( A , B, vars, deg ) 
  ret := [ Universe(A) | ];
  BB := B;

  for a in A do
    lm := LeadingMonomial(a);
    D := DiffStairs(lm, BB, vars, deg);
    ret cat:= [ (d div lm)*a : d in D ];
    Append(~BB, lm);
  end for;
  return ret;
end function;

intrinsic BasisSyzyiges( U :: Rec, deg ) -> []
  {}
  return BasisAtDegree( U`syz, U`tsyzlm, U`vars, deg + 1 );
end intrinsic;


/****************
 ** Initialisation
 ** */


// Structure pour stocker les calculs.
RKrecformat := recformat<
  f,      // Polynôme homogène
  ring,   // L'anneau dans lequel f vit
  xring,  //  k[x0, ..., xn, u, v], ordonné avec grevlex, avec
    // u et v n'apparaissant pas dans f.

  tox, fromx,
  deg,    // Le degré de f
  df,     // La suite de ses dérivées partielles
  tsyzlm,   // Base de Gröbner des syzygies triviales
  syz,    // Base de Gröbner des syzygies
  dim,    // Dimension du problème (le nombre de variables dans f)
  jac,
  basisWdown, basisU,
  vars,   // Variables de f
  r,
  gens,  //  Encodage
  u, v, vshift,
  variant,
  prof, profmode,
  repmode,
  emod
  >;

RKprof := recformat< tsyzlm, syzlm >;

intrinsic InitRK( f :: RngMPolElt : variant := { }, der := 1, r := 1, prof := rec< RKprof | > ) -> Rec
  {}

  U := rec<RKrecformat |
    f := f,
    r := r,
    dim := Rank(Parent(f)),
    ring := Parent(f),
    basisU := AssociativeArray(),
    basisWdown := AssociativeArray(),
    deg := Degree(f),
    variant := variant,
    prof := prof
  >;

  n := U`dim;
  R := PolynomialRing(CoefficientRing(U`ring), n+2, "grevlex");
  
  if assigned prof`syzlm then U`profmode := "get";
  else
    if "profile" in variant then U`profmode := "set";
    else U`profmode := "";
    end if;
  end if;

  if not "altord" in variant then
    AssignNames(~R, [ "u", "v" ] cat [ "x" cat IntegerToString(i-1) : i in [1..U`dim] ] ); 
    u := R.1; v := R.2;  
    tox := hom< U`ring -> R | [ R.(i+2) : i in [1..n]] >;
    fromx := hom< R -> U`ring | [U`ring | 1, 0] cat [ U`ring.i : i in [1..n]]   >;
    U`vshift := 2;
  else
    AssignNames(~R, [ "x" cat IntegerToString(i-1) : i in [1..n] ] cat [ "u", "v" ]); 
    u := R.(n + 1); v := R.(n + 2);
    tox := hom< U`ring -> R | [ R.i : i in [1..n]] >;
    fromx := hom< R -> U`ring | [ U`ring | U`ring.i : i in [1..n]] cat [U`ring | 1, 0]  >;
    U`vshift := 0;
  end if;

  U`u := u; U`v := v;
  U`xring := R;
  U`tox := tox; U`fromx := fromx;

  U`df := [ tox(Derivative(f, i)) : i in [1..n]];
  U`vars := [ R | tox(U`ring.i) : i in [1..n]];
  
  U`gens := [ u^(n-i)*v^i : i in [0..n] ];
  xrels := [ u^i*v^(n+1-i) : i in [0..n+1] ];


  vprintf User1 : "Computing Groebner basis of Jacobian ideal... ";
  U`jac := ideal< U`xring | [ U`df[i]*U`gens[1] - U`gens[1+i] : i in [1..n]] cat xrels >;
  Groebner(U`jac);
  U`syz := [ p : p in Basis(U`jac) | Degree(p, u) lt n ];

  if assigned prof`tsyzlm then
    U`tsyzlm := [ Monomial(R, e) : e in prof`tsyzlm ];
  else
    tsyz := Ideal([ U`df[i]*U`gens[1+j]-U`df[j]*U`gens[1+i] : i, j in [ 1..n ]] cat  xrels);
    vprintf User1 : "Computing syzygies... ";
    vtime User1 : U`tsyzlm := Basis(LeadingMonomialIdeal(tsyz));
    U`prof`tsyzlm := [ Exponents(p) : p in U`tsyzlm ];
  end if;

  if "cert" in variant then
    U`emod := EModule(U`xring, 2, "pot");
    U`repmode := "R:c";
  elif U`profmode eq "set" then
    U`emod := EModule(U`xring, 3, "pot");
    U`repmode := "R:p";
    vprintf User2 : "with profile.\n ";
  else
    U`emod := U`xring;
    U`repmode := "R";
  end if;

  return U;
end intrinsic;


/*******************
 * Réduction via Rham-Koszul à la Dimca
 */

//intrinsic ExtDiff( U :: Rec, a :: RngMPolElt ) -> RngMPolElt {}
function ExtDiff(U, a)
  c := Coefficients(a, U`v);
  if #c gt 0 then
    sh := U`vshift;
    return c[1] + &+[ U`xring | Derivative(c[i], i-1 + sh)*U`u^(i-1) : i in [2..#c] ];
  else
    return Zero(U`xring);
  end if;
end function;

//intrinsic ExtProd( U :: Rec, a :: RngMPolElt ) -> RngMPolElt {}
function ExtProd(U, a)
  c := Coefficients(a, U`v);  
  return c[1] + &+[ U`xring | U`df[i-1]*c[i]*U`u^(i-1) : i in [2..#c] ];
end function;

function TotDiff( U, a )
  return ExtDiff(U, a) - ExtProd(U, a);
end function;


/************************
 * Différents modes de réprésentation
 */

function ERedStep( U, L0 ) 
  if #L0 gt 0 then
    vprintf User1 : " --- Normalising %o elements of degree %o...  ", #L0, Maximum([Degree(p) : p in L0]);
  else
    return L0;
  end if;
  vtime User1 : case U`repmode :
  when "R" :
    L := NormalForm(L0, U`jac);
    return [ U`emod | ExtDiff(U, p) : p in L ];
  when "R:c" :
    L := NormalForm([p[1] : p in L0], U`jac);
    Lcof := [ p - Evaluate(p, U`v, 0) : p in L ];
    return [ U`emod | [ ExtDiff(U, L[i]), L0[i, 2] + Lcof[i] ] : i in [1..#L] ];
  when "R:p" :
   L := NormalForm([ p[3] : p in L0 ], U`jac);
   return [ U`emod | [ Coefficient(L[i], 1, U`dim), L0[i,2], ExtDiff(U, L[i]) ] : i in [1..#L0] ];
  end case;
end function;

function ESplit( U, L0, q )
  case U`repmode :
  when "R" : return [ p : p in L0 | Degree(p) eq q ], [ p : p in L0 | Degree(p) lt q ];
  when "R:c" : return [ p : p in L0 | Degree(p[1]) eq q ], [ p : p in L0 | Degree(p[1]) lt q ];
  when "R:p" : return [ p : p in L0 | p[1] ne 0 ], [ p : p in L0 | p[1] eq 0 ];
  end case;
end function;

function ECastSyz( U, S )
  dS := [ ExtDiff(U, p) : p in S ];
  case U`repmode :
  when "R" : return dS;
  when "R:c": return [ U`emod | [ dS[i], S[i] ] : i in [1..#S]];
  when "R:p" : return [ U`emod | [ 0, LeadingMonomial(S[i]), dS[i] ] : i in [1..#S]];  
  end case;
end function;

function EEncode( U, L )
  case U`repmode :
  when "R" : return [ U`emod | U`tox(p)*U`gens[1] : p in L ];
  when "R:c" : return [ U`emod | U`tox(p)*U`gens[1]*U`emod.1 : p in L ];
  when "R:p" : return [ U`emod | U`tox(p)*U`gens[1]*U`emod.3 : p in L ];  
  end case;
end function;

function EDecode( U, L )
  case U`repmode :
  when "R" : return [ U`ring | U`fromx(p) : p in L ];
  when "R:c": return [ U`ring | U`fromx(p[1]) : p in L ];
  when "R:p": return [ U`ring | U`fromx(p[3]) : p in L ];
  end case;
end function;

function EWeight(U, L )
  case U`repmode :
  when "R" : return Integers() ! Maximum([ Degree(p) : p in L ]);
  when "R:c": return Integers() ! Maximum([ Degree(p[1]) : p in L ]);
  when "R:p": return Integers() ! Maximum([ Degree(p[3]) : p in L ]);
  end case;
end function;
  

/****************
  * Coeur de l'algorithme
  */

intrinsic BasisU( ~U :: Rec, r, q )
  {Compute the vector space U^r_q. Slight variation compared to the paper.}

  requirege r, 0;
  IndentPush();

  if IsDefined(U`basisU, <r, q>) then
  elif r eq 0 then
    U`basisU[<r,q>] := [ U`emod | ];
  elif r eq 1 then
    syz := BasisSyzyiges(U, q-U`deg);
    if assigned U`prof`syzlm then
      syz := [ p : p in syz | Exponents(LeadingMonomial(p)) in U`prof`syzlm ];
    end if;

    U`basisWdown[<r,q>] := ECastSyz(U, syz);
    U`basisU[<r,q>] := [ U`emod | ];
  elif r gt 1 then
    vprintf User1 : "Computing U for r = %o and q = %o. \n ", r, q; 
    BasisU(~U, r-1, q);
    BasisU(~U, r-1, q+U`deg);

    rels := ERedStep(U, U`basisWdown[<r-1,q+U`deg>]);
    new := EchelonForm(U`basisU[<r-1,q>] cat rels);

    U`basisU[<r,q>], U`basisWdown[<r,q>] := ESplit(U, new, q);
  end if;

  IndentPop();
end intrinsic;


procedure HomReduce_rec( ~U, ~L, r )
  q := EWeight(U, L);  
  while q gt 0 do
    L := ERedStep(U, L);

    BasisU(~U, r, q);
    L := LinNormalForm_p(L, U`basisU[<r,q>], false);

    q -:= U`deg;
  end while;
end procedure;


intrinsic HomReduce( ~U :: Rec, ~L :: [], r :: RngIntElt )
  {L a list of polynomial with adequate degree. Returns the reduction []_r.}

  requirege r, 1;
  require Universe(L) eq U`ring : "Bad argument type";

  L := EEncode(U, L);
  HomReduce_rec(~U, ~L, r);
  L := EDecode(U, L);
end intrinsic;


RKGMfmt := recformat< basis, ebasis, proj, gm >;
intrinsic ComputeGM(~U, der, L, ~ret)
  {L a list of polynomials. der a polynomial. Returns (in ret) the monomial
  basis of the space generated by L and the multiplication by der.  Returns the
  matrix in this basis of the multiplication by der. All modulo []_r, with r =
  U`r.}

  proj := L;
  HomReduce(~U, ~proj, U`r);

  basis := [];
  gm := [];
  xmons := Setseq(&join[ Seqset(Monomials(p)) : p in L ]);
  
  while #xmons gt 0 do
    Sort(~xmons);
    basis cat:= xmons;
    nf := [ -der*p : p in xmons ];
    HomReduce(~U, ~nf, U`r);
    gm cat:= nf;
    if Maximum([Degree(p) : p in gm]) gt (U`dim-1)*U`deg then
      error Error("r_toosmall");
    end if;
    xmons := Setseq(&join[ Seqset(Monomials(p)) : p in nf ] diff Seqset(basis));
  end while;
  
  ret := rec<RKGMfmt |  >;
  
  ret`basis := basis;

  ret`gm := Matrix( CoefficientRing(U`ring), #basis, #basis,
    [ [ MonomialCoefficient(gm[j], basis[i]) : j in [1..#basis] ] : i in [1..#basis] ] );
    
  ret`proj := Matrix( CoefficientRing(U`ring), #basis, #L,
    [ [ MonomialCoefficient(proj[j], basis[i]) : j in [1..#L] ] : i in [1..#basis] ] );
    
  ret`ebasis := [ Exponents(m) : m in basis ];
end intrinsic;


intrinsic ComputeProfile(~U)
  {}

  if U`repmode eq "R:p" then
    U`prof`syzlm := {};
    for k in Keys(U`basisU) do
      U`prof`syzlm join:= &join[ { Exponents(m) : m in Monomials(p[2]) } : p in U`basisU[k] ];
    end for;
  else

  end if;
end intrinsic;


