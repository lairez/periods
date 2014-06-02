
//////////////////

// Basic certification over F_p

import "/Users/lairez/Applications/lib/magma/PicardFuchs/RhamKoszul.m": HomReduce_rec;
import "/Users/lairez/Applications/lib/magma/PicardFuchs/RhamKoszul.m": TotDiff;

A<x0,x1,x2,x3> := PolynomialRing(GF(65521), 4, "grevlex");
f := 2*x1*x2*x3*(x0-x1)*(x0-x2)*(x0-x3) - x0^3*(x0^3 - x0^2*x3 + x1*x2*x3);
U := InitRK(f : r:=3, variant := {"cert"});

L := [ x0^8 ];
//L := EEncode(U, L);
HomReduce(~U, ~L, 3); 

L[1,1] - TotDiff(U, L[1,2]);

L2 := [ x0^8 ];

f_prime := x1*x2*x3*(x0-x1)*(x0-x2)*(x0-x3);
ComputeGM(~U, f_prime , L2, ~ret);

dim := #ret`basis;

for i in [1..dim] do
  (Vector(ret`basis)*ChangeRing(ret`gm, U`ring))[i] - (-f_prime*ret`basis[i] + U`fromx(TotDiff(U, ret`gmcerts[i])));
end for;



///////////////////////

// GM certification over F_p(t)

SetVerbose("User2", true);

Kt<t> := FunctionField(GF(65521));
A<x0,x1,x2,x3> := PolynomialRing(Kt, 4, "grevlex");


//f := t*x1*x2*x3*(x0-x1)*(x0-x2)*(x0-x3) - x0^3*(x0^3 - x0^2*x3 + x1*x2*x3);
f :=t*x0^3*x1+t*x0^2*x2*x3+t*x1^2*x2*x3+t*x1*x2^2*x3+t*x1*x2*x3^2-x0*x1*x2*x3;


ret := GaussManin(f, 3, [ A | 1 ] : variant := {"cert"} );


dim := #ret`ebasis;

MB := Vector( [ Monomial(A, m) : m in ret`ebasis ] );
f_prime := A! Polynomial( [ Derivative(c) : c in Coefficients(f) ], Monomials(f) );

tdiff := function(pol)
  c := Coefficients(pol, Parent(pol).2);
  fun := hom<Parent(pol) -> A | [1,1] cat [A.i : i in [1..Rank(A)]]>;
  return &+[ fun(Derivative(c[i], i-1 + 2)) - Derivative(f,i-1)*fun(c[i]) : i in [2..#c] ] ;
end function;

 (MB*ChangeRing(ret`gm, A))[1] - (-f_prime*MB[1] + tdiff(ret`gmcerts[1]));


for i in [1..dim] do
  (MB*ChangeRing(ret`gm, A))[i] - (-f_prime*MB[i] + tdiff(ret`gmcerts[i]));
end for;


//////////////////////////

// GM certification over Q(t)
// Evaluation/reconstruction method down to F_p

SetVerbose("User2", true);

Kt<t> := FunctionField(Rationals());
A<x0,x1,x2,x3> := PolynomialRing(Kt, 4, "grevlex");

f :=t*x0^3*x1+t*x0^2*x2*x3+t*x1^2*x2*x3+t*x1*x2^2*x3+t*x1*x2*x3^2-x0*x1*x2*x3;
R := <f, A ! 1>;

f := t*x0^5+t*x0^4*x3+3*t*x0^3*x2*x3+2*t*x0^2*x1*x2*x3+3*t*x0^2*x2^2*x3+t*x0*x2^3*x3+t*x1^2*x2^2*x3+t*x1*x2^3*x3+t*x1*x2^2*x3^2-x0*x1*x2^2*x3;
R := <f, A ! x2>;

f_prime := A! Polynomial( [ Derivative(c) : c in Coefficients(f) ], Monomials(f) );

tdiff := function(pol)
  c := Coefficients(pol, Parent(pol).2);
  fun := hom<Parent(pol) -> A | [1,1] cat [A.i : i in [1..Rank(A)]]>;
  return &+[ fun(Derivative(c[i], i-1 + 2)) - Derivative(f,i-1)*fun(c[i]) : i in [2..#c] ] ;
end function;

basis, L := GaussManinQ(R,2 : variant := {"cert"} );

MB := Vector( [ Monomial(A, m) : m in basis ] );
dim := #basis;


for i in [1..dim] do
  (MB*ChangeRing(L[1], A))[i] - (-f_prime*MB[i] + tdiff(L[3][i]));
end for;

CyclicEquation2(L[1], L[2] : theta := false);




///////////////

// Direct method over Q(t)


SetMemoryLimit(20*2^30);
SetVerbose("User1", true);

Kt<t> := FunctionField(Rationals());
A<x0,x1,x2,x3> := PolynomialRing(Kt, 4, "grevlex");

f := t*x0^5+t*x0^4*x3+3*t*x0^3*x2*x3+2*t*x0^2*x1*x2*x3+3*t*x0^2*x2^2*x3+t*x0*x2^3*x3+t*x1^2*x2^2*x3+t*x1*x2^3*x3+t*x1*x2^2*x3^2-x0*x1*x2^2*x3;
//f := t*x0^4*x1+t*x0^4*x2+t*x0^2*x1*x2*x3+t*x0^2*x2^2*x3+2*t*x0*x1*x2^2*x3+t*x1^3*x2*x3+t*x1^2*x2^2*x3+t*x1^2*x2*x3^2+t*x1*x2^2*x3^2-x0*x1^2*x2*x3;

f_prime := A! Polynomial( [ Derivative(c) : c in Coefficients(f) ], Monomials(f) );

time U := InitRK(f : r := 2, variant := {"cert"});

time ComputeGM(~U, f_prime, [ x2 ], ~ret);

basis := ret`basis;
MB := Vector( basis );
dim := #basis;


tdiff := function(pol)
  c := Coefficients(pol, Parent(pol).2);
  fun := hom<Parent(pol) -> A | [1,1] cat [A.i : i in [1..Rank(A)]]>;
  return &+[ fun(Derivative(c[i], i-1 + 2)) - Derivative(f,i-1)*fun(c[i]) : i in [2..#c] ] ;
end function;


for i in [1..dim] do
  (MB*ChangeRing(ret`gm, A))[i] - (-f_prime*MB[i] + tdiff(ret`gmcerts[i]));
end for;

time deq := CyclicEquation2(ret`gm, ret`proj : theta := false);





