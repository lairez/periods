
// This compares different methods for reducing polymials
// modulo a jacobian ideal, with cofactors.

///// METHODE 1

A<x0,x1,x2,x3,x4> := PolynomialRing(GF(65521), 5, "grevlex");
f := 5*x0^3*x1^2+5*x0^3*x1*x2+5*x0^3*x1*x4+5*x0^2*x1^2*x2+5*x0^2*x1^2*x4+5*x0^2*x1*x2*x3+5*x0^2*x1*x2*x4+5*x0^2*x1*x3*x4+5*x0^2*x2*x3*x4+5*x0^2*x3*x4^2+5*x0*x1^2*x2*x3+5*x0*x1^2*x2*x4+5*x0*x1^2*x3*x4+5*x0*x1*x2^2*x3-x0*x1*x2*x3*x4+5*x0*x1*x3*x4^2+5*x0*x2^2*x3*x4+5*x0*x2*x3^2*x4+5*x0*x2*x3*x4^2+5*x1^2*x2*x3*x4+5*x1*x2^2*x3*x4+5*x1*x2*x3^2*x4+5*x1*x2*x3*x4^2+5*x2^2*x3^2*x4;
n := 5;

Jac := IdealWithFixedBasis([ Derivative(f, i) : i in [1..n]]);
time Groebner(Jac);
// 0.040s

L := Monomials( &+[ A.i : i in [1..n]]^30 );
SetSeed(10);
L := [ Random(L) : i in [1..200]];

time Lred := NormalForm(L, Jac);
// 0.860s

time Cof := [ Coordinates( Jac, L[i]-Lred[i] ) : i in [1..#L] ];
// > 1 min



///// METHODE 2

//SetVerbose("Groebner", 2);
A<x0,x1,x2,x3,x4, u, v> := PolynomialRing(GF(65521), 7, "grevlex");
vars := [x0,x1,x2,x3,x4];
f := 7*x0^3*x1^2+7*x0^3*x1*x2+7*x0^3*x1*x4+7*x0^2*x1^2*x2+7*x0^2*x1^2*x4+7*x0^2*x1*x2*x3+7*x0^2*x1*x2*x4+7*x0^2*x1*x3*x4+7*x0^2*x2*x3*x4+7*x0^2*x3*x4^2+7*x0*x1^2*x2*x3+7*x0*x1^2*x2*x4+7*x0*x1^2*x3*x4+7*x0*x1*x2^2*x3-x0*x1*x2*x3*x4+7*x0*x1*x3*x4^2+7*x0*x2^2*x3*x4+7*x0*x2*x3^2*x4+7*x0*x2*x3*x4^2+7*x1^2*x2*x3*x4+7*x1*x2^2*x3*x4+7*x1*x2*x3^2*x4+7*x1*x2*x3*x4^2+7*x2^2*x3^2*x4;

n := 5;

Jac := Ideal([ Derivative(f, vars[i])*u^n - v^i*u^(n-i) : i in [1..n]] cat [ u^i*v^(n+1-i) : i in [0..n+1] ]);
time Groebner(Jac);
// 0.280 s


L := Monomials( u^n*(&+vars)^20 );
SetSeed(10);
L := [ Random(L) : i in [1..200]];
time Lred := NormalForm(L, Jac);
// 3.050s


///// METHODE 2 bis

A<u, v, x0,x1,x2,x3,x4> := PolynomialRing(GF(65521), 7, "grevlex");
vars := [x0,x1,x2,x3,x4];
f := 5*x0^3*x1^2+5*x0^3*x1*x2+5*x0^3*x1*x4+5*x0^2*x1^2*x2+5*x0^2*x1^2*x4+5*x0^2*x1*x2*x3+5*x0^2*x1*x2*x4+5*x0^2*x1*x3*x4+5*x0^2*x2*x3*x4+5*x0^2*x3*x4^2+5*x0*x1^2*x2*x3+5*x0*x1^2*x2*x4+5*x0*x1^2*x3*x4+5*x0*x1*x2^2*x3-x0*x1*x2*x3*x4+5*x0*x1*x3*x4^2+5*x0*x2^2*x3*x4+5*x0*x2*x3^2*x4+5*x0*x2*x3*x4^2+5*x1^2*x2*x3*x4+5*x1*x2^2*x3*x4+5*x1*x2*x3^2*x4+5*x1*x2*x3*x4^2+5*x2^2*x3^2*x4;

n := 5;

Jac := Ideal([ Derivative(f, vars[i])*u^n - v^i*u^(n-i) : i in [1..n]] cat [ u^i*v^(n+1-i) : i in [0..n+1] ]);
time Groebner(Jac);
// 0.140 s

L := Monomials( u^n*(&+vars)^20 );
SetSeed(10);
L := [ Random(L) : i in [1..200]];
time Lred := NormalForm(L, Jac);
// 2.430s



////// METHODE 3


A<x0,x1,x2,x3,x4> := PolynomialRing(GF(65521), 5, "grevlex");
vars := [x0,x1,x2,x3,x4];

f := 5*x0^3*x1^2+5*x0^3*x1*x2+5*x0^3*x1*x4+5*x0^2*x1^2*x2+5*x0^2*x1^2*x4+5*x0^2*x1*x2*x3+5*x0^2*x1*x2*x4+5*x0^2*x1*x3*x4+5*x0^2*x2*x3*x4+5*x0^2*x3*x4^2+5*x0*x1^2*x2*x3+5*x0*x1^2*x2*x4+5*x0*x1^2*x3*x4+5*x0*x1*x2^2*x3-x0*x1*x2*x3*x4+5*x0*x1*x3*x4^2+5*x0*x2^2*x3*x4+5*x0*x2*x3^2*x4+5*x0*x2*x3*x4^2+5*x1^2*x2*x3*x4+5*x1*x2^2*x3*x4+5*x1*x2*x3^2*x4+5*x1*x2*x3*x4^2+5*x2^2*x3^2*x4;

n := 5;

M := EModule( A, n+1, "top" );
S := sub< M | [  Derivative(f, vars[i])*M.1 - M.(i+1) : i in [1..n] ] >;
time Groebner(S);


L := Monomials( (&+vars)^20 * M.1 );
SetSeed(10);
L := [ Random(L) : i in [1..200]];
time Lred := [NormalForm(l, S) : l in L];
// Longtemps...



