

SetVerbose("User2", true);
MDer := func< m | Matrix(BaseRing(m), NumberOfRows(m), NumberOfColumns(m), [Derivative(p) : p in Eltseq(m)]) >;

A<w,x,y,z> := PolynomialRing(Rationals(), 4);

// Target polynoms. Select yours.
// Random sparse
f1 := -28*w^2*x^2+53*w^2*x*z+13*w*x^2*z-48*w*x*y^2+5*w*x*y*z-10*x*y^2*z;

// Random dense
f1 := 72*w^4-44*w^3*x+75*w^3*y+37*w^3*z-62*w^2*x^2+62*w^2*x*y+71*w^2*x*z+42*w^2*y^2-92*w^2*y*z-23*w^2*z^2-55*w*x^3-56*w*x^2*y+97*w*x^2*z-83*w*x*y^2-82*w*x*y*z-17*w*x*z^2-7*w*y^3-50*w*y^2*z+6*w*y*z^2+87*w*z^3-7*x^4+22*x^3*y-94*x^3*z+87*x^2*y^2-73*x^2*z^2-4*x*y^3-10*x*y^2*z+80*x*y*z^2-75*x*z^3-10*y^4-40*y^3*z+23*y^2*z^2+74*y*z^3+44*z^4;

// cf 64 curves of degree 6.
f1 := 100*w^4-12500*w^2*x^2+104*x^4-12500*w^2*y^2+1640*x^2*y^2 + 1550*y^4+12500*w^2*y*z-75*x^2*y*z-1552*y^3*z+9375*w^2*z^2 - 487*x^2*z^2-1533*y^2*z^2+354*y*z^3+314*z^4;

// Emre's example
//f1 := -3*x^4+9*x*w^3-8*y^3*z-4*z^4+w^4;


// Picard rank 16
f1 := x^4 + y^4 + z^4 + w^4 + 2*x*y*z*w + 3*(x^2*y^2+z^2*w^2)+4*(x^2*z^2+y^2*w^2) + 5*(z^2*y^2+x^2*w^2);


// Start polynom
f0 := &+ [ MonomialCoefficient(f1, v^4)*v^4 : v in [w,x,y,z] ] ;



///////////// Without path splitting
time gm := GaussManinLin(f0, f1 : projection := true);

/* gm is record with the following fields :
    mat : Matrix with univariate polynomials coefficients
    den : univariate polynomial
    genbasis : basis of the cohomology of V(f_t)
    basis : basis of the cohomology of V(f_0)
    proj : matrix with univariate rational coefficients
    ini : matrices to compute the initial conditions

They satisfy :
    den * genbasis' = genbasis * mat
    basis * proj = genbasis
*/


// Consistency check : two different ways of computing the initial conditions
K<t> := CoefficientRing(gm`proj);
ev0 := hom<K -> Rationals() | 0 >;

dproj := Matrix(21, 21, [Derivative(p) : p in Eltseq(gm`proj)]);

gm`inimat[1] - ChangeRing(gm`proj, ev0);
gm`inimat[2] - ChangeRing(gm`proj*gm`mat/gm`den, ev0);
M2 := gm`proj*gm`mat^2/gm`den^2 + gm`proj*(MDer(gm`mat)*gm`den - Derivative(gm`den)*gm`mat)/gm`den^2;
gm`inimat[3] - ChangeRing(M2, ev0);

/////////////////////////////////////////
// With path splitting

L := DeformationSeq(f0, f1 : randomize := true);
gms := [];

#L;

for i in [1..#L-1] do
    time gm  := GaussManinLin(L[i], L[i+1]);
    Append(~gms, gm);
end for;


//////////////////////////////////////
/// Numerical periods



SetVerbose("User2", true);
MDer := func< m | Matrix(BaseRing(m), NumberOfRows(m), NumberOfColumns(m), [Derivative(p) : p in Eltseq(m)]) >;

A<w,x,y,z> := PolynomialRing(Rationals(), 4);

// Target polynoms. Select yours.
// Random sparse
f1 := -28*w^2*x^2+53*w^2*x*z+13*w*x^2*z-48*w*x*y^2+5*w*x*y*z-10*x*y^2*z;

// Random dense
f1 := 72*w^4-44*w^3*x+75*w^3*y+37*w^3*z-62*w^2*x^2+62*w^2*x*y+71*w^2*x*z+42*w^2*y^2-92*w^2*y*z-23*w^2*z^2-55*w*x^3-56*w*x^2*y+97*w*x^2*z-83*w*x*y^2-82*w*x*y*z-17*w*x*z^2-7*w*y^3-50*w*y^2*z+6*w*y*z^2+87*w*z^3-7*x^4+22*x^3*y-94*x^3*z+87*x^2*y^2-73*x^2*z^2-4*x*y^3-10*x*y^2*z+80*x*y*z^2-75*x*z^3-10*y^4-40*y^3*z+23*y^2*z^2+74*y*z^3+44*z^4;

// cf 64 curves of degree 6.
f1 := 100*w^4-12500*w^2*x^2+104*x^4-12500*w^2*y^2+1640*x^2*y^2 + 1550*y^4+12500*w^2*y*z-75*x^2*y*z-1552*y^3*z+9375*w^2*z^2 - 487*x^2*z^2-1533*y^2*z^2+354*y*z^3+314*z^4;

// Emre's example
//f1 := -3*x^4+9*x*w^3-8*y^3*z-4*z^4+w^4;


// Picard rank 16 ???
f1 := x^4 + y^4 + z^4 + w^4 + 2*x*y*z*w + 3*(x^2*y^2+z^2*w^2)+4*(x^2*z^2+y^2*w^2) + 5*(z^2*y^2+x^2*w^2);


// Start polynom
f0 := &+ [ MonomialCoefficient(f1, v^4)*v^4 : v in [w,x,y,z] ] ;



///////////// Without path splitting
time gm := GaussManinLin(f0, f1);





