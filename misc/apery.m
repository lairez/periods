SetVerbose("User2", true);
SetAssertions(2);

// A PERIOD

A<t,x,y,z> := FunctionField(Rationals(), 4);
f1 := 1/(1-(1-x*y)*z-t*x*y*z*(1-x)*(1-y)*(1-z));
// sum( t^n * sum(binomial(n,k)^2*binomial(n+k,k)^2, k=0..n), n=0..infinity ) is a period of int(f1 dx dy dz)
// (Beukers, 1983)

// Gives an equation of order 4.
time deq1 := Periods(f1);

// Gives an equation of order 3.
time deq1 := Periods(f1 : r := 2);

// This may speed up the computation
// The first evaluation is slower, but all other are faster
// This example is not big enough to see the speed-up
time deq1 := Periods(f1 : r := 2, variant := {"profile"});

// This introduces a non-deterministic heuristic
time deq1 := Periods(f1 : variant := {"mindeg"});
time deq1 := Periods(f1 : variant := {"mindeg"});
// This seems catastrophic but with r = 2, this is much faster
time deq1 := Periods(f1 : r := 2, variant := {"mindeg"});

time deq1 := Periods(f1 : r := 2, variant := {"mindeg", "profile"});



// A DIAGONAL

f2 := 1/(1-y*(1+x)*(x+t*(x+1))*(1+z)*(t*z+z+1));
// The diagonal of this rational function are again the generating function of the Apery numbers
// (Bostan & Salvy, 2013)

time deq2 := Diagonal(f2);  // Order 8, degree 30
time deq2 := Diagonal(f2 : r := 2 ); // Order 5
time deq2 := Diagonal(f2 : r := 3 ); // Order 3, but quite slow
time deq2 := Diagonal(f2 : r := 3, variant := {"profile"} );

time deq2 := Diagonal(f2 : r := 2, variant := {"profile", "mindeg"} ); // Much better


// OTHER DIAGONALS
variant := {"profile", "mindeg"};

f3 := 1/(1 - (1 + x)*(1 + y)*t - z*(1 + x*y*(1 + t)));  // (Lairez, 2013)
time deq3 := Diagonal(f3 : r := 2, variant := variant);

f4 := 1/(1 - (y + t*x*y + z + t*z + x*z + x*y + t*x*y*z));  // (Lairez, 2013)
time deq4 := Diagonal(f4 : r := 2, variant := variant);

f5 := 1/((1-x-y)*(1-z-t)-x*y*z*t);    // (Straub, 2014)
time deq5 := Diagonal(f5 : r := 2, variant := variant);

// AND A LAURENT POLYNOMIAL
A<x1,x2,x3> := FunctionField(Rationals(), 3);
f6 := (1 + x1)*(1 + x2)*(1 + x3)*(1 + x2 + x3 + x2*x3 + x1*x2*x3) /x1/x2/x3; // (Rowland & Zeilberger, 2013)
time deq6 := LaurentSequence(f6 : r := 2, variant := variant);


// Hopefully, all are equal
assert deq1 eq deq2;
assert deq2 eq deq3;
assert deq3 eq deq4;
assert deq4 eq deq5;
assert deq5 eq deq6;
