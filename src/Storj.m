/* This software is governed by the CeCILL license under French law and abiding
 * by the rules of distribution of free software.  You can use, modify or
 * redistribute the software under the terms of the CeCILL license as
 * circulated by CEA, CNRS and INRIA at the following URL
 * 
 *     www.cecill.info
 * 
 *  Author: Alin Bostan (2013)
 *  Modified by: Pierre Lairez (2014)
 *  
 **/



//---------------------------------------------------
// maps the function <<fun>> to all entries of S
//---------------------------------------------------


function mapFun(fun, S)
    m:=NumberOfRows(S);
    n:=NumberOfColumns(S);
    return Matrix(m, n, [[fun(S[i,j]) : j in [1..n]] : i in [1..m]]);
end function;

function ValuationMatrix(M);
    return mapFun(func<x|Valuation(x)>, M);
end function;    

function DegreeMatrix(M);
    return Max(ElementToSequence(mapFun(func<x|Degree(x)>, M)));
end function;

function CoefficientsMatrix(M,n,m);  
    k:=BaseRing(BaseRing(Parent(M)));
    U<t>:=PolynomialRing(k); 
    return mapFun(func<x| U![Coefficient(x,i) : i in [n..m-1]]>, M);
end function;   

function DerivativeMat(M);
    return mapFun(func<x|Derivative(x)>, M);
end function;


//---------------------------------------------------
// ring, field and random generation used 
// in the tests of correctness and timings
//---------------------------------------------------


p:=NextPrime(2^20);
k:=GF(p);
Polyk<t>:=PolynomialRing(k);
Frack<t>:=RationalFunctionField(k);

RandomPoly := function(d)
  return Polyk![k!Random(0,p-1) : i in [0..d]];
end function;

RandomMat := function(n,m,d)
  return Matrix(Polyk, n,m, [[RandomPoly(d) : j in [1..m]] : i in [1..n]]);
end function;

function Size(M);
  res := 0;
  s := 0;
  if (Type(BaseRing(M)) eq FldFunRat) then s := 1; end if;
  for i in [1..NumberOfRows(M)] do
  for j in [1..NumberOfColumns(M)] do
    res +:= Degree(Numerator(M[i,j])) + Degree(Denominator(M[i,j])) + 1 + s;
  end for;
  end for;
  return res;
end function;


//---------------------------------------------------
// Padé approximation
//---------------------------------------------------


PadeApproximant := function(s,order,n,d)
  PS:=Parent(s);
  F:=BaseRing(Parent(s));
  UP:=PolynomialAlgebra(F);
  RF<T>:=FieldOfFractions(UP);
  if s eq 0 then return true, RF!0; end if;
  if n+d gt order then return false,RF!0; end if;
  P:=UP![Coefficient(s,i): i in [0..order-1]];
  if Degree(P) le 0 then return true,RF!P; end if;
  M:=UP.1^(order);
  u0:=M;
  v0:=UP!0;
  u1:=P;
  v1:=UP!1;
  while Degree(v1) le d do
    if Degree(u1) le n then return true, RF!u1/RF!v1; end if;
    q,r:=Quotrem(u0,u1);
    u2:=u0-q*u1;
    v2:=v0-q*v1;
    u0:=u1;
    v0:=v1;
    u1:=u2;
    v1:=v2;
  end while;
print v1;
  return false,RF!0;
end function;


//---------------------------------------------------
// compute power series expansion of 
// A^(-1)*b mod t^prec
//---------------------------------------------------


Storjohann := function(A,b,prec)
	d:=Max(DegreeMatrix(A),DegreeMatrix(b)+1);    
 
	function MiddleMatrix(M);
		return  CoefficientsMatrix(M,d,2*d);
	end function;
	
	k:=BaseRing(BaseRing(Parent(A)));
	U<t>:=PolynomialRing(k);
	L<t>:=LaurentSeriesRing(k,d+1);
	RFF<t>:=RationalFunctionField(k);
	P:=U.1^d;             
// s is chosen such that d*2^s > prec	     
	s:=Ceiling(Log(2,prec/d));
//	print "s =", s;
		
//	RFF<t>:=RationalFunctionField(k);
//    C0b:=CoefficientsMatrix(Matrix(L,Matrix(RFF,A)^(-1)),0,d);  
//tt:=Cputime();
       C0:=CoefficientsMatrix(Matrix(L,A)^(-1),0,d);  
       C1:=-CoefficientsMatrix(C0*P*CoefficientsMatrix(A*C0,d,2*d),d,2*d) ;
//print("initial conditions"), Cputime()-tt;

//high order lifting 
//tt:=Cputime();	
	CC:=[C0,C1];
	for k in [2..s-1] do
	    CC[2^k-2+1]:=- MiddleMatrix((CC[2^(k-1)-2+1]+CC[2^(k-1)-1+1]*P)*
				MiddleMatrix(A*CC[2^(k-1)-2+1])); 
		CC[2^k-1+1]:=- MiddleMatrix((CC[2^(k-1)-2+1]+CC[2^(k-1)-1+1]*P)*
				MiddleMatrix(A*CC[2^(k-1)-1+1]));			
	end for;			  
	
	init:=(CC[1]+P*CC[2])*b;
	PP:=HorizontalJoin(CoefficientsMatrix(init,0,d), CoefficientsMatrix(init,d,2*d));
	Mat:=0;  
//print("high order lifting"), Cputime()-tt;

// Generalized Keller-Gehrig
//tt:=Cputime();	
	for K in [2..s] do           
		Mat:=-MiddleMatrix((CC[2^(K-1)-2+1]+CC[2^(K-1)-1+1]*P) * MiddleMatrix(A*PP)); 
	//	print Mat;
		PP:=HorizontalJoin(PP,Mat); 
	end for;      
//print("generalized Keller-Gehrig"), Cputime()-tt;

	//[Valuation( U!Coefficients(y[J,1])  -  &+[PP[J,K]*P^(K-1) : K in [1..s+1]]) : J in [1..n]];

//tt:=Cputime();	
	z:=&+[ColumnSubmatrix(PP,K,1)*P^(K-1) : K in [1..NumberOfColumns(PP)]];
//print("conclude"), Cputime()-tt;
	
	return z;
end function;


//---------------------------------------------------
// solve the system A*x = b
//---------------------------------------------------


intrinsic SolveByStorjohann(A,b) -> Any
  {}

	k:=BaseRing(BaseRing(Parent(A)));
	U<t>:=PolynomialRing(k);
	n:=Ncols(A);
   	d:=Max(DegreeMatrix(A),DegreeMatrix(b)+1); 
	prec:=2*d*n;
//	time 
        z:= Storjohann(A,b,prec);  
	L<t>:=LaurentSeriesRing(k,prec);   
	Stsol:=Matrix(L,z);
//	tt:=Cputime();
	bool, pad:=PadeApproximant(&+[Stsol[k,1] : k in [1..n]], prec, prec div 2 - 1, prec div 2);
//	print("Pade approximants"), Cputime()-tt;
//	tt:=Cputime();
//	time 
  denomSol:=Denominator(pad);
//	time 
  numerSol:=Eltseq(Stsol*denomSol);
//	time 
  RES:=Matrix(n,1,[U!Coefficients(N)/denomSol : N in numerSol]);
//	time res:=Matrix(RationalFunctionField(k),n,1,[U!Coefficients(N) : N in numerSol]);
//	time RES:=1/denomSol*res;
//	print "conclude", Cputime()-tt;
return RES;
end intrinsic;


//---------------------------------------------------
// CVM
//---------------------------------------------------

/*
The differential system is Y' = 1/q * M Y.
The initial vector is 1/r * v.
square matrix M, row vector v, both with polynomial coefficients
q and r are polynomials
We work with polynomial instead of rationnal functions,
and distinguish the numerators (M and v) from the denominators (q and r).
*/

// compute P and \delta^n u
CVMConstruction := function(M,q,v,r)
  K := BaseRing(M);
  n := NumberOfRows(M);
  P := ZeroMatrix(K, n, n);
  dqr := Derivative(q*r);
  u := v;
  for i in [1..n] do
    InsertBlock(~P,u,i,1);
    u := r*(u*M + DerivativeMat(q*u)) - i*dqr*u;
  end for;
  return <P,u>;
end function;

/*
the coefficients of the differential equation 
that cancels 1/r * v Y for any solution Y' = 1/q * M Y
are given by the vector
u*P^(-1) * diag(1/(q*r)^n , 1/(q*r)^(n-1) , ... , 1/(q*r))
*/

CVMResolution := function(P,u,qr)
  K := BaseRing(P);
  FracK := FieldOfFractions(K);
  n := NumberOfRows(P);
  resResol := Transpose(SolveByStorjohann(Transpose(P),Transpose(u)));
  if resResol * ChangeRing(P,FracK) ne ChangeRing(u,FracK) 
    then 
      print("singular matrix P"); 
      return P;
    else return Matrix(1,n,[resResol[1,i]/qr^(n+1-i): i in [1..n]]);
  end if;
end function;


CVM := function(M,q,v,r)
  resResol := CVMConstruction(M,q,v,r);
  P := resResol[1];
  u := resResol[2];
  return CVMResolution(P,u,q*r);
end function;


//---------------------------------------------------
// computation of P and delta^n u 
// with balanced vector-matrix product
//---------------------------------------------------


CVMConstructionBalanced := function(M,q,v,r)
  K := BaseRing(M);
  x := K.1;
  n := NumberOfRows(M);
  d := Max(Degree(q), DegreeMatrix(M));
  degu := Max(Degree(r), DegreeMatrix(v));
  D := d + degu + 1;
  vectZero := Matrix(K,1,n,[[0 : j in [1..n]]]);
  U := v;
  P := ZeroMatrix(K, n, n);
  dqr := Derivative(q*r);

  MatToVect := function(A)
    res := ZeroMatrix(K,1,n);
    for j in [1..n] do
      coefs := [];
      for i in [1..NumberOfRows(A)] do
        coefs cat:= [Coefficient(A[i,j],l) : l in [0..D-1]];
      end for;
      res[1,j] := K!coefs;
    end for;
    return res;
  end function;

  Balance := function(A,k)
    res := ZeroMatrix(K,NumberOfRows(A),NumberOfColumns(A));
    for row in [1..k] do
      for i in [row..NumberOfRows(res)] do
        for j in [1..NumberOfColumns(res)] do
          res[i,j] := res[i,j] + 
            K![Coefficient(A[i-row+1,j],l) : l in [(row-1)*D..row*D-1]];
        end for;
      end for;
    end for;
    return res;
  end function;

  BalancedDerivative := function(A)
    res := D*x^(D-1)*VerticalJoin(RowSubmatrix(A,2,NumberOfRows(A)-1),vectZero);
    for i in [1..(NumberOfRows(A)-1)] do
      MultiplyRow(~res,i,i);
    end for;
    return res + DerivativeMat(A);
  end function;

  for i in [1..n] do
    InsertBlock(~P,MatToVect(U),i,1);
    U := VerticalJoin(U,vectZero);
    U := Balance(r*(U*M + BalancedDerivative(q*U)) - i*dqr*U, 3);
  end for;
  return <P,MatToVect(U)>;
end function;


//---------------------------------------------------
// DBZ algorithm
//---------------------------------------------------


DBZ := function(Minput)
  M := Minput;
  n := NumberOfRows(M);
  P := ScalarMatrix(BaseRing(M),n,1);

  pivot := procedure(~M,~P,i,j,v)
    AddRow(~M,v,j,i);
    AddColumn(~M,-v,i,j);
    M[i,j] := M[i,j] + Derivative(v);
    AddRow(~P,v,j,i);
  end procedure;

  pivotDiag := procedure(~M,~P,i,v)
    MultiplyRow(~M,v,i);
    MultiplyColumn(~M,1/v,i);
    M[i,i] := M[i,i] + Derivative(v)/v;
    MultiplyRow(~P,v,i);
  end procedure;

  for i in [1..(n-1)] do
    j := i+1;
    while (M[i,j] eq 0) do
      j := j+1;
    end while;
    if (j eq n+1) then return M; end if;
    SwapRows(~M,i+1,j);
    SwapColumns(~M,i+1,j);
    SwapRows(~P,i+1,j);
    pivotDiag(~M,~P,i+1,M[i,i+1]);
    for j in [1..i] do
      pivot(~M,~P,i+1,j,M[i,j]);
    end for;
    for j in [(i+2)..n] do
      pivot(~M,~P,i+1,j,M[i,j]);
    end for;
  end for;
  return <P,M>;
end function;

