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


/*

mat : Matrix with univariate polynomials coefficients
den : univariate polynomial
genbasis : basis of the cohomology of V(f_t)
basis : basis of the cohomology of V(f_0), or a basis given by user
proj : matrix with univariate polynomials coefficients

den * genbasis' = genbasis * mat
basis = genbasis * proj

*/

GMLfmt := recformat< f0, f1, mat, den, proj, ini, basis, genbasis, inimat >;
intrinsic
    GaussManinLin(f0, f1 : basis := [], r := 1, variant := {}) -> Rec {}

    RH := RHnew();

    Ustart := InitRK(f0 : variant := variant, r := r);
    ComputeCohomologyBasis(~Ustart);
    mybasis := basis;
    if #mybasis eq 0 then
        mybasis := Ustart`basis;
    end if;

    ipoint := CoefficientRing(Parent(f0)) ! 100;
    point_counter := 0;
    gm := 0;
    genbasis := 0;

    IndentPush();
    while not assigned RH`candidate do
        ipoint +:= 1;
        point_counter +:= 1;
        vprintf User2 : "Computing connection at point number %o (%o)... ", point_counter, ipoint ;

        U := InitRK((1-ipoint)*f0 + ipoint*f1 : variant := variant, r := r);

        ComputeCohomologyBasis(~U);
        genbasis := U`basis;
        ebasis := [Exponents(m):m in U`basis];

        gm := [ -(f1-f0)*p : p in U`basis ];
        vtime User2 : HomReduceMatrix(~U, ~gm, ~gmmat);

        proj := mybasis;
        HomReduceMatrix(~U, ~proj, ~projmat);
        RHAddRat(~RH, [* gmmat, projmat *], ipoint : xkey := ebasis, denom := true);
    end while;
    IndentPop();

    den := RH`candidate[2];
    mat := RH`candidate[1][1];

    clist := Eltseq(den) cat &cat[Eltseq(c) : c in Eltseq(mat)];
    clist := [Denominator(c) : c in clist];
    iden := LCM(clist);

    ret := rec<GMLfmt |
              f0 := f0, f1 := f1,
              den := iden*den,
              mat := iden*mat,
              basis := mybasis,
              genbasis := genbasis
              >;

    proj := RH`candidate[1][2];
    ret`proj := Matrix(#genbasis, #mybasis, [p/den : p in Eltseq(proj)]);


    /* ini := []; */
    /* inimat := []; */

    /* L := mybasis; */
    /* Tmat := 0; */
    /* HomReduceMatrix(~Ustart, ~L, ~Tmat); */

    /* k := -1; */
    /* vprintf User2 : "Evaluating formal initial conditions... \n"; */
    /* repeat */
    /*     k := k+1; */
    /*     L := [ (-f1+f0)^k*p : p in genbasis ]; */
    /*     Lmat := 0; */
    /*     vtime User2 : HomReduceMatrix(~Ustart, ~L, ~Lmat); */
    /*     /\* Append(~ini, L); *\/ */
    /*     Append(~inimat, Tmat^(-1)*Lmat); */
    /* until Coefficient(den, k) ne 0; */

    /* /\* ret`ini := ini; *\/ */
    /* ret`inimat := inimat; */
    return ret;
end intrinsic;



intrinsic ScalarEquations(gm) -> Any {}

     RR := BaseRing(gm`proj);
     KK := FieldOfFractions(RR);

     M := ChangeRing(gm`mat, KK)/gm`den;
     P := gm`proj;

     ceqs := [];
     for i := 1 to NumberOfColumns(P) do
         vprintf User2 : "Computing ODE %o/%o... \n", i, NumberOfColumns(P) ;
         ceq := CyclicEquation(M, ColumnSubmatrixRange(P, i,i));
         Append(~ceqs, ceq);
     end for;

     return ceqs;
end intrinsic;





function issmooth(f)
    return Dimension(Ideal(Eltseq(JacobianMatrix([f])))) eq 0;
end function;

intrinsic DeformationSeq(f0, f1 : randomize := false) -> Any {}
    A := Parent(f0);

    terms := Terms(f1) cat Terms(-f0);

    if randomize then
        randl := [Random(100000) : i in terms];
        ParallelSort(~randl, ~terms);
    end if;

    L := [f0];
    cur := f0;
    for i in [1..#terms] do
        cur +:= terms[i];
        if issmooth(cur) then
            Append(~L, cur);
        end if;
    end for;

    return L;
end intrinsic;


procedure AppendJSON(~ret, elt : quote := false)
    if ISA(Type(elt), SeqEnum) then
        Append(~ret, "[ ");
        for i in [1..#elt-1] do
            AppendJSON(~ret, elt[i] : quote := quote);
            Append(~ret, ", ");
        end for;
        if #elt gt 0 then
            AppendJSON(~ret, elt[#elt] : quote := quote);
        end if;
        Append(~ret, " ]");
    elif ISA(Type(elt), RngUPolElt) then
        AppendJSON(~ret, Eltseq(elt) : quote := quote);
    elif ISA(Type(elt), Mtrx) then
        AppendJSON(~ret, RowSequence(elt) : quote := quote);
    elif quote then
        Append(~ret, Sprintf("\"%o\"\n", elt));
    else
        Append(~ret, Sprint(elt));
    end if;
end procedure;

intrinsic
    JSONOutput(file, gm) {}

    degree := Degree(gm`f0);
    ret := ["{\n"];
    Append(~ret, Sprintf("\"degree\": %o,\n", degree));
    Append(~ret, "\"vars\": "); AppendJSON(~ret, GeneratorsSequence(Parent(gm`f0)) : quote := true); Append(~ret, ",\n");
    Append(~ret, Sprintf("\"f0\": \"%o\",\n", gm`f0));
    Append(~ret, Sprintf("\"f1\": \"%o\",\n", gm`f1));

    fermatpol := &+[ MonomialCoefficient(gm`f0, v^degree)*v^degree : v in GeneratorsSequence(Parent(gm`f0)) ];
    if fermatpol eq gm`f0 then
        Append(~ret, "\"isfermat\": true,\n");
        Append(~ret, Sprintf("\"fermatcoeffs\": %o,\n", CoefficientsAndMonomials(gm`f0)));
    else;
        Append(~ret, "\"isfermat\": false,\n");
    end if;

    Append(~ret, Sprintf("\"basis\": %o,\n", [Exponents(m) : m in gm`basis]));
    Append(~ret, Sprintf("\"genbasis\": %o,\n", [Exponents(m) : m in gm`genbasis]));

    Append(~ret, "\"gm\": "); AppendJSON(~ret, gm`mat : quote := true); Append(~ret, ",\n");
    Append(~ret, "\"inicond\": "); AppendJSON(~ret, gm`inimat : quote := true); Append(~ret, ",\n");
    Append(~ret, "\"singpol\": "); AppendJSON(~ret, gm`den : quote := true);

    Append(~ret, "\n}\n");

    f := Open(file, "w");
    for s in ret do
        Put(f, s);
    end for;

end intrinsic;






