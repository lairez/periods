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

Input :
polynomials f0 and f1.
basis can be "generic", "start"
//pols is a list of polynomials.

Output :

mat : Matrix with univariate polynomials coefficients
den : univariate polynomial
genbasis : basis of the cohomology of V(f_t)
basis : basis of the cohomology of V(f_0) if basis="start", or the given basis.

proj : matrix with univariate polynomials coefficients

den * B' = B * mat
//pols = B * proj

where B = genbasis or startbasis, depending on the parameter `basis`.


*/

GMLfmt := recformat< f0, f1, mat, den, basis, genbasis, name >;
intrinsic
    GaussManinLin(f0, f1 : basis := "generic", r := 1, variant := {}, name := "") -> Rec {}

    RH := RHnew();

    mybasis := [];
    if basis eq "start" then
        Ustart := InitRK(f0 : variant := variant, r := r);
        ComputeCohomologyBasis(~Ustart);
        mybasis := Ustart`basis;
    elif Type(basis) eq SeqEnum then
        mybasis := basis;
    end if;

    ipoint := CoefficientRing(Parent(f0)) ! 100;
    point_counter := 0;
    gm := 0;
    genbasis := 0;

    IndentPush();
    while not assigned RH`candidate do
        ipoint +:= 1;
        point_counter +:= 1;
        vprintf User2 : "Computing connection at point number %o (%o) in family \"%o\... ", point_counter, ipoint, name;

        U := InitRK((1-ipoint)*f0 + ipoint*f1 : variant := variant, r := r);

        ComputeCohomologyBasis(~U);
        genbasis := U`basis;
        ebasis := [Exponents(m):m in U`basis];

        thebasis := [];
        if basis eq "start" then
            thebasis := mybasis;
        else
            thebasis := U`basis;
        end if;

        gm := [ -(f1-f0)*p : p in thebasis ];
        vtime User2 : HomReduceMatrix(~U, ~gm, ~gmmat);


        tocompute := 0;
        if basis eq "generic" then
            tocompute := gmmat;
        else
            HomReduceMatrix(~U, ~thebasis, ~thebasismat);
            tocompute := thebasismat^(-1)*gmmat;
        end if;

        RHAddRat(~RH, tocompute, ipoint : xkey := ebasis, denom := true);
    end while;
    IndentPop();

    den := RH`candidate[2];
    mat := RH`candidate[1];

    clist := Eltseq(den) cat &cat[Eltseq(c) : c in Eltseq(mat)];
    clist := [Denominator(c) : c in clist];
    iden := LCM(clist);

    ret := rec<GMLfmt |
              f0 := f0, f1 := f1,
              den := iden*den,
              mat := iden*mat,
              genbasis := genbasis,
              name := name
              >;

    if #mybasis gt 0 then
        ret`basis := mybasis;
    end if;



    //proj := RH`candidate[1][2];
    //ret`proj := Matrix(#genbasis, #mybasis, [p/den : p in Eltseq(proj)]);


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



intrinsic ScalarEquationOfCoordinate(gm, i : maxorder := 100) -> Any {}
     M := gm`mat*(1/gm`den);
     vec := Matrix(NumberOfColumns(M), 1, [CoefficientRing(M) | 0 : i in [1..NumberOfColumns(M)]]);
     vec[i,1] := 1;

     vprintf User2 : "Computing ODE... \n" ;
     ceq := CyclicEquation(M, vec : maxorder:=maxorder);

     return ceq;
end intrinsic;

MDer := func< m | Matrix(BaseRing(m), NumberOfRows(m), NumberOfColumns(m), [Derivative(p) : p in Eltseq(m)]) >;

intrinsic InitialConditionsOfCoordinate(gm, i) -> Any {}

    M := gm`mat*(1/gm`den);
    vec := Matrix(NumberOfColumns(M), 1, [CoefficientRing(M) | 0 : i in [1..NumberOfColumns(M)]]);
    vec[i,1] := 1;

    K := CoefficientRing(M);
    Kev := CoefficientRing(K);
    ev0 := hom< K -> Kev | 0 >;

    vecs := [vec];
    repeat
        vec := M*vec + MDer(vec);
        Append(~vecs, vec);
        ini := Matrix([ChangeRing(v, Kev, ev0) : v in vecs]);
    until Rank(ini) lt #vecs;

    return ini;
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


intrinsic AppendJSON(~ret, elt : quote := true) {}
    if ISA(Type(elt), SeqEnum) then
        Append(~ret, "[ ");
        for i in [1..#elt-1] do
            AppendJSON(~ret, elt[i] : quote := quote);
            Append(~ret, ", ");
        end for;
        if #elt gt 0 then
            AppendJSON(~ret, elt[#elt] : quote := quote);
        end if;
        Append(~ret, " ]\n");
    elif ISA(Type(elt), Assoc) then
        Append(~ret, "{ ");
        cnt := 0;
        ks := Keys(elt);
        for k in ks do
            cnt := cnt+1;
            Append(~ret, Sprintf("\"%o\":", k));
            AppendJSON(~ret, elt[k] : quote := quote);
            if cnt lt #ks then
                Append(~ret, ",\n");
            end if;
        end for;
        Append(~ret, " }");
    elif ISA(Type(elt), RngUPolElt) then
        AppendJSON(~ret, Eltseq(elt) : quote := quote);
    elif ISA(Type(elt), Mtrx) then
        AppendJSON(~ret, RowSequence(elt) : quote := quote);
    elif quote then
        Append(~ret, Sprintf("\"%o\"", elt));
    else
        Append(~ret, Sprint(elt));
    end if;
end intrinsic;



intrinsic
    JSONOutput(file, elt) {}

    ret := [];
    AppendJSON(~ret, elt);

    f := Open(file, "w");
    for s in ret do
        Put(f, s);
    end for;

end intrinsic;


