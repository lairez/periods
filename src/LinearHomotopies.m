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



intrinsic
    GaussManinLin(f0, f1 : r := 1, variant := {}) -> Any, Any {}

    RH := RHnew();

    ipoint := CoefficientRing(Parent(f0)) ! 100;
    point_counter := 0;

    IndentPush();
    while not assigned RH`candidate do
        ipoint +:= 1;
        point_counter +:= 1;
        vprintf User2 : "Computing connexion at point number %o (%o)... ", point_counter, ipoint ;

        U := InitRK((1-ipoint)*f0 + ipoint*f1 : variant := variant, r := r);
        vtime User2 : ComputeGM(~U, f1-f0, [U`ring | ], ~gm : fullbasis := true);

        RHAddRat(~RH, gm`gm, ipoint : xkey := gm`ebasis);

    end while;
    IndentPop();

    return RH`candidate, gm`basis;

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



