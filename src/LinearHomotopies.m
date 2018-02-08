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








