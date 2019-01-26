// Created: Thu Dec 14 11:25:07 2017
// Last modified: Tue Oct  9 15:22:41 2018
// Hash: 7f91f4d9d8eec30c749afa05ceb88f4e

load "MollerSig.m";

ring := true;
// If false, runs the test with the same polynomials over a finite
// field. This should compute a Gröbner basis.

if ring then
    
    P<X,Y,H> := PolynomialRing(IntegerRing(),3,"grevlex");

    F := [3*X*Y + 7*Y*H,
          4*Y^2 - 5*X*H,
          X-2*Y+H
         ];

    funs := <Euclid_SatIdeal, Euclid_CosetRep, Euclid_LinDecomp>;

    time G1,S1 := Moller_GB(F,funs
                         : Signature := false,
                           F5_Criterion := false,
                           Sing_Criterion := false);
    printf "--------------------\n";
    time G2,S2 := Moller_GB(F,funs
                         : Signature := true,
                           F5_Criterion := false,
                           Sing_Criterion := false);
    printf "--------------------\n";
    time G3,S3 := Moller_GB(F,funs
                         : Signature := true,
                           F5_Criterion := true,
                           Sing_Criterion := false); 
    printf "--------------------\n";
    time G4,S4 := Moller_GB(F,funs
                         : Signature := true,
                           F5_Criterion := true,
                           Sing_Criterion := true); 
    printf "--------------------\n";


    I_test := Ideal([LeadingTerm(g) : g in GroebnerBasis(F)]);
    I1 := Ideal([LeadingTerm(g) : g in G1]);
    I1 eq I_test;

    [b : b in Basis(I_test) | not b  in I1];
    
    I2 := Ideal([LeadingTerm(g) : g in G2]);
    I2 eq I_test;

    I3 := Ideal([LeadingTerm(g) : g in G3]);
    I3 eq I_test;

    I4 := Ideal([LeadingTerm(g) : g in G4]);
    I4 eq I_test;


else

    P<X,Y,H> := PolynomialRing(GF(65521),3,"grevlex");

    F := [3*X^2*Y + 7*Y^2*H,
          4*X*Y^2 - 5*X*H^2,
          X-2*Y+H];

    funs := <Field_SatIdeal, Field_CosetRep, Field_LinDecomp>;

    time G1 := Moller_GB(F,funs
                         : Signature := false,
                           F5_Criterion := false,
                           Sing_Criterion := false);
    printf "--------------------\n";
    time G2,S2 := Moller_GB(F,funs
                            : Signature := true,
                              F5_Criterion := false,
                              Sing_Criterion := false);
    printf "--------------------\n";
    time G3,S3 := Moller_GB(F,funs
                            : Signature := true,
                              F5_Criterion := true,
                              Sing_Criterion := false); 
    printf "--------------------\n";
    time G4,S4 := Moller_GB(F,funs
                            : Signature := true,
                              F5_Criterion := true,
                              Sing_Criterion := true); 


    I_test := Ideal([LeadingTerm(g) : g in GroebnerBasis(F)]);
    Ideal([LeadingTerm(g) : g in G1]) eq I_test;
    Ideal([LeadingTerm(g) : g in G2]) eq I_test;
    Ideal([LeadingTerm(g) : g in G3]) eq I_test;

end if;

