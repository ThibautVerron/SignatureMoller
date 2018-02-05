// Created: Thu Dec 14 11:25:07 2017
// Last modified: Mon Feb  5 14:51:13 2018
// Hash: 74020a18536ce03a8d22a7de84410558

load "MollerSig.m";

char := 23;
R<A,B> := PolynomialRing(GF(char),2,"grevlex");
P<X,Y,H> := PolynomialRing(R,3,"grevlex");

F := [3*(A+B)*X^2 + (2*A+B)*Y*H,
      (4*A*B)*Y^2 - 5*(A-B)*X*H,
      X-A*Y+H
     ];

funs := <Pol_SatGen, Pol_CosetRep, Pol_BasisCoords>;

time G1 := Moller_GB(F,funs
                     : Signature := false,
                       F5_Criterion := false,
                       Sing_Criterion := false);
printf "--------------------\n";
time G2 := Moller_GB(F,funs
                     : Signature := true,
                       F5_Criterion := false,
                       Sing_Criterion := false);
printf "--------------------\n";
time G3 := Moller_GB(F,funs
                     : Signature := true,
                       F5_Criterion := true,
                       Sing_Criterion := false);
printf "--------------------\n";
time G4 := Moller_GB(F,funs
                     : Signature := true,
                       F5_Criterion := true,
                       Sing_Criterion := true);
printf "--------------------\n";


G1r := Moller_ReduceGB(G1,funs);
G2r := Moller_ReduceGB(G2,funs);
G3r := Moller_ReduceGB(G3,funs);


Pt<At,Bt,Xt,Yt,Ht> := PolynomialRing(GF(char),5,<"elim",2>);

hR := hom<R -> Pt | At,Bt>;
hP := hom<P -> Pt | hR, Xt, Yt, Ht>;

Ft := [hP(f) : f in F];
G1t := [hP(g) : g in G1];
G2t := [hP(g) : g in G2];
G3t := [hP(g) : g in G3];
G4t := [hP(g) : g in G4];

I_test := Ideal(Ft);
I1 := Ideal(G1t);
I2 := Ideal(G2t);
I3 := Ideal(G3t);
I4 := Ideal(G4t);

I1 eq I_test;
I2 eq I_test;
I3 eq I_test;
I4 eq I_test;

L1 := [hP(LeadingTerm(g)) : g in G1];
I1l := Ideal(L1);

L2 := [hP(LeadingTerm(g)) : g in G2];
I2l := Ideal(L2);

L3 := [hP(LeadingTerm(g)) : g in G3];
I3l := Ideal(L3);

L4 := [hP(LeadingTerm(g)) : g in G4];
I4l := Ideal(L4);


I1l eq I2l;
I1l eq I3l;
I1l eq I4l;

