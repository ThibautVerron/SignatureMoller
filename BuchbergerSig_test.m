// Created: Thu Dec 14 11:25:07 2017
// Last modified: Tue May 15 16:11:27 2018
// Hash: 99122ebf9728f158f9107cc5c0d4f3aa

ChangeDirectory("/home/guests/verron/Dropbox/Recherche/2017-Moller-sig/web");

load "BuchbergerSig.m";
  
P<X,Y,Z> := PolynomialRing(IntegerRing(),3,"grevlex");

F := [3*X^2*Y + 7*Y^2*Z,
      X*Y-2*Y*Z+Z^2,
      4*X*Y^2 - 5*X*Z^2
     ];

/* F := [7*X^2*Y-3*X, 4*X*Y^2-X*Y, 3*Y^3]; */

FF := [F[1],F[2],
       8*Y^3 - 4*Y^2*Z - 5*X*Z^2 // Result of reducing
      ];

GG,SG,sigs,sigsSG,T := BuchbergerSig(F :
                                     Signature := true,
                                     GebauerMoller := true);
G := GG;
Gp := [];
while G ne Gp do
    Gp := G;
    G := Reduce(Gp);
end while;

SSG := ReduceGroebnerBasis(SG);
      

test := IsGroebner(G);
test;
Ideal(G) eq Ideal(F);

if not test then
    G_missing := [g : g in GroebnerBasis(G) | NormalForm(g,G) ne 0];
    G_missing;
    
    gg := G_missing[1];
    
    I := IdealWithFixedBasis(F);
    
    Coordinates(I,gg);

end if;

LTG := [LeadingTerm(g) : g in GG];
LTI := [LeadingTerm(g) : g in GroebnerBasis(G)];
Ideal(LTG) eq Ideal(LTI);

/* GG2 := BuchbergerSig(FF); */
/* G2 := Reduce(GG2); */

/* IsGroebner(G2); */
/* Ideal(G2) eq Ideal(FF); */

/* Ideal(FF) eq Ideal(F); */
/* Ideal(G2) eq Ideal(G); */


/* /!\  BUG WITH S-POLYNOMIAL */

if false then
P<X,Y,Z> := PolynomialRing(IntegerRing(),3,"grevlex");

f := 4*X-Y;
g := 6*X-Z;

SPolynomial(f,g);
SPol(f,g);
3*f - 2*g;
end if;

for i in [1..#GG] do
    printf "%o\t\t%o\n", GG[i], Sig_ToString(sigs[i]);
end for;
