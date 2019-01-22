// Created: Thu Dec 14 11:25:07 2017
// Last modified: Fri Dec  7 09:37:36 2018
// Hash: d87d5ecfc957667bfb2160211f0bcc4f

ChangeDirectory("/home/guests/verron/Recherche/2017-Moller-sig/web");

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
IsGroebner(SSG);

/* if not test then */
/*     G_missing := [g : g in GroebnerBasis(G) | NormalForm(g,G) ne 0]; */
/*     G_missing; */
    
/*     gg := G_missing[1]; */
    
/*     I := IdealWithFixedBasis(F); */
    
/*     Coordinates(I,gg); */

/* end if; */

LTG := [LeadingTerm(g) : g in GG];
LTI := [LeadingTerm(g) : g in GroebnerBasis(G)];
Ideal(LTG) eq Ideal(LTI);

/* GG2 := BuchbergerSig(FF); */
/* G2 := Reduce(GG2); */

/* IsGroebner(G2); */
/* Ideal(G2) eq Ideal(FF); */

/* Ideal(FF) eq Ideal(F); */
/* Ideal(G2) eq Ideal(G); */

PQ := PolynomialRing(RationalField(),Rank(P),"grevlex");

FQ := [PQ!f : f in F];

S<T> := RationalFunctionField(RationalField());

H1 := S ! HilbertSeries(Ideal(FQ)); H1;
H2 := &*[1-T^Degree(f) : f in F]/(1-T)^(Rank(P)); H2;



/* /!\  BUG WITH S-POLYNOMIAL */

if false then
P<X,Y,Z> := PolynomialRing(IntegerRing(),3,"grevlex");

f := 4*X-Y;
g := 6*X-Z;

SPolynomial(f,g);
SPol(f,g);
3*f - 2*g;

for i in [1..#GG] do
    printf "%o\t\t%o\n", GG[i], Sig_ToString(sigs[i]);
end for;
end if;


/* /!\ Looking for reductions to zero */

