// Created: Thu Dec 14 11:25:07 2017
// Last modified: Tue Jan 22 09:27:42 2019
// Hash: 3b403c63e1fb8a3a4b1b2f277aebcfcb

ChangeDirectory("/home/guests/verron/Recherche/2017-Moller-sig/web");

load "BuchbergerSig.m";
  
P<X,Y,Z> := PolynomialRing(IntegerRing(),3,"grevlex");

function RandomPolynomial(P,dmax : homo := true, size := 20)
    if homo then
        deglist := [dmax];
    else
        deglist := [i : i in [0..dmax]];
    end if;

    f := 0;
    for d in deglist do
        M := MonomialsOfDegree(P,d);
        for m in M do
            c := Random(-size, size);
            f +:= c*m;
        end for;
    end for;
    
    return f;
end function;


F := [RandomPolynomial(P,3 : size := 3),
      RandomPolynomial(P,3 : size := 3),
      RandomPolynomial(P,2 : size := 3),
      RandomPolynomial(P,2 : size := 3)
     ];

/* /\* No reduction to 0, output is not a GB *\/ */
/* F := [ */
/*     -X^2*Y + X*Y^2 - X^2*Z + X*Y*Z + Y^2*Z + X*Z^2 - Y*Z^2, */
/*     X^2 - Y^2 + 2*X*Z - Z^2, */
/*     -X^2 - X*Y + Y^2 - X*Z - 2*Y*Z - Z^2 */
/* ]; */

/* Previous one fixed. Here, reductions to 0 and output is not a GB. */
/* F := [ */
/*     -X*Y^2 + X^2*Z + X*Z^2 - Y*Z^2 + Z^3, */
/*     X^2 + X*Y - 2*Y^2 - X*Z + 2*Y*Z, */
/*     2*X^2 + Y^2 - X*Z - 2*Y*Z - Z^2 */
/* ]; */

GG,SG,sigs,sigsSG,T := BuchbergerSig(F :
                                     Signature := true,
                                     F5_Criterion := true,
                                     Sing_Criterion := true,
                                     GebauerMoller := true);
G := GG;
Gp := [];
while G ne Gp do
    Gp := G;
    G := Reduce(Gp);
end while;

SSG := ReduceGroebnerBasis(SG);
    

test := IsGroebner(G);
printf "Is Groebner (weak)? %o\n", test;
printf "Is Groebner (strong, after reduction)? %o\n", IsGroebner(SSG);
printf "Correct ideal? %o\n", Ideal(G) eq Ideal(F);

LTG := [LeadingTerm(g) : g in G];
LTI := [LeadingTerm(g) : g in GroebnerBasis(F)];
printf "Correct leading ideal? %o\n", Ideal(LTG) eq Ideal(LTI);



/* /!\ Looking for reductions to zero */

PQ := PolynomialRing(RationalField(),Rank(P),"grevlex");

FQ := [PQ!f : f in F];

S<T> := RationalFunctionField(RationalField());

H1 := S ! HilbertSeries(Ideal(FQ)); H1;
H2 := &*[1-T^Degree(f) : f in F]/(1-T)^(Rank(P)); H2;

sf := Sig_Create(-2,X^2*Z,3);
slim := Sig_Create(1,1,sf`i);

LPols := [];                    /* Refix */

mon := sf`k * sf`mu;
mon_red,_ := StrongReduce(mon,sf,LPols,sigsSG : Signature:=false);

res := mon_red ne 0;

s1 := Sig_Create(-1,X*Y,3);
s2 := Sig_Create(-1,X^2,3);

if false then

sf := Sig_Create(-2,X^2*Z,3);
iPols := [i : i in [1..#GG] | Sig_Lt(sigs[i],sf)];
Pols := [GG[i] : i in iPols];
SigPols := [sigs[i] : i in iPols];

for i in [1..#Pols] do printf "%o %o\n",i, LeadingTerm(Pols[i]); end for;

f := -2 * X^2*Z * F[3];f;
f1 := f  - 2*X^2*Z*  Pols[2]; f1;
f2 := f1 + 2*X*Z*    Pols[1]; f2;
f3 := f2 - 2*Y^2*Z*  Pols[2]; f3;
f4 := f3 - 2*Y*Z*    Pols[6]; f4;
f5 := f4 + 4*X*Z^2*  Pols[2]; f5;
f6 := f5 - 4*Y*Z^2*  Pols[2]; f6;
f7 := f6 - 2*Z^2*    Pols[3]; f7;
f8 := f7 - 4*Z^2*    Pols[6]; f8;
f9 := f8 - 12*Z^3*   Pols[2]; f9;
f10 := f9 + 2*Z^3*   Pols[5]; f10;
f11 := f10 + 2*Z*    Pols[8]; f11;

Sig_ToString(sf);
SS := [];
SS[1] := Sig_Multiply(SigPols[2],2,X^2*Z);
SS[2] := Sig_Multiply(SigPols[1],2,X*Z);
SS[3] := Sig_Multiply(SigPols[2],2,Y^2*Z);
SS[4] := Sig_Multiply(SigPols[6],2,Y*Z);
SS[5] := Sig_Multiply(SigPols[2],2,X*Z^2);
SS[6] := Sig_Multiply(SigPols[2],2,Y*Z^2);
SS[7] := Sig_Multiply(SigPols[3],2,Z^2);
SS[8] := Sig_Multiply(SigPols[6],2,Z^2);
SS[9] := Sig_Multiply(SigPols[2],2,Z^3);
SS[10] := Sig_Multiply(SigPols[5],2,Z^3);
SS[11] := Sig_Multiply(SigPols[8],2,Z);

[Sig_Lt(ss,sf) : ss in SS];


iPols := [i : i in [1..#SG] | Sig_Lt(sigsSG[i],sf)];
Pols := [SG[i] : i in iPols];
SigPols := [sigsSG[i] : i in iPols];

for i in [1..#Pols] do printf "%o %o\n",i, LeadingTerm(Pols[i]); end for;

f1 := f - 2*X^2*Z*Pols[2]; f1;
f2 := f1 + 2*X*Z*Pols[1]; f2;
f3 := f2 - 2*Y^2*Z*Pols[2]; f3;
f4 := f3 - 2*Y*Z*Pols[9]; f4;
f5 := f4 + 4*X*Z^2*Pols[2]; f5;
f6 := f5 - 4*Y*Z^2*Pols[2]; f6;
f7 := f6 - 2*Z^2*Pols[3]; f7;
f8 := f7 - 4*Z^2*Pols[9]; f8;
f9 := f8 - 12*Z^3*Pols[2]; f9;
f10 := f9 + 2*Z^3*Pols[6]; f10;
f11 := f10 + 2*Z*Pols[13]; f11;

SS := [];
SS[1] := Sig_Multiply(SigPols[2],2,X^2*Z);
SS[2] := Sig_Multiply(SigPols[1],2,X*Z);
SS[3] := Sig_Multiply(SigPols[2],2,Y^2*Z);
SS[4] := Sig_Multiply(SigPols[9],2,Y*Z);
SS[5] := Sig_Multiply(SigPols[2],2,X*Z^2);
SS[6] := Sig_Multiply(SigPols[2],2,Y*Z^2);
SS[7] := Sig_Multiply(SigPols[3],2,Z^2);
SS[8] := Sig_Multiply(SigPols[9],2,Z^2);
SS[9] := Sig_Multiply(SigPols[2],2,Z^3);
SS[10] := Sig_Multiply(SigPols[6],2,Z^3);
SS[11] := Sig_Multiply(SigPols[13],2,Z);

[Sig_Lt(ss,sf) : ss in SS];
end if;


/*

F with pairs eliminated by both B and M:

[
    -2*X^3 - X^2*Y + 3*X*Y^2 + 3*Y^3 - 3*X^2*Z + X*Y*Z - Y*Z^2 + 2*Z^3,
    2*X^2 + 2*X*Y + 2*Y^2 - X*Z - 2*Y*Z + Z^2,
    -3*X*Y + 2*X*Z - 3*Z^2
]

*/



/* true false true false */

F := [
    -2*X^3 + 2*Y^3 - 2*X^2*Z + 3*X*Y*Z - 3*Y^2*Z - X*Z^2 - Y*Z^2 - Z^3,
    -3*X^3 - X*Y^2 - Y^3 + X^2*Z - 3*X*Y*Z - 3*Y^2*Z - 3*X*Z^2 + 3*Y*Z^2 - 
                                                                 2*Z^3,
    -X^2 - X*Y - 3*Y^2 - X*Z + 2*Y*Z + 3*Z^2,
    2*Y^2 + X*Z + 3*Y*Z + 2*Z^2
];

{LeadingMonomial(g) : g in G} eq {LeadingMonomial(g) : g in SG};


//[<LeadingTerm(G[i]),LeadingTerm(SSG[i])> : i in [1..#G]];

