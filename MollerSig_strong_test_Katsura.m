// Created: Tue Oct  9 14:20:56 2018
// Last modified: Mon Jan 28 14:24:08 2019
// Hash: 9138490b3df282899b03dcd80b903ba8

load "MollerSig_strong.m";

if assigned n and Type(n) eq MonStgElt then
    n := eval n;
elif not assigned n then
    n := 3;
end if;

if assigned sig and Type(sig) eq MonStgElt then
    sig := eval n;
elif not assigned sig then
    sig := true;
end if;

if assigned F5 and Type(F5) eq MonStgElt then
    F5 := eval n;
elif not assigned F5 then
    F5 := true;
end if;

if assigned sing and Type(sing) eq MonStgElt then
    sing := eval n;
elif not assigned sing then
    sing := true;
end if;




load "def_Katsura.m";


time G,SG := MollerSig(K:
                       Signature := true,
                       F5_Criterion := true,
                       Sing_Criterion := true,
                       GebauerMoller := true);

SSG := ReduceGroebnerBasis(SG);
printf "Is the weak GB Gröbner? %o\n", IsGroebner(G);
printf "Generates the correct ideal? %o\n", Ideal(G) eq Ideal(K);
printf "Is the strong GB Gröbner? %o\n", IsGroebner(SSG);


/* Katsura 3:

Magma 2.24:
Total # of S-polynomials: 178
Total # of considered pairs: 504
Total # of reductions to 0: 0
Total # of skipped pairs with coprime criterion: 157
Total # of skipped pairs with Gebauer-Moller criteria: 153
Total # of skipped pairs with F5 criterion: 115
Total # of skipped pairs with sing criterion: 1
Total # of skipped 1-singular-reducible pols: 6
Time: 1.330

Magma 2.20:
Total # of S-polynomials: 62
Total # of considered pairs: 214
Total # of reductions to 0: 0
Total # of skipped pairs with coprime criterion: 83
Total # of skipped pairs with Gebauer-Moller criteria: 52
Total # of skipped pairs with F5 criterion: 30
Total # of skipped pairs with sing criterion: 0
Total # of skipped 1-singular-reducible pols: 4
Time: 0.060

###############
Katsura 4:

Magma 2.24:
Total # of S-polynomials: 603
Total # of considered pairs: 1660
Total # of reductions to 0: 0
Total # of skipped pairs with coprime criterion: 509
Total # of skipped pairs with Gebauer-Moller criteria: 517
Total # of skipped pairs with F5 criterion: 388
Total # of skipped pairs with sing criterion: 9
Total # of skipped 1-singular-reducible pols: 84
Time: 16.910



*/
