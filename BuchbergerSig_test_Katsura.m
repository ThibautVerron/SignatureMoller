// Created: Tue Oct  9 14:20:56 2018
// Last modified: Mon Jan 21 16:38:17 2019
// Hash: 89f49bb14d16b1c757234cbbae68bd55

load "MollerSig.m";
load "BuchbergerSig.m";

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

funs := <Euclid_SatIdeal, Euclid_CosetRep, Euclid_LinDecomp>;



load "def_Katsura.m";

/* time G,S := Moller_GB(K,funs: */
/*                       Signature := sig, */
/*                       F5_Criterion := F5, */
/*                       Sing_Criterion := sing); */

time G,SG := BuchbergerSig(K:
                          Signature := true,
                          F5_Criterion := true,
                          Sing_Criterion := true,
                          GebauerMoller := false);

SSG := ReduceGroebnerBasis(SG);
printf "Is the weak GB Gröbner? %o\n", IsGroebner(G);
printf "Generates the correct ideal? %o\n", Ideal(G) eq Ideal(K);
printf "Is the strong GB Gröbner? %o\n", IsGroebner(SSG);


/* Katsura 3:

Total # of S-polynomials: 606
Total # of considered pairs: 990
Total # of reductions to 0: 0
Total # of skipped pairs with coprime criterion: 340
Total # of skipped pairs with Gebauer-Moller "B" criterion: 0
Total # of skipped pairs with Gebauer-Moller "M" criterion: 0
Total # of skipped pairs with Gebauer-Moller "F" criterion: 0
Total # of skipped pairs with F5 criterion: 492
Total # of skipped pairs with sing criterion: 10
Total # of skipped 1-singular-reducible pols: 25
Time: 82.810

After changing the criteria:

Total # of S-polynomials: 606
Total # of considered pairs: 990
Total # of reductions to 0: 0
Total # of skipped pairs with coprime criterion: 340
Total # of skipped pairs with Gebauer-Moller criteria: 0
Total # of skipped pairs with F5 criterion: 492
Total # of skipped pairs with sing criterion: 10
Total # of skipped 1-singular-reducible pols: 25
Time: 56.330

Katsura 4:



*/
