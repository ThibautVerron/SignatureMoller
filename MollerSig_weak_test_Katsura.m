// Created: Tue Oct  9 14:20:56 2018
// Last modified: Mon Jan 28 17:00:18 2019
// Hash: 79cf174933ac5230c0105e0185d12628

load "MollerSig_weak.m";
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

funs := <Euclid_SatIdeal, Euclid_CosetRep, Euclid_LinDecomp>;



load "def_Katsura.m";

/* time G,S := MollerSig_weak(K,funs: */
/*                       Signature := sig, */
/*                       F5_Criterion := F5, */
/*                       Sing_Criterion := sing); */

time G,S := MollerSig(K:
                          Signature := false,
                          GebauerMoller := true);


/*
Katsura 2
#####
true true true
###
Total # of vectorsets: 13
Total # of saturated sets: 170
Total # of reductions to 0: 0
Total # of skipped singular S-pairs: 3
Total # of skipped F5 S-pairs: 154
Total # of skipped 1-singular-reducible pols: 0
Time: 4.590

#####
true false false
###
Total # of vectorsets: 235
Total # of saturated sets: 235
Total # of reductions to 0: 219
Total # of skipped singular S-pairs: 0
Total # of skipped F5 S-pairs: 0
Total # of skipped 1-singular-reducible pols: 0
Time: 10.440


#####
GM criteria, no signatures
###
Total # of S-polynomials: 20
Total # of considered pairs: 78
Total # of reductions to 0: 7
Total # of skipped pairs with coprime criterion: 28
Total # of skipped pairs with Gebauer-Moller "B" criterion: 4
Total # of skipped pairs with Gebauer-Moller "M" criterion: 17
Total # of skipped pairs with Gebauer-Moller "F" criterion: 1
Total # of skipped pairs with F5 criterion: 0
Total # of skipped pairs with sing criterion: 0
Total # of skipped 1-singular-reducible pols: 0
Time: 0.080

########################################################################

Katsura 3
#####
true true true
###
Total # of vectorsets: 51
Total # of saturated sets: 2227
Total # of reductions to 0: 0
Total # of skipped singular S-pairs: 51
Total # of skipped F5 S-pairs: 2125
Total # of skipped 1-singular-reducible pols: 0
Time: 51777.590

#####
GM criteria
###

Total # of S-polynomials: 246
Total # of considered pairs: 861
Total # of reductions to 0: 159
Total # of skipped pairs with coprime criterion: 310
Total # of skipped pairs with Gebauer-Moller "B" criterion: 50
Total # of skipped pairs with Gebauer-Moller "M" criterion: 247
Total # of skipped pairs with Gebauer-Moller "F" criterion: 17
Total # of skipped pairs with F5 criterion: 0
Total # of skipped pairs with sing criterion: 0
Total # of skipped 1-singular-reducible pols: 0
Time: 28.130




*/

