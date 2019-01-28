// Created: Thu Dec 14 11:25:07 2017
// Last modified: Mon Jan 28 16:08:02 2019
// Hash: 4b9198de2d029d0ab1d11993ed534ac7

load "MollerSig_strong.m";
  
function RandomPolynomial(A,dmax : homo := true, size := 20)
    if homo then
        deglist := [dmax];
    else
        deglist := [i : i in [0..dmax]];
    end if;

    f := 0;
    for d in deglist do
        M := MonomialsOfDegree(A,d);
        for m in M do
            c := Random(-size, size);
            f +:= c*m;
        end for;
    end for;
    
    return f;
end function;

n := 3;
degree := 2;
size := 10;
A := PolynomialRing(IntegerRing(),n,"grevlex");

F := [RandomPolynomial(A,degree : size := size) : i in [1..n]];

time G,SG := MollerSig(F:
                           Signature := true,
                           F5_Criterion := true,
                           Sing_Criterion := true,
                           GebauerMoller := true);


SSG := ReduceGroebnerBasis(SG);
printf "Is the weak GB Gröbner? %o\n", IsGroebner(G);
printf "Generates the correct ideal? %o\n", Ideal(G) eq Ideal(F);
printf "Is the strong GB Gröbner? %o\n", IsGroebner(SSG);

/*

n=3, deg = 2,2,2, size = 5,5,5

Total # of S-polynomials: 132
Total # of considered pairs: 215
Total # of reductions to 0: 0
Total # of skipped pairs with coprime criterion: 51
Total # of skipped pairs with Gebauer-Moller criteria: 11
Total # of skipped pairs with F5 criterion: 90
Total # of skipped pairs with sing criterion: 0
Total # of skipped 1-singular-reducible pols: 7
Time: 0.180

n=3, deg = 2,2,2, size = 10,10,10

Total # of S-polynomials: 192
Total # of considered pairs: 383
Total # of reductions to 0: 0
Total # of skipped pairs with coprime criterion: 73
Total # of skipped pairs with Gebauer-Moller criteria: 99
Total # of skipped pairs with F5 criterion: 117
Total # of skipped pairs with sing criterion: 1
Total # of skipped 1-singular-reducible pols: 19
Time: 1.150

n=3, deg = 3,3,3, size = 3,3,3

Total # of S-polynomials: 1269
Total # of considered pairs: 1830
Total # of reductions to 0: 0
Total # of skipped pairs with coprime criterion: 304
Total # of skipped pairs with Gebauer-Moller criteria: 204
Total # of skipped pairs with F5 criterion: 885
Total # of skipped pairs with sing criterion: 0
Total # of skipped 1-singular-reducible pols: 91
Time: 36.920

n=3, deg = 3,3,3, size = 5,5,5
Total # of S-polynomials: 1161
Total # of considered pairs: 2211
Total # of reductions to 0: 0
Total # of skipped pairs with coprime criterion: 155
Total # of skipped pairs with Gebauer-Moller criteria: 911
Total # of skipped pairs with F5 criterion: 842
Total # of skipped pairs with sing criterion: 0
Total # of skipped 1-singular-reducible pols: 78
Time: 195.810



*/
