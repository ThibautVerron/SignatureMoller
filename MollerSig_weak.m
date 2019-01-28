// Created: Wed Dec 13 17:47:42 2017
// Last modified: Tue Oct  9 15:35:17 2018
// Hash: 6de1ab6d18ab8e847aa9ba5ac0ac5f9a

load "Signatures.m";

function SatSet_of_mon(LMs,m,XS)
    /* Returns the largest saturated set of {1..m} wrt LMs[1]...LMs[m]
    whose lcm divides XS.

    The output is the set of all j in {1..m} such that LMs[j] divides
    XS.
   */
    S := [];
    while exists(k){k : k in [1..m] | (not k in S)
                                      and IsDivisibleBy(XS,LMs[k])} do
        Append(~S,k);
    end while;
    return S;
end function;

function SatSet_lcm(S,LMs)
    /* Given a saturated set S, returns its lcm x^S */
    return Lcm([LMs[j] : j in S]);
end function;

function SatSets_Generate(LMs,ss)
    /* Generate all saturated sets of [1..ss] containing ss */
    ExistingLcms := {};
    SS := [];
    m := ss-1;
    /* subsets := Subsets({1..m}); */
    /* subsets := [Include(S,ss) : S in subsets]; */
    for size_S in [0..m] do     
        subsets := Subsets({1..m},size_S);
        subsets := [Sort(Append(Setseq(S),ss)) : S in subsets];
        for S in subsets do
            XS := SatSet_lcm(S,LMs);
            if XS in ExistingLcms then
                continue;
            else
                Include(~ExistingLcms,XS);
            end if;
            SExt := SatSet_of_mon(LMs,ss,XS);
            Include(~SS,SExt);
        end for;
    end for;
    return SS;
end function;


function SatSets_Generate_with_grouping(LMs,ss)
    /* Generate all saturated sets of [1..ss] containing ss.

    This function implements the following optimization: it first
    groups elements with the same LM together, and then make a call to
    SatSets_Generate with a list of distinct LMs. The result is then
    expanded again.

    The complexity is thus exponential in the number of distinct
    elements in LMs[1..ss], instead of exponential in ss.
   */
    ExistingLMs := [LMs[ss]];
    Indices := [[ss]];
    for i in [1..ss-1] do
        j := Index(ExistingLMs,LMs[i]);
        /* print i,LMs[i],ExistingLMs,j; */
        if j gt 0 then
            Indices[j] := Append(Indices[j],i);
        else
            Append(~ExistingLMs,LMs[i]);
            Append(~Indices,[i]);
        end if;
    end for;
    ExistingLMs := ExistingLMs[[2..#ExistingLMs]] cat [ExistingLMs[1]];
    printf "npols=%o\tnLMs=%o\n", ss, #ExistingLMs; 
    Indices := Indices[[2..#Indices]] cat [Indices[1]];
    /* print ExistingLMs; */
    /* print Indices; */
    SS := SatSets_Generate(ExistingLMs,#ExistingLMs);
    SS := [Sort(&cat[Indices[i] : i in S]) : S in SS];
    return SS;
end function;

function Max_sigs(sigs)
    /* Given a set of signatures, returns the greatest one, as well as
    the list of indices realizing this maximum. */
    ires := [1]; res :=
    sigs[1]; for i in [2..#sigs] do
        if Sig_Lt(res,sigs[i]) then
            res := sigs[i];
            ires := [i];
        elif Sig_Simeq(res,sigs[i]) then
            Append(~ires,i);
        end if;
    end for;
    return res,ires;
end function;

function Sig_OfSatSet(S,LMs,sigs)
    /* Computes the signature of a saturated set, together with the
    list of indices realizing that signature. */
    XS := SatSet_lcm(S,LMs);
    sigsS := [Sig_Multiply(sigs[i],1,XS div LMs[i]) : i in S];
    sig_ss,ii := Max_sigs(sigsS);
    ss := [S[i] : i in ii];
    return sig_ss,ss;
end function;

function Sig_RegularizeSatSet(S,LMs,sigs)
    /* Given a saturated set, computes all regular saturated sets which
    have the same lcm */
    sig_ss,SS := Sig_OfSatSet(S,LMs,sigs);
    XS := SatSet_lcm(S,LMs);
    Srest := [s : s in S | not s in SS];
    res := [];
    for s in SS do
        Scand := Append(Srest,s);
        if XS eq SatSet_lcm(Scand,LMs) then
            Append(~res,Scand);
        end if;
    end for;
    return res;
end function;

function Moller_Reduce(gg,sigG,ss,pols,sigs,LMs,LCs,funs :
                       Criterion := true,
                       Tail := true)
    /* Implements weak reduction of gg, with signature sigG, wrt
    module elements alpha_1..alpha_ss. The alpha_i's are given with
    their signature sigs[i] and their polynomial pols[i].
    
    For all i in [1..ss], LMs[i] = LeadingMonomial(pols[i]) and LCs[i] = LeadingCoefficient(pols[i]).

    Optional parameters:
    - Criterion: True iff we only do regular reductions (if false, the contents of sigG and sigs are ignored) 
    - Tail: True iff we want to reduce beyond the leading coefficient of gg (it makes the algorithm more efficient and the output more readable)
   */
    
    SatIdeal,CosetRep,LinDecomp := Explode(funs);
    reducible := true;
    m := #pols;
    sing_red := false;
    g := gg;
    res := 0;
    first := true;
    main_term := 0;
    
    while first or (Tail and g ne 0) do
        first := false;
        reducible := true;
        while reducible do
            /* print(g); */
            if g eq 0 then
                reducible := false;
                break;
            end if;
            lm := LeadingMonomial(g);
            S := SatSet_of_mon(LMs,m,lm);
            
            if Criterion then
                done := false;
                while not IsEmpty(S) and not done do

                    XS := LeadingMonomial(g);
                    sigsS := [Sig_Multiply(sigs[i],1,XS div LMs[i]) : i in S];
                    
                    if exists(iii){i : i in [1..#S]
                                   | Sig_Simeq(sigsS[i],sigG)
                                     or Sig_Lt(sigG,sigsS[i])} then
                        
                        Remove(~S,iii);
                    else
                        done := true;
                    end if;
                end while;
            end if;
            
            if IsEmpty(S) then
                /* Then we cannot reduce any more */
                reducible := false;
            else     
                LC_S := [LCs[j] : j in S];
                lc := LeadingCoefficient(g);
                lc_red := CosetRep(LC_S,lc);
                /* printf "S=%o, LC_S=%o, lc=%o, lc_red=%o\n", S, LC_S,lc,lc_red; */
                if lc_red ne 0 then
                    /* We cannot eliminate the leading coefficient, so we
                mark the polynomial as irreducible and we perform one
                last reduction step to bring the LC to coset
                representative form */
                    reducible := false;
                    lc := lc-lc_red;
                end if;
                
                bb := LinDecomp(LC_S,lc);
                for j in [1..#LC_S] do
                    ii := S[j];
                    g -:= bb[j]*(lm div LMs[ii])*pols[ii];
                end for;
            end if;
        end while;
        if Tail then
            res +:= LeadingTerm(g);
            g -:= LeadingTerm(g);
        else
            res := g;
        end if;
    end while;
    return res;
end function;


function Sig_F5Criterion(sig_ss,ss,LMs,LCs,sigs,interm_ideals,funs)
    /* True iff the signature sig_ss satisfies the F5 criterion (and
    should be kept)

    That is, if sig_ss = k*m*e_i, it is True iff k*m is not reducible
    modulo a basis of the initial ideal of <f_1...f_(i-1)>. This basis
    is recovered from LMs and LCs (respectively the LMs and LCs of
    already computed elements) and interm_ideals[i-1] (which holds the
    index of the last polynomial in the basis with signature
    #*#*e_(i-1)).
   */
    
    if sig_ss`i eq 1 then
        return true;
    end if;
    lpols := [LCs[i]*LMs[i] : i in [1..interm_ideals[sig_ss`i]-1]];
    mon := sig_ss`k * sig_ss`mu;
    mon_red := Moller_Reduce(mon,0,ss,lpols,sigs,LMs,LCs,funs : Criterion := false);
    return mon_red ne 0;
end function;


function SatSets_Generate_maybe_regular(ss,LMs,sigs
                                        : Criterion := true)
    /* Generates (regular) saturated sets of [1..ss]

    Optional parameters:
    - Criterion: if false, just compute all saturated sets,
      disregarding the signatures
   */
    
    new_satsets := SatSets_Generate_with_grouping(LMs,ss);
    /* print "New candidate satsets:", new_satsets; */
    if Criterion then
        /* If we are computing with signatures, we need to extend the
        set of saturated sets whenever we add a polynomial to the
        basis */

        res := [];
        for S in new_satsets do
            res cat:= Sig_RegularizeSatSet(S,LMs,sigs);
        end for;
        new_satsets := res;
    end if;
    return new_satsets;
end function;


function OneSingularReducible(g,SigG,sigs,LMs,ss)
    /* Test if a candidate basis element is 1-singular reducible.

    Implementation of 1-SingularReducible (Algorithm 4)
   */
    LMg := LeadingMonomial(g);
    test := exists{j : j in [1..ss-1] | IsDivisibleBy(LMg,LMs[j])
                                        and ((LMg div LMs[j])*(sigs[j]`mu))
                                            eq SigG`mu
                                        and sigs[j]`i eq SigG`i
                                        and IsDivisibleBy(SigG`k,sigs[j]`k) };
    return test;
end function;

function Moller_GB (F,funs :
                    Signature := true,
                    F5_Criterion := true,
                    Sing_Criterion := true)
    /*
    Compute a Gröbner basis of F.

    funs are the required algorithms for the base ring: SatIdeal,
    CosetRep and LinDecomp.  CosetRep is not described in the paper,
    for applicable rings it gives the possibility to perform "total
    reductions", giving to each Leading Coefficient a unique
    representation modulo the leading coefficient of candidate
    reducers.

    For example over ZZ, the Euclidean remainder can be used, and over
    a multivariate polynomial ring, the Normal Form modulo a Gröbner basis.

    When not applicable, a generic "do-nothing" CosetRep function is provided.

    Optional parameters:
    - Signature: True iff we want to compute a signature Gröbner basis (if false, the algorithm is just the classical version of Möller's algorithm)
    - F5_Criterion: True iff we want to exclude S-vectorsets using the F5 criterion
    - Sing_Criterion: True iff we want to exclude S-vectorsets using the singular criterion
   */
                   
    SatIdeal,CosetRep,LinDecomp := Explode(funs);
    pols := [];
    sigs := [];
    LMs := [];
    LCs := [];
    interm_ideals := [];
    m := #F;
    ss := 1;
    cnt_vectsets := 0;
    cnt_satsets := 0;
    cnt_red0 := 0;
    cnt_sing_pairs := 0;
    cnt_1sing_red := 0;
    cnt_F5_pairs := 0;
    SS := [];
    prev_sig := Sig_Create(1,1,1);
    for i in [1..m] do
        sigi := Sig_Create(1,1,i);
        fred := Moller_Reduce(F[i],sigi,ss,pols,sigs,LMs,LCs,funs :
                              Criterion := Signature);
        
        if fred eq 0 then
            printf "F[%o] reduces to 0\n", i;
            Append(~interm_ideals,#pols);
            printf "i=%o, interm_ideals=%o\n",i,interm_ideals;
            continue;
            // In this case we completely skip this polynomial
        end if;
        Append(~pols,fred);
        Append(~sigs,sigi);
        Append(~LMs, LeadingMonomial(fred));
        Append(~LCs, LeadingCoefficient(fred));
        Append(~interm_ideals,#pols);
        printf "i=%o, interm_ideals=%o\n",i,interm_ideals;

        new_satsets :=
            SatSets_Generate_maybe_regular(#pols,LMs,sigs
                                           :Criterion := Signature);
        printf "Adding %o new saturated sets\n", #new_satsets;
        SS cat:= new_satsets;
        SS := Setseq(Seqset(SS)); /* Eliminate duplicates */

        
        while not IsEmpty(SS) do
            printf "#SS=%o\n", #SS;
            if Signature then
                Sort(~SS,func<S1,S2 | Sig_Compare(Sig_OfSatSet(S1,LMs,sigs),
                                                  Sig_OfSatSet(S2,LMs,sigs))>);
            end if;
    
            /* If we are using the signature algorithm, SS is sorted by increasing signatures */
            S := SS[1];
            Remove(~SS,1);
            print "S=", S;

            if Signature then
                sigS,smax := Sig_OfSatSet(S,LMs,sigs);
                ss := smax[1];
            else
                ss := Max(S);
            end if;
            
            if #S eq 1 then
                continue;
            end if;

            cnt_satsets +:= 1;
            
            XS := SatSet_lcm(S,LMs);

            /* ss := Max(S); */
            f_current := pols[ss];
            lm_current := LeadingMonomial(f_current);
            
            Srest := [j : j in S | j ne ss];
            LC_S := [LCs[j] : j in Srest];
            gens := SatIdeal(LC_S,LCs[ss]);
            for b_S in gens do
                if Signature then
                    SigG := Sig_Multiply(sigS,b_S,1);
                    printf "Signature of saturated set: %o\n",
                           Sig_ToString(SigG);
                    if Sing_Criterion and exists{s : s in sigs | Sig_Eq(s,SigG)} then
                        printf "Polynomial excluded by singular criterion\n";
                        cnt_sing_pairs +:= 1;
                        continue;
                    elif F5_Criterion
                         and not Sig_F5Criterion(SigG,ss,LMs,LCs,sigs,
                                                 interm_ideals,funs) then
                        printf "Polynomial excluded by F5 criterion\n";
                        cnt_F5_pairs +:= 1;
                        continue;
                    end if;
                else
                    SigG := 0; // Arbitrary, for the call to reduce
                end if;

                cnt_vectsets +:= 1;
                
                bb := LinDecomp(LC_S,b_S*LCs[ss]);
                g := b_S*(XS div lm_current) * f_current;
                /* print LC_S,S; */
                for j in [1..#LC_S] do
                    ii := Srest[j];
                    g -:= bb[j]
                          *(XS div LeadingMonomial(pols[ii]))
                          *pols[ii];
                end for;
                gg := Moller_Reduce(g,SigG,ss,pols,sigs,LMs,LCs,funs
                                    : Criterion := Signature);

                if gg eq 0 then
                    /* Regular syzygy */
                    
                    printf "Reduction to 0\n";
                    cnt_red0 +:= 1;
                    //error "";
                elif Signature and OneSingularReducible(g,SigG,sigs,LMs,ss) then
                    /* 1-Singular reducible */
                    
                    printf "1-singular reducible: %o\n", gg;
                    cnt_1sing_red +:= 1;
                else
                    /* Otherwise: added to the basis */

                    if Signature then
                        printf "Adding %o with signature (%o,%o,%o)\n",
                               gg, SigG`k,SigG`mu,SigG`i;
                    end if;
                    Append(~pols,gg);
                    if Signature then
                        Append(~sigs,SigG);
                    end if;
                    Append(~LMs, LeadingMonomial(gg));
                    Append(~LCs, LeadingCoefficient(gg));
                    new_satsets :=
                        SatSets_Generate_maybe_regular(#pols,LMs,sigs
                                                       :Criterion := Signature);
                    printf "Adding %o new saturated sets\n", #new_satsets;
                    SS cat:= new_satsets;
                    SS := Setseq(Seqset(SS)); /* Eliminate duplicates */

                end if;
            end for;
        end while;
    end for;
    printf "Total # of vectorsets: %o\n", cnt_vectsets;
    printf "Total # of saturated sets: %o\n", cnt_satsets;
    printf "Total # of reductions to 0: %o\n", cnt_red0;
    printf "Total # of skipped singular S-pairs: %o\n", cnt_sing_pairs;
    printf "Total # of skipped F5 S-pairs: %o\n", cnt_F5_pairs;
    printf "Total # of skipped 1-singular-reducible pols: %o\n", cnt_1sing_red;
    return pols,sigs;
end function;

function Moller_ReduceGB(G,funs)
    /* Given a Gröbner basis, compute a reduced Gröbner basis */
    
    finished := false;
    while not finished do
        while 0 in G do
            Exclude(~G,0);
        end while;
        done_anything := false;
        for i in [1..#G] do
            rest := [j : j in [1..#G] | j ne i];
            pols := [G[j] : j in rest];
            LMs := [LeadingMonomial(G[j]) : j in rest];
            LCs := [LeadingCoefficient(G[j]) : j in rest];
            gg := Moller_Reduce(G[i],0,#G,pols,[],LMs,LCs,funs
                                : Criterion := false);
            if gg ne G[i] then
                done_anything := true;
                G[i] := gg;
                if gg eq 0 then
                    break;
                end if;
            end if;
        end for;
        if not done_anything then
            finished := true;
        end if;
    end while;
    return G;
end function;


/* Implementation of the ring procedures */


// Functions for euclidian rings

function Euclid_SatIdeal(F,g)
    d := Gcd(F);
    m := Lcm(d,g);
    return [m div g];
end function;

function Euclid_CosetRep(F,g)
    res := g mod (Gcd(F));
    return res;
end function;

function Euclid_LinDecomp(F,g)
    d,bb := ExtendedGreatestCommonDivisor(F);
    if g mod d ne 0 then
        error "Not divisible";
    else
        dd := g div d;
        return [b*dd : b in bb];
    end if;
end function;


// Functions for fields

function Field_SatIdeal(F,g)
    return [1];
end function;

function Field_CosetRep(F,g)
    return 0;
end function;

function Field_LinDecomp(F,g)
    return [0 : i in [1..#F-1]] cat [g/F[#F]];
end function;


// Functions for multivariate polynomial rings

function Pol_SatIdeal(F,g)
    return GroebnerBasis(ColonIdeal(Ideal(F),Ideal(g)));
end function;

/*
Behind the scenes:

I : (f) = 1/f (I cap (f))
I cap f = elim(t, t I + (1-t)f)
*/

function Pol_CosetRep(F,g)
    return NormalForm(g,Ideal(F));
end function;

function Pol_LinDecomp(F,g)
    I := IdealWithFixedBasis(F);
    return Coordinates(I,g);
end function;


// Generic CosetRep function for rings without definite coset
// representatives

function Generic_CosetRep(F,g)
    return g;
end function;
