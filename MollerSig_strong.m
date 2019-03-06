// Created: Fri May  4 13:28:56 2018
// Last modified: Wed Mar  6 11:49:32 2019
// Hash: 3ef3a23b147270a205604a50dfacab4c

Attach("general.m");

load "Signatures.m";


function SPol_Sig(f1,f2,t,s1,s2)
    /* Return a signature similar to the signature of a S-polynomial.

    The point of this function is to give a faster computation of the signature whenever an exact value is not required.

    TODO: Further optimization: cache the results.

    INPUT:
    - f1, f2 two polynomials
    - t = lcm(LT(f1),LT(f2))
    - s1, s2 the signatures of f1 and f2 respectively

    ASSUMPTION:
    - the S-polynomial (f1,f2) is admissible

    OUTPUT:
    - s such that s \simeq sig(SPol(f1,f2))
   */
    m := LeadingMonomial(t);
    m1 := m div LeadingMonomial(f1);
    m2 := m div LeadingMonomial(f2);
    sf1 := Sig_Multiply(s1,1,m1);
    sf2 := Sig_Multiply(s2,1,m2);
    return Sig_Max(sf1,sf2);
end function;

function SPol(f1,f2,t,s1,s2)
    /* Compute a S-polynomial and its signature.

    INPUT:
    - f1, f2 two polynomials
    - t = lcm(LT(f1),LT(f2))
    - s1, s2 the signatures of f1 and f2 respectively

    OUTPUT:
    - f = SPol(f1,f2)
    - s = sig(SPol(f1,f2)) if the S-polynomial is admissible and Sig_Null
      otherwise
    
   */
    if t eq 0 then
        t := Lcm(LeadingTerm(f1),LeadingTerm(f2));
    end if;
    t1 := t div LeadingTerm(f1);
    t2 := t div LeadingTerm(f2);
    mm1 := LeadingMonomial(t1);
    cc1 := LeadingCoefficient(t1);
    mm2 := LeadingMonomial(t2);
    cc2 := LeadingCoefficient(t2);
    /* print t; */
    f := cc1*mm1*f1 - cc2*mm2*f2;
    sf1 := Sig_Multiply(s1,cc1,mm1);
    sf2 := Sig_Multiply(s2,cc2,mm2);
    // This excludes all singular S-polynomials 
    if Sig_IsNull(sf1) or not Sig_Simeq(sf1,sf2) then
        msf2 := Sig_Multiply(sf2,-1,1);
        sf := Sig_Max(sf1,msf2);
    else
        sf := Sig_Null;
    end if;
    /* sf := Sig_Add(sf1,msf2); // Null iff strictly singular */
    return f,sf;
end function;

function GPol(f1,f2,s1,s2)
    /*
    Compute a G-polynomial and its G-signature

    INPUT:
    - f1, f2 two polynomials
    - s1, s2 the signatures of f1 and f2 respectively

    OUTPUT:
    - f = GPol(f1,f2)
    - s \simeq S_G(s1,s2)

    NOTE:
    - s is actually a true signature (S-labelling) if the combination
      is not a signature drop.  Using sig(GPol(f1,f2)) whenever
      possible makes the 1-singular criterion more efficient (against
      G_s).

    sig(GPol(f1,f2)) anymore

   */
    m1 := LeadingMonomial(f1);
    c1 := LeadingCoefficient(f1);
    m2 := LeadingMonomial(f2);
    c2 := LeadingCoefficient(f2);
    m := Lcm(m1,m2);
    d,a1,a2 := ExtendedGreatestCommonDivisor(c1,c2);
    if a1 ne 0 and a2 ne 0 then
        mm1 := m div m1;
        mm2 := m div m2;
        f := a1*mm1*f1 + a2*mm2*f2;
        sf1 := Sig_Multiply(s1,a1,mm1);
        sf2 := Sig_Multiply(s2,a2,mm2);
        sf := Sig_Add(sf1,sf2);
        if Sig_IsNull(sf) then
            sf := Sig_Max(sf1,sf2);
        end if;
    else
        f := Parent(f1)!0;
        sf := s1;
    end if;
    if sf`k eq 0 then
        error("Illegal signature computed.");
    end if;

    return f,sf;
end function;

function LCReduce(f,sf,G,sigs : Signature := false)
    /*
    Implement (regular) LC reduction.

    INPUT:
    - f, sf a polynomial and its signature
    - G a family of strong reducers
    - sigs their respective signatures
    - Signature (default: false): whether to require the reductions to
      be regular

    ASSUMPTION:
    - the coefficient ring is Euclidean
    - f is (regular) reduced modulo G

    OUTPUT:
    - g such that f = g modulo G, LM(f) = LM(g) and |LC(g)| <= |LC(f)|

    NOTE:
    - this function is not used at the moment
    
   */

    mf := LeadingMonomial(f);
    N := #G;
    for i in [1..N] do
        g := G[i];
        test,md :=  IsDivisibleBy(mf, LeadingMonomial(g));
        if test and ((not Signature) or Sig_Lt(Sig_Multiply(sigs[i],1,md),sf)) then
            cg := LeadingCoefficient(g);
            cf := LeadingCoefficient(f);
            cd := cf div cg;
            cr := cf mod cg;
            if cr lt cf and cr gt cg/2 then
                cd +:= 1;
            end if;
            f -:= cd*md*g;
        end if;
    end for;
    return f;
end function;

function StrongReduce(f,sf,G,sigs
                      : Signature := false,
                        LC_red := false)
    /*
    Implement (regular) top-reduction.

    INPUT:
    - f, sf a polynomial and its signature
    - G a family of strong reducers
    - sigs their respective signatures
    - Signature (default: false): whether to require the reductions to
      be regular
    - LC_red (default: true): ignored

    OUTPUT:
    - g such that f = g modulo G, LM(g) <= LM(f) and g is (regular)
      top-reduced modulo G
   */
    done := false;
    while not done and f ne 0 do
        done := true;
        tf := LeadingTerm(f);
        for i := 1 to #G do
            g := G[i];
            test,d := IsDivisibleBy(tf,LeadingTerm(g));
            if test then
                /* sig_res := Sig_Add(sf,sig_red); */
                if ((not Signature)
                    or
                    // Only regular reductions
                    (Sig_Lt(Sig_Multiply(sigs[i],1,LeadingMonomial(d)),sf))
                    // Only non strictly singular reductions
                    /* (Sig_Leq(Sig_Multiply(sigs[i],1,md),sf) */
                    /*  and not Sig_IsNull(sig_res)) */
                   )  then

                    f -:= d * g;
                    done := false;

                    if f eq 0 then
                        break; // Break for, so go back to the beginning of the while
                    else
                        tf := LeadingTerm(f); // It seems to be better to continue through the list here. Why?
                    end if;
                end if;
            end if;
        end for;
    end while;

    // LC reductions, for the future?
    if LC_red and f ne 0 then
        f := LCReduce(f,sf,G,sigs : Signature := Signature);
    end if;
    
    /* printf "\n"; */
    return f;
end function;

function TotalStrongReduce(f,sf,G,sigs 
                           : Signature := false, LC_red := true)
    /*
    Implement (regular) reduction (including tail coefficients).

    INPUT:
    - f, sf a polynomial and its signature
    - G a family of strong reducers
    - sigs their respective signatures
    - Signature (default: false): whether to require the reductions to
      be regular

    OUTPUT:
    - g such that f = g modulo G, LM(g) <= LM(f) and g is totally
      (regular) reduced modulo G
   */

    
    res := 0;
    ff := f;
    while ff ne 0 do
        ff := StrongReduce(ff,sf,G,sigs : Signature := Signature, LC_red := LC_red);
        res +:= LeadingTerm(ff);
        ff -:= LeadingTerm(ff);
    end while;

    return res;
end function;


function Criterion_Coprime(f,g)
    /* Implement the coprime criterion.

    INPUT:
    - f,g two polynomials

    OUTPUT:
    - true if and only if the S-pair (f,g) should not be eliminated with the coprime criterion    
    
   */
    
    return Gcd(LeadingMonomial(f),LeadingMonomial(g)) ne 1;
end function;

function Criterion_GebauerMoller_admissible(T,G,sigs,i,j,k)
    /* Implement the signature check for the chain criterion

    INPUT:
    - T cache of lcm(leading terms) (see the description of
      algo. SigMoller)
    - G currently constructed basis
    - sigs their respective signatures
    - i,j,k integers at most #G

    ASSUMPTION:
    - T(k) divides T(i,j)

    OUTPUT:
    - true if and only S(i,j) > T(i,j)/T(k) S(k) and (i,j) > (i,k) and (i,j) > (j,k)
   */
    
    if i eq k or j eq k or i eq j then
        return false;
    end if;

    if i gt j then
        jii := j; jij := i;
    else
        jii := i; jij := j;
    end if;

    if j gt k then
        kjj := k; kjk := j;
    else
        kjj := j; kjk := k;
    end if;

    if i gt k then
        kii := k; kik := i;
    else
        kii := i; kik := k;
    end if;
    
    mji := LeadingMonomial(T[jij][jii]);
    mki := LeadingMonomial(T[kik][kii]);
    mkj := LeadingMonomial(T[kjk][kjj]);

    /* mji := LeadingMonomial(T[j][i]); */
    
    Si := Sig_Multiply(sigs[i],1,mji div LeadingMonomial(G[i]));
    Sj := Sig_Multiply(sigs[j],1,mji div LeadingMonomial(G[j]));
    Sk := Sig_Multiply(sigs[k],1,mji div LeadingMonomial(G[k]));

    Sji := Sig_Max(Si,Sj);

    /* (i,k) < (i,j) */
    testki := mji ne mki
              or (mji eq mki
                  and (kik lt jij
                       or (kik eq jij and kii lt jii)
                      ));

    /* (j,k) < (i,j) */
    testkj := mji ne mkj
              or (mji eq mkj
                  and (kjk lt jij
                       or (kjk eq jij and kjj lt jii)
                      ));

    /* TODO : a lot of those tests are probably useless */
    
    return /* Sig_Lt(Sk,Sji) or  */(Sig_Lt(Sk,Sji) and testki and testkj);
end function;


function IsEqualUpToUnit(a,b)
    /* Implement comparison of polynomials up to an invertible

    INPUT:
    - a,b two polynomials

    OUTPUT:
    - true iff a = u*b with u an invertible scalar

    NOTE:
    - this function is not used anywhere
    
   */
    return IsDivisibleBy(a,b) and IsUnit(a div b);
end function;


function Criterion_Chain(T,G,sigs,i,j,k)
    /* Implement the chain criterion with signatures

    INPUT:
    - T cache of lcm(leading terms) (see the description of
      algo. SigMoller)
    - G currently constructed basis
    - sigs their respective signatures
    - i,j,k integers at most #G

    OUTPUT:
    - true if and only Chain(i,j;k) does not hold
   */
    if #{i,j,k} lt 3 then
        return true;
    else
        if i gt j then
            tmp := i; i := j; j := tmp;
        end if;
    end if;

    test := IsDivisibleBy(T[j][i],LeadingTerm(G[k])) and Criterion_GebauerMoller_admissible(T,G,sigs,i,j,k);

    return not test;
end function;
    
function Criterion_Chain_back(T,G,sigs,i,j)
    /* Implement the chain criterion with signatures, looking back for
    a k

    INPUT:
    - T cache of lcm(leading terms) (see the description of
      algo. SigMoller)
    - G currently constructed basis
    - sigs their respective signatures
    - i,j integers at most #G

    OUTPUT:
    - true if and only for all k <= #G, Chain(i,j;k) does not hold
   */
    test := true;
    kk := 0;
    for k in [1..j-1] do
        if not Criterion_Chain(T,G,sigs,i,j,k) then
            kk := k;
            test := false;
            break;
        end if;
    end for;
    return test,kk;
end function;
        


function Criterion_GebauerMoller_B(T,G,sigs,i,j,k)
    /* Implements Gebauer-Möller's "B" criterion, without signature.

    (True iff the polynomial should be kept)
   */

    test := i lt j and j lt k
            and IsDivisibleBy(T[j][i],LeadingTerm(G[k]))
            and T[k][j] ne T[j][i]
            and T[j][i] ne T[k][j];
    return not test;
end function;
    
function Criterion_GebauerMoller_M(T,G,sigs,i,k)
    /* Implements Gebauer-Möller's "M" criterion, without signature.
   */
    test := i lt k
            and exists{j : j in [1..k-1] |
                       IsDivisibleBy(T[k][i],T[k][j])
                       and T[k][j] ne T[k][i]};
    return not test;
end function;

function Criterion_GebauerMoller_F(T,G,sigs,i,k)
    /* Implements Gebauer-Möller's "F" criterion, without signature.
     */
    test := i lt k
            and exists{j : j in [1..i-1] | T[k][j] eq T[k][i]};
    return not test;
end function;

function Criterion_1SingularReducible(f,sf,G,sigs)
    /* Test whether f is 1-singular reducible modulo G

    INPUT:
    - f a polynomial
    - sf its signature
    - G a family of reducers
    - sigs their respective signatures

    ASSUMPTION:
    - f is regular reduced modulo G

    OUTPUT:
    - true if and only if f is 1-singular reducible modulo G    
   */

    test := false;
    tf := LeadingTerm(f);
    mf := LeadingMonomial(f);
    cf := LeadingCoefficient(f);

    for i in [1..#G] do
        g := G[i];
        sg := sigs[i];
        test2, mmg := IsDivisibleBy(mf,LeadingMonomial(g));
        if test2
           and sg`i eq sf`i
           and (sg`mu * mmg) eq sf`mu
           and IsDivisibleBy(sf`k,sg`k) then
            test := true;
            break;
        end if;
    end for;
    return test;
end function;

function Criterion_F5(f,sf,G,sigs)
    /* Implement the F5 criterion

    INPUT:
    - f a polynomial
    - sf its signature
    - G the currently constructed basis
    - sigs their respective signatures

    OUTPUT:
    - true if and only if f should be kept after applying the F5 criterion 
    
   */
    
    if sf`i eq 1 then
        return true;
    end if;
    slim := Sig_Create(1,1,sf`i);
    LPols := [LeadingTerm(G[i])
              : i in [1..#G]
              | Sig_Lt(sigs[i],slim)];
    mon := sf`k * sf`mu;
    mon_red := StrongReduce(mon,sf,LPols,sigs : Signature:=false, LC_red := false);
    res := mon_red ne 0;
    return res;
end function;

function Criterion_Singular(f,sf,G,sigs)
    /* Implement the singular criterion

    INPUT:
    - f a polynomial (ignored)
    - sf its signature
    - G the currently constructed Gröbner basis
    - sigs their respective signatures

    OUTPUT:
    - true if and only if no element in G has exactly the same signature as f
   */
    
    test := exists{s : s in sigs | s`i eq sf`i
                                   and s`mu eq sf`mu
                                   and s`k eq sf`k
                                   /* and IsDivisibleBy(sf`k,s`k) */};
    return not test;
end function;







procedure UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,f,sf,
                           ~cnt_coprime,~cnt_GM_B,~cnt_GM_M,~cnt_GM_F,~cnt_GM_all,
                           ~cnt_pairs,~cnt_Spairs
                           : Signature := false, GebauerMoller := false)
    /* Implement the procedure "Update": update the two Gröbner bases, the list of pairs and the caches

    INPUT:
    - P the current list of S-pairs
    - G the current weak Gröbner basis
    - sigs their respective signatures
    - SG the current strong Gröbner basis
    - sigsSG their respective signatures
    - T the current cache of lcm(leading terms)
    - f the polynomial to add
    - sf its signature
    - cnt_coprime an integer counting pairs eliminated with the
      coprime criterion
    - cnt_GM_B an integer counting pairs eliminated with
      Gebauer-Möller's B criterion
    - cnt_GM_F an integer counting pairs eliminated with
      Gebauer-Möller's F criterion
    - cnt_GM_M an integer counting pairs eliminated with
      Gebauer-Möller's M criterion
    - cnt_GM_all an integer counting pairs eliminated with the chain
      criterion with signatures
    - cnt_pairs an integer counting how many pairs are considered
    - cnt_Spairs an integer counting how many pairs are added to P

    ACTION:
    - the list of pairs P is updated
    - the weak Gröbner basis and its signatures are updated
    - the strong Gröbner basis and its signatures are updated
    - T is updated
    - the counters are updated
   */
    
    // Updating the weak basis
    Append(~G,f);
    N := #G;
    Append(~sigs,sf);

    // Updating T
    Append(~T,[]);
    t := LeadingTerm(f);
    for i in [1..N-1] do
        /* tt := Lcm(LeadingTerm(G[i]),t); */
        /* Append(~T[i],Lc) */
        Append(~T[N],Lcm(LeadingTerm(G[i]),t));
    end for;
    cnt_pairs +:= N-1;

    
    // Updating the list of critical pairs
    for i in [1..N-1] do
        if not Criterion_Coprime(f,G[i]) then
            cnt_coprime +:= 1;
        elif Signature then
            test_chain,k := Criterion_Chain_back(T,G,sigs,i,N);
            if GebauerMoller and not test_chain then
                cnt_GM_all +:= 1;
                vprintf MollerSig,3: "Eliminated pair due to chain criterion (back): (i,j;k) = (%o,%o;%o) sig=%o\n",
                                     i, N, k,
                Sig_ToString(SPol_Sig(f,G[i],T[N][i],sf,sigs[i]));
                
            else
                cnt_Spairs +:= 1;
                p,sp := SPol(f,G[i],T[N][i],sf,sigs[i]);
                if p ne 0 and not Sig_IsNull(sp) then
                    Append(~P,<p,sp,<i,N>>);
                end if;
            end if;
        else
            if GebauerMoller and not Criterion_GebauerMoller_M(T,G,sigs,i,N) then
                cnt_GM_M +:= 1;
            elif GebauerMoller and not Criterion_GebauerMoller_F(T,G,sigs,i,N) then
                cnt_GM_F +:= 1;
            else
                cnt_Spairs +:= 1;
                p,sp := SPol(f,G[i],T[N][i],sf,sigs[i]);
                if p ne 0 then
                    Append(~P,<p,sp,<i,N>>);
                end if;
            end if;
        end if;
    end for;
    
    if Signature then
        Sort(~P, func<P1,P2 | Sig_Compare_Full(P1[2],P2[2])>);
    end if;

    if GebauerMoller then
        toRemove := [];
        for k in [1..#P] do
            pp := P[k];
            ii,jj := Explode(pp[3]);
            if Signature then
                if not Criterion_Chain(T,G,sigs,ii,jj,N) then
                    cnt_GM_all +:= 1;
                    vprintf MollerSig,3: "Eliminated pair due to chain criterion: (i,j;k) = (%o,%o;%o) sig=%o\n",
                                         ii, jj, N, Sig_ToString(pp[2]);
                    Append(~toRemove,k);
                end if;
            else
                if not Criterion_GebauerMoller_B(T,G,sigs,ii,jj,N) then
                    cnt_GM_B +:= 1;
                    Append(~toRemove,k);
                    cnt_Spairs -:= 1;
                end if;
            end if;
        end for;
        for k in Reverse(toRemove) do
            Remove(~P,k);
        end for;
    end if;
        
    // Updating the strong basis
    Append(~SG,f);
    Append(~sigsSG,sf);
    for i in [1..#SG-1] do
        p,sp := GPol(f,SG[i],sf,sigsSG[i]);
        if sp`k eq 0 then
            error("Illegal signature computed.");
        end if;
        if p ne 0 then
            Append(~SG,p);
            Append(~sigsSG,sp);
        end if;
    end for;
end procedure;




function MollerSig(F:
                    Signature := true,
                    F5_Criterion := true,
                    Sing_Criterion := true,
                    GebauerMoller := true,
                    InterReduce := true)
    /* Uses Möller's strong GB algorithm to compute a Gröbner basis.

    INPUT:
    - F : polynomial system over R
    - Signature (default: true): whether to use signatures
    - F5_Criterion (default: true): whether to use the F5 criterion
    - Sing_Criterion (default: true): whether to use the Singular
      criterion
    - GebauerMoller (default: true): whether to use Buchberger's chain
      criterion (through Gebauer-Möller's criteria, if no signatures)
    - InterReduce (default: true): whether to inter-reduce the Gröbner
      basis whenever we process a new polynomial (see below)

    OUTPUT:
    - G : weak Gröbner basis of Ideal(F)
    - SG : strong Gröbner basis of Ideal(F)
    - sigs : sigs[i] is the signature (S-label) of G[i] (unless
      InterReduce is true, then see below)
    - sigsSG : sigsSG[i] is the G-signature of SG[i]
    - T: T[i][j], if i < j is an admissible pair, is
      lcm(LT(G[i]),LT(G[j])) if InterReduce is false (otherwise, see
      below)

    ASSUMPTION:
    - the coefficient ring of R is a PID

    NOTES:
    - If Signature is false, sigs and sigsSG are obviously meaningless
    
    - If InterReduce is true, whenever the algorithm adds F[i] to the
      Gröbner basis, it knows that all elements which will be computed
      later have signature at least e_i, and all elements computed
      before have signature at most m*e_(i-1) for m large enough. So
      it can inter-reduce the Gröbner basis, disregarding signature
      restrictions, and give every polynomial in the result label
      m*e_(i-1) (or even e_1 if we don't want the output to be a
      S-GB).

      This leads to a huge speed-up in the computations. However, the
      result is that sigs is only a S-labelling from signature e_i on,
      and only a G-labelling before that. And T[i][j], if i and j are
      less than the index of F[i], no longer matches the indices in
      G. This is harmless in the computations, but the user who cares
      about this part of the output should set InterReduce to false.

    - The algorithm obeys the verbosity flag "MollerSig", with values
      from 0 to 3.    
    
   */

    
    if not Signature then
        F5_Criterion := false;
        Sing_Criterion := false;
    end if;
    
    cnt_coprime := 0;
    cnt_F5 := 0;
    cnt_GM_B := 0;
    cnt_GM_M := 0;
    cnt_GM_F := 0;
    cnt_GM_all := 0;
    cnt_1sing_red := 0;
    cnt_sing := 0;
    cnt_syz := 0;
    cnt_pairs := 0;
    cnt_Spairs := 0;

    A := Parent(F[1]);
    R := CoefficientRing(A);
    
    if InterReduce and IsEuclideanDomain(CoefficientRing(A)) then
        printf "Warning: for Euclidean domains, InterReduce can in theory lead to incorrect results.\n";
        printf "Please use MollerSig_Euclidean instead.\n";
    end if;
    
    G := [];
    SG := [];
    P := [];
    sigs := [];
    sigsSG := [];
    T := []; // T[j][i] is the lcm of the LT of G[i] and G[j]
    m := #F;
    for i in [1..m] do
        vprintf MollerSig,1: "############ i=%o ############\n",i;

        if i gt 1 and InterReduce then
            SG := ReduceGroebnerBasis(SG);
            sigsSG := [Sig_Create(1,1,i-1) : g in SG];
            G := SG;
            sigs := sigsSG;
            T := [[Lcm(LeadingTerm(G[j]),LeadingTerm(G[i])) : j in [1..i-1]] : i in [1..#G]];
        end if;
        
        f := F[i]; 
        sf := Sig_Create(1,1,i);
        f := TotalStrongReduce(f,sf,SG,sigsSG
                               : Signature := Signature, LC_red := false); 
        if f eq 0 then
            continue;
        end if;
        UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,f,sf,
                         ~cnt_coprime,~cnt_GM_B,~cnt_GM_M,~cnt_GM_F,~cnt_GM_all,
                         ~cnt_pairs,~cnt_Spairs
                         : Signature := Signature,
                           GebauerMoller := GebauerMoller);
        while #P gt 0 do
            vprintf MollerSig,2: "#P=%o #G=%o\n", #P, #G;
            next := 1; 
            pp := P[next]; Remove(~P,next);
            p := pp[1]; sp := pp[2];
            if Signature then
                if (F5_Criterion
                    and not Criterion_F5(p,sp,SG,sigsSG)) then
                    vprintf MollerSig,3: "Polynomial excluded by F5 criterion: <%o,%o>, sig=%o, LT=%o\n",
                                         pp[3][1], pp[3][2], Sig_ToString(sp), LeadingTerm(p);
                    cnt_F5 +:= 1;
                    continue;
                elif (Sing_Criterion
                      and not Criterion_Singular(p,sp,G,sigs)) then
                    vprintf MollerSig,3: "Polynomial excluded by Singular criterion\n";
                    cnt_sing +:= 1;
                    continue;
                end if;
            end if;
            
            r := StrongReduce(p,sp,SG,sigsSG
                              : Signature := Signature, LC_red := false);
            if r eq 0 then
                vprintf MollerSig,3 : "Reduction to zero: sig=%o\n", Sig_ToString(sp);
                cnt_syz +:= 1;
            elif Signature
                 and Criterion_1SingularReducible(r,sp,SG,sigsSG) then
                vprintf MollerSig,3 : "Basis element excluded because 1-singular reducible\n";
                cnt_1sing_red +:= 1;
            else
                r := TotalStrongReduce(r,sp,SG,sigsSG : Signature := Signature, LC_red := false);
                vprintf MollerSig,3 : "New basis element: sig=%o, LT=%o\n",
                       Sig_ToString(sp), LeadingTerm(r);//, pp[3];
                /* end if; */
                UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,r,sp,
                                 ~cnt_coprime,~cnt_GM_B,~cnt_GM_M,~cnt_GM_F,~cnt_GM_all,
                                 ~cnt_pairs,~cnt_Spairs
                                 : Signature := Signature,
                                   GebauerMoller := GebauerMoller);
            end if;
        end while;
    end for;

    vprintf MollerSig,1 : "Total # of S-polynomials: %o\n", cnt_Spairs;
    vprintf MollerSig,1 : "Total # of considered pairs: %o\n", cnt_pairs;
    vprintf MollerSig,1 : "Total # of reductions to 0: %o\n", cnt_syz;
    vprintf MollerSig,1 : "Total # of skipped pairs with coprime criterion: %o\n", cnt_coprime;
    if Signature then
        vprintf MollerSig,1 : "Total # of skipped pairs with chain criterion: %o\n", cnt_GM_all;
    else
        vprintf MollerSig,1 : "Total # of skipped pairs with Gebauer-Moller \"B\" criterion: %o\n", cnt_GM_B;
        vprintf MollerSig,1 : "Total # of skipped pairs with Gebauer-Moller \"M\" criterion: %o\n", cnt_GM_M;
        vprintf MollerSig,1 : "Total # of skipped pairs with Gebauer-Moller \"F\" criterion: %o\n", cnt_GM_F;
    end if;
    vprintf MollerSig,1 : "Total # of skipped pairs with F5 criterion: %o\n", cnt_F5;
    vprintf MollerSig,1 : "Total # of skipped pairs with sing criterion: %o\n", cnt_sing;
    vprintf MollerSig,1 : "Total # of skipped 1-singular-reducible pols: %o\n", cnt_1sing_red;
                                                                                    
    return G,SG,sigs,sigsSG,T;    
end function;
