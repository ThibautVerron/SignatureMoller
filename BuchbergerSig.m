// Created: Fri May  4 13:28:56 2018
// Last modified: Tue Jan 22 09:31:08 2019
// Hash: f791a494bf535835675f747367705c37

load "Signatures.m";

function SPol_Sig(f1,f2,t,s1,s2)
    m := LeadingMonomial(t);
    m1 := m div LeadingMonomial(f1);
    m2 := m div LeadingMonomial(f2);
    sf1 := Sig_Multiply(s1,1,m1);
    sf2 := Sig_Multiply(s2,1,m2);
    return Sig_Max(sf1,sf2);
end function;

function SPol(f1,f2,t,s1,s2)
    t1 := t div LeadingTerm(f1);
    t2 := t div LeadingTerm(f2);
    mm1 := LeadingMonomial(t1);
    cc1 := LeadingCoefficient(t1);
    mm2 := LeadingMonomial(t2);
    cc2 := LeadingCoefficient(t2);
    f := cc1*mm1*f1 - cc2*mm2*f2;
    sf1 := Sig_Multiply(s1,cc1,mm1);
    sf2 := Sig_Multiply(s2,cc2,mm2);
    // This excludes all singular S-polynomials
    /* if not Sig_Simeq(sf1,sf2) then */
    /*     sf := Sig_Max(sf1,sf2); */
    /* else */
    /*     sf := Sig_Null; */
    /* end if; */
    msf2 := Sig_Multiply(sf2,-1,1);
    sf := Sig_Add(sf1,msf2); // Null iff strictly singular
    return f,sf;
end function;

function GPol(f1,f2,s1,s2)
    m1 := LeadingMonomial(f1);
    c1 := LeadingCoefficient(f1);
    m2 := LeadingMonomial(f2);
    c2 := LeadingCoefficient(f2);
    m := Lcm(m1,m2);
    d,a1,a2 := ExtendedGreatestCommonDivisor(c1,c2);
    if d ne c1 and d ne c2 then
        mm1 := m div m1;
        mm2 := m div m2;
        f := a1*mm1*f1 + a2*mm2*f2;
        sf1 := Sig_Multiply(s1,a1,mm1);
        sf2 := Sig_Multiply(s2,a2,mm2);
        sf := Sig_Max(sf1,sf2);
        // Should it be max? We don't care if strictly singular,
        // but we don't want to lose the information about the signature 
    else
        f := Parent(f1)!0;
        sf := s1;
    end if;
    return f,sf;
end function;

function LCReduce(f,sf,G,sigs : Signature := false)
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
            if cr gt cg/2 then
                cd +:= 1;
            end if;
            f -:= cd*md*g;
        end if;
    end for;
    return f;
end function;

function StrongReduce(f,sf,G,sigs
                      : Signature := false,
                        LC_red := true)
    done := false;
    while not done and f ne 0 do
        done := true;
        for i in [1..#G] do
            g := G[i];
            sg := sigs[i];
            tf := LeadingTerm(f);
            tg := LeadingTerm(g);
            test,d := IsDivisibleBy(tf,tg);
            if test then
                md := LeadingMonomial(d);
                cd := LeadingCoefficient(d);
                /* sig_red := Sig_Multiply(sigs[i],(-1)*cd,md); */
                /* sig_res := Sig_Add(sf,sig_red); */
                if ((not Signature)
                    or
                    // Only regular reductions
                    (Sig_Lt(Sig_Multiply(sigs[i],1,md),sf))
                    // Only non strictly singular reductions
                    /* (Sig_Leq(Sig_Multiply(sigs[i],1,md),sf) */
                    /*  and not Sig_IsNull(sig_res)) */
                   )  then
                    /* printf "%o ",i; */
                    f -:= d * g;
                    /* sf := sig_res; */
                    done := false;
                    if f eq 0 then
                        break;
                    end if;
                end if;
            end if;
        end for;
    end while;

    if LC_red and f ne 0 then
        f := LCReduce(f,sf,G,sigs : Signature := Signature);
    end if;
    
    /* printf "\n"; */
    return f;
end function;

function TotalStrongReduce(f,sf,G,sigs 
                           : Signature := false)
    res := 0;
    ff := f;
    /* sff := sf; */
    while ff ne 0 do
        ff := StrongReduce(ff,sf,G,sigs : Signature := Signature);
        res +:= LeadingTerm(ff);
        ff -:= LeadingTerm(ff);
    end while;

    return res;
end function;

/* function StrongReduce(f,G) */
/*     return NormalForm(f,G); */
/* end function; */

function Criterion_Coprime(f,g)
    return Gcd(LeadingMonomial(f),LeadingMonomial(g)) ne 1;
    //return true;
end function;

function Criterion_GebauerMoller_admissible(T,G,sigs,i,j,k)
    if i eq k or j eq k or i eq j then
        return false;
    end if;
    if i gt j then
        tmp := i; i := j; j := tmp;
    end if;
    Si := Sig_Multiply(sigs[i],1,T[j][i] div LeadingMonomial(G[i]));
    Sj := Sig_Multiply(sigs[i],1,T[j][i] div LeadingMonomial(G[j]));
    Sk := Sig_Multiply(sigs[i],1,T[j][i] div LeadingMonomial(G[k]));
    return Sig_Geq(Si,Sk) or Sig_Geq(Sj,Sk);
end function;

function IsEqualUpToUnit(a,b)
    return IsDivisibleBy(a,b) and IsUnit(a div b);
end function;

function Criterion_GebauerMoller_all(T,G,sigs,i,j,k)
    if #{i,j,k} lt 3 then
        return true;
    else
        if i gt j then
            tmp := i; i := j; j := tmp;
        end if;
    end if;

    // Comparing the LTs
    return not (IsDivisibleBy(T[j][i],LeadingTerm(G[k])) and Criterion_GebauerMoller_admissible(T,G,sigs,i,j,k));
    /* if Tijk eq T[j][i] then */
    /*     ii := i; jj := j; kk := k; */
    /* elif Tijk eq T[k][i] then */
    /*     ii := i; jj := k; kk := j; */
    /* elif Tijk eq T[k][j] then */
    /*     ii := j; jj := k; kk:= j; */
    /* else */
    /*     return true; */
    /* end if; */

    /* // Comparing the signatures */
    /* return not  */
end function;
    
function Criterion_GebauerMoller_all_back(T,G,sigs,i,j)
    test := true;
    for k in [1..j-1] do
        if not Criterion_GebauerMoller_all(T,G,sigs,i,j,k) then
            test := false;
            break;
        end if;
    end for;
    return test;
end function;
        


function Criterion_GebauerMoller_B(T,G,sigs,i,j,k)
    if i eq k or j eq k then
        return true;
    end if;
    test := true;
    /* Sij := SPol_Sig(G[i],G[j],T[j][i],sigs[i],sigs[j]); */
    /* Sjk := SPol_Sig(G[i],G[k],T[k][i],sigs[i],sigs[k]); */
    /* Sik := SPol_Sig(G[j],G[k],T[k][j],sigs[j],sigs[k]); */
    /* Tijk := Lcm(T[j][i],LeadingTerm(G[k])); */
    test := j ge k
                     /* or Sig_Lt(Sij, Sig_Multiply(Sik, 1, Tijk div T[k][i])) */
                     /* or Sig_Lt(Sij, Sig_Multiply(Sjk, 1, Tijk div T[k][j])) */
            or (not(IsDivisibleBy(T[j][i],LeadingTerm(G[k]))
                                /* and LeadingMonomial(T[k][i]) ne LeadingMonomial(T[j][i]) */
                                /* and LeadingMonomial(T[k][j]) ne LeadingMonomial(T[j][i]) */
                   and (T[k][i]) ne (T[j][i])
                   and (T[k][j]) ne (T[j][i])
                  ))
            or (not Criterion_GebauerMoller_admissible(T,G,sigs,i,j,k))
    ;
    return test;
end function;
    
function Criterion_GebauerMoller_M(T,G,sigs,i,k)
    test := true;

    /* if i gt j then */
    /*     i,j := Explode(<j,i>); */
    /* end if; */

    for j in [1..k-1] do
        if i eq j then // Can't satisfy the criterion in that case anyway
            continue;
        elif i gt j then
            Tji := T[i][j];
        else
            Tji := T[j][i];
        end if;
        /* if i lt j then */
        /*     Sij := SPol_Sig(G[i],G[j],T[j][i],sigs[i],sigs[j]); */
        /* else */
        /*     Sij := SPol_Sig(G[i],G[j],T[i][j],sigs[i],sigs[j]); */
        /* end if;            */
        /* Sjk := SPol_Sig(G[i],G[k],T[k][i],sigs[i],sigs[k]); */
        /* Sik := SPol_Sig(G[j],G[k],T[k][j],sigs[j],sigs[k]); */
        /* Tijk := Lcm(T[k][i],LeadingTerm(G[j])); */

        if /* Sig_Geq(Sij, Sig_Multiply(Sik, 1, Tijk div T[k][i])) */
            /* and Sig_Geq(Sij, Sig_Multiply(Sjk, 1, Tijk div T[k][j])) */
            IsDivisibleBy(Tji,T[k][j])
                         /* and LeadingMonomial(T[k][i]) ne LeadingMonomial(T[k][j]) */
            and (T[k][j]) ne (Tji)
            and Criterion_GebauerMoller_admissible(T,G,sigs,i,j,k)
            then
            test := false;
            break;
        end if;
    end for;
    return test;
end function;

function Criterion_GebauerMoller_F(T,G,sigs,i,k)
    test := true;
    for j in [1..i-1] do
        /* Sij := SPol_Sig(G[i],G[j],T[i][j],sigs[i],sigs[j]); */
        /* Sjk := SPol_Sig(G[i],G[k],T[k][i],sigs[i],sigs[k]); */
        /* Sik := SPol_Sig(G[j],G[k],T[k][j],sigs[j],sigs[k]); */
        /* Tijk := Lcm(T[k][i],LeadingTerm(G[i])); */

        if T[i][j] eq T[k][i]
           /* and Sig_Geq(Sij, Sig_Multiply(Sik, 1, Tijk div T[k][i])) */
                       /* and Sig_Geq(Sij, Sig_Multiply(Sjk, 1, Tijk div T[k][j]))      */
           and Criterion_GebauerMoller_admissible(T,G,sigs,i,j,k)
            then
            test := false;
            break;
        end if;
    end for;
    return test;
end function;

/* function Criterion_GH_C1 */

function Criterion_1SingularReducible(f,sf,G,sigs)
    // Assumes that f is regular-reduced modulo G

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

        /* test2, ttg := IsDivisibleBy(tf,LeadingTerm(g)); */
        /* if test2 then */
        /*     ccg := LeadingCoefficient(ttg); */
        /*     mmg := LeadingMonomial(ttg); */
        /*     if Sig_Eq(Sig_Multiply(sg,ccg,mmg),sf) then */
        /*         test := true; */
        /*         break; */
        /*     end if; */
        /* end if; */
                
        /* if IsDivisibleBy(tf,LeadingTerm(g)) then */
        /*     mmg := mf div LeadingMonomial(g); */
        /*     ccg := cf div LeadingCoefficient(g); */
        /*     s := Sig_Multiply(sg,ccg,mmg); */
        /*     if Sig_Simeq(sf,s) then */
        /*         // QUESTION: Why does it work better with simeq? */
        /*     /\* if sg`i eq sf`i and sg`mu*mmg eq sf`mu and IsDivisibleBy(sf`k,sg`k) then *\/ */
        /*         test := true; */
        /*         break; */
        /*     end if; */
        /* end if; */
    end for;
    return test;
end function;

function Criterion_F5(f,sf,G,sigs)
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
    /* printf "Criterion_F5: testing %o\n",Sig_ToString(sf); */
    /* if sf`i eq 3 and sf`k eq -1 and sf`mu eq (Parent(f).1)^2 then */
    /*     Error("Time to check"); */
    /* end if; */
    return res;
end function;

function Criterion_Singular(F,sf,G,sigs)
    test := exists{s : s in sigs | s`i eq sf`i
                                   and s`mu eq sf`mu
                                   and s`k eq sf`k
                                   /* and IsDivisibleBy(sf`k,s`k) */};
    return not test;
end function;



procedure UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,f,sf,
                           ~cnt_coprime,~cnt_GM_B,~cnt_GM_M,~cnt_GM_F,~cnt_GM_all,
                           ~cnt_GH_C1,~cnt_GH_C2,~cnt_GH_C3,
                           ~cnt_pairs,~cnt_Spairs
                           : Signature := false, GebauerMoller := false)
    
    // Updating the weak basis
    Append(~G,f);
    N := #G;
    Append(~sigs,sf);

    // Updating T
    Append(~T,[]);
    t := LeadingTerm(f);
    for i in [1..N-1] do
        Append(~T[N],Lcm(LeadingTerm(G[i]),t));
    end for;
    cnt_pairs +:= N;
    
    // Updating the list of critical pairs
    for i in [1..N-1] do
        if not Criterion_Coprime(f,G[i]) then
            cnt_coprime +:= 1;
            cnt_GH_C1 +:= 1;
        elif GebauerMoller and not Criterion_GebauerMoller_all_back(T,G,sigs,i,N) then
            cnt_GM_all +:= 1;
        /* elif GebauerMoller and not Criterion_GH_C2(T,G,sigs,i,N) then */
        /*     cnt_GH_C2 +:= 1; */
        /* elif GebauerMoller and not Criterion_GH_C3(T,G,sigs,i,N) then */
            /*     cnt_GH_C3 +:= 1; */
        /* elif GebauerMoller and not Criterion_GebauerMoller_M(T,G,sigs,i,N) then */
        /*     cnt_GM_M +:= 1; */
        /* elif GebauerMoller and not Criterion_GebauerMoller_F(T,G,sigs,i,N) then */
        /*     cnt_GM_F +:= 1; */
        else
            cnt_Spairs +:= 1;
            p,sp := SPol(f,G[i],T[N][i],sf,sigs[i]);
            if p ne 0 and (not Signature or not Sig_IsNull(sp)) then
                Append(~P,<p,sp,<i,N>>);
            end if;
        end if;
    end for;
    
    if Signature then
        Sort(~P, func<P1,P2 | Sig_Compare(P1[2],P2[2])>);
    end if;

    if GebauerMoller then
        toRemove := [];
        for k in [1..#P] do
            pp := P[k];
            ii,jj := Explode(pp[3]);
            if not Criterion_GebauerMoller_all(T,G,sigs,ii,jj,N) then
            /* if not Criterion_GebauerMoller_B(T,G,sigs,ii,jj,N) then */
                /* printf "Removed pair due to Gebauer-Moller B criterion\n"; */
                cnt_GM_all +:= 1;
                Append(~toRemove,k);
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
        if p ne 0 /* and (not Signature or not Sig_IsNull(sp)) */ then
            Append(~SG,p);
            Append(~sigsSG,sp);
        end if;
    end for;
end procedure;

function BuchbergerSig(F:
                    Signature := true,
                    F5_Criterion := true,
                    Sing_Criterion := true,
                    GebauerMoller := true)

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
    cnt_GH_C1 := 0;
    cnt_GH_C2 := 0;
    cnt_GH_C3 := 0;
    cnt_1sing_red := 0;
    cnt_sing := 0;
    cnt_syz := 0;
    cnt_pairs := 0;
    cnt_Spairs := 0;
    
    G := [];
    SG := [];
    P := [];
    sigs := [];
    sigsSG := [];
    T := []; // T[j][i] is the lcm of the LT of G[i] and G[j]
    m := #F;
    A := Parent(F[1]);
    for i in [1..m] do
        printf "############ i=%o ##############\n",i;

        /* if i gt 1 then */
        /*     SG := ReduceGroebnerBasis(SG); */
        /*     sigsSG := [Sig_Create(1,1,i-1) : g in SG]; */
        /*     G := SG; */
        /*     sigs := sigsSG; */
        /*     T := [[] : g in SG]; */
        /* end if; */
        
        f := F[i]; // We get a wrong result if we reduce first???
        sf := Sig_Create(1,1,i);
        f := TotalStrongReduce(f,sf,SG,sigsSG
                               : Signature := Signature); 
        if f eq 0 then
            continue;
        end if;
        UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,f,sf,
                         ~cnt_coprime,~cnt_GM_B,~cnt_GM_M,~cnt_GM_F,~cnt_GM_all,
                         ~cnt_GH_C1,~cnt_GH_C2,~cnt_GH_C3,
                         ~cnt_pairs,~cnt_Spairs
                         : Signature := Signature,
                           GebauerMoller := GebauerMoller);
        while #P gt 0 do
            printf "#P=%o #G=%o\n", #P, #G;
            next := 1; 
            pp := P[next]; Remove(~P,next);
            p := pp[1]; sp := pp[2];
            if Signature then
                if (F5_Criterion
                    and not Criterion_F5(p,sp,SG,sigsSG)) then
                    printf "Polynomial excluded by F5 criterion: sig=%o, LT=%o\n", Sig_ToString(sp), LeadingTerm(p);
                    cnt_F5 +:= 1;
                    continue;
                elif (Sing_Criterion
                      and not Criterion_Singular(p,sp,G,sigs)) then
                    printf "Polynomial excluded by Singular criterion\n";
                    cnt_sing +:= 1;
                    continue;
                end if;
            end if;
            
            r := StrongReduce(p,sp,SG,sigsSG
                              : Signature := Signature, LC_red := false);
            if r eq 0 then
                printf "Reduction to zero: sig=%o\n", Sig_ToString(sp);
                cnt_syz +:= 1;
            elif Signature
                 and Criterion_1SingularReducible(r,sp,G,sigs) then
                printf "Basis element excluded because 1-singular reducible\n";
                cnt_1sing_red +:= 1;
            else
                r := TotalStrongReduce(r,sp,SG,sigsSG : Signature := Signature);
                printf "New basis element: sig=%o, LT=%o (from %o)\n",
                       Sig_ToString(sp), LeadingTerm(r), pp[3];
                UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,r,sp,
                                 ~cnt_coprime,~cnt_GM_B,~cnt_GM_M,~cnt_GM_F,~cnt_GM_all,
                                 ~cnt_GH_C1,~cnt_GH_C2,~cnt_GH_C3,
                                 ~cnt_pairs,~cnt_Spairs
                                 : Signature := Signature,
                                   GebauerMoller := GebauerMoller);
            end if;
        end while;
    end for;

    printf "Total # of S-polynomials: %o\n", cnt_Spairs;
    printf "Total # of considered pairs: %o\n", cnt_pairs;
    printf "Total # of reductions to 0: %o\n", cnt_syz;
    printf "Total # of skipped pairs with coprime criterion: %o\n", cnt_coprime;
    printf "Total # of skipped pairs with Gebauer-Moller criteria: %o\n", cnt_GM_all;
    /* printf "Total # of skipped pairs with Gebauer-Moller \"B\" criterion: %o\n", cnt_GM_B; */
    /* printf "Total # of skipped pairs with Gebauer-Moller \"M\" criterion: %o\n", cnt_GM_M; */
    /* printf "Total # of skipped pairs with Gebauer-Moller \"F\" criterion: %o\n", cnt_GM_F; */
    /* printf "Total # of skipped pairs with Gerdt-Hashemi \"C1\" criterion: %o\n", cnt_GH_C1; */
    /* printf "Total # of skipped pairs with Gerdt-Hashemi \"C2\" criterion: %o\n", cnt_GH_C2; */
    /* printf "Total # of skipped pairs with Gerdt-Hashemi \"C3\" criterion: %o\n", cnt_GH_C3; */
    printf "Total # of skipped pairs with F5 criterion: %o\n", cnt_F5;
    printf "Total # of skipped pairs with sing criterion: %o\n", cnt_sing;
    printf "Total # of skipped 1-singular-reducible pols: %o\n", cnt_1sing_red;
    
    return G,SG,sigs,sigsSG,T;    
end function;


