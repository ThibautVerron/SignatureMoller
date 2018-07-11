// Created: Fri May  4 13:28:56 2018
// Last modified: Thu Jun  7 11:24:25 2018
// Hash: dbbe7dc9e34bf22ad51477b70910d18b

load "Signatures.m";

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
    if not Sig_Simeq(sf1,sf2) then
        sf := Sig_Max(sf1,sf2);
    else
        sf := Sig_Null;
    end if;
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
        sf := Sig_Add(sf1,sf2);
    else
        f := Parent(f1)!0;
        sf := s1;
    end if;
    return f,sf;
end function;

function StrongReduce(f,sf,G,sigs
                      : Signature := false)
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
                if ((not Signature)
                    or
                    (Sig_Lt(Sig_Multiply(sigs[i],md,1),sf))) then
                    f -:= d * g;
                    done := false;
                    if f eq 0 then
                        break;
                    end if;
                end if;
            end if;
        end for;
    end while;
    return f;
end function;

function TotalStrongReduce(f,sf,G,sigs 
                           : Signature := false)
    res := 0;
    ff := f;
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
end function;

function Criterion_GebauerMoller_B(T,G,i,j,k)
    test := true;
    test := j ge k or not(IsDivisibleBy(T[j][i],LeadingTerm(G[k]))
                          and T[k][i] ne T[j][i]
                          and T[k][j] ne T[j][i]);
    return test;
end function;
    
function Criterion_GebauerMoller_M(T,i,k)
    test := true;

    /* if i gt j then */
    /*     i,j := Explode(<j,i>); */
    /* end if; */

    for j in [1..k-1] do
        if IsDivisibleBy(T[k][i],T[k][j])
           and T[k][i] ne T[k][j] then
            test := false;
            break;
        end if;
    end for;
    return test;
end function;

function Criterion_GebauerMoller_F(T,i,k)
    test := true;
    for j in [1..i-1] do
        if T[k][j] eq T[k][i] then
            test := false;
            break;
        end if;
    end for;
    return test;
end function;

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

function Criterion_F5(f,sf,SG,sigsSG)
    if sf`i eq 1 then
        return true;
    end if;
    slim := Sig_Create(1,1,sf`i);
    LPols := [LeadingTerm(SG[i])
              : i in [1..#SG]
              | Sig_Lt(sigsSG[i],slim)];
    mon := sf`k * sf`mu;
    mon_red := StrongReduce(mon,sf,LPols,sigsSG : Signature:=false);
    res := mon_red ne 0;
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
                           ~cnt_coprime,~cnt_GM_B,~cnt_GM_M,~cnt_GM_F
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
    
    // Updating the list of critical pairs
    for i in [1..N-1] do
        if not Criterion_Coprime(f,G[i]) then
            cnt_coprime +:= 1;
        elif GebauerMoller and not Criterion_GebauerMoller_M(T,i,N) then
            cnt_GM_M +:= 1;
        elif GebauerMoller and not Criterion_GebauerMoller_F(T,i,N) then
            cnt_GM_F +:= 1;
        else
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
            if not Criterion_GebauerMoller_B(T,G,ii,jj,N) then
                /* printf "Removed pair due to Gebauer-Moller B criterion\n"; */
                cnt_GM_B +:= 1;
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
        if p ne 0 and (not Signature or not Sig_IsNull(sp)) then
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
    cnt_1sing_red := 0;
    cnt_sing := 0;
    cnt_syz := 0;
    
    G := [];
    SG := [];
    P := [];
    sigs := [];
    sigsSG := [];
    T := []; // T[j][i] is the lcm of the LT of G[i] and G[j]
    m := #F;
    A := Parent(F[1]);
    for i in [1..m] do
        printf "i=%o\n",i;
        f := F[i]; // We get a wrong result if we reduce first???
        sf := Sig_Create(1,1,i);
        f := StrongReduce(f,sf,SG,sigsSG
                               : Signature := Signature); 
        if f eq 0 then
            continue;
        end if;
        UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,f,sf,
                         ~cnt_coprime,~cnt_GM_B,~cnt_GM_M,~cnt_GM_F
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
                    printf "Polynomial excluded by F5 criterion\n";
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
                              : Signature := Signature);
            if r eq 0 then
                printf "Reduction to zero: sig=%o\n", Sig_ToString(sp);
                cnt_syz +:= 1;
            elif Signature
                 and Criterion_1SingularReducible(r,sp,SG,sigsSG) then
                printf "Basis element excluded because 1-singular reducible\n";
                cnt_1sing_red +:= 1;
            else
                printf "New basis element: LT=%o\n", LeadingTerm(r);
                UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,r,sp,
                                 ~cnt_coprime,~cnt_GM_B,~cnt_GM_M,~cnt_GM_F
                                 : Signature := Signature,
                                   GebauerMoller := GebauerMoller);
            end if;
        end while;
    end for;

    printf "Total # of reductions to 0: %o\n", cnt_syz;
    printf "Total # of skipped pairs with coprime criterion: %o\n", cnt_coprime;
    printf "Total # of skipped pairs with Gebauer-Moller \"B\" criterion: %o\n", cnt_GM_B;
    printf "Total # of skipped pairs with Gebauer-Moller \"M\" criterion: %o\n", cnt_GM_M;
    printf "Total # of skipped pairs with Gebauer-Moller \"F\" criterion: %o\n", cnt_GM_F;
    printf "Total # of skipped pairs with F5 criterion: %o\n", cnt_F5;
    printf "Total # of skipped pairs with sing criterion: %o\n", cnt_sing;
    printf "Total # of skipped 1-singular-reducible pols: %o\n", cnt_1sing_red;
    
    return G,SG,sigs,sigsSG,T;    
end function;


