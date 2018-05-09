// Created: Fri May  4 13:28:56 2018
// Last modified: Wed May  9 11:26:07 2018
// Hash: fe0a4f6a249ceb21b241e431fe5caf5c

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
                    (not Sig_Simeq(sf,Sig_Multiply(sigs[i],md,1)))) then
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

function Criterion_GebauerMoller(T,G,i,j)
    test := true;

    if i gt j then
        i,j := Explode(<j,i>);
    end if;

    // Testing B_k for all k>j
    for k in [j+1..#G] do
        if IsDivisibleBy(T[j][i],LeadingTerm(G[k]))
           and #{T[k][i],T[j][i],T[k,j]} eq 3 then
            test := false;
        end if;
    end for;

    if test then
        // Testing M
        for k in [1..j-1] do
            if IsDivisibleBy(T[j][k],T[j][i])
               and T[j][k] div T[j][i] eq T[j][k] then
                test := false;
                break;
            end if;
        end for;

        if test then
            // Testing F
            for k in [1..i-1] do
                if T[j][k] eq T[j][i] then
                    test := false;
                    break;
                end if;
            end for;
        end if;
    end if;
    return test;
end function;


procedure UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,f,sf
                           : Signature := false)

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
        if Criterion_Coprime(f,G[i])
           and Criterion_GebauerMoller(T,G,i,N) then
            p,sp := SPol(f,G[i],T[N][i],sf,sigs[i]);
            if p ne 0 and (not Signature or not Sig_IsNull(sp)) then
                Append(~P,<p,sp>);
            end if;
        end if;
    end for;
    if Signature then
        Sort(~P, func<P1,P2 | Sig_Compare(P1[2],P2[2])>);
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
                    F5_Criterion := false,
                    Sing_Criterion := false)
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
        f := StrongReduce(f,sf,SG,sigs
                               : Signature := Signature); 
        if f eq 0 then
            continue;
        end if;
        UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,f,sf
                         : Signature := Signature);
        while #P gt 0 do
            printf "#P=%o #G=%o\n", #P, #G;
            next := 1; 
            pp := P[next]; Remove(~P,next);
            p := pp[1]; sp := pp[2];
            r := StrongReduce(p,sp,SG,sigsSG
                                   : Signature := Signature);
            if r ne 0 then
                printf "   LT=%o\n", LeadingTerm(r);
                UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,~T,r,sp
                                 : Signature := Signature);
            end if;
        end while;
    end for;
    return G,SG,sigs,sigsSG;    
end function;


