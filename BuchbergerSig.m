// Created: Fri May  4 13:28:56 2018
// Last modified: Wed May  9 10:28:34 2018
// Hash: 223d09f12dda75ab87e558ebdfc94fe9

load "Signatures.m";

function SPol(f1,f2,s1,s2)
    m1 := LeadingMonomial(f1);
    m2 := LeadingMonomial(f2);
    if Gcd(m1,m2) ne 1 then 
        c1 := LeadingCoefficient(f1);
        c2 := LeadingCoefficient(f2);
        m := Lcm(m1,m2);
        c := Lcm(c1,c2);
        mm1 := m div m1;
        cc1 := c div c1;
        mm2 := m div m2;
        cc2 := c div c2;
        f := cc1*mm1*f1 - cc2*mm2*f2;
        sf1 := Sig_Multiply(s1,cc1,mm1);
        sf2 := Sig_Multiply(s2,cc2,mm2);
        if not Sig_Simeq(sf1,sf2) then
            sf := Sig_Max(sf1,sf2);
        else
            sf := Sig_Null;
        end if;
    else
        f := Parent(f1)!0;
        sf := s1;
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


procedure UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,f,sf
                           : Signature := false)

    // Updating the weak basis
    Append(~G,f);
    Append(~sigs,sf);
    
    // Updating the list of critical pairs
    N := #G;
    for i in [1..N-1] do
        p,sp := SPol(f,G[i],sf,sigs[i]);
        if p ne 0 and (not Signature or not Sig_IsNull(sp)) then
            Append(~P,<p,sp>);
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
        UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,f,sf
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
                UpdatePairsAndGB(~P,~G,~sigs,~SG,~sigsSG,r,sp
                                 : Signature := Signature);
            end if;
        end while;
    end for;
    return G,SG,sigs,sigsSG;    
end function;


