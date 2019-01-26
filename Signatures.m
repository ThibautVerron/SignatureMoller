// Created: Tue May  8 16:03:43 2018
// Last modified: Tue Jan 22 11:50:12 2019
// Hash: ae55b8fc35c8328ff1727094efc35863

Sig := recformat<k,mu,i>;

function Sig_Create(coef,mon,i)
    /* Create a signature coef * mon * e_i */
    aa := rec<Sig|>;
    aa`k := coef;
    aa`mu := mon;
    aa`i := i;
    return aa;
end function;

Sig_Null := Sig_Create(1,1,0);

function Sig_IsNull(s)
    return s`i eq 0 or s`k eq 0;
end function;

function Sig_Simeq(s1,s2)
    /* True iff s1 \simeq s2 (equality of the module monomial parts)
     */
    return (Sig_IsNull(s1) and Sig_IsNull(s2)) or (s1`mu eq s2`mu and s1`i eq s2`i);
end function;

function Sig_Eq(s1,s2)
    /* True iff s1 = s2 */
    return Sig_Simeq(s1,s2) and s1`k eq s2`k;
end function;

function Sig_Lt(s1,s2)
    /* True iff s1 \prec s2 */
    return Sig_IsNull(s1) or s1`i lt s2`i or (s1`i eq s2`i and s1`mu lt s2`mu);
end function;

function Sig_Leq(s1,s2)
    /* True iff s1 \prec s2 or s1 \simeq s2 */
    return Sig_Lt(s1,s2) or Sig_Simeq(s1,s2);
end function;

function Sig_Geq(s1,s2)
    return not Sig_Lt(s1,s2);
end function;


function Sig_Multiply(aa,coef,mon)
    /* Multiply the signature aa with coef*mon */
    return Sig_Create(aa`k*coef,aa`mu*mon,aa`i);
end function;

function Sig_Max(aa,bb)
    if Sig_Lt(aa,bb) then
        return bb;
    else
        return aa;
    end if;
end function;

function Sig_Add(aa,bb)
    if Sig_Simeq(aa,bb) then
        return Sig_Null;
        k := aa`k + bb`k;
        if k eq 0 then
            return Sig_Null;
        else
            return Sig_Create(k,aa`mu,aa`i);
        end if;
    else
        return Sig_Max(aa,bb);
        end if;
end function;


function Sig_Compare(s1,s2)
    /* Comparison function, suitable for Sort */
    if Sig_Lt(s1,s2) then
        return -1;
    elif Sig_Simeq(s1,s2) then
        return 0;
    else
        return 1;
    end if;
end function;

function Sig_Compare_Full(s1,s2)
    /* Comparison function, suitable for Sort */
    if Sig_Lt(s1,s2) then
        return -1;
    elif Sig_Simeq(s1,s2) then
        if Abs(s1`k) lt Abs(s2`k) then
            return -1;
        else
            return 1;
        end if;
    else
        return 1;
    end if;
end function;


function Sig_ToString(s)
    /* Convert a signature to a printable string */
    return Sprintf("%o*%o*e_%o",s`k,s`mu,s`i);
end function;
