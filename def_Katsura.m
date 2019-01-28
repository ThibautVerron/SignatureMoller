// Created: Tue Oct  9 16:17:43 2018
// Last modified: Tue Oct  9 16:18:12 2018
// Hash: 648aff09d2eea4dfd847d9e783b30224

if not assigned n or not Type(n) eq RngIntElt then
    error("n is not defined");
end if;

A := PolynomialRing(IntegerRing(),n+1,"grevlex");

function varU (i)
    if i lt 0 then
        return varU(-i);
    elif i gt n then
        return 0;
    else
        return A.(i+1);
    end if;
end function;

K := [];
for m in [-n+1..n-1] do
    Append(~K,&+([varU(l)*varU(m-l) : l in [-n..n]]) - varU(m));
end for;
Append(~K,&+([varU(l) : l in [-n..n]]) - 1);

K := Setseq(Seqset(K));
