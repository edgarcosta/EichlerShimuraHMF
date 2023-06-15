

intrinsic ArtinSymbol(K::FldNum, I::RngOrdIdl) -> RngIntElt
{ Given an ideal I of ZF and a quadratic extension K/F, return Artin symbol (K/F | I) }
    ZK := Integers(K);
    if IsPrime(I) then
        if IsRamified(I,ZK) then
            return 0;
        end if;
        if IsSplit(I,ZK) then
            return 1;
        else
            return -1;
        end if;
    else
        return #fac eq 0 select 1 else &*[$$(K, q)^e where q, e := Explode(elt) : elt in fac] where fac:=Factorisation(I);
    end if;
end intrinsic;

// Artin Symbol on infinite places
intrinsic ArtinSymbolInfinite(K::FldNum, v::PlcNumElt) -> RngIntElt
{ Given an infinite place v of ZF and a quadratic extentsion of K/F, return Artin Symbol (K/F | v)}
    F := NumberField(Parent(v));
    mp := Coercion(F,K);
    n := #[w[1] : w in Decomposition(mp, v) | IsComplex(w[1])];
    return (-1)^n;
end intrinsic;