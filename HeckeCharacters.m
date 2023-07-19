

intrinsic QuadraticCharactersUpTo(B, F) -> List
{ All the Hecke characters of order at most with norm of the conductor bounded by B}
    return [* elt : elt in Elements(HeckeCharacterGroup(N, [1..Degree(F)])), N in IdealsUpTo(B, F) | Order(elt) le 2 and Conductor(elt) eq N *];
end intrinsic;

intrinsic HodgeSigns(psi::GrpHeckeElt) -> SeqEnum[SeqEnum[RngIntElt]]
{ the Hodge signs à la Oda }
    return [ IsIdentity(Component(psi, p)) select 1 else -1 : p in InfinitePlaces(Order(Modulus(Parent(psi)))) ];
end intrinsic;


intrinsic GaussSumOdaSimpleModuloSign(chi, signs, CC) -> FldComElt
{ (-1)^? GaussSum(chi) }
    N := Sqrt(CC!Abs(Norm(Modulus(chi))));
    if signs[1] ne signs[2] then
        N *:= CC.1;
    end if;
    return N;
end intrinsic;