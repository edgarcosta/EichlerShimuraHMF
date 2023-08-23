// Given a totally real field F of degree g and a g-tuple of points in the upper half-plane, return the corresponding big period matrix
intrinsic ModuliToBigPeriodMatrix(F, points : fix_signs := false) -> AlgMatElt
{ Given a list of taus and a totally real field, compute a big period matrix. }
    prec := Min([Precision(Parent(elt)) : elt in points]);
    CC := ComplexFieldExtra(prec);
    // should they be purely imaginary?
    //assert &and[Abs(Re(p)) lt CC`epscomp : p in points];
    if fix_signs then
        points := [ Im(p) lt 0 select 1/p else p : p in points]; // is this allowed?
    end if;
    OF := Integers(F);
    g := Degree(F);
    betas := [[CC | Evaluate(OF.i, pl : Precision := prec+10) : pl in InfinitePlaces(F)] : i in [1..g]];
    Pi1 := Transpose(Matrix(CC, betas));
    Pi2 := Transpose(Matrix(CC, [[bij*points[j] : j->bij in bi] : bi in betas]));
    bigres := HorizontalJoin(Pi2, Pi1);
    return bigres;
end intrinsic;

// Given a totally real field F and a g-tuple of points in the upper half-plane, return the corresponding small period matrix
intrinsic ModuliToSmallPeriodMatrix(F, points : fix_signs := false) -> AlgMatElt
{ Given a list of taus and a totally real field, compute a small period matrix. }
    return SmallPeriodMatrix(ModuliToBigPeriodMatrix(F, points : fix_signs := fix_signs));
end intrinsic;

// Given a totally real field F of degree g and a g-tuple of points in the upper half-plane, return the corresponding big period matrix
intrinsic ModuliToBigPeriodMatrixNoam(F, points : fix_signs := false) -> AlgMatElt
{ Modified version of the ModiliToBigPeriodMatrix. }
    prec := Min([Precision(Parent(elt)) : elt in points]);
    CC := ComplexFieldExtra(prec);
    // should they be purely imaginary?
    //assert &and[Abs(Re(p)) lt CC`epscomp : p in points];
    if fix_signs then
        points := [ Im(p) lt 0 select 1/p else p : p in points]; // is this allowed?
    end if;
    OF := Integers(F);
    g := Degree(F);
    betas := [[CC | Evaluate(OF.i, pl : Precision := prec+10) : pl in InfinitePlaces(F)] : i in [1..g]];
    Pi1 := Transpose(Matrix(CC, betas));
    Pi2 := DiagonalMatrix(points)*(Transpose(Pi1)^-1);
    //bigres := HorizontalJoin(Pi2, Pi1);
    //return Pi1, Pi2;
    return HorizontalJoin(Pi1, Pi2);
end intrinsic;
