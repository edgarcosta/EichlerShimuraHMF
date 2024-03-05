/*
Old functions that resulted in pairing in the inverse different or something instead of ZZ

// Given a totally real field H of degree g and a g-tuple of points in the upper half-plane, return the corresponding big period matrix
intrinsic ModuliToBigPeriodMatrix(H, points) -> AlgMatElt
{ Given a list of taus and a totally real field, compute a big period matrix. }
    prec := Min([Precision(Parent(elt)) : elt in points]);
    CC := ComplexFieldExtra(prec);
    // should they be purely imaginary?
    //assert &and[Abs(Re(p)) lt CC`epscomp : p in points];
    OF := Integers(H);
    g := Degree(H);
    betas := [[CC | Evaluate(OF.i, pl : Precision := prec+10) : pl in InfinitePlaces(H)] : i in [1..g]];
    Pi1 := Transpose(Matrix(CC, betas));
    Pi2 := Transpose(Matrix(CC, [[bij*points[j] : j->bij in bi] : bi in betas]));
    bigres := HorizontalJoin(Pi2, Pi1);
    return bigres;
end intrinsic;

// Given a totally real field F and a g-tuple of points in the upper half-plane, return the corresponding small period matrix
intrinsic ModuliToSmallPeriodMatrix(F, points) -> AlgMatElt
{ Given a list of taus and a totally real field, compute a small period matrix. }
    return SmallPeriodMatrix(ModuliToBigPeriodMatrix(F, points));
end intrinsic;
*/

// Given a totally real field H of degree g and a g-tuple of points in the upper half-plane, return the corresponding big period matrix
intrinsic ModuliToBigPeriodMatrixNoam(H, points : fix_signs := false) -> AlgMatElt
{ Modified version of the ModiliToBigPeriodMatrix. }
    prec := Min([Precision(Parent(elt)) : elt in points]);
    CC := ComplexFieldExtra(prec);
    // should they be purely imaginary?
    //assert &and[Abs(Re(p)) lt CC`epscomp : p in points];
    OH := Integers(H);
	B := Basis(OH);
    g := Degree(H);
    betas := [[CC | Evaluate(B[i], pl : Precision := prec+10) : pl in InfinitePlaces(H)] : i in [1..g]];
    Pi1 := Transpose(Matrix(CC, betas));
    Pi2 := DiagonalMatrix(points)*(Transpose(Pi1)^-1);
    //bigres := HorizontalJoin(Pi2, Pi1);
    //return Pi1, Pi2;
    return HorizontalJoin(Pi2, Pi1);
end intrinsic;

intrinsic ModuliToSmallPeriodMatrixNoam(F, points) -> AlgMatElt
{ Given a list of taus and a totally real field, compute a small period matrix. }
    return SmallPeriodMatrix(ModuliToBigPeriodMatrixNoam(F, points));
end intrinsic;


// TODO: PeriodMatrixToModuli