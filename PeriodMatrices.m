freeze;



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


/* We decided to go for the Goren standard
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
*/


intrinsic Polarization(A::RngOrdFracIdl, B::RngOrdFracIdl) -> AlgMatElt
{ given two fractional ideals, returns the matrix representing the pairing E_r on A+B defined as
  E_r((x1, y1), (x2, y2)) = Trace(r*(x1*y2 - x2*y1)) }
  // we expect A and B to be two fractional ideals
  O := Order(A);
  require O eq Order(B) : "A and B must be ideals of the same order";
  D := Different(O);
  b, r := IsNarrowlyPrincipal((D*A*B)^-1);
  require b : "A and B must be so that A*B*Different is narrowly principal";
  // Alternatively
  // E := Matrix([[Trace(r*(x1*y2-x2*y1)) where x2, y2 := Explode(b2) : b2 in B] where x1, y1 := Explode(b1): b1 in B]) where B := [<x,0> : x in Basis(A)] cat [<0,y> : y in Basis(B)];
  P := Matrix(Integers(), [[Trace(r*x*y) : x in Basis(B)] : y in Basis(A)]);
  E := BlockMatrix([[0, P], [-Transpose(P), 0]]);
  return E;
end intrinsic;

intrinsic ModuliToPeriodMatrix(z::SeqEnum[FldComElt], A::RngOrdFracIdl, B::RngOrdFracIdl) -> ModMatFldElt
{ Returns the period matrix asociated to the lattice A*z + B*(1,...,1) }
  prec := Min([Precision(Parent(elt)) : elt in z]);
  CC := ComplexFieldExtra(prec);
  O := Order(A);
  K := NumberField(O);
  require &and[ Im(elt) gt 0 : elt in z]: "We expect the entries of z have positive imaginary part";
  require Degree(K) eq #z: "The degree of numberfield K must match the number of elements in the upper half-plane";
  PA := Matrix([[CC | Evaluate(a, pl : Precision := prec + 10)*z[i] : a in Basis(A) ] : i->pl in InfinitePlaces(K)]);
  PB := Matrix([[CC | Evaluate(b, pl : Precision := prec + 10) : i->b in Basis(B)] : pl in InfinitePlaces(K)]);
  return HorizontalJoin([PA, PB]);
end intrinsic;

intrinsic ModuliToBigPeriodMatrix(z, A, B) -> ModMatFldElt
{ Returns the period matrix asociated to the lattice A*z + B*(1,...,1), in basis, such that it is equipped with the standard symplectic pairing }
  P := ModuliToPeriodMatrix(z, A, B);
  E := Polarization(A, B);
  g := Nrows(E) div 2;
  S, F := FrobeniusFormAlternating(E);
  assert S eq StandardSymplecticMatrix(g);
  bigP := P*Transpose(ChangeRing(F, BaseRing(P)));
  return bigP;
end intrinsic;

intrinsic ModuliToSmallPeriodMatrix(z, A, B) -> ModMatFldElt
{ Returns the small period matrix asociated to the lattice A*z + B*(1,...,1) }
  return SmallPeriodMatrix(ModuliToBigPeriodMatrix(z, A, B));
end intrinsic;
