freeze;


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


function PolarizationToStandard(A, B)
  // FIXME: cache?
  E := Polarization(A, B);
  g := Nrows(E) div 2;
  S, F := FrobeniusFormAlternating(E);
  assert S eq StandardSymplecticMatrix(g);
  return F;
end function;


intrinsic PeriodMatrix(z::SeqEnum[FldComElt], A::RngOrdFracIdl, B::RngOrdFracIdl) -> ModMatFldElt
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

intrinsic BigPeriodMatrix(z::SeqEnum[FldComElt], A::RngOrdFracIdl, B::RngOrdFracIdl) -> ModMatFldElt
{ Returns the period matrix asociated to the lattice A*z + B*(1,...,1), in basis, such that it is equipped with the standard symplectic pairing }
  P := PeriodMatrix(z, A, B);
  F := PolarizationToStandard(A, B);
  bigP := P*Transpose(ChangeRing(F, BaseRing(P)));
  return bigP, F;
end intrinsic;

intrinsic SmallPeriodMatrix(z::SeqEnum[FldComElt], A::RngOrdFracIdl, B::RngOrdFracIdl) -> ModMatFldElt
{ Returns the small period matrix asociated to the lattice A*z + B*(1,...,1) }
  B, F := BigPeriodMatrix(z, A, B);
  return SmallPeriodMatrix(B), F;
end intrinsic;


function Coordinates(r, O)
    return Eltseq(O!r);
end function;

function MultiplicationMatrix(r, A, B)
    O := Order(A);
    assert Order(A) eq Order(B);
    return Matrix(Rationals(), Solution(Matrix([Coordinates(b, O) : b in Basis(A)]), Matrix([Coordinates(r*b, O) : b in Basis(B)])));
end function;

intrinsic MobiusModuliToSiegel(M::AlgMatElt, A::RngOrdFracIdl, B::RngOrdFracIdl : ToStandard:=false) -> AlgMatElt
{ Given a Mobius transformation on h^g gives the corresponding matrix for in Siegel upper half-space}
  a, b, c, d := Explode(Eltseq(M));
  M :=  BlockMatrix([
    [MultiplicationMatrix(a, A, A), MultiplicationMatrix(b, B, A)],
    [MultiplicationMatrix(c, A, B), MultiplicationMatrix(d, B, B)]
  ]);
  if ToStandard cmpeq false then
    F := PolarizationToStandard(A, B);
  end if;
  return F*M*F^-1;
end intrinsic;
