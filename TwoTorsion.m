freeze;


/*
Given a small period matrix tau (g by g), return the sequence of theta(z + m)*theta(z - m) (these are sections of the divisor 2*Theta), where
    * theta: CC^g -> CC is an L-quasiperiodic function representing a nonzero section of Theta;
    * L is the period lattice ZZ^g + tau*ZZ^g;
    * m ranges over coset representatives of ZZ^g/(2*ZZ^g)
*/
function ThetaFunctions(tau : Reduce:=true, theta:="Flint")
  if Reduce then
    tau := ReduceSmallPeriodMatrix(tau);
  end if;
  if theta eq "Flint" then
    Theta := ThetaFlint;
  end if;
  g := Nrows(tau);
  CC<I> := BaseRing(Parent(tau));
  return [map< KMatrixSpace(CC,g,1)->CC |
    z :-> Theta(m, z, tau)>
    where m := Matrix(2*g,1, [c[i] : i in [1..2*g]])
    : c in CartesianPower({CC|0,1/2},2*g) ];
end function;


function EvaluateE4(Z)
    return &+[t(0)^8 : t in ThetaFunctions(Z)];
end function;


intrinsic TwoTorsionPolynomial(z::SeqEnum[FldComElt], A::RngOrdFracIdl, B::RngOrdFracIdl) -> RngUPolElt[FldCom]
  {returns the two torsion polynomial associated to z}
  P, F := BigPeriodMatrix(z, A, B);
  Z := SmallPeriodMatrix(P);
  O := Order(B);
  // Mobius matrices representing two isogenies
  Ms := [MobiusModuliToSiegel(x, A, B : ToStandard:=F) : x in HeckeCosetRepresentatives(2*O)];
  // two isogenous big period matrices
  Ps := [P*MCC where MCC:=ChangeRing(M, BaseRing(P)) : M in Ms];
  // two isogenous small period matrices
  Zs := [SmallPeriodMatrix(P) : P in Ps];
  g := #z;
  dets := [Determinant(Z*Submatrix(M, 1, g+1, g, g) + Submatrix(M, g+1, g+1, g, g)) where M:=ChangeRing(M, BaseRing(Z)) : M in Ms];
  e4 := EvaluateE4(Z);
  e4s := [2^(4*g)*EvaluateE4(Z)*dets[i]^-4 : i->Z in Zs];
  roots := Eltseq(Vector(e4s)/e4);
  CCT<T> := PolynomialRing(Universe(roots));
  return &*[T - elt : elt in roots];
end intrinsic;


