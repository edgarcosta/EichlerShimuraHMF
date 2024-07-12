freeze;
/***
 *  Reconstructing genus 4 curves
 *
 *  Jeroen Hanselman
 *  Andreas Pieper
 *  Sam Schiavone
 *
 *  See LICENSE.txt for license details.
 */
 
// copied from reconstructing-g4/magma/theta.m
/*
intrinsic SiegelReduction(tau::AlgMatElt) -> Any
  {}

  g := Nrows(tau);
  CC<I> := BaseRing(tau);
  RR := BaseRing(Real(tau));
  QQ := Rationals();
  ZZ := Integers();

  vprint Theta: "Setting up block matrices";
  Aq := VerticalJoin(HorizontalJoin(ZeroMatrix(RR,1,1), ZeroMatrix(RR,1,g-1)), HorizontalJoin(ZeroMatrix(RR,g-1,1), IdentityMatrix(RR,g-1)));
  Bq := VerticalJoin(HorizontalJoin(-IdentityMatrix(RR,1), ZeroMatrix(RR,1,g-1)), HorizontalJoin(ZeroMatrix(RR,g-1,1), ZeroMatrix(RR,g-1,g-1)));
  Cq := -Bq;
  Dq := Aq;

  quasi_inversion := VerticalJoin(HorizontalJoin(Aq, Bq), HorizontalJoin(Cq,Dq));

  Gamma := IdentityMatrix(RR, 2*g);
  e := RR!0;

  vprint Theta: "Entering while loop";
  while e le 1 do
    Y := Imaginary(tau);
    Y := (Y + Transpose(Y))/2; // make sure matrix is symmetric
    T := Cholesky(Y);
    T, U := LLL(T);
    Tt := Transpose(T);

    short := 1;
    //i := 1;
    //while i le g do
    for i := 1 to g do
      if L2Norm(Rows(T)[short]) gt L2Norm(Rows(T)[i]) then
        short := i;
      end if;
      //i +:= 1;
    //end while;
    end for;
    vprintf Theta: "short = %o\n", short;

    if short ne 1 then
      S := SwapColumns(IdentityMatrix(RR,g),1,short);
      T := S*T;
      U := S*U;
    end if;

    Tt := Transpose(T);
    Y := T*Tt;

    //Gamma := VerticalJoin(HorizontalJoin(U,ZeroMatrix(ZZ,g)), HorizontalJoin(ZeroMatrix(ZZ,g), (Transpose(U)^-1)))*Gamma;
    R := BaseRing(Parent(U));
    Gamma := VerticalJoin(HorizontalJoin(U,ZeroMatrix(R,g)), HorizontalJoin(ZeroMatrix(R,g), (Transpose(U)^-1)))*Gamma;
    tau := U*Real(tau)*Transpose(U) + I*Y;
    X := Real(tau);

    B := Parent(X)!0;
    for i := 1 to Nrows(B) do
      for j := 1 to Ncols(B) do
        B[i,j] := Round(X[i,j]);
      end for;
    end for;
    tau -:= ChangeRing(B,CC);
    Gamma := VerticalJoin(HorizontalJoin(IdentityMatrix(RR,g), -B), HorizontalJoin(ZeroMatrix(RR,g,g), IdentityMatrix(RR,g)))*Gamma;
    e := Abs(tau[1,1]);
    vprintf Theta: "Now e = %o\n", e;
    if e gt 1 then
      return tau, MatrixRing(Integers(),2*g)!Gamma;
    else
      Gamma := quasi_inversion*Gamma;
      tau := (Aq*tau + Bq)*((Cq*tau + Dq)^-1);
    end if;
  end while;
end intrinsic;
*/

// copied from reconstructing-g4/magma/schottky.m
intrinsic SchottkyModularFormMagma(tau::AlgMatElt : prec := -1) -> Any
  {}
  
  require (Nrows(tau) eq 4) and (Ncols(tau) eq 4): "period matrix must be 4 by 4";
  
  if prec eq -1 then
    prec := Precision(BaseRing(Parent(tau)));
  end if;
  C := ComplexField(prec);
  char := Matrix(C, 8, 1, [0,0,0,0,0,0,0,0]);
  z := Matrix(C, 4, 1, [0,0,0,0]);

  m1 := 1/2*Matrix(C, 8, 1, [1,0,1,0,1,0,1,0]);
  m2 := 1/2*Matrix(C, 8, 1, [0,0,0,1,1,0,0,0]);
  m3 := 1/2*Matrix(C, 8, 1, [0,0,1,1,1,0,1,1]);
  n0 := Matrix(C, 8, 1, [0,0,0,0,0,0,0,0]);
  n1 := 1/2*Matrix(C, 8, 1, [0,0,0,1,1,1,1,0]);
  n2 := 1/2*Matrix(C, 8, 1, [0,0,1,1,0,0,0,1]);
  n3 := 1/2*Matrix(C, 8, 1, [0,0,1,0,1,0,1,1]);
  n4 := n1+n2;
  n5 := n1+n3;
  n6 := n2+n3;
  n7 := n1+n2+n3;
  SchottkyN := [n0,n1,n2,n3,n4,n5,n6,n7];
  M1 := [m1 + n: n in SchottkyN];
  M2 := [m2 + n: n in SchottkyN];
  M3 := [m3 + n: n in SchottkyN];
  pi1 := 1;
  pi2 := 1;
  pi3 := 1;

  tau_prec := MatrixAlgebra(C, Nrows(tau))!tau;
  
  for m in M1 do
    pi1 := pi1*Theta(m, z, tau_prec);
  end for;

  for m in M2 do
    pi2 := pi2*Theta(m, z, tau_prec);
  end for;

  for m in M3 do
    pi3 := pi3*Theta(m, z, tau_prec);
  end for;

  Schottky := pi1^2 + pi2^2 + pi3^2 - 2*(pi1*pi2 + pi2*pi3 + pi1*pi3);
  return Schottky;
end intrinsic;

intrinsic ThetaCharacteristicToIndex(m::SeqEnum) -> RngIntElt
  {Given a theta characteristic m as a sequence of length 2*g with entries in [0, 1/2], return
  the index of the corresponding theta constant output by ThetaFlint}
  
  CC := Universe(m);
  require &and[el in [CC | 0, 1/2] : el in m]: "entries must be 0 or 1/2";
  m := Reverse([Integers()!(2*el) : el in m]);
  return Seqint(m,2)+1;
end intrinsic;

intrinsic ThetaCharacteristicToIndex(m::ModMatFldElt) -> RngIntElt
  {Given a theta characteristic m as a 1 by 2*g matrix with entries in [0, 1/2], return
  the index of the corresponding theta constant output by ThetaFlint}
  
  return ThetaCharacteristicToIndex(Eltseq(m));
end intrinsic;

intrinsic SchottkyModularFormFlint(tau::AlgMatElt : prec := -1) -> Any
  {Compute the Schottky modular form evaluated at tau using Kieffer's implementation of theta functions in Flint}
  
  require (Nrows(tau) eq 4) and (Ncols(tau) eq 4): "period matrix must be 4 by 4";
  
  if prec eq -1 then
    prec := Precision(BaseRing(Parent(tau)));
  end if;
  C := ComplexField(prec);
  char := Matrix(C, 8, 1, [0,0,0,0,0,0,0,0]);
  z := Matrix(C, 4, 1, [0,0,0,0]);
  
  tau_prec := MatrixAlgebra(C, Nrows(tau))!tau;
  thetas := ThetaFlint(char, z, tau);
  pis := [C | 1,1,1];
  Ms := [
    [ 171, 181, 156, 130, 134, 160, 177, 175 ],
    [ 25, 7, 42, 52, 56, 46, 3, 29 ],
    [ 60, 38, 11, 17, 21, 15, 34, 64 ]
  ]; // indices corresponding to theta characteristics in the Magma version
  for i := 1 to #Ms do
      for j := 1 to #Ms[i] do
          pis[i] *:= thetas[Ms[i][j]];
      end for;
  end for;
  pi1, pi2, pi3 := Explode(pis);
  return pi1^2 + pi2^2 + pi3^2 - 2*(pi1*pi2 + pi2*pi3 + pi1*pi3);
end intrinsic;

intrinsic SchottkyModularForm(tau::AlgMatElt : prec := -1, flint := true) -> Any
  {Compute Schottky modular form of small period matrix tau. If flint, uses Flint to compute theta functions}
  
  if flint then
    return SchottkyModularFormFlint(tau : prec := prec);
  end if;
  return SchottkyModularFormMagma(tau : prec := prec);
end intrinsic;
