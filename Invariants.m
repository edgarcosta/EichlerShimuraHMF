freeze;
//import "FlintWrapper.m": ThetaFlint

/*
Given a small period matrix tau (g by g), return the sequence of theta(z + m)*theta(z - m) (these are sections of the divisor 2*Theta), where
    * theta: CC^g -> CC is an L-quasiperiodic function representing a nonzero section of Theta;
    * L is the period lattice ZZ^g + tau*ZZ^g;
    * m ranges over coset representatives of ZZ^g/(2*ZZ^g)
*/
// this uses Magma's implementation of theta functions
function ThetaSections(tau : Reduce:=true)
    if Reduce then
        tau := ReduceSmallPeriodMatrix(tau);
    end if;
    g := Nrows(tau);
    CC<I> := BaseRing(Parent(tau));
    return [map< KMatrixSpace(CC,g,1)->CC |
        z :-> Theta(zero, z + m, tau)*Theta(zero, z - m, tau)>
        where m := Matrix(g,1, [c[i] : i in [1..g]])
        : c in CartesianPower({CC|0,1/2},g) ]
        where zero := Matrix(2*g,1,[CC | 0 : i in [1..2*g]]);
end function;

function ThetaFunctions(tau : theta:="Flint")
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



/*
    Given a generator E for complex geometric endomorphism representation of extended_tau (computed via GeometricEndomorphismRepresentationCC(extended_tau)[2][2]), return the set of 1-dimensional k-subspaces of A[2], where A is the abelian variety corresponding to tau, and k = GF(2^g)
*/

function OneDimensionalTwoTorsionSubspaces(E : IncludeTrivial := false)
  // This function computes the 1-dimensional k-subspaces of A[2]. Here k is the residue field of the endomorphism ring at 2 (i.e. F_{2^g}).
  // The input E gives the action of the generator of the endomorphism ring on A.
    g := Nrows(E) div 2;
    E2 := ChangeRing(E, GF(2));
  assert Order(E2) eq 2^g - 1;
    U := VectorSpace(GF(2), 2*g);
    X := Set(U);
    G := Sym(X)![x*Transpose(E2) : x in X]; // This is E acting on A[2] (as a set).
    Vs := [ sub<U | [c : c in s] cat [U!0]>  : s in CycleDecomposition(G) | #s gt 1 or not(U!0 in s) ]; // Here we enumerate all the orbits of the action, except for the orbit {0}. Each such orbit, after adjoining 0, becomes a subspace invariant under E, i,e, a k-subspace.
    //print "#Vs = ", #Vs;
    assert #Vs eq 2^g + 1; // Check the total count.
    if IncludeTrivial then
        Vs cat:= [ U ]; // sub<U | [U|0]> ];
    end if;
    return Vs;
end function;



function KiefferMatrix(W)
  // Given an isotropic subspace of the symplectic space F2^g, find a block matrix satisying c = 0, ad^t = l^n*id, ab^t is symmetric, representing the subspace.
  U := Generic(W);
  p := Characteristic(BaseField(U));
  g := Dimension(U) div 2;
  if Dimension(W) eq Dimension(U) then
    return IdentityMatrix(Integers(), 2*g);
  end if;
  TWprev := sub<U | 0>;
  R := [];
  for i in [2*g..g+1 by -1] do
    T := sub<U | [U.j : j in [i..2*g]]>;
    TW := T meet W;
    if TW eq TWprev then
      Append(~R, [i eq j select p else 0 : j in [1..2*g]]);
    else
      v := [TW.i : i in [1..Dimension(TW)] | not(TW.i) in TWprev][1];
      Append(~R, [Integers()!v[j] : j in [1..2*g]]);
    end if;  
    TWprev := TW;
  end for;
  valW := Dimension(W);
  BottomMatrix := Matrix([r[[2*g..g+1 by -1]] : r in R]);
  TopMatrix := p^(1)*Transpose(ChangeRing(BottomMatrix, Rationals())^(-1));
  M := Matrix([ [i eq j select 1 else 0 : j in [1..g] ] : i in [1..2*g] ]);
  for i in [g..1 by -1] do
    newRow := [Integers() | TopMatrix[g+1-i][j] : j in [g..1 by -1]];
    T := sub<U | [U.j : j in [i..2*g]]>;
    TW := T meet W;
    if newRow[i] eq 2 then
      newRow cat:= [0 : j in [1..g]];
    else
      v := Solution((Matrix([[v[j] : j in [1..g]] : v in Basis(W)])), ChangeRing(Vector(newRow), GF(2)));
      w := &+[ v[i]*b : i->b in Basis(W)];
      newRow cat:= [Integers()!w[g+j] : j in [1..g]];
    end if;
    Append(~R, newRow);
    TWprev := TW;
  end for;
  return Matrix(Reverse(R));
end function;


function act_gamma(tau, gamma)
    g := Nrows(gamma) div 2;
    a := Submatrix(gamma, 1, 1, g, g);
    b := Submatrix(gamma, 1, g + 1, g, g);
    c := Submatrix(gamma, g + 1, 1, g, g);
    d := Submatrix(gamma, g + 1, g + 1, g, g);
    //print "Det =", [Determinant(elt) : elt in [a,b,c,d]];
    return (a*tau + b)*((c*tau + d)^-1);
end function;

function TwoIsogenousAVs(tau, Vs)
    g := Nrows(tau);
    assert #Vs eq 2^g + 1;
    return [act_gamma(tau, gamma) where gamma := KiefferMatrix(v) : v in Vs];
end function;

/*
function TwoIsogenousAVs(tau, Vs)
  O := [];
    g := Nrows(tau);
    CC<I> := BaseRing(Parent(tau));
    U := Generic(Vs[1]);
    assert #Vs eq 2^g + 1;
  extended_tau := HorizontalJoin(tau, IdentityMatrix(CC, g));
  for v in Vs do
    M := KiefferMatrix(v);
    isogenous_tau := SmallPeriodMatrix(extended_tau*ChangeRing(M,CC));
    Append(~O, isogenous_tau);
  end for;
    return O;
end function;
*/


function CosetDeterminantProducts(tau, Vs)
    /*
    Given the small period matrix tau and the set Vs of 1-dimensional k-subspaces of A[2], where A is the abelian variety corresponding to tau, and k = GF(2^g), return a sequence containing sequences of determinants of the products of matrices whose entries are the theta functions evaluated at the coset representatives of the Vs
    */
    g := Nrows(tau);
    CC<I> := BaseRing(Parent(tau));
    U := Generic(Vs[1]);
    assert #Vs eq 2^g + 1;
    extended_tau := HorizontalJoin(tau, IdentityMatrix(CC, g));//BigPeriodMatrix(tau);
    theta := ThetaSections(tau);
    coset_reps := [[[(v @@ b) + w : w in V] : v in a] where a,b:=U/V : V in Vs];
    coset_reps_matrix := [[Matrix(Integers(), Matrix(x)) : x in y] : y in coset_reps];
    return [&*[Determinant(Matrix([[t(Eltseq(r)) : r in Rows(Transpose(extended_tau*Matrix(CC, Transpose(m))/2))] : t in theta])) : m in v] : v in coset_reps_matrix];
end function;

function EighthPowersSum(tau, v : eps := 1E-6, n := 1, m := false, flint := true)
    // Given a small period matrix tau and a one-dimensional subspace v of the 2-torsion
    g := Nrows(tau);

    CC<I> := BaseRing(Parent(tau));
    M := KiefferMatrix(v);
  isogenous_tau := act_gamma(tau, M);
  assert IsSmallPeriodMatrix(isogenous_tau);
  theta := ThetaFunctions(isogenous_tau : theta:=flint cmpeq true select "Flint" else "");
  if m cmpeq false then
      m := 4*Round(Log(2, Determinant(Submatrix(M, 1, 1, g, g)))) - g;
  end if;
  return 2^m *  &+[ t(0)^(8*n) : t in theta ];
end function;

intrinsic E4Ratios(tau::AlgMatElt : extra_endos := true, m := false, flint := true) -> Any
    {}
  CC<I> := BaseRing(Parent(tau));
  if extra_endos cmpeq true then
    g := Nrows(tau);
    extended_tau := HorizontalJoin(tau, IdentityMatrix(CC, g));
    E := GeometricEndomorphismRepresentationCC(extended_tau);
    assert #E eq 2;
    assert IsIdentity(E[1][2]);
  else
    E := [ extra_endos, extra_endos ];
  end if;
  Vs := OneDimensionalTwoTorsionSubspaces(E[2][2] : IncludeTrivial);
  E4s := [EighthPowersSum(tau, v : m := m, flint := flint) : v in Vs];
  E4rs := [x/y : x in E4s[1..#E4s-1]] where y := E4s[#E4s]; // last one is E_4(tau)
    //print E4s;
  return E4rs, E4s;
end intrinsic;


/*
  Given a point in projective space, determine a polynomial whose zeros are exactly the coordinates of this point, normalised in such a way that the highest degree coefficients are all zero.
*/
function NormalisedPolynomialWithZeros(L)
  CCz<z> := PolynomialRing(Universe(L));
  PV0 := &*[z - elt : elt in L];
  //c := Coefficient(PV0, Degree(PV0)-1);
  return PV0, 1;
  //return Reverse(Evaluate(Reverse(PV0), z/c)), c; We used to rescale the polynomial, but it turned out that this was not necessary and actually made it harder.
end function;

function NormalizedPolynomialWithZeros(L)
    return NormalisedPolynomialWithZeros(L);
end function;

function NormalisedPolynomialWithZeroes(L)
    return NormalisedPolynomialWithZeros(L);
end function;

function NormalizedPolynomialWithZeroes(L)
    return NormalisedPolynomialWithZeros(L);
end function;

// wrapper
intrinsic InvariantsPolynomial(tau::AlgMatElt : flint := true, extra_endos := true) -> Any
    {Given a small period matrix tau, compute the invariants polynomial.}
    CC<I> := BaseRing(Parent(tau));
  //print Sprintf("%m", E);
    E4s := E4Ratios(tau : flint := flint, extra_endos := extra_endos);
  return NormalisedPolynomialWithZeros(E4s);
end intrinsic;

intrinsic InvariantsPolynomial_old(tau::AlgMatElt) -> Any
    {Given a small period matrix tau, compute the invariants polynomial.}
    CC<I> := BaseRing(Parent(tau));
  g := Nrows(tau);
  extended_tau := HorizontalJoin(tau, IdentityMatrix(CC, g));
  E := GeometricEndomorphismRepresentationCC(extended_tau);
  if g eq 1 then
    Append(~E, E[1]);
  else
    assert #E eq 2;
  end if;
  assert IsIdentity(E[1][2]);
  //print Sprintf("%m", E);
  Vs := OneDimensionalTwoTorsionSubspaces(E[2][2]);
  deltaVs := CosetDeterminantProducts(tau, Vs);
  return NormalisedPolynomialWithZeros(deltaVs);
end intrinsic;

intrinsic RecogniseConjugatePolynomials(F::FldNum, Es::Any) -> Any
  {}
  assert #Es eq 2;
  assert Degree(F) eq 2;
  CCz<z> := PolynomialRing(Universe(Es[1]));
  _<x> := PolynomialRing(F);
  fs := [&*[z - elt : elt in L] : L in Es];
  vsCC := [Reverse(Coefficients(f)) : f in fs];
  weights := [0..Degree(fs[1])];
  vs := [];
  maxe := 0;
  CC := Universe(vsCC[1]);
  for i->w in weights do
    aCC := vsCC[1,i];
    bCC := vsCC[2,i];
    _, t := RationalReconstruction(aCC + bCC);
    _, n := RationalReconstruction(aCC * bCC);
    minpoly := x^2 - t*x + n;
    roots := Roots(minpoly, F);
    _, j := Min([Abs(EmbedExtra(r[1]) - aCC) : r in roots]);
    a := roots[j,1];
    _, e := AlmostEqual(aCC, a);
    maxe := Max(e, maxe);
    if e^2 gt CC`epscomp then
      return false, vs, maxe;
    end if;
    Append(~vs, a);
    f, p := PowerFreePart(Rationals()!Denominator(a), w);
    s := &*PrimeDivisors(Integers()!f);
    vsCC[1] := WPSMultiply(weights, vsCC[1], s * p);
    vsCC[2] := WPSMultiply(weights, vsCC[2], s * p);
    vs := WPSMultiply(weights[1..i], vs, s * p);
  end for;
  return true, vs, maxe;
end intrinsic;

intrinsic RecognisePolynomial(f::RngUPolElt) -> RngUPolElt
    {}
  R<x> := PolynomialRing(Rationals());
  return R![ cQQ where _, cQQ := RationalReconstruction(c) : c in Coefficients(f)];
end intrinsic;

intrinsic RecognizePolynomial(f::RngUPolElt) -> RngUPolElt
  {}
  return RecognisePolynomial(f);
end intrinsic;

intrinsic FindGaloisGroup(vs::Any) -> Any
  {}
  pol := Polredbest(ChangeRing(Polynomial(vs) * Polynomial([Trace(elt) - elt : elt in vs]), Rationals()));
  G2 := GaloisGroup(Factorization(pol));
  return G2;
end intrinsic;
