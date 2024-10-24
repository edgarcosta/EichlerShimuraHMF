freeze;

intrinsic PositeElementsUpTo(B::RngIntElt, O::RngOrd : CoprimeTo:=[]) -> SeqEnum
{Returns a sequence containing the positive elements of the maximal order O or the maximal order of K with norm at most B which are coprime to any ideals given in CoprimeTo.}
  L := IdealsUpTo(B, O);
  E := [ O | ];
  for I in L do
    b, x := IsNarrowlyPrincipal(I);
    if b then
      Append(~E, x);
    end if;
  end for;
  return E;
end intrinsic;


intrinsic PositeElementsUpTo(B::RngIntElt, K::FldNum : CoprimeTo:=[]) -> SeqEnum
{ " }//"
  return [K | x : x in PositeElementsUpTo(B, Integers(K) : CoprimeTo:=CoprimeTo)];
end intrinsic;


// FIXME: this doc string doesnt make much sense, but is the best I could come up with
intrinsic HeckeCosetRepresentatives(ell::RngOrdIdl) -> SeqEnum
{ returns left/right coset decomposition of the Hecke operator corresponding ell }
  O := Order(ell);
  K := NumberField(O);
  res := [MatrixAlgebra(K, 2) | ];
  for divisor in Divisors(ell) do
    b, d := IsNarrowlyPrincipal(divisor);
    if not b then continue; end if;
    elloverd := ell/d;
    b, e := IsNarrowlyPrincipal(elloverd);
    if not b then continue; end if;
    Q, phi := quo< O | elloverd>;
    for r in Q do
      rLift := r @@ phi;
      while not(IsTotallyPositive(rLift)) do
        rLift +:= e;
      end while;
      Append(~res, Matrix([ [K | d, rLift], [0, e] ]));
    end for;
  end for;
  return res;
end intrinsic;


intrinsic ReconstructConjugatePolynomialsPair(F::FldNum, fs::SeqEnum) -> .
{ Given a pair of polynomial's corresponding the two embeddings of a quadratic number field F, reconstruct the original polynomial }
  mult_fact := 1;
  assert #fs eq 2;
  assert Degree(F) eq 2;
  CCz<z> := Universe(fs);
  _<x> := PolynomialRing(F);
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
    if #roots eq 0 then
      print "Failed", minpoly;
    end if;
    _, j := Min([Abs(EmbedExtra(r[1]) - aCC) : r in roots]);
    a := roots[j,1];
    _, e := AlmostEqual(aCC, a);
    maxe := Max(e, maxe);
    if e^2 gt CC`epscomp then
      return false, vs, maxe, mult_fact;
    end if;
    Append(~vs, a);
    f, p := PowerFreePart(Rationals()!Denominator(a), w);
    s := &*PrimeDivisors(Integers()!f);
    vsCC[1] := WPSMultiply(weights, vsCC[1], s * p);
    vsCC[2] := WPSMultiply(weights, vsCC[2], s * p);
    vs := WPSMultiply(weights[1..i], vs, s * p);
    mult_fact *:= s*p;
  end for;
  return true, vs, maxe, mult_fact;
end intrinsic;
