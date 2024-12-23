freeze;

intrinsic PositiveElementsUpTo(B::RngIntElt, O::RngOrd : CoprimeTo:=[]) -> SeqEnum
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


intrinsic PositiveElementsUpTo(B::RngIntElt, K::FldNum : CoprimeTo:=[]) -> SeqEnum
{ " }//"
  return [K | x : x in PositiveElementsUpTo(B, Integers(K) : CoprimeTo:=CoprimeTo)];
end intrinsic;


// FIXME: this doc string doesnt make much sense, but is the best I could come up with
intrinsic HeckeCosetRepresentatives(ell::RngOrdIdl) -> SeqEnum[AlgMatElt]
{ returns left/right coset decomposition of the Hecke operator T_ell }
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
    res cat:= [Matrix([ [K | d, r @@ phi], [0, e] ]) : r in Q];
  end for;
  return res;
end intrinsic;

function ApplyIsogeny(zs, isog)
  H := BaseRing(isog);
  a, b, c, d := Explode(Eltseq(isog));
  assert c eq 0;
  pl := InfinitePlaces(H);
  return [(Evaluate(a, pl[i])*z + Evaluate(b, pl[i]))/Evaluate(d, pl[i]) : i->z in zs];
end function;

intrinsic IsogenousModuli(zs::SeqEnum[FldComElt], ell::RngOrdIdl) -> SeqEnum[SeqEnum[FldComElt]]
{ returns isogenies associated with the coset decomposition of the Hecke operator T_ell }
    return [ApplyIsogeny(zs, t) : t in HeckeCosetRepresentatives(ell)];
end intrinsic;

intrinsic TwoIsogenous(zs::SeqEnum[FldComElt], H::FldNum) -> SeqEnum[SeqEnum[FldComElt]]
{}
  prec := Precision(Universe(zs));
  OH := Integers(H);
  Q, phi := quo<OH | 2*OH>;
  reps := [r @@ phi : r in Q];
  pl := InfinitePlaces(H);
  return [[(z + Evaluate(r, pl[i] : Precision:=prec))/2 : i->z in zs] : r in reps] cat [[2*z : z in zs]];
end intrinsic;

intrinsic RationalReconstructPolynomial(g::RngUPolElt[FldCom]) -> .
{ Given a complex polynomial that is embedding of rational polynomial, try to reconstruct the original polynomial }

CCz<z> := Parent(g);
vCC := Reverse(Coefficients(g));
v := [];
maxe := 0;
CC := Universe(vCC);
mult_fact := 1;
weights := [0..Degree(g)];
  for i->w in weights do
      _, q := RationalReconstruction(vCC[i]);
      Append(~v, q);
      _, e := AlmostEqual(vCC[i], q);
      maxe := Max(e, maxe);
      if e^2 gt CC`epscomp then
        Undefine(~v, #v);
        v := Reverse(WPSMultiply(weights[1..i-1], v, 1/mult_fact));
        return false, v, maxe, mult_fact;
      end if;
      f, p := PowerFreePart(Rationals()!Denominator(q), w);
      s := &*PrimeDivisors(Integers()!f);
      vCC := WPSMultiply(weights, vCC, s * p);
      v := WPSMultiply(weights[1..i], v, s * p);
      mult_fact *:= s*p;
  end for;
  gQQ := Polynomial(Reverse(WPSMultiply(weights, v, 1/mult_fact)));
  return true, gQQ, maxe, mult_fact;
end intrinsic;

intrinsic ReconstructConjugatePolynomialsPair(F::FldNum, fs::SeqEnum) -> .
{ Given a pair of polynomial's corresponding the two embeddings of a quadratic number field F, reconstruct the original polynomial }
  mult_fact := 1;
  assert #fs eq 2;
  assert Degree(F) eq 2;
  CCz<z> := Universe(fs);
  x := PolynomialRing(F).1;
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
      Undefine(~v, #v);
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
