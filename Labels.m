intrinsic LMFDBField(label::MonStgElt) -> FldNum
  {Given an LMFDB label for a number field, return that field}
  deg, r, D, i := Explode([StringToInteger(el) : el in Split(label, ".")]);
  require deg eq 2: "Only for quadratic fields for now";
  return NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
end intrinsic;


x := PolynomialRing(Integers()).1;
// label, level generators in F, dimension, p -> Tr(ap), hecke field
data := 
[*
  <"2.2.12.1-578.1-c", [[ -17, 17 ]], 4, [<"2.1", -1*4>], x^4 - 10*x^3 + 20*x^2 + 25*x - 25>,
  <"2.2.12.1-578.1-d", [[ -17, 17 ]], 4, [<"2.1",  1*4>], x^4 + 10*x^3 + 20*x^2 - 25*x - 25>, //involution of c
  <"2.2.12.1-722.1-i", [[ -19, 19 ]], 4, [<"2.1", -1*4>, <"25.1", -1*4>], x^4 - 9*x^3 + 26*x^2 - 24*x + 1>,
  <"2.2.12.1-722.1-j", [[ -19, 19 ]], 4, [<"2.1",  1*4>, <"25.1", -5*4>], x^4 - x^3 - 32*x^2 - 2*x + 149>,
  <"2.2.12.1-722.1-k", [[ -19, 19 ]], 4, [<"2.1",  1*4>, <"25.1", -1*4>], x^4 + 9*x^3 + 26*x^2 + 24*x + 1>, // involution of i
  <"2.2.12.1-722.1-l", [[ -19, 19 ]], 4, [<"2.1", -1*4>, <"25.1", -5*4>], x^4 + x^3 - 32*x^2 + 2*x + 149>, // involution of k
  <"2.2.12.1-1587.1-i", [[0, -23]], 4, [<"2.1", -2>, <"3.1",  1*4>, <"23.1",  1*4>], x^4 + 3*x^3 - 30*x^2 - 64*x + 179>,
  <"2.2.12.1-1587.1-l", [[0, -23]], 4, [<"2.1",  6>, <"3.1", -1*4>, <"23.1",  1*4>], x^4 - 4*x^3 - 9*x^2 + 26*x + 31>,
  <"2.2.12.1-1587.1-m", [[0, -23]], 4, [<"2.1", -6>, <"3.1",  1*4>, <"23.1", -1*4>], x^4 + 4*x^3 - 9*x^2 - 26*x + 31>, //involution of l
  <"2.2.12.1-1587.1-n", [[0, -23]], 4, [<"2.1", 2>, <"3.1", -1*4>, <"23.1", -1*4>], x^4 + 3*x^3 - 30*x^2 - 64*x + 179>, //invoution of i
  <"2.2.5.1-61.2-a", [[-7, -3]], 2, [], x^2 + 2*x - 4>,
  <"2.2.5.1-500.1-a", [[-10, 20]], 2, [<"4.1", -1*2>], x^2 - 5*x - 25>,
  <"2.2.5.1-500.1-b", [[-10, 20]], 2, [<"4.1", 1*2>], x^2 + 5*x - 25>,
  <"2.2.8.1-2601.1-j", [[51,0]], 4, [<"9.1", 1*4>], x^4 + 6*x^3 + 6*x^2 - 9*x - 9>,
  <"2.2.8.1-2601.1-k", [[51,0]], 4, [<"9.1", -1*4>], x^4 - 4*x^3 - 14*x^2 + 51*x + 11>,
  <"2.2.8.1-2738.1-e", [[0,37]], 4, [<"2.1", 1*4>], x^4 + 3*x^3 - 6*x^2 - 18*x + 1>,
  <"2.2.8.1-2738.1-f", [[0,37]], 4, [<"2.1", -1*4>], x^4 + 3*x^3 - 4*x - 1>
*];
label_to_data := AssociativeArray();
for elt in data do
    label_to_data[elt[1]] := <x : i->x in elt | i gt 1>;
end for;

intrinsic LMFDBHMF(label) -> ModFrmHilElt
{ Create an eigenform from a label. }
    require label in Keys(label_to_data) : "This label is not supported, edit the data List accordingly";
    level_gens, dim, trev, hecke_eigenvalue_field := Explode(label_to_data[label]);
    field_label, level_label, _ := Explode(Split(label, "-"));
    F<w> := LMFDBField(field_label);
    OF := Integers(F);
    NN := ideal<OF|[F!g : g in level_gens]>;
    M := NewformDecomposition(NewSubspace(HilbertCuspForms(F, NN)));
    possible_fs := [* Eigenform(elt) : elt in M | Dimension(elt) eq dim *];
    primes := [<elt[1], LMFDBIdeal(OF, elt[1])> : elt in trev];
    possible_trev := [[<elt[1], Trace(HeckeEigenvalue(f, elt[2]))> : elt in primes] : f in possible_fs];
    index := [i : i->elt in possible_trev | trev eq elt];
    assert #index eq 1;
    f := possible_fs[index[1]];
    assert DefiningPolynomial(HeckeEigenvalueField(Parent(f))) eq hecke_eigenvalue_field;
    return f;
end intrinsic;