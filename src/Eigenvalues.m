freeze;

intrinsic WriteEigenvalues(f, filename : Overwrite:=false) -> RngIntElt
{ Write eigenvalues to a file. }
  F := NumberField(Ring(Universe(Keys(f`hecke_eigenvalues))));
  keys := [k : k in Keys(f`hecke_eigenvalues)];
  FastFormat := #filename ge 5 and filename[#filename-4..#filename] eq ".fast";
  labels := [[StringToInteger(elt) : elt in Split(LMFDBLabel(k), ".")] : k in keys];
  ParallelSort(~labels, ~keys);
  output := [];

  for i->k in keys do
    if FastFormat then
      ideal := Sprint([Eltseq(g) : g in Generators(k)]);
    else
      // recompute label from sorting
      ideal := Join([Sprint(elt) : elt in labels[i]], ".");
    end if;
    eigenval := Sprint(Eltseq(f`hecke_eigenvalues[k]));
    Append(~output, StripWhiteSpace(Join([ideal, eigenval], ":")));
  end for;
  Write(filename, Join(output, "\n") : Overwrite:=Overwrite);
  return #output;
end intrinsic;

intrinsic LoadEigenvalues(~f, filename)
{ Load the eigenvalues from a file. }

  F<w> := BaseRing(Parent(f));
  OF := Integers(F);
  K := HeckeEigenvalueField(Parent(f));
  coeffs := getrecs(filename);

  to_ideal := "." in coeffs[1,1]  select func<elt | LMFDBIdeal(OF, elt)> else func<elt | ideal<OF | [OF!g : g in atoiii(elt)]>>;

  to_ev := func<elt | K!StringToRationalArray(elt)>;
  evs := [<to_ideal(rec[1]), to_ev(rec[2])> : rec in coeffs];
  for elt in evs do
    //if IsZero(elt[1]) then continue; end if;
    f`hecke_eigenvalues[elt[1]] := elt[2];
  end for;
end intrinsic;

intrinsic LMFDBHMFwithEigenvalues(label, path : Convert:=true) -> ModFrmHilElt
  {Create an eigenform from a label and loads its precomputed eigenvalues}
  f := LMFDBHMF(label);
  filename := path cat label cat ".txt";
  filenamefast := filename cat ".fast";

  // let's figure out if there is anything to do
  bslow, slow := OpenTest(filename, "r");
  require bslow: Sprintf("Cannot open %o", filename);

  // file doesn't exist or the number of lines do not match
  bfast, fast := OpenTest(filenamefast, "r");
  if bfast and #Split(Read(slow), "\n") eq #Split(Read(fast), "\n") then
    LoadEigenvalues(~f, filenamefast);
    Convert := false;
  else
    LoadEigenvalues(~f, filename);
  end if;
  delete slow;
  if bfast then delete fast; end if;
  if Convert then
    _ := WriteEigenvalues(f, filenamefast : Overwrite:=true);
  end if;
  return f;
end intrinsic;


