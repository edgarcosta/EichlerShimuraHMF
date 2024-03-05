intrinsic WriteEigenvalues(f, filename : Overwrite := false) -> RngIntElt
{ Write eigenvalues to a file. }
	if Overwrite then
    	System("rm " cat filename);
	end if;
    F := NumberField(Ring(Universe(Keys(f`hecke_eigenvalues))));
    keys := [k : k in Keys(f`hecke_eigenvalues)];
    labels := [[StringToInteger(elt) : elt in Split(LMFDBLabel(k), ".")] : k in keys];
    ParallelSort(~labels, ~keys);
    for i->k in keys do
        label := Join([Sprint(elt) : elt in labels[i]], ".");
        eigenval := Sprint(Eltseq(f`hecke_eigenvalues[k]));
        Write(filename, Join([label, eigenval], ":"));
    end for;
    return #keys + 1;
end intrinsic;

intrinsic LoadEigenvalues(~f, filename : hasheader := false)
{ Load the eigenvalues from a file. }
	F<w> := BaseRing(Parent(f));
	OF := Integers(F);
	K := HeckeEigenvalueField(Parent(f));
	coeffs := getrecs(filename);

    range := [1..#coeffs];

	for i in range do
		rec := coeffs[i];
        if "." in rec[1] then
            ideal := LMFDBIdeal(OF, rec[1]);
        else
            ideal := ideal<OF | [OF!g : g in eval rec[1]]>;
        end if;
        if IsZero(ideal) then continue; end if;
        try
		    f`hecke_eigenvalues[ideal] := K!eval rec[2];
        catch e
            print "Could not process", rec;
        end try;
	end for;
end intrinsic;

intrinsic ConvertEigenvalues(label, path)
{ }
    f := LMFDBHMF(label);
    LoadEigenvalues(~f, path cat label cat ".txt");
    Write(path cat label cat ".txt.fast",
        Join(
            [StripWhiteSpace(Join([Sprint([Eltseq(g) : g in Generators(k)]),Sprint(Eltseq(v))], ":"))
            :
            k->v in f`hecke_eigenvalues],"\n") cat "\n" : Overwrite:=true);
end intrinsic;
