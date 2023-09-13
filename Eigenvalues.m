intrinsic WriteEigenvalues(f, filename) -> RngIntElt
{ Write eigenvalues to a file. }
    F := NumberField(Ring(Universe(Keys(f`hecke_eigenvalues))));
    keys := [k : k in Keys(f`hecke_eigenvalues)];
    labels := [[StringToInteger(elt) : elt in Split(LMFDBLabel(k), ".")] : k in keys];
    ParallelSort(~labels, ~keys);
    header := StripWhiteSpace(Join([Sprint(Eltseq(DefiningPolynomial(elt))) : elt in [F, Parent(f`hecke_eigenvalues[keys[2]])]], ":"));
    Write(filename, header : Overwrite:=true);
    for i->k in keys do
        label := Join([Sprint(elt) : elt in labels[i]], ".");
        eigenval := Sprint(Eltseq(f`hecke_eigenvalues[k]));
        Write(filename, Join([label, eigenval], ":"));
    end for;
    return #keys + 1;
end intrinsic;

intrinsic LoadEigenvalues(~f, filename : hasheader:=true)
{ Load the eigenvalues from a file. }
	F<w> := BaseRing(Parent(f));
	OF := Integers(F);
	K := HeckeEigenvalueField(Parent(f));
	coeffs := getrecs(filename);
    if hasheader then
	    assert StripWhiteSpace(Sprint(Eltseq(MinimalPolynomial(OF.2)))) eq coeffs[1][1];
	    assert StripWhiteSpace(Sprint(Eltseq(DefiningPolynomial(HeckeEigenvalueField(Parent(f)))))) eq coeffs[1][2];
        range := [1..#coeffs];
    else
        range := [1..#coeffs];
    end if;
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



procedure compute_eigenvalues(label, start, congclass, congmod, bound : known:={})
    f := 1;
    F := 1;
    normbound := 1;
    ct := 0;
    while true do
        // reset caching
        delete f;
        delete F;
        f := make_eigenform(label);
        F := NumberField(Ring(Universe(Keys(f`hecke_eigenvalues))));
        ideals := PrimesUpTo(normbound + 1000*Ceiling(Log(normbound + 1)), F);
        newct := #ideals;
        ideals := ideals[ct + 1..#ideals];
        labels := [[StringToInteger(elt) : elt in Split(LMFDBLabel(k), ".")] : k in ideals];
        ParallelSort(~labels, ~ideals);
        for i->p in ideals do
            if i + ct lt start then
                continue;
            end if;
            if (i + ct) mod congmod ne congclass then
                continue;
            end if;
            if labels[i][1] gt bound then
                break;
            end if;
            if labels[i] in known then
                continue;
            end if;
            plabel := Join([Sprint(elt) : elt in labels[i]], ".");
            eigenval := Sprint(Eltseq(HeckeEigenvalue(f, p)));
            print StripWhiteSpace(Join([plabel, eigenval], ":"));
        end for;
        ct +:= #ideals;
        assert ct eq newct;
        normbound := Norm(ideals[#ideals]);
        if normbound gt bound then
            break;
        end if;
    end while;
end procedure;