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

intrinsic make_eigenform(label) -> ModFrmHilElt
{ Create an eigenform from a label. }
    d := StringToInteger(Split(label, ".")[3]);
    norm := StringToInteger(Split(Split(label, "-")[2],".")[1]);
    endlabel := Split(label, "-")[3];
    R<x> := PolynomialRing(Integers());
    if d eq 12 then
        F<w> := NumberField(x^2 -3);
        OF := Integers(F);
        NN := [elt : elt in [(17*w - 17)*OF, (19*w - 19)*OF, (-23*w)*OF] | Norm(elt) eq norm][1];
        labels := [elt[2] : elt in [
        <578, ["c", "d"]>,
        <722, ["i", "j", "l", "k"]>,
        <1587, ["i", "j", "k", "l", "m", "n"]>] | elt[1] eq norm][1];
		dim := 4;
    elif d eq 8 then
        F<w> := NumberField(x^2 -2);
        OF := Integers(F);
        NN := [elt : elt in [(51)*OF, (37*w)*OF] | Norm(elt) eq norm][1];
        labels := [elt[2] : elt in [<2601, ["j", "k"]>, <2738, ["f", "e"]>] | elt[1] eq norm][1];
		dim := 4;
    elif d eq 24 then
        F<w> := NumberField(x^2 -6);
        OF := Integers(F);
        NN := (-11*w)*OF;
        labels := ["j", "i","l", "k"];
		dim := 4;
    elif d eq 5 then
        assert label eq "2.2.5.1-61.2-a";
        F<w> := NumberField(x^2 - x - 1);
        OF := Integers(F);
        NN := [elt : elt in [(-3*w-7)*OF] | Norm(elt) eq norm][1];
        labels := ["a"];
		dim := 2;
    end if;
    M := NewformDecomposition(NewSubspace(HilbertCuspForms(F, NN)));
    possible := [* Eigenform(elt) : elt in M | Dimension(elt) eq dim *];
    assert #possible eq #labels;
    return [* Eigenform(elt) : elt in M | Dimension(elt) eq dim *][Index(labels, endlabel)];
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