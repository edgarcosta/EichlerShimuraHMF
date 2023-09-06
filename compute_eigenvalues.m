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
        labels := [<StringToInteger(elt) : elt in Split(LMFDBLabel(k), ".")> : k in ideals];
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
if assigned bound then
    bound := StringToInteger(bound);
else
    bound := 10^6;
end if;
b, F := OpenTest(label cat ".txt", "r");
if b then
    known := {<StringToInteger(x) : x in Split(Split(elt, ":")[1], ".")> : elt in Split(Read(F)) | Regexp("^[0-9]+.[0-9]:\\[.*\\]$", elt)};
else
    known := {};
end if;
if assigned p then
    f := make_eigenform(label);
    F := NumberField(Ring(Universe(Keys(f`hecke_eigenvalues))));
    D := Discriminant(Integers(F));
    primes := PrimesUpTo(bound);
    inert := [<p^2, Sprintf("%o.1", p^2)> : p in primes | p gt 2 and LegendreSymbol(D, p) eq -1 and p^2 lt bound];
    split := &cat[[<p, Sprintf("%o.1", p)>, <p, Sprintf("%o.2", p)>] : p in primes | p gt 2 and LegendreSymbol(D, p) eq 1];
    labelsprimesF := Sort(inert cat split);
    plabel := labelsprimesF[StringToInteger(p)][2];
    if <StringToInteger(x) : x in Split(plabel, ".")> in known then
        exit;
    end if;
    prime := LMFDBIdeal(F, plabel);
    eigenval := Sprint(Eltseq(HeckeEigenvalue(f, prime)));
    print StripWhiteSpace(Join([plabel, eigenval], ":"));
else
    assert assigned start;
    assert assigned congclass;
    assert assigned congmod;
    start, congclass, congmod := Explode([StringToInteger(elt) : elt in [start, congclass, congmod]]);
    compute_eigenvalues(label, start, congclass, congmod, bound : known := known);
end if;
exit;