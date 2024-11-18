AttachSpec("~/EichlerShimuraHMF/spec");
AttachSpec("~/CHIMP/CHIMP.spec");
assert(assigned(label));
assert(assigned(B));
f := LMFDBHMFwithEigenvalues(label, "~/eigenvalues/");
B := StringToInteger(B);
F := BaseField(Parent(f));
chis := QuadraticCharactersUpTo(B, F);
chi_signs := [HodgeSigns(elt) : elt in chis];
maxn := NormBoundOnComputedEigenvalues(f);
for I in Keys(f`hecke_eigenvalues) do
	if Norm(I) gt maxn then
		Remove(~f`hecke_eigenvalues, I);
	end if;
end for;

host := "localhost";
port := 10000 + (Hash(label) mod 55000);
function Leval(inp)
    j, emb := Explode(inp);
    cond := [];
    chi := chis[j];
    try
		L := LSeriesTwisted(f, chi : Embedding:=emb);
	catch e
		print e, inp;
		return <j, emb, 0.0, 0.0, Sprint(e)>;
	end try;
    MaximizePrecision(~L, maxn);
    err := CFENew(L);
    special := Evaluate(L, 1);
    return <j, emb, special, err, "">;
end function;
DistributedWorker(host, port, Leval);
quit;
