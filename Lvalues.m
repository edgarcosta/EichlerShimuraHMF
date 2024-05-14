if not(assigned(StoredLValues)) then
	StoredLValues := NewStore();
end if;

intrinsic ComputeLValues(label::MonStgElt, B::RngIntElt, F::FldNum : cores := 4, dim := 4)->.
{
	Compute (and store) L values for the form with label over number field F, with characters up to bound B. Optionally the number of cores and the dimension of the form can be given as an argument.
	}
	isStored, storedValues := StoreIsDefined(StoredLValues, Sprintf("%m", <label, B, F>));
	if isStored then
		chis, chi_signs, res2 := Explode(storedValues);
		return chis, chi_signs, res2;
	end if;
	chis := QuadraticCharactersUpTo(B, F);
	chi_signs := [HodgeSigns(chi) : chi in chis];
	tasks := [<i,j> : i in [1..#chis], j in [1..dim]];
	socket := Socket(: LocalHost := "localhost", LocalPort := 10000 + (Hash(label) mod 55000));
	for i in [1..cores] do
		System("screen -d -m -S Child" cat Sprint(i) cat " timeout -k 10 4h magma label:=" cat label cat " B:=" cat Sprint(B) cat " ~/EichlerShimuraHMF/Lfunctionworker.m");
		// Alternatively, run "for i in {1..N}; do screen -d -m -S Child$i timeout -k 10 4h magma Lfunctionworker.m; done" in a terminal to start N workers.
		// To kill all of them: do for session in $(screen -ls | grep -o '[0-9]*\.Child[0-9]*'); do screen -S "${session}" -X quit; done
	end for;
	Lvals := DistributedManager(socket, tasks : initial_results := [* *]);

	// Read out results: with the embeddings
	res2 := [* *];
	desired_signs := [ [1,1], [1,-1], [-1,1], [-1,-1] ];
	for s in desired_signs do
		possible_chis := Indices(chi_signs, s);
		sign_res := [* *];
		for j in possible_chis do
			chi_res := [* *];
			for emb in [1..dim] do
				entry := [x : x in Lvals | x[1] eq j and x[2] eq emb][1];
				if #entry[5] ne 0 then
					print <j,s>, entry[5];
					continue;
				end if;
				special := entry[3];
				err := entry[4];
				prec := Precision(special);
				if Abs(special) gt 10^-(prec*0.75) then
					CC := ComplexFieldExtra(prec);
					special := CC!special;
					omega := -4*Pi(CC)^2*Sqrt(CC!2)*GaussSumOdaSimpleModuloSign(chis[j], chi_signs[j], CC)*special;
					Append(~chi_res, <omega, j, Abs(err)>);
				else
					print "Character with sign", s, "is skipped";
					print "Precision:", Precision(special), Abs(err);
				end if;
			end for;
			if #chi_res eq dim then
				Append(~sign_res, chi_res);
			end if;
		end for;
		Append(~res2, sign_res);
	end for;
	StoreSet(StoredLValues, Sprintf("%m", <label, B, F>), <chis, chi_signs, res2>);

	return chis, chi_signs, res2;
end intrinsic;
