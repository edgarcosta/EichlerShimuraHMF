if not(assigned(StoredOmegaValues)) then
  StoredOmegaValues := NewStore();
end if;

intrinsic ComputeOmegaValues(label::MonStgElt, B::RngIntElt : cores:=4)->.
{
  Compute (and store) Omega values for the form with label over number field F, with characters up to bound B. Optionally the number of cores.
  Returns the list of characters, their signs, and a list of four lists aligned with the signs [ [1,1], [1,-1], [-1,1], [-1,-1] ]
  // each list has elements has a triple
  // 1. index of the character chi in the SeqEnum chis
  // 2. A sequence of Omega_f,chi for each embedding of f
  // 3. A sequence of CFENew(L(f, chi)) for each embedding of f
  }
  isStored, storedValues := StoreIsDefined(StoredOmegaValues, label);
  if isStored then
    Bstored, chis, chi_signs, res2, skipped := Explode(storedValues);
    if Bstored ge B then
      return chis, chi_signs, res2, skipped;
    end if;
  end if;
  f := LMFDBHMF(label);
  dim := Dimension(Parent(f));
  F := BaseField(Parent(f));
  chis := QuadraticCharactersUpTo(B, F);
  chi_signs := [HodgeSigns(chi) : chi in chis];
  tasks := [<i,j> : i in [1..#chis], j in [1..dim]];
  socket := Socket(: LocalHost := "localhost", LocalPort := 10000 + (Hash(label) mod 55000));
  for i in [1..cores] do
    System("screen -d -m -S Child" cat Sprint(i) cat " timeout -k 10 4h magma label:=" cat label cat " B:=" cat Sprint(B) cat " ~/EichlerShimuraHMF/Lfunctionworker.m");
    // Alternatively, run "for i in {1..N}; do screen -d -m -S Child$i timeout -k 10 4h magma Lfunctionworker.m; done" in a terminal to start N workers.
    // To kill all of them: do for session in $(screen -ls | grep -o '[0-9]*\.Child[0-9]*'); do screen -S "${session}" -X quit; done
  end for;

  // Lvals is a list of tuples for each L(emb(f), chi)
  // 1. index of the character chi in the SeqEnum chis
  // 2. index of the embedding of the Hecke field
  // 3. The special value to maximum precision
  // 4. CFENew(L(f, chi)), i.e., how far the root number is from Norm 1
  // 5. The error message of any error
  Lvals := DistributedManager(socket, tasks : initial_results := [* *]);

  // Read out results: with the embeddings
  res2 := [* *];
  skipped := [* *];
  desired_signs := [ [1,1], [1,-1], [-1,1], [-1,-1] ];
  for s in desired_signs do
    possible_chis := Indices(chi_signs, s);
    sign_res := [* *];
    for j in possible_chis do
      chi_res := [* *];
      for emb in [1..dim] do
        // pick the right
        entry := [x : x in Lvals | x[1] eq j and x[2] eq emb][1];
        _, _, special, err, error_message := Explode(entry);
        if #error_message ne 0 then
          // Something went wrong for this combination, and we report it via print
          print <j, s>, entry[5];
          continue;
        end if;
        prec := Precision(special);
        if Abs(special) gt 10^-(prec*0.75) then
          CC := ComplexFieldExtra(prec);
          special := CC!special;
          omega := -4*Pi(CC)^2*Sqrt(CC!2)*GaussSumOdaSimpleModuloSign(chis[j], chi_signs[j], CC)*special;
          Append(~chi_res, <omega,  Abs(err)>);
        else
          // the special value is too close to zero
          Append(~skipped, entry);
          // print "Character with sign", s, "is skipped";
          // print "Precision:", Precision(special), Abs(err);
        end if;
      end for;
      if #chi_res eq dim then
        // we are done looping over embeddings, and we got all the embeddings
        // chi_res is a list of <omega, Abs(err)> for each embedding
        Append(~sign_res, <j, <elt[1] : elt in chi_res>, <elt[2] : elt in chi_res> > );
      end if;
    end for;
    Append(~res2, sign_res);
  end for;


  StoreSet(StoredOmegaValues, label, <B, chis, chi_signs, res2, skipped>);
  return chis, chi_signs, res2, skipped;
end intrinsic;
