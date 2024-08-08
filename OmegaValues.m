freeze;

if not(assigned(SpecialValuesStore)) then
  SpecialValuesStore := NewStore();
end if;

function GetLvaluePIPE(label, B, char_index, embedding, eigenvalues_dir : maxn:=false)
  pathfn := [Join(s[1..#s-1], "/") where s := Split(fn,"/") where fn := GetFilenames(f)[1,1] :  f in [LMFDBHMFwithEigenvalues, CHIMP]];
  specfn := [Sprintf("/%o/spec", pathfn[1]), Sprintf("/%o/CHIMP.spec", pathfn[2])];
  // load spec files
  cmd := [Sprintf("AttachSpec(\"%o\");", fn) : fn in specfn];
  cmd cat:= [
    "start := Time();",
    Sprintf("label := \"%o\";", label),
    Sprintf("eigenvalues_dir := \"%o\";", eigenvalues_dir),
    Sprintf("B := %o;", B),
    Sprintf("char_index := %o;", char_index),
    Sprintf("embedding := %o;", embedding),
    Sprintf("maxn := %o;", maxn),
    "
    try
      special, err := LMFDBTwistedLvalue(label, eigenvalues_dir, B, char_index, embedding : maxn:=maxn);
      msg := \"\";
    catch e
      special := false;
      err := false;
      msg := e;
    end try;
    Sprintf(\"%m\", < char_index, embedding, special, msg,  Time(start)>);
    exit;"
  ];
  return Join(cmd, "\n");
end function;

intrinsic ComputeSpecialValues(cores::RngIntElt, label::MonStgElt, eigenvalues_dir::MonStgElt, B::RngIntElt : maxn:=false) -> List
{
  Compute (and store) L(sigma(f), chi)(1) values for the form with label over number field F, with characters up to bound B.
  Returns a list of tuples. Each tuple has 5 elements:
  - chi
  - embedding index
  - L(sigma(f), chi)(1)
  - CFENew(L(f, chi)), i.e., how far the root number is from Norm 1
  - the error message of any error
  - time to compute all this
  }
  isStored, storedValues := StoreIsDefined(SpecialValuesStore, label);
  if isStored then
    Bstored, maxnstored, res := Explode(storedValues);
    if Bstored ge B and (maxnstored cmpeq false or (maxn cmpne false and maxnstored ge maxn)) then
      return res;
    end if;
  end if;
  f := LMFDBHMFwithEigenvalues(label, eigenvalues_dir);
  dim := Dimension(Parent(f));
  F := BaseField(Parent(f));
  chis := QuadraticCharactersUpTo(B, F);
  cmds := [GetLvaluePIPE(label, B, char_index, emb_index, eigenvalues_dir : maxn:=maxn) : char_index in [1..#chis], emb_index in [1..dim]];
  execs := ["magma -b" : _ in cmds];
  out := ParallelPipe(cores, execs, cmds);
  res := [* eval elt : elt in out *]; // different precisions
  StoreSet(SpecialValuesStore, label, <B, maxn, res>);
  return res;
end intrinsic;

intrinsic ComputeOmegaValues(cores::RngIntElt, label::MonStgElt, eigenvalues_dir::MonStgElt, B::RngIntElt : maxn:=false)->.
{
  Compute  Omega values for the form with label over number field F, with characters up to bound B. Optionally the number of cores.
  Returns the list of characters, their signs, and a list of four lists aligned with the signs [ [1,1], [1,-1], [-1,1], [-1,-1] ]
  // each list has elements has a triple
  // 1. index of the character chi in the SeqEnum chis
  // 2. A sequence of Omega_f,chi for each embedding of f
  // 3. A sequence of CFENew(L(f, chi)) for each embedding of f
  }

  f := LMFDBHMF(label);
  dim := Dimension(Parent(f));
  F := BaseField(Parent(f));
  chis := QuadraticCharactersUpTo(B, F);
  chi_signs := [HodgeSigns(chi) : chi in chis];

  // Lvals is a list of tuples for each L(emb(f), chi)
  // 1. index of the character chi in the SeqEnum chis
  // 2. index of the embedding of the Hecke field
  // 3. The special value to maximum precision
  // 4. CFENew(L(f, chi)), i.e., how far the root number is from Norm 1
  // 5. The error message of any error
  // 6. time of the computation
  Lvals := ComputeSpecialValues(cores, label, eigenvalues_dir, B : maxn:=maxn);

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
        entry := [x : x in Lvals | x[1] eq j and x[2] eq emb];
        assert #entry eq 1;
        _, _, special, err, error_message := Explode(entry[1]);
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
  return chis, chi_signs, res2, skipped;
end intrinsic;
