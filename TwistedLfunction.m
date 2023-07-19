

procedure MaximizePrecision(~L, maxn)
    prec := 1;
    while LCfRequired(L : Precision:=prec+1) le maxn do
        prec +:=1;
    end while;
    LSetPrecision(L, prec);
end procedure;

intrinsic GuessConductor(f::ModFrmHilElt, chi::GrpHeckeElt : Precision:=4, max_precision:=false, EC:=false) -> RngIntelt, FldReElt
  { Using the functional equation compute the possible conductor }
    /*
     We guess the conductor with assumption that it is easy to compute ap for p <= max{n : an computed}
     We refuse to try to compute any more ap's
    */

  function PossibleConductors(f, chi_conductor)
    Mf:= Parent(f);
    N := Level(Mf);
    c2 := chi_conductor^2;
    // M | LCM(cond(chi)^2, N)
    divisors := Divisors(c2 meet N);
    // some wishful thinking from CMFs
    // cond(chi^2) | LCM(M, N)
    Mf:= Parent(f);
    K := BaseRing(Mf);
    return Reverse(Sort([Norm(elt)*Discriminant(Integers(K))^2 : elt in divisors | (elt meet N) subset c2 ]));
  end function;


    conductors := PossibleConductors(f, Conductor(chi));
    if max_precision cmpeq false then
        if not EC cmpeq false then
            max_precision := 100;
        else
            maxn := Max([Norm(I) : I in Keys(f`hecke_eigenvalues) | not IsZero(I)]);
            L := LSeriesTwisted(f, chi : KnownConductor := conductors[1]);
            MaximizePrecision(~L, maxn);
            max_precision := L`precision;
        end if;
    end if;
    if Precision gt max_precision then assert false; end if; // life is hard
    
    res := Sort([<CFENew(LSeriesTwisted(f, chi : KnownConductor:=c, Precision:=Precision, EC:=EC)), c>  : c in conductors ]);
    // filter obvious out
    threshold := 10^(-Precision*1.0/3);
    res_pos := [elt : elt in res | elt[1] lt threshold];
    res_pos2 := [elt : elt in res | elt[1] lt threshold^2];
    if #res_pos eq 1 and #res_pos2 eq 1 then
        return res_pos[1,2], res_pos[1,1];
    else
        return $$(f, chi: max_precision:=max_precision, Precision := Precision + 2);
    end if;
end intrinsic;

intrinsic LSeriesTwisted(f::ModFrmHilElt, chi::GrpHeckeElt : Embedding:=1, Precision:=0, EC:=false, KnownConductor:=false) -> LSer
 { return the twisted L-series of the Hilbert modular newform f}
 Mf:= Parent(f);
 K := BaseRing(Mf);
 N := Level(Mf);
 WT := Weight(Mf);
 require assigned Mf`HeckeIrreducible and Mf`HeckeIrreducible:  "The argument must be a Hilbert modular newform (obtained from 'Eigenform')";
 require Type(DirichletCharacter(Mf)) eq RngIntElt: "Only trivial character is currently implemented";
 if Type(WT) eq RngIntElt then W:=[WT,WT]; else W:=Sort(Weight(Mf)); end if;
 w := W[#W];
 require &and[IsEven(w) : w in W] : "All weights must be even";
 require #SequenceToSet(W) eq 1: "Only parallel weight is currently implemented";
 
 E := HeckeEigenvalueField(Mf);
 A := AbsoluteField(E);
 r, c := Signature(A);
 RF := c eq 0 select RealField else ComplexField;
 prec := (Precision eq 0) select GetPrecision(RF()) else Precision;
 R1<T> := PowerSeriesRing(Integers(),1+2*Degree(K));
 ip := InfinitePlaces(A)[Embedding];


 twist := chi;



 function cfK(p, d : Precision:=prec)
  fp := Degree(p);
  P := Norm(p);
  if fp gt d then
   return 1+O(T^(d+1));
  end if;

  if Degree(A) eq 1 then
    if EC cmpeq false then
      ap := HeckeEigenvalue(f, p);
    else
      ef := EulerFactor(EC, p);
      //print p, ef;
      ap := -Coefficient(ef, fp);
    end if;
  else
    ap := Evaluate(HeckeEigenvalue(f,p), ip : Precision:=Precision);
  end if;

  eps := Valuation(N, p) gt 0 select 0 else 1; // need character generally

  // original euler factor: 1 - ap*(U^fp) + eps*P^(w-1)*U^(2*fp);
  tp := twist(p);
    _<U> := PolynomialRing(Parent(ap));
  return 1 - ap*tp*(U^fp) + eps*tp^2*P^(w-1)*U^(2*fp);
 end function;

 function cf(p,d : Precision:=prec) // need prec compatible
  return &*[cfK(f[1],d : Precision:=Precision) : f in Factorization(p*Integers(K)) ];
 end function;

 name:=<"L-series of ",f," twisted">;
 gamma:=&cat[[0-e,1-e] where e:=(w-W[i]) div 2 : i in [1..Degree(K)]];
 if KnownConductor cmpeq false then
   KnownConductor := GuessConductor(f, chi : EC:=EC);
 end if;
 L:=LSeries(
     w,
     gamma,
     KnownConductor,
     cf : Name:=name, Precision:=prec);
 L`cffuncK := cfK;
 L`degreeK := <2, K>;
 L`condK := N; // this is wrong, as Norm(N) != KnownConductor
 IP := InfinitePlaces(K);
 L`hodgeK := &cat[[<[w-W[i],W[i]-1,2],IP[i]>,<[W[i]-1,w-W[i],2],IP[i]>] : i in [1..#IP]];
 L`object := <f, chi>;
 L`embed := Embedding;

 return L;
end intrinsic;