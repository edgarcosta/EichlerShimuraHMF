freeze;
intrinsic NormBoundOnComputedEigenvalues(f::ModFrmHilElt : lower_bound:=1000) -> RngIntElt
  { the retuns N such that a_p(f) < N has been computed and p is a good prime}
  bound := Max([Norm(elt) : elt in Keys(f`hecke_eigenvalues) | elt ne 0*elt]);
  missing_evs := Set(PrimesUpTo(bound, BaseRing(Parent(f)))) diff Set(Keys(f`hecke_eigenvalues));
  // ignore bad primes
  missing_evs := missing_evs diff {pe[1] : pe in Factorization(Level(Parent(f)))};
  norms := [Norm(elt) : elt in missing_evs | Norm(elt) gt lower_bound];
  if #norms eq 0 then
    return bound;
  else
   return Min(norms);
  end if;
end intrinsic;

intrinsic MaxPrecision(L, maxn) -> .
    { maximize precision assuming using only the a_n for n <= N }
    prec := 0;
    while LCfRequired(L : Precision:=prec+1) le maxn do
        prec +:=1;
    end while;
    return prec;
end intrinsic;

intrinsic GuessConductor(f::ModFrmHilElt, chi::GrpHeckeElt : Precision:=4, max_precision:=false, maxn:= false, EC:=false, conductors:=false) -> RngIntelt, FldReElt
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

    if conductors cmpeq false then
        conductors := PossibleConductors(f, Conductor(chi));
    end if;
    if #conductors eq 1 then
        return conductors[1], 0;
    end if;
    if max_precision cmpeq false then
        if EC cmpne false then
            max_precision := 100;
        else 
            if maxn cmpeq false then
                maxn := NormBoundOnComputedEigenvalues(f);
            end if;
            L := LSeriesTwisted(f, chi : KnownConductor := conductors[1]);
            max_precision := MaxPrecision(L, maxn);
        end if;
    end if;
    if Precision gt max_precision then
        error "Not enough eigenvalues computed to pin down the conductor";
    end if;

    res := Sort([<CFENew(LSeriesTwisted(f, chi : KnownConductor:=c, Precision:=Precision, EC:=EC)), c>  : c in conductors ]);
    // filter obvious out
    threshold := 10^(-Precision*1.0/3);
    res_pos := [elt : elt in res | elt[1] lt threshold];
    res_pos2 := [elt : elt in res | elt[1] lt threshold^2];
    if #res_pos eq 1 and #res_pos2 eq 1 then
      return res_pos[1,2], res_pos[1,1];
    else
        return $$(f, chi: max_precision:=max_precision, Precision:=Precision + 2, conductors:=conductors);
    end if;
end intrinsic;

intrinsic LSeriesTwisted(f::ModFrmHilElt, chi::GrpHeckeElt : Embedding:=1, Precision:=0, EC:=false, KnownConductor:=false, maxn:=false) -> LSer
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
   KnownConductor := GuessConductor(f, chi : EC:=EC, maxn:=maxn);
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

intrinsic LMFDBTwistedLvalue(label, eigenvalues_dir, conductor_bnd, char_index, embedding : maxn:=false) -> Tup
{ L(f, chi)(1) and Abs(root_number) - 1 }
  f := LMFDBHMFwithEigenvalues(label, eigenvalues_dir);
  F := BaseField(Parent(f));
  chi := QuadraticCharactersUpTo(conductor_bnd, F)[char_index];
  if maxn cmpeq false then
    maxn := NormBoundOnComputedEigenvalues(f);
  end if;
  L := LSeriesTwisted(f, chi : Embedding:=embedding, maxn:=maxn);
  LSetPrecision(L, MaxPrecision(L, maxn));
  err := CFENew(L);
  special := Evaluate(L, 1);
  return special, err;
end intrinsic;

