function NumberFieldLCM(L)
	K := Parent(L[1]);
	OK := Integers(K);
	I := [OK*x : x in L];
	_, a := IsPrincipal(&meet I);
	return K!a;
end function;

function NumberFieldGCD(L)
	K := Parent(L[1]);
	OK := Integers(K);
	I := [OK*x : x in L];
	_, a := IsPrincipal(&+I);
	return K!a;
end function;

intrinsic CremonaTrick(rec)->.
{ Cremona's trick. }
	if #rec lt 2 then
		return rec[1][1];
	end if;
	prec := Min(&cat[ [Precision(x) : x in L[1] ] : L in rec]); 
	K1 := BaseField(rec[1][2][1]`name[2]);
	K<a> := NumberFieldExtra(ChangeRing(DefiningPolynomial(K1), RationalsExtra(prec)));
	c := [ [ y where _,y := AlgebraizeElementExtra(L[1][i] / rec[1][1][i], K) : L in rec[[1..#rec]] ] : i in [1,2] ];
	GCDs := [NumberFieldGCD(L[2..#L]) : L in c];
	return K, c, [Norm(x) :x in GCDs];
end intrinsic;

function MatchRoots(H, poly, qs)
    prec := Precision(Universe(qs));
    err := 10^(-prec/2);
	//poly_facts := Factorisation(poly);
	//assert( Min([Abs(q1-q2) : q1,q2 in qs | q1 ne q2]) gt 2*err ); 
    vs := InfinitePlaces(H);
    rs := [el[1] : el in Roots(poly, H)];
    rs_sorted := [];
    for r in rs do
        for i->q in qs do
            if Abs(Evaluate(r, vs[i]) - q) gt err then
				continue r;
			end if;
        end for;
		return r;
    end for;
end function;

intrinsic CremonaTrickWithEmbeddings(H,res_i : dim := 4)->.
{ Cremona's trick with embeddings. }
	if #res_i lt 2 then
		return [ res_i[1][k][1] : k in [1..dim] ];
	end if;
    L := [H | 1];
    for j := 2 to #res_i do
        qs := [res_i[j][k][1]/res_i[1][k][1] : k in [1..dim]];
        R<x> := PolynomialRing(Universe(qs));
        poly := &*[x - q : q in qs];
        cs := Eltseq(poly);
        cs_QQ := [];
        for c in cs do
			mp := MinimalPolynomial(c, 1);
			bool := true;
			if Degree(mp) ne 1 then
				bool := false;
			else
				c_QQ := - Coefficients(mp)[1] / Coefficients(mp)[2];
				if Abs(c_QQ - c) gt 1/Abs(Coefficients(mp)[2])^3 then
					bool := false;
				end if;
			end if;
            //bool, c_QQ := RationalReconstruction(ComplexFieldExtra(Precision(c)-2)!c);
            if not bool then
				print "Character", j, "skipped as", c, "could not be recognised";
				print poly;
				print mp;
                continue j;
            end if;
            Append(~cs_QQ, c_QQ);
        end for;
        QQt<t> := PolynomialRing(Rationals());
        poly_QQ := QQt!cs_QQ;
        Append(~L, MatchRoots(H, poly_QQ, qs));
    end for;
	//print L, [Norm(x) : x in L];
    GCD := NumberFieldGCD(L);
    return [ res_i[1][k][1] * Evaluate(GCD, InfinitePlaces(H)[k]) : k in [1..dim]], GCD, Norm(GCD);
end intrinsic;