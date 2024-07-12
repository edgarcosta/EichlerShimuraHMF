freeze;
/*function AlternativeRationalReconstruction(x)
	f := MinimalPolynomial(x, 1);
	y := Roots(f, Rationals())[1][1];
	if Abs(x-y) lt 1/(10*Denominator(y)^2) then
		return true, y;
	end if;
	return false, 0;
end function;*/

function NumberFieldDivisors(x)
	H := Parent(x);
	if H eq Rationals() then
		return [<d, Abs(Numerator(x)) div d> : d in Divisors(Numerator(Abs(x)))], [<d, Abs(Denominator(x)) div d> : d in Divisors(Denominator(Abs(x)))];
	end if;
	O := RingOfIntegers(H);
	Ifact := Factorisation(ideal<O|x>);
	xfact := [ <s,f[2]> where _,s := IsPrincipal(f[1]): f in Ifact ];
	xfact_pos := [f : f in xfact | f[2] gt 0];
	xfact_neg := [f : f in xfact | f[2] lt 0];
	if #xfact_pos eq 0 then
		num_fact := [<H!1,H!1>];
	else
		num_fact := [ <&*[H!xfact_pos[i][1]^c[i] : i in [1..#xfact_pos]], &*[H!xfact_pos[i][1]^(xfact_pos[i][2]-c[i]) : i in [1..#xfact_pos]]> : c in CartesianProduct( [ {0..f[2]} : f in xfact_pos ] ) ];
	end if;
	if #xfact_neg eq 0 then
		den_fact := [<H!1,H!1>];
	else
		den_fact := [ <&*[H!xfact_neg[i][1]^(-c[i]) : i in [1..#xfact_neg]], &*[H!xfact_neg[i][1]^(-xfact_neg[i][2]+c[i]) : i in [1..#xfact_neg]]> : c in CartesianProduct( [ {f[2]..0} : f in xfact_neg ] ) ];
	end if;
	return num_fact, den_fact;
end function;

function TausGuess(res_Cremona, dim, pnum, pden)
	H := Parent(pnum[1]);
	mod_factors := [pden[1], pnum[1], pnum[2], pden[2]];
	for i in [1..dim] do
		for j in [1..4] do
			res_Cremona[j][i] *:= Evaluate(mod_factors[j], InfinitePlaces(H)[i]);
		end for;
	end for;
	m, i := Min([Precision(Universe(r)) : r in res_Cremona]);
	if i eq 1 then
		taus := [ [res_Cremona[2][i]/res_Cremona[4][i] : i in [1..dim]], [res_Cremona[3][i]/res_Cremona[4][i] : i in [1..dim]]];
	elif i eq 2 then
		taus := [ [res_Cremona[1][i]/res_Cremona[3][i] : i in [1..dim]], [res_Cremona[3][i]/res_Cremona[4][i] : i in [1..dim]]];
	elif i eq 3 then
		taus := [ [res_Cremona[2][i]/res_Cremona[4][i] : i in [1..dim]], [res_Cremona[1][i]/res_Cremona[2][i] : i in [1..dim]]];
	else
		taus := [ [res_Cremona[1][i]/res_Cremona[3][i] : i in [1..dim]], [res_Cremona[1][i]/res_Cremona[2][i] : i in [1..dim]]];
	end if;
	return taus;
end function;

function FixTaus(F, taus)
	U, phi := UnitGroup(F);
	G := [g : g in Generators(U)];
	taus_signs := [Sign(Imaginary(tau)) : tau in taus];
	for c in CartesianPower({0,1}, #Generators(U)) do
		u := F!&*[phi(g)^c[i] : i->g in G];
		u_signs := [-Sign(Real(Evaluate(u, rho))) : rho in InfinitePlaces(F)];
		taus_signs := [Sign(Imaginary(tau)) : tau in taus];
		if taus_signs eq u_signs then
			return [taus[i]*Evaluate(u, rho) : i->rho in InfinitePlaces(F)];
		end if;
	end for;
	assert(false);
end function;

intrinsic PeriodMatrixOda(label::MonStgElt : B := 75, cores := 4, eps := 1E-6)->.
{ Compute the period matrix à l'Oda }
// Find the Omega values
	chis, chi_signs, values, skipped := ComputeOmegaValues(label, B : cores:=cores);

	Omegas_per_sign := [* [* elt[2] : elt in r *] : r in values *];
	// Do the Cremona trick
	H := HeckeEigenvalueField(Parent(f));
	Omegas := [* CremonaTrickWithEmbeddings(H, r) : r in Omegas_per_sign *];

	// Detect the cross product
	cross_prod := [  Omegas[1][i]*Omegas[4][i]/Omegas[2][i]/Omegas[3][i]  : i in [1..Degree(H)]];
	_<x> := PolynomialRing(Universe(cross_prod));
	cross_pol := &*[x-c : c in cross_prod];
	// RationalReconstruction returns a boolean, and the approximation x
	// the boolean = AlmostEqual(x, input), ie, x is a good approximation
	coeffs_Q := [<a,b> where a,b := RationalReconstruction(ComplexFieldExtra(Precision(c)) ! c) : c in Coefficients(cross_pol)];
	// check that we got good approximation
	assert(not(false in {x[1] : x in coeffs_Q}));
	// Now construct the polynomial over Q
	RQ<xQ> := PolynomialRing(Rationals());
	cross_pol_Q := RQ![x[2] : x in coeffs_Q];
	// we check that is a power of an irreducible polynomial
	fact := Factorisation(cross_pol_Q);
	assert(#fact eq 1);
	// take its radical, i.e., the irreducible polynomial
	cross_pol_Q := fact[1][1];

	// pick the root that matches the complex embeddings of H
	eps := 1E-6; // FIXME, maybe sort by the difference?
	roots := Roots(cross_pol_Q, H);
	differences := [Max([Abs( Evaluate(r[1], InfinitePlaces(H)[j]) - cross_prod[j] ) : j in [1..dim]]) : r in roots];
	ParallelSort(~differences, ~roots);
	assert differences[1]/differences[2] lt 10^(-Precision(Universe(differences))*0.5);
	cross_prod_H := roots[1,1];
	cnum, cden := NumberFieldDivisors(cross_prod_H);

	// Find the taus and period matrices
	possible_taus := [TausGuess(Omegas, dim, pnum, pden) : pnum in cnum, pden in cden];
	fixed_taus := [[ FixTaus(H, tau) : tau in taus] : taus in possible_taus];
	PeriodMatrices := [ [ModuliToBigPeriodMatrixNoam(H, tau) : tau in taus] : taus in fixed_taus];
		return <PeriodMatrices, <cnum, cden>, fixed_taus>;
end intrinsic;
