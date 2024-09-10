freeze;


// baed on reconstructing-g4/magma/schottky.m
intrinsic SchottkyModularForm(tau::AlgMatElt : theta:="Flint") -> Any
  {FIXME}

  require (Nrows(tau) eq 4) and (Ncols(tau) eq 4): "period matrix must be 4 by 4";

  require theta in ["Flint", "Magma"] : "the optional argument theta must be either \"Flint\" or \"Magma\"";

  // replace Theta by ThetaFlint
  if theta eq "Flint" then
    Theta := ThetaFlint;
  end if;

  prec := Precision(BaseRing(Parent(tau)));


  C := ComplexField(prec);
  char := Matrix(C, 8, 1, [0,0,0,0,0,0,0,0]);
  z := Matrix(C, 4, 1, [0,0,0,0]);

  m1 := 1/2*Matrix(C, 8, 1, [1,0,1,0,1,0,1,0]);
  m2 := 1/2*Matrix(C, 8, 1, [0,0,0,1,1,0,0,0]);
  m3 := 1/2*Matrix(C, 8, 1, [0,0,1,1,1,0,1,1]);
  n0 := Matrix(C, 8, 1, [0,0,0,0,0,0,0,0]);
  n1 := 1/2*Matrix(C, 8, 1, [0,0,0,1,1,1,1,0]);
  n2 := 1/2*Matrix(C, 8, 1, [0,0,1,1,0,0,0,1]);
  n3 := 1/2*Matrix(C, 8, 1, [0,0,1,0,1,0,1,1]);
  n4 := n1+n2;
  n5 := n1+n3;
  n6 := n2+n3;
  n7 := n1+n2+n3;
  SchottkyN := [n0,n1,n2,n3,n4,n5,n6,n7];
  M := [[m + n: n in SchottkyN] : m in [m1, m2, m3]];


  pi1, pi2, pi3 := Explode([ &*[Theta(mi, z, tau) : mi in Mi] : Mi in M ]);

  return pi1^2 + pi2^2 + pi3^2 - 2*(pi1*pi2 + pi2*pi3 + pi1*pi3);
end intrinsic;
