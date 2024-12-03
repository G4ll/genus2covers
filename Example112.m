/*  We apply our algorithmic criterion
    for the existence of the push out in the category of curves
    to an interesting example:
    we choose a generic cover Y -> X of degree 3,
    and prove that the correspondence X <- Y -> W does not fit in a Galois diagram. */

SetLogFile("Example112.out");

Q := Rationals();
P<x> := PolynomialRing(Q);

/*  In [Kuh88, Section 6] there is a parametrization of all such covering maps,
    we choose a nice looking one. Feel free to tweak the parameters
    to get more examples. */
a := 0;
b := 0;
c := -4;

/*  We have a paremetric description of both phi.... */
B := x^3+a*x^2+b*x+c;
phi_den := B;
phi_num := x^2;
phi := phi_num/phi_den;
"The map phi_X is:", phi;

/*  ... and the map psi: Y -> W! */
d := -3/c;
e := (3*a*c^2-b^2*c)/(9*c^2-4*a*b*c+b^3);
psi_num := (x-d)^2*(x-e);
psi_den := (4*c*x^3+b^2*x^2+2*b*c*x+c^2);
psi := psi_num/psi_den;
"The map phi_W is:", psi;

/*  Finally, we make the fibers computation for y=2 in P1.
    Feel free to change the parameter y = 2;
    You get an infinite family for all but finitely many
    starting points.    */
C := ComplexField(100);
y := 2;
checking_set := {C!y};
for i in [1..50] do
    image1 := [ Evaluate(phi, z) : z in checking_set ];
    preimage1 := &cat[ Roots(phi_num-y*phi_den, C) : y in image1 ];
    preimage1 := [ rr[1] : rr in preimage1 ];
    preimage1 := Set(preimage1);

    image2 := [ Evaluate(psi, z) : z in checking_set ];
    preimage2 := &cat[ Roots(psi_num-y*psi_den, C) : y in image2 ];
    preimage2 := [ rr[1] : rr in preimage2 ];
    preimage2 := Set(preimage2);

    checking_set := checking_set join preimage1 join preimage2;

    "The set F_i(y), where i =", i, ", has cardinality at least:", #checking_set;
end for;