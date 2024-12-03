
SetLogFile("Example18.out");

Q := Rationals();
P<x> := PolynomialRing(Q);

/*  In [Kuh88, Section 6] there is a parametrization of all such covering maps,
    we choose a nice looking one. Feel free to tweak the parameters
    to get more examples. */
a := 0;
b := 0;
c := -4;

/*  We have a paremetric description of both phi.... */
phi_num := x^2;
phi_den := x^3+a*x^2+b*x+c;
phi := phi_num/phi_den;
"The map phi_X is:", phi;
"----------";

/*  ... and the map psi: Y -> W! */
d := -3/c;
e := (3*a*c^2-b^2*c)/(9*c^2-4*a*b*c+b^3);
psi_num := (x-d)^2*(x-e);
psi_den := (4*c*x^3+b^2*x^2+2*b*c*x+c^2);
psi := psi_num/psi_den;
jW := 256*(3*b-a^2)^3/(27*c^2 - 18*a*b*c + 4*a^3*c + 4*b^3 - a^2*b^2);

/* From the explicit description of phi we derive
a model for the elliptic curve X */
SupportPolyRing<u, e> := PolynomialRing(Q, 2);
ramification_polynomial := Evaluate(phi_num, u) - e*Evaluate(phi_den, u);
A := Evaluate(Resultant(ramification_polynomial, Derivative(ramification_polynomial, 1), 1), [0,x]);
A := ChangeRing(A, Q);
fX := P!(SquarefreePart(A)/x);
//X := EllipticCurve(fX);




/*--------------------------------------------------------------*/

A4<X,y,t1,t2> := AffineSpace(Q, 4);
equations_for_Z := [y^2 - Evaluate(fX, X)];
Append(~equations_for_Z, Evaluate(phi_num, t1)-X*Evaluate(phi_den, t1) );
Append(~equations_for_Z, Evaluate(phi_num, t2)-X*Evaluate(phi_den, t2) );

Z := Curve(Scheme(A4, equations_for_Z));
eta := iso < Z -> Z | [X, -y, t2, t1], [X, -y, t2, t1]  >;

"The curve Z has", #IrreducibleComponents(Z), "connected components.";
"----------";

/* We check that W1 has genus 0 */
Z1 := Curve(IrreducibleComponents(Z)[2]);
Z1 := ProjectiveClosure(Z1);

eta_list := [Z1.1, -Z1.2, Z1.4, Z1.3, Z1.5];
eta1 := iso < Z1 -> Z1 | eta_list, eta_list >;
G1 := AutomorphismGroup(Z1, [eta1]);

"The quotient computation that inevitably outputs gibberish:";
time W1 := CurveQuotient(G1);
"----------";
"The genus of W1 is", Genus(W1);
"----------";

/* We compute W2 */
Z2 := Curve(IrreducibleComponents(Z)[1]);
Z2 := ProjectiveClosure(Z2);

eta_list := [Z2.1, -Z2.2, Z2.4, Z2.3, Z2.5];
eta2 := iso < Z2 -> Z2 | eta_list, eta_list >;
G2 := AutomorphismGroup(Z2, [eta2]);

"The quotient computation that inevitably outputs gibberish:";
time W2 := CurveQuotient(G2);
"----------";

/*--------------------------------------------------------------*/

/* We got an horrendous model for W2, we are going to find a better one,
by projecting away from a point untile we get a smooth model in P3.
We then find a rational points and get a Weiestrass model. */
model2 := Curve(IsomorphicProjectionToSubspace(W2));        
IsSingular(model2);
amb := AmbientSpace(model2);
//AssignNames(~amb, ["x","y","z","w"]);

/* Luckly, there is an easy rational point on this model! */
P := amb![1,0,0,0];
W2 := EllipticCurve(model2, P);
"W2 is the", W2;

"----------";
"W2 has the j-invariant predicted by Kuhn:", jW eq jInvariant(W2);