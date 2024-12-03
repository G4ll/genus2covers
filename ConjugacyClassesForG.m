/*** We compute possible conjugacy classes for G in Sn.
We prove in Lemma 3.12 that G is transitive and primitive,
has a maximal subgroup of order n and, when
the ramification type is II, it contains a double transposition.
We also impose that G must be a quotient of the free group
on two generators, and the double transposition must
coincide with their commutator.
We only need to check the cases with n < 9. ***/

SetLogFile("ConjugacyClassesForG.out");

/********************************************************/

for n in [1..8] do
	G := Sym(n);
for d in [1..NumberOfPrimitiveGroups(n)] do
	H := PrimitiveGroup(n, d);
	
	/* Check for a maximal subgroup of index n */
	max := MaximalSubgroups(H);
	index_of_subgroups := [Index(H, x`subgroup) eq n : x in max];
	
	check1 := false;
	for b in index_of_subgroups do
		check1 := check1 or b;
	end for;
	
	/* Check for a double transposition */
	if n ge 4 then
		dbl := [<2, 2>, <1, n-4>];
		check2 := dbl in [CycleStructure(h): h in H];
	elif n eq 4 then
		check2 := [<2,2>] in [CycleStructure(h): h in H];
	elif n le 4 then
		check2 := false;
	end if;
	
	/* Computes number of orbits */
	if check1 then
		nn := GSet(H);
		orbits := [#Orbits(x`subgroup, nn): x in max |Index(H, x`subgroup) eq n];
		nn_orbs := Max(orbits);
	end if;

	/* Checks for generators alpha, beta
	whose commutator is a double transposition */
	check3 := false;
	if check1 and check2 then
		for cc in ConjugacyClasses(H) do
		alpha := cc[3];
		for beta in H do
			gamma := alpha*beta*Inverse(alpha)*Inverse(beta);
			Hab := sub< H | [alpha, beta] >;
			if (CycleStructure(gamma)[1] eq <2,2>) and Hab eq H then
				check3 := true;
			end if;
		end for;
		end for;
	end if;
	
	/* output */
	if check1 and check2 and check3 then
		"n=", n,", d=", d;
		"The group is",  PrimitiveGroupDescription(n, d), H;
		"The maximal number of orbits is", nn_orbs;
		"****************************************";
	end if;
	
end for;
end for;

/********************************************************/

H := PrimitiveGroup(6, 2);

possibleGenerators := [];
for cc in ConjugacyClasses(H) do
	alpha := cc[3];
	for beta in H do
		gamma := alpha*beta*Inverse(alpha)*Inverse(beta);
		Hab := sub< H | [alpha, beta] >;
		if (CycleStructure(gamma)[1] eq <2,2>) and Hab eq H then
			Append(~possibleGenerators, <alpha, beta>);
		end if;
	end for;
end for;

"We can ralize PGL(2, 5):", #possibleGenerators ge 0;
