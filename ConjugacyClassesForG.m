/*** We compute possible conjugacy classes for G in Sn.
We prove in Lemma 3.13 that G is transitive and primitive,
has a maximal subgroup of order n and, when
the ramification type is II, it contains a double transposition.
We only need to check the casis n < 9. ***/

SetLogFile("ConjugacyClassesForG.out");

for n in [1..8] do
	G := Sym(n);
for d in [1..NumberOfPrimitiveGroups(n)] do
	H := PrimitiveGroup(n, d);
	
	/* Check for a maximal subgroup of index n */
	max := MaximalSubgroups(H);
	index_n_subgroup := [Index(H, x`subgroup) eq n : x in max];
	
	check1 := false;
	for b in index_n_subgroup do
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
	
	/* output */
	if check1 and check2 then
		"n=", n,", d=", d;
		"The group is",  PrimitiveGroupDescription(n, d), H;
		"The maximal number of orbits is", nn_orbs;
		"********";
	end if;
	
end for;
end for;



/* wild exceptional case */
n := 5;
d := 2;
H := PrimitiveGroup(n, d);
max := MaximalSubgroups(H);
"The exceptional subgroup of S5 is", PrimitiveGroupDescription(n, d);
nn := GSet(H);
"The orbits are ", [#Orbits(x`subgroup, nn) : x in max | Index(H, x`subgroup) eq n];
