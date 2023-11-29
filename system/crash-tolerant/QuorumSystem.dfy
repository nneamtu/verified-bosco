include "Defs.dfy"
include "../shared/abstr/QuorumSystem_A.dfy"	
	
module QSystem refines QSystem_A {

	import opened Defs

	predicate valid_config...
	{
		C.P != {} && C.Q != {}
		&& (forall q :: q in C.Q ==> q <= C.P)
		&& three_intersection(C.Q)
	}

	/*predicate valid_quorum_system(QS : QuorumSystem)
	{
		valid_config(QS.C)
			&& exists q | q in QS.C.Q :: q <= QS.R
			&& QS.R <= QS.C.P
	}*/

	method construct_system...
	{
		var P := {};
		var i := 0;
		while i < N
			invariant 0 <= i <= N
			invariant |P| == i
			invariant forall i :: i in P ==> 0 <= i < |P|
		{
			P := P + {i};
			i := i + 1;
		}
		var R := P;
		var Q := {P};
		var C := QuorumConfig(P, Q);
		QS := QuorumSystem(C, R);
	}	
}
