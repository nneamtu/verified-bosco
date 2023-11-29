include "../Types.dfy"
	
abstract module QSystem_A {

	import opened Types

	predicate valid_config(C : QuorumConfig)

	predicate valid_quorum_system(QS : QuorumSystem)
	{
		valid_config(QS.C)
		&& exists q | q in QS.C.Q :: q <= QS.R
		&& QS.R <= QS.C.P
	}
	
	method construct_system(N : nat) returns (QS : QuorumSystem)
		requires N != 0
		ensures valid_quorum_system(QS)
		ensures N == |QS.C.P|
		ensures (forall i :: i in QS.C.P ==> 0 <= i < N)
		ensures (forall i :: i in QS.R ==> 0 <= i < N)
}