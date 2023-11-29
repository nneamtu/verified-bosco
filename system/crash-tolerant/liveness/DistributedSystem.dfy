include "../Defs.dfy"
include "../../shared/liveness/DistributedSystem_L.dfy"
include "UBosco.dfy"

module DistributedSystem refines DistributedSystem_L {

	import opened UBosco
	import Defs

	predicate valid_distributed_system_impl...
	{
		(forall i :: 0 <= i < |S| ==> S[i].NBProcess?)
	}

	method init_impl...
	{
		QS := QSystem.construct_system(N);

		S := [];
		var i := 0;
		while i < N
			invariant i == |S|
			invariant 0 <= i <= N
			invariant forall j :: 0 <= j < i ==> S[j].id == j
			invariant forall j :: 0 <= j < i ==> S[j].NBProcess?
			invariant forall j :: 0 <= j < i ==> S[j].C == QS.C
			invariant forall j :: 0 <= j < i ==> UBosco.valid_process(S[j])
			invariant forall j :: 0 <= j < i ==> S[j].val_hist[0] in V
			invariant forall j :: 0 <= j < i ==> S[j].inbox == {}
			invariant Network.valid_network(S)
		{
			var val :| val in V;
			var p := UBosco.init_impl(i, val, QS.C);
			S := S + [p];
			i := i + 1;
		}
	}

	lemma quorum_nonempty_placeholder...
	{
		var _ := Defs.quorum_nonempty(QS.C.Q, qR);
	}

	lemma network_step_preserves_invariants...
	{
		...;
		assert ...;
	}
	
	lemma safe_network_step_preserves_invariants...
	{
		...;
		assert ...;
	}

	lemma nonbyzantine_process_step_preserves_invariants...
	{
		assert ...;
		...;
		assert ...;
	}

	lemma byzantine_process_step_preserves_invariants...
	{
		assert S[i].BProcess?;
		assert valid_distributed_system_impl(S, QS);
		assert S[i].NBProcess?;
		assert false;
		assert ...;
	}
}

	
