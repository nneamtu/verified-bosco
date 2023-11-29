include "../Defs.dfy"
include "../../shared/liveness/DistributedSystem_L.dfy"
include "UBosco.dfy"

module DistributedSystem refines DistributedSystem_L {

	import opened UBosco
	import Defs

	predicate valid_distributed_system_impl...
	{
		true
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
			invariant forall j :: 0 <= j < |S| ==> (j in QS.R <==> S[j].NBProcess?)
			invariant forall j :: 0 <= j < i && S[j].NBProcess? ==> UBosco.valid_process(S[j])
			invariant forall j :: 0 <= j < i && S[j].NBProcess? ==> S[j].C == QS.C
			invariant forall j :: 0 <= j < i && S[j].NBProcess? ==> S[j].val_hist[0] in V
			invariant forall j :: 0 <= j < i ==> S[j].inbox == {}
			invariant Network.valid_network(S)
		{
			var val :| val in V;
			if i in QS.R {
				var ub := UBosco.init_impl(i, val, QS.C);
				S := S + [ub];
			} else {
				var byz := byzantine_process_init_impl(S, QS, i, init_byz_st);
				S := S + [byz];
			}
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
		assert ...;
	}
}

	
