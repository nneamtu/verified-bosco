include "../Types.dfy"
include "DistributedSystem_S.dfy"
include "Proof_S.dfy"

abstract module Main_S {

	import opened Types
  import opened DistributedSystem : DistributedSystem_S
	import Proof : Proof_S

	method
	{:fuel Proof.agreement<T, S>, 0, 0}
	{:fuel Proof.validity<T, S>, 0, 0}
	Main<T(==), S>(N : nat, V : set<T>, T : nat, init_byz_st : S)
		requires N > 0
		requires V != {}
	{
		var S, QS := DistributedSystem.init_impl(N, V, init_byz_st);

		var t := 0;

		safety_props_placeholder(S, QS, V);

		while t < T
			invariant N == |S|
			invariant valid_distributed_system(S, QS)
			invariant valid_distributed_system_impl(S, QS)
		{
			var id :| 0 <= id <= N;
			if id == N {
				var S' := DistributedSystem.network_step_impl(S, QS);
				DistributedSystem.network_step_preserves_invariants(S, QS, S');
				S := S';
			} else {
				if S[id].NBProcess? {
					var S' := DistributedSystem.nonbyzantine_process_step_impl(S, id, QS);
					DistributedSystem.nonbyzantine_process_step_preserves_invariants(S, id, QS, S');
					S := S';
				} else {
					var S' := DistributedSystem.byzantine_process_step_impl(S, id, QS);
					DistributedSystem.byzantine_process_step_preserves_invariants(S, id, QS, S');
					S := S';
				}
			}
			t := t + 1;
			safety_props_placeholder(S, QS, V);
		}
	}

	lemma safety_props_placeholder<T, S>(S : seq<Process>, QS : QuorumSystem, V : set<T>)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
}
