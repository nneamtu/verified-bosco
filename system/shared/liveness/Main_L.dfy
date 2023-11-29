include "../Types.dfy"
include "Defs_L.dfy"
include "Progress_L.dfy"

abstract module Main_L {

	import opened Types
	import opened Defs_L
	import opened Progress : Progress_L
	
	method Main<T(==), S>(T : nat, N : nat, V : set<T>, init_byz_st : S)
		requires N > 0
		requires V != {}
	{
		var S, QS := Execution.DistributedSystem.init_impl(N, V, init_byz_st);

		var t := 0;
		
		while t < T
			invariant N == |S|
			invariant Execution.DistributedSystem.valid_distributed_system(S, QS)
			invariant Execution.DistributedSystem.valid_distributed_system_impl(S, QS)
			invariant forall j :: 0 <= j < |S| && j in QS.R && S[j].NBProcess? ==> S[j].rnd >= t
		{
			S := step_all_correct(S, QS, t);
			t := t + 1;
		}
	}

	method
	{:fuel Execution.DistributedSystem.valid_distributed_system<T, S>, 0, 0}
	{:fuel Execution.valid_execution<T, S>, 0, 0}
	step_single<T(==), S>(S : seq<Process>, QS : QuorumSystem, i : nat, ghost t : nat)
		returns (S' : seq<Process>)
		requires Execution.DistributedSystem.valid_distributed_system(S, QS)
		requires Execution.DistributedSystem.valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires i in QS.R && S[i].NBProcess?
		requires S[i].rnd >= t
		ensures Execution.same_ids_nondecr_rnds(S, S')
		ensures S'[i].rnd >= t + 1
		ensures Execution.DistributedSystem.valid_distributed_system(S', QS)
		ensures Execution.DistributedSystem.valid_distributed_system_impl(S', QS)
		ensures exists Exec :: Execution.valid_execution(S, S', Exec, QS)
	{
		var S'' := Progress.run_until_has_msgs_from_quorum(S, i, QS);
		assert Execution.same_ids_nondecr_rnds(S, S'');
		
		S' := Execution.DistributedSystem.nonbyzantine_process_step_impl(S'', i, QS);
		Execution.DistributedSystem.nonbyzantine_process_step_preserves_invariants(S'', i, QS, S');
		Execution.process_step_same_ids_rnds_incr_single(S'', i, QS, S');
		
		assert {:fuel Execution.valid_execution<T, S>, 0, 1} exists Exec' :: Execution.valid_execution(S, S'', Exec', QS);
		ghost var Exec' :| Execution.valid_execution(S, S'', Exec', QS);
		assert Execution.system_step(S'', S');
		Execution.valid_execution_append(Exec', S, S'', S', QS);
		assert Execution.valid_execution(S, S', Exec' + [S'], QS);
	}
	
	method
	{:fuel Execution.DistributedSystem.valid_distributed_system<T, S>, 0, 0}
	step_all_correct<T(==), S>(S : seq<Process>, QS : QuorumSystem, ghost t : nat) 
	returns (S' : seq<Process>)
		requires Execution.DistributedSystem.valid_distributed_system(S, QS)
		requires Execution.DistributedSystem.valid_distributed_system_impl(S, QS)
		requires forall j :: 0 <= j < |S| && j in QS.R && S[j].NBProcess? ==> S[j].rnd >= t
		ensures Execution.same_ids_nondecr_rnds(S, S')
		ensures Execution.DistributedSystem.valid_distributed_system(S', QS)
		ensures Execution.DistributedSystem.valid_distributed_system_impl(S', QS)
		ensures forall j :: 0 <= j < |S'| && j in QS.R && S'[j].NBProcess? ==> S'[j].rnd >= t + 1
	{
		assert forall i :: i in QS.R ==> S[i].NBProcess?;
		assert Execution.valid_execution(S, S, [S], QS);
		var R' := {};
		S' := S;
		while R' != QS.R
			invariant R' <= QS.R
			invariant Execution.same_ids_nondecr_rnds(S, S')
			invariant forall j :: 0 <= j < |S'| && j in R' ==> S'[j].rnd >= t + 1
			invariant forall j :: 0 <= j < |S'| && j in QS.R - R' ==> S'[j].rnd >= t
			invariant Execution.DistributedSystem.valid_distributed_system(S', QS)
			invariant Execution.DistributedSystem.valid_distributed_system_impl(S', QS)
			invariant exists Exec :: Execution.valid_execution(S, S', Exec, QS);
			decreases QS.R - R'
		{
			var i :| i in QS.R - R';
			var S'' := step_single(S', QS, i, t);

			ghost var Exec0 :| Execution.valid_execution(S, S', Exec0, QS);
			ghost var Exec1 :| Execution.valid_execution(S', S'', Exec1, QS);
			Execution.valid_execution_concat(Exec0, Exec1, S, S', S'', QS);
			assert Execution.valid_execution(S, S'', Exec0 + Exec1[1..], QS);

			S' := S'';
			R' := R' + {i};
		}
	}
}
