include "../../shared/safety/Proof_S.dfy"
include "../Defs.dfy"
include "DistributedSystem.dfy"

module Proof refines Proof_S {

	import opened Defs
	import opened DistributedSystem
	
	/* Agreement */

	lemma unanimous_intersect_2_sym<T, S>(S : seq<Process>, QS : QuorumSystem, i : nat, j : nat, v : T, t : nat)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires 0 <= j < |S|
		requires 0 <= t < S[i].rnd
		requires t < S[j].rnd
		requires unanimous_intersect_2(S[i].quorum_hist[t], S[j].quorum_hist[t], S[i].proposals_hist[t], v)
		ensures unanimous_intersect_2(S[j].quorum_hist[t], S[i].quorum_hist[t], S[j].proposals_hist[t], v)
	{
		forall pr_j | pr_j in intersect_2(S[j].quorum_hist[t], S[i].quorum_hist[t], S[j].proposals_hist[t])
			ensures pr_j.val == v
		{
			assert pr_j.id in S[i].quorum_hist[t];
			var pr_i := Defs.instantiate_quorum_proposals_refl(
				S[i].quorum_hist[t],
				S[i].proposals_hist[t],
				pr_j.id);
			DistributedSystem.unique_proposals_by_nonbyzantine_process(S, QS, i, j, pr_i, pr_j, t);
			assert v == pr_j.val;
		}
		var _ := Defs.intersect_2_nonempty(QS.C.Q, S[j].quorum_hist[t], S[i].quorum_hist[t], S[j].proposals_hist[t]);
	}

  lemma
	{:opaque}
	{:fuel valid_distributed_system<T, S>, 0, 0}
	{:fuel valid_distributed_system_impl<T, S>, 0, 0}
	decision_implies_unanimous_results'...
	{
		assert unanimous(S[i].proposals_hist[t], S[i].re_hist[t].val);
		Defs.unanimous_implies_unanimous_intersect_2(
			QS.C.Q,
			S[i].quorum_hist[t],
			S[j].quorum_hist[t],
			S[i].proposals_hist[t],
			S[i].re_hist[t].val);

		unanimous_intersect_2_sym(S, QS, i, j, S[i].re_hist[t].val, t);
		assert S[i].quorum_hist[t] in QS.C.Q; 
		assert unanimous_intersect_2(S[j].quorum_hist[t], S[i].quorum_hist[t], S[j].proposals_hist[t], S[i].re_hist[t].val);
		UBosco.LBosco.instantiate_maybe_condition(
			S[j].proposals_hist[t],
			S[j].quorum_hist[t],
			S[j].val_hist[t],
			QS.C.Q,
			S[j].re_hist[t],
			S[j].other_quorums_hist[t],
			S[i].quorum_hist[t],
			S[i].re_hist[t].val);

		assert S[j].other_quorums_hist[t].q2 in QS.C.Q;
		assert unanimous_intersect_2(
			S[j].quorum_hist[t],
			S[j].other_quorums_hist[t].q2,
			S[j].proposals_hist[t],
			S[j].re_hist[t].val);

		Defs.unanimous_intersect_3_same(
			QS.C.Q,
			S[j].quorum_hist[t],
			S[i].quorum_hist[t],
			S[j].other_quorums_hist[t].q2,
			S[j].proposals_hist[t],
			S[i].re_hist[t].val,
			S[j].re_hist[t].val);
	}

	lemma 	
	{:opaque}
	{:fuel valid_distributed_system<T, S>, 0, 0}
	unanimous_proposals_implies_unanimous_results'...
	{
		forall pr | pr in S[i].proposals_hist[t]
			ensures pr.val == v
		{
			DistributedSystem.proposals_from_vals(S, QS, i, pr, t);
		}
		assert unanimous(S[i].proposals_hist[t], v);
		assert S[i].re_hist[t].val == v;
	}


	/* Validity */

	lemma
	{:opaque}
	{:fuel valid_distributed_system<T, S>, 0, 0}
	single_round_validity_base_case'...
	{
		var pr :| pr in S[i].proposals_hist[0] && S[i].re_hist[0].val == pr.val;
		DistributedSystem.proposals_from_vals(S, QS, i, pr, 0);
		assert S[i].re_hist[0].val == S[pr.id].val_hist[0];
	}

	lemma
	{:opaque}
	{:fuel valid_distributed_system<T, S>, 0, 0}
	single_round_validity_inductive_step'...
	{
		var pr :| pr in S[i].proposals_hist[t + 1] && S[i].re_hist[t + 1].val == pr.val;
		assert forall i :: 0 <= i < |S| ==> S[i].NBProcess?;
		DistributedSystem.proposals_from_results'(S, QS, i, pr, t);
		assert S[pr.id].re_hist[t].val == S[i].re_hist[t + 1].val;
			
		assert single_round_validity(S, QS, t);
		assert forall i :: 0 <= i < |S| && t < S[i].rnd ==> S[i].re_hist[t].val in initial_proposals(S, QS);
		assert S[pr.id].re_hist[t].val in initial_proposals(S, QS);
	}

	/* Unanimity */

	predicate unanimous_correct_proposals<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, v : T)
		requires valid_distributed_system(S, QS)
	{
		forall i ::
			0 <= i < |S|
			&& i in QS.R
			&& t <= S[i].rnd ==>
			S[i].val_hist[t] == v
	}
		

	predicate unanimity<T, S>(S : seq<Process>, QS : QuorumSystem, v : T)
		requires valid_distributed_system(S, QS)
	{
		unanimous_correct_proposals(S, QS, 0, v) ==>
			forall i, t ::
			0 <= i < |S|
			&& S[i].NBProcess?
			&& 0 <= t < S[i].rnd ==>
			S[i].re_hist[t].status == D ==> S[i].re_hist[t].val == v
	}

	lemma
	{:opaque}
	{:fuel valid_distributed_system<T, S>, 0, 0}
	unanimous_correct_proposals_implies_unanimous_results'<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, i : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires valid_distributed_system_single(S, QS, S[i], i)
		requires S[i].NBProcess?
		requires 0 <= t < S[i].rnd
		requires unanimous_correct_proposals(S, QS, t, v)
		ensures S[i].re_hist[t].val == v
	{
		var qR := DistributedSystem.exists_qR(S, QS);
		forall pr | pr in S[i].proposals_hist[t] && pr.id in S[i].quorum_hist[t] * qR
			ensures pr.val == v
		{
			DistributedSystem.proposals_from_vals(S, QS, i, pr, t);
		}
			
		var _ := Defs.intersect_2_nonempty(QS.C.Q, S[i].quorum_hist[t], qR, S[i].proposals_hist[t]);
		assert unanimous_intersect_2(S[i].quorum_hist[t], qR, S[i].proposals_hist[t], v);

		UBosco.LBosco.instantiate_maybe_condition(
			S[i].proposals_hist[t],
			S[i].quorum_hist[t],
			S[i].val_hist[t],
			QS.C.Q,
			S[i].re_hist[t],
			S[i].other_quorums_hist[t],
			qR,
			v);
		assert unanimous_intersect_2(
			S[i].quorum_hist[t],
			S[i].other_quorums_hist[t].q2,
			S[i].proposals_hist[t],
			S[i].re_hist[t].val);
		assert S[i].other_quorums_hist[t].q2 in QS.C.Q;
				
		Defs.unanimous_intersect_3_same(
			QS.C.Q,
			S[i].quorum_hist[t],
			qR,
			S[i].other_quorums_hist[t].q2,
			S[i].proposals_hist[t],
			v,
			S[i].re_hist[t].val);
	}

	lemma {:opaque} unanimous_correct_proposals_implies_unanimous_results<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires unanimous_correct_proposals(S, QS, t, v)
		ensures unanimous_results(S, QS, t, v)
	{
		forall i | 0 <= i < |S| && S[i].NBProcess? && t < S[i].rnd
			ensures S[i].re_hist[t].val == v
		{
			unanimous_correct_proposals_implies_unanimous_results'(S, QS, t, i, v);
		}
	}

	lemma unanimity_lemma<T, S>(S : seq<Process>, QS : QuorumSystem, v : T)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		ensures unanimity(S, QS, v)
	{
		if unanimous_correct_proposals(S, QS, 0, v) {
			unanimous_correct_proposals_implies_unanimous_results(S, QS, 0, v);
			
			forall i, t | 0 <= i < |S| && S[i].NBProcess? && 0 <= t < S[i].rnd
				ensures S[i].re_hist[t].val == v
			{
				unanimous_results_stable(S, QS, 0, t, v);
			}
		}
	}
}
