include "../../shared/Types.dfy"
include "../Defs.dfy"
include "DistributedSystem.dfy"

module ProofUtil {

	import opened Types
	import opened Defs
	import opened DistributedSystem

	lemma unanimous_intersect_3_qR_sym<T, S>(S : seq<Process>, QS : QuorumSystem, i : nat, j : nat, qR : set<nat>, v : T, t : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S| && S[i].NBProcess?
		requires 0 <= j < |S| && S[j].NBProcess?
		requires qR in QS.C.Q && qR <= QS.R
		requires 0 <= t < S[i].rnd
		requires t < S[j].rnd
		requires unanimous_intersect_3(S[i].quorum_hist[t], S[j].quorum_hist[t], qR, S[i].proposals_hist[t], v)
		ensures unanimous_intersect_3(S[j].quorum_hist[t], S[i].quorum_hist[t], qR, S[j].proposals_hist[t], v)
	{
		forall pr_j | pr_j in intersect_3(S[j].quorum_hist[t], S[i].quorum_hist[t], qR, S[j].proposals_hist[t])
			ensures v == pr_j.val
		{
			assert pr_j.id in S[i].quorum_hist[t];
			var pr_i := Defs.instantiate_quorum_proposals_refl(
				S[i].quorum_hist[t],
				S[i].proposals_hist[t],
				pr_j.id);
			DistributedSystem.unique_proposals_by_nonbyzantine_process(S, QS, i, j, pr_i, pr_j, t);
			assert v == pr_j.val;
		}

		var _ := Defs.intersect_3_nonempty(QS.C.Q, S[j].quorum_hist[t], S[i].quorum_hist[t], S[i].quorum_hist[t], S[j].proposals_hist[t]);
	}

	lemma unanimous_intersect_4_qR_same<T, S>(S : seq<Process>, QS : QuorumSystem, i : nat, j : nat, q1 : set<nat>, q2 : set<nat>, qR : set<nat>, v1 : T,  v2 : T, t : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S| && S[i].NBProcess?
		requires 0 <= j < |S| && S[j].NBProcess?
		requires 0 <= t < S[i].rnd
		requires t < S[j].rnd
		requires unanimous_intersect_3(S[j].quorum_hist[t], S[i].quorum_hist[t], qR, S[j].proposals_hist[t], v1)
		requires q1 in QS.C.Q && q2 in QS.C.Q
		requires qR in QS.C.Q && qR <= QS.R
		requires unanimous_intersect_3(S[j].quorum_hist[t], q1, q2, S[j].proposals_hist[t], v2)
		ensures v1 == v2
	{
		var id := Defs.five_intersection_nonempty(QS.C.Q, S[j].quorum_hist[t], S[i].quorum_hist[t], q1, q2, qR);
		assert id in QS.R;
		var pr := Defs.instantiate_quorum_proposals_refl(
			S[j].quorum_hist[t],
			S[j].proposals_hist[t],
			id);
		
		assert pr in intersect_3(S[j].quorum_hist[t], S[i].quorum_hist[t], qR, S[j].proposals_hist[t]);
		assert v1 == pr.val;
		assert pr in intersect_3(S[j].quorum_hist[t], q1, q2, S[j].proposals_hist[t]);
		assert v2 == pr.val;
		assert v1 == v2;
	}


	lemma 
	{:fuel valid_distributed_system<T, S>, 0, 0}
	correct_proposal_decide<T, S>(S : seq<Process>, QS : QuorumSystem, i : nat, t : nat)
		returns (j : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S|
		requires valid_distributed_system_single(S, QS, S[i], i)
		requires S[i].NBProcess?
		requires 0 <= t < S[i].rnd
		requires S[i].re_hist[t].status == D
		ensures 0 <= j < |S|
		ensures valid_distributed_system_single(S, QS, S[j], j)
		ensures S[j].NBProcess?
		ensures j in QS.R
		ensures t <= S[j].rnd
		ensures S[j].val_hist[t] == S[i].re_hist[t].val
	{
		assert UBosco.LBosco.step_quorum(
			S[i].proposals_hist[t],
			S[i].quorum_hist[t],
			S[i].val_hist[t],
			S[i].C.Q,
			S[i].re_hist[t],
			S[i].other_quorums_hist[t]);

		var id := UBosco.QSystem.quorum_contains_correct_process(QS, S[i].quorum_hist[t]);
		var pr := Defs.instantiate_quorum_proposals_refl(
			S[i].quorum_hist[t],
			S[i].proposals_hist[t],
			id);

		assert unanimous(S[i].proposals_hist[t], S[i].re_hist[t].val);
		assert S[i].re_hist[t].val == pr.val;	

		assert {:fuel valid_distributed_system<T, S>, 0, 1} 
			pr.id in QS.R
			&& 0 <= pr.id < |S|
			&& S[pr.id].NBProcess?
			&& valid_distributed_system_single(S, QS, S[pr.id], pr.id);
		DistributedSystem.proposals_from_vals(S, QS, i, pr, t);

		j := pr.id;
	}

	lemma 
	{:fuel valid_distributed_system<T, S>, 0, 0}
	correct_proposal_maybe<T, S>(S : seq<Process>, QS : QuorumSystem, i : nat, t : nat)
		returns (j : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= i < |S|
		requires valid_distributed_system_single(S, QS, S[i], i)
		requires S[i].NBProcess?
		requires 0 <= t < S[i].rnd
		requires S[i].re_hist[t].status == M
		ensures 0 <= j < |S|
		ensures valid_distributed_system_single(S, QS, S[j], j)
		ensures S[j].NBProcess?
		ensures j in QS.R
		ensures t <= S[j].rnd
		ensures S[j].val_hist[t] == S[i].re_hist[t].val
	{
		assert UBosco.LBosco.step_quorum(
			S[i].proposals_hist[t],
			S[i].quorum_hist[t],
			S[i].val_hist[t],
			S[i].C.Q,
			S[i].re_hist[t],
			S[i].other_quorums_hist[t]);

		var q2 := S[i].other_quorums_hist[t].q2;
		var q3 := S[i].other_quorums_hist[t].q3;
		assert q2 in QS.C.Q && q3 in QS.C.Q;
	  var id := UBosco.QSystem.three_intersection_contains_correct_process(
			QS, 
			S[i].quorum_hist[t], 
			q2, 
			q3);
		var pr := Defs.instantiate_quorum_proposals_refl(
			S[i].quorum_hist[t],
			S[i].proposals_hist[t],
			id);

		assert unanimous_intersect_3(
			S[i].quorum_hist[t], 
			q2, 
			q3, 
			S[i].proposals_hist[t], 
			S[i].re_hist[t].val);
		assert S[i].re_hist[t].val == pr.val;

		assert {:fuel valid_distributed_system<T, S>, 0, 1} 
			pr.id in QS.R
			&& 0 <= pr.id < |S|
			&& S[pr.id].NBProcess?
			&& valid_distributed_system_single(S, QS, S[pr.id], pr.id);
		DistributedSystem.proposals_from_vals(S, QS, i, pr, t);

		j := pr.id;
	}
}
