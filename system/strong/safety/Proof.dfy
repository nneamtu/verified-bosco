include "../../shared/safety/Proof_S.dfy"
include "../Defs.dfy"
include "DistributedSystem.dfy"
include "ProofUtil.dfy"

module Proof refines Proof_S {

	import opened Defs
	import opened DistributedSystem
	import ProofUtil

	/* Agreement */

	lemma 
	{:fuel valid_distributed_system<T, S>, 0, 0}
	decision_implies_unanimous_results'...
	{
		assert Defs.unanimous_intersect_2(
			S[i].quorum_hist[t],
			S[i].other_quorums_hist[t].q2,
			S[i].proposals_hist[t],
			S[i].re_hist[t].val);
			
		var qR := DistributedSystem.exists_qR(S, QS);

		Defs.unanimous_intersect_2_implies_unanimous_intersect_4(
			QS.C.Q,
			S[i].quorum_hist[t],
			S[i].other_quorums_hist[t].q2,
			qR,
			S[j].quorum_hist[t],
			S[i].proposals_hist[t],
			S[i].re_hist[t].val);

		ProofUtil.unanimous_intersect_4_qR_sym(
			S,
			QS,
			i,
			j,
			S[i].other_quorums_hist[t].q2,
			qR,
			S[i].re_hist[t].val,
			t);

		UBosco.LBosco.instantiate_maybe_condition(
			S[j].proposals_hist[t],
			S[j].quorum_hist[t],
			S[j].val_hist[t],
			QS.C.Q,
			S[j].re_hist[t],
			S[j].other_quorums_hist[t],
			S[i].quorum_hist[t],
			S[i].other_quorums_hist[t].q2,
			qR,
			S[i].re_hist[t].val
		);
		assert Defs.unanimous_intersect_4(
			S[j].quorum_hist[t],
			S[j].other_quorums_hist[t].q2,
			S[j].other_quorums_hist[t].q3,
			S[j].other_quorums_hist[t].q4,
			S[j].proposals_hist[t],
			S[j].re_hist[t].val);

		ProofUtil.unanimous_intersect_7_qR_same(
			S,
			QS,
			j,
			S[j].other_quorums_hist[t].q2,
			S[j].other_quorums_hist[t].q3,
			S[j].other_quorums_hist[t].q4,
			S[i].quorum_hist[t],
			S[i].other_quorums_hist[t].q2,
			qR,
			S[j].re_hist[t].val,
			S[i].re_hist[t].val,
			t);
	}

	lemma 
	{:fuel valid_distributed_system<T, S>, 0, 0}
	unanimous_proposals_implies_unanimous_decisions'<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, i : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires valid_distributed_system_single(S, QS, S[i], i)
		requires S[i].NBProcess?
		requires 0 <= t < S[i].rnd
		requires unanimous_proposals(S, QS, t, v)
		ensures S[i].re_hist[t] == Result(v, D)
	{
		var qR := DistributedSystem.exists_qR(S, QS);
		ProofUtil.intersect_qR_unanimous(S, QS, i, qR, v, t);

		UBosco.LBosco.instantiate_decide_condition(
			S[i].proposals_hist[t],
			S[i].quorum_hist[t],
			S[i].val_hist[t],
			QS.C.Q,
			S[i].re_hist[t],
			S[i].other_quorums_hist[t],
			qR,
			v
		);
		assert Defs.unanimous_intersect_2(
			S[i].quorum_hist[t],
			S[i].other_quorums_hist[t].q2,
			S[i].proposals_hist[t],
			S[i].re_hist[t].val);
		assert S[i].re_hist[t].status == D;
		ProofUtil.unanimous_intersect_3_qR_same(
			S,
			QS,
			i,
			S[i].other_quorums_hist[t].q2,
			qR,
			S[i].re_hist[t].val,
			v,
			t);
	}

	lemma unanimous_proposals_implies_unanimous_results'...
	{
		unanimous_proposals_implies_unanimous_decisions'(S, QS, t, i, v);
	}	

	/* Validity */
	
	lemma 
	{:fuel valid_distributed_system<T, S>, 0, 0}
	single_round_validity_base_case'...
	{
		match S[i].re_hist[0].status {
			case D => {
				var j := ProofUtil.correct_proposal_decide(S, QS, i, 0);
				assert S[j].val_hist[0] in initial_proposals(S, QS);
			}
			case M => {
				var j := ProofUtil.correct_proposal_maybe(S, QS, i, 0);
				assert S[j].val_hist[0] in initial_proposals(S, QS);
			}
			case U => {
				assert S[i].re_hist[0].val == S[i].val_hist[0];
			}
		}
	}

	lemma
	{:fuel valid_distributed_system<T, S>, 0, 0}
	single_round_validity_inductive_step'...
	{
		match S[i].re_hist[t + 1].status {
			case D => {
				var j := ProofUtil.correct_proposal_decide(S, QS, i, t + 1);
				assert S[j].val_hist[t + 1] == S[j].re_hist[t].val;
				assert single_round_validity(S, QS, t);
				assert S[j].re_hist[t].val in initial_proposals(S, QS);
			}
			case M => {
				var j := ProofUtil.correct_proposal_maybe(S, QS, i, t + 1);
				assert S[j].val_hist[t + 1] == S[j].re_hist[t].val;
				assert single_round_validity(S, QS, t);
				assert S[j].re_hist[t].val in initial_proposals(S, QS);
			}
			case U => {
				assert S[i].re_hist[t + 1].val == S[i].val_hist[t + 1];
				assert S[i].re_hist[t].val == S[i].val_hist[t + 1];
				assert single_round_validity(S, QS, t);
				assert S[i].re_hist[t].val in initial_proposals(S, QS);
			}
		}
	}

	/* Strongly one-step */
	
	predicate strongly_one_step<T, S>(S : seq<Process>, QS : QuorumSystem, v : T)
		requires valid_distributed_system(S, QS)
	{
		unanimous_proposals(S, QS, 0, v) ==>
			forall i :: 
				0 <= i < |S| 
				&& S[i].NBProcess? 
				&& 0 < S[i].rnd ==> 
				S[i].re_hist[0] == Result(v, D)
	}

	lemma {:opaque} unanimous_proposals_implies_unanimous_decisions<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires 0 <= t
		requires unanimous_proposals(S, QS, t, v)
		ensures unanimous_decisions(S, QS, t, v)
	{
		forall i | 0 <= i < |S| && S[i].NBProcess? && t < S[i].rnd
			ensures S[i].re_hist[t] == Result(v, D)
		{
			unanimous_proposals_implies_unanimous_decisions'(S, QS, t, i, v);
		}
	}

	lemma strongly_one_step_lemma<T, S>(S : seq<Process>, QS : QuorumSystem, v : T)
		requires valid_distributed_system(S, QS)
		ensures strongly_one_step(S, QS, v)
	{
		if unanimous_proposals(S, QS, 0, v) {
			unanimous_proposals_implies_unanimous_decisions(S, QS, 0, v);
		}
	}
}
