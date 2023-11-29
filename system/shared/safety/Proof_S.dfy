include "../Types.dfy"
include "DistributedSystem_S.dfy"	

abstract module Proof_S {

	import opened Types
	import opened DistributedSystem : DistributedSystem_S

	/* Agreement */

	function method max_rnd(S : seq<Process>) : nat
		ensures forall p : Process :: p in S && p.NBProcess? ==> p.rnd <= max_rnd(S)
	{
		if S == [] then 0
		else
			var max' := max_rnd(S[1..]);
			if !S[0].NBProcess? || max' >= S[0].rnd then max' else S[0].rnd 
	}

	predicate unanimous_proposals<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires 0 <= t
	{
		forall i ::
			0 <= i < |S|
			&& S[i].NBProcess?
			&& t <= S[i].rnd ==>
			S[i].val_hist[t] == v
	}

	predicate unanimous_results<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires 0 <= t
	{
		forall i ::
			0 <= i < |S|
			&& S[i].NBProcess?
			&& t < S[i].rnd ==>
			S[i].re_hist[t].val == v
	}

	predicate unanimous_decisions<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires 0 <= t
	{
		forall i ::
			0 <= i < |S|
			&& S[i].NBProcess?
			&& t < S[i].rnd ==>
			S[i].re_hist[t] == Result(v, D)
	}

	predicate interround_agreement(S : seq<Process>, QS : QuorumSystem, t : nat, s : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= t <= s
	{
		forall i, j ::
			0 <= i < |S|
			&& S[i].NBProcess?
			&& t < S[i].rnd
			&& 0 <= j < |S|
			&& S[j].NBProcess?
			&& s < S[j].rnd ==>
			S[i].re_hist[t].status == D && S[j].re_hist[s].status == D ==>
			S[i].re_hist[t].val == S[j].re_hist[s].val
	}

	predicate agreement(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
	{
		forall t, s :: 0 <= t <= s <= max_rnd(S) ==> interround_agreement(S, QS, t, s)
	}

	lemma {:opaque} decision_implies_unanimous_results'<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, i : nat, j : nat)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S| 
		requires 0 <= j < |S|
		requires valid_distributed_system_single(S, QS, S[i], i)
		requires valid_distributed_system_single(S, QS, S[j], j)
		requires S[i].NBProcess?
		requires S[j].NBProcess?
		requires 0 <= t < S[i].rnd
		requires t < S[j].rnd
		requires S[i].re_hist[t].status == D
		ensures S[i].re_hist[t].val == S[j].re_hist[t].val

	lemma {:opaque} decision_implies_unanimous_results(S : seq<Process>, QS : QuorumSystem, t : nat, i : nat)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S| 
		requires S[i].NBProcess?
		requires 0 <= t < S[i].rnd
		requires S[i].re_hist[t].status == D
		ensures unanimous_results(S, QS, t, S[i].re_hist[t].val)
	{
		forall j | 0 <= j < |S| && S[j].NBProcess? && t < S[j].rnd
			ensures S[i].re_hist[t].val == S[j].re_hist[t].val
		{
			decision_implies_unanimous_results'(S, QS, t, i, j);
		}
	}

	lemma {:opaque} unanimous_results_implies_unanimous_proposals<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires 0 <= t
		requires unanimous_results(S, QS, t, v)
		ensures unanimous_proposals(S, QS, t + 1, v)
	{}

	lemma {:opaque} unanimous_proposals_implies_unanimous_results'<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, i : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires valid_distributed_system_single(S, QS, S[i], i)
		requires S[i].NBProcess?
		requires 0 <= t < S[i].rnd
		requires unanimous_proposals(S, QS, t, v)
		ensures S[i].re_hist[t].val == v

	lemma {:opaque} unanimous_proposals_implies_unanimous_results<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= t
		requires unanimous_proposals(S, QS, t, v)
		ensures unanimous_results(S, QS, t, v)
	{
		forall i | 0 <= i < |S| && S[i].NBProcess? && t < S[i].rnd
			ensures S[i].re_hist[t].val == v
		{
			unanimous_proposals_implies_unanimous_results'(S, QS, t, i, v);
		}
	}

	lemma
	{:fuel unanimous_results<T, S>, 0, 0}
	{:fuel unanimous_proposals<T, S>, 0, 0}
	{:opaque}
  unanimous_results_stable<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, s : nat, v : T)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= t <= s
		requires unanimous_results(S, QS, t, v)
		ensures unanimous_results(S, QS, s, v)
	{
		var s' := t;
		while s' < s
			invariant t <= s' <= s
			invariant unanimous_results(S, QS, s', v);
		{
			unanimous_results_implies_unanimous_proposals(S, QS, s', v);
			assert unanimous_proposals(S, QS, s' + 1, v);
			unanimous_proposals_implies_unanimous_results(S, QS, s' + 1, v);
			s' := s' + 1;
		}
		assert unanimous_results(S, QS, s', v);
		assert s' == s;
		assert unanimous_results(S, QS, s, v);
	}

	lemma agreement_lemma<T, S>(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		ensures agreement(S, QS)
	{
		forall t, s | 0 <= t <= s <= max_rnd(S)
			ensures interround_agreement(S, QS, t, s)
		{
			forall i | 0 <= i < |S| && S[i].NBProcess? && t < S[i].rnd && S[i].re_hist[t].status == D
				ensures unanimous_results(S, QS, s, S[i].re_hist[t].val)
			{
				decision_implies_unanimous_results(S, QS, t, i);
				unanimous_results_stable(S, QS, t, s, S[i].re_hist[t].val);
			}
		}
	}

	/* Validity */
	
	function method initial_proposals<T(==), S>(S : seq<Process>, QS : QuorumSystem) : set<T>
		requires valid_distributed_system(S, QS)
	{
		set i | 0 <= i < |S| && S[i].NBProcess? :: S[i].val_hist[0]
	}

	predicate single_round_validity(S : seq<Process>, QS : QuorumSystem, t : nat)
		requires valid_distributed_system(S, QS)
		requires 0 <= t
	{
		forall i :: 0 <= i < |S| && S[i].NBProcess? && t < S[i].rnd ==> S[i].re_hist[t].val in initial_proposals(S, QS)
	}

	predicate validity(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
	{
		forall t :: 0 <= t <= max_rnd(S) ==> single_round_validity(S, QS, t)
	}

	lemma {:opaque} single_round_validity_base_case'<T, S>(S : seq<Process>, QS : QuorumSystem, i : nat)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires valid_distributed_system_single(S, QS, S[i], i)
		requires S[i].NBProcess?
		requires 0 < S[i].rnd
		ensures S[i].re_hist[0].val in initial_proposals(S, QS)

	
	lemma {:opaque} single_round_validity_base_case(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		ensures single_round_validity(S, QS, 0)
	{
		forall i | 0 <= i < |S| && S[i].NBProcess? && 0 < S[i].rnd
			ensures S[i].re_hist[0].val in initial_proposals(S, QS)
		{
			single_round_validity_base_case'(S, QS, i);
		}
	}

	lemma {:opaque} single_round_validity_inductive_step'<T, S>(S : seq<Process>, QS : QuorumSystem, t : nat, i : nat)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		requires 0 <= i < |S|
		requires valid_distributed_system_single(S, QS, S[i], i)
		requires S[i].NBProcess?
		requires 0 <= t + 1 < S[i].rnd
		requires single_round_validity(S, QS, t)
		ensures S[i].re_hist[t + 1].val in initial_proposals(S, QS)

	
	lemma {:opaque} single_round_validity_inductive_step(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		ensures forall t : nat :: single_round_validity(S, QS, t) ==> single_round_validity(S, QS, t + 1)
	{
		forall t : nat
			ensures single_round_validity(S, QS, t) ==> single_round_validity(S, QS, t + 1)
		{
			if single_round_validity(S, QS, t) {
				forall i | 0 <= i < |S| && S[i].NBProcess? && t + 1 < S[i].rnd
					ensures S[i].re_hist[t + 1].val in initial_proposals(S, QS)
				{
					single_round_validity_inductive_step'(S, QS, t, i);
				}
			}
		}
	}

	lemma validity_lemma(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
		requires valid_distributed_system_impl(S, QS)
		ensures validity(S, QS)
	{
		single_round_validity_base_case(S, QS);
		var t := 0;
		while t < max_rnd(S)
			invariant 0 <= t <= max_rnd(S)
			invariant S == old(S)
			invariant forall t' :: 0 <= t' <= t ==> single_round_validity(S, QS, t')
		{
			assert single_round_validity(S, QS, t);
			single_round_validity_inductive_step(S, QS);
			assert single_round_validity(S, QS, t + 1);
			t := t + 1;
		}
	}
}
