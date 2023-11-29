include "../Types.dfy"
include "../abstr/Defs_A.dfy"
include "Defs_L.dfy"
include "DistributedSystem_L.dfy"

/* Proofs of *safety properties* that describe how the system makes progress. */

abstract module Proof_L {

	import opened Types
  import opened Defs_A
	import opened Defs_L	
	import opened DistributedSystem : DistributedSystem_L

  /* No lone wolves */

  predicate two_intersection_completed_prev_rnd(S : seq<Process>, QS : QuorumSystem, i : nat, q1 : set<nat>, q2 : set<nat>)
    requires 0 <= i < |S| 
    requires S[i].NBProcess?
  {
    q1 in QS.C.Q 
    && q2 in QS.C.Q 
    && q1 * q2 <= QS.R
    && (forall j :: j in q1 * q2  ==>
        0 <= j < |S| 
        && S[j].NBProcess? 
        && S[j].rnd >= S[i].rnd - 1)
  }

  predicate exists_two_intersection_completed_prev_rnd(S : seq<Process>, QS : QuorumSystem, i : nat)
    requires 0 <= i < |S| 
    requires S[i].NBProcess?
  {
    exists q1, q2 :: two_intersection_completed_prev_rnd(S, QS, i, q1, q2)
  }

	predicate no_lone_wolves(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
	{
		forall i :: 0 <= i < |S| && S[i].NBProcess? ==> 
		exists_two_intersection_completed_prev_rnd(S, QS, i)
	}

  lemma quorum_proposals_refl_placeholder(p : Process, t : nat)
    requires UBosco.valid_process(p)
    requires t < p.rnd
    ensures quorum_proposals_refl(p.quorum_hist[t], p.proposals_hist[t])

  lemma quorum_hist_placeholder(p : Process, t : nat)
    requires UBosco.valid_process(p)
    requires t < p.rnd
    ensures p.quorum_hist[t] in p.C.Q

  lemma no_lone_wolves_lemma'(S : seq<Process>, QS : QuorumSystem, i : nat)
    returns (q1 : set<nat>, q2 : set<nat>)
    requires valid_distributed_system(S, QS)
    requires 0 <= i < |S|
    requires S[i].NBProcess?
    ensures two_intersection_completed_prev_rnd(S, QS, i, q1, q2)
  {
    var t := S[i].rnd - 1;
		if (t >= 0) {
      q1 :| q1 in QS.C.Q && q1 <= QS.R; // q1 is qR
      q2 := S[i].quorum_hist[t];
      quorum_hist_placeholder(S[i], t);
      forall j | j in q1 * q2
        ensures 0 <= j < |S|
        ensures S[j].NBProcess?
			  ensures S[j].rnd >= S[i].rnd - 1
      {
        assert forall j :: j in q1 ==> 0 <= j < |S| && S[j].NBProcess?;
        assert t < S[i].rnd;
        quorum_proposals_refl_placeholder(S[i], t);
			  var pr :| pr in S[i].proposals_hist[t] && pr.id == j;
			  var msg := DistributedSystem.proposals_from_messages(S, QS, i, pr, t);
			  assert msg.rnd <= S[j].rnd;
        assert msg.rnd == t == S[i].rnd - 1;
		  }
		} else {
      q1 :| q1 in QS.C.Q && q1 <= QS.R; // q1 is qR
      q2 := q1;
      forall j | j in q1 * q2
        ensures 0 <= j < |S|
        ensures S[j].NBProcess?
        ensures S[j].rnd >= S[i].rnd - 1
      {
        assert 0 <= j < |S| && S[j].NBProcess?;
			  assert S[j].rnd >= 0;
      }
		}
  }

	lemma 
  {:fuel two_intersection_completed_prev_rnd<T, S>, 0, 0}
  no_lone_wolves_lemma<T, S>(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
		ensures no_lone_wolves(S, QS)
	{
		forall i | 0 <= i < |S| && S[i].NBProcess?
			ensures exists_two_intersection_completed_prev_rnd(S, QS, i)
    {
      var q1, q2 := no_lone_wolves_lemma'(S, QS, i);
      assert two_intersection_completed_prev_rnd(S, QS, i, q1, q2);
		}
	}

  /* No one left behind */

  predicate quorum_with_msgs_to_deliver(S : seq<Process>, QS : QuorumSystem, i : nat, q : set<nat>)
    requires 0 <= i < |S|
    requires S[i].NBProcess?
  {
    q in QS.C.Q
    && q <= QS.R
    && (forall j :: j in q ==> 
        0 <= j < |S|
        && S[j].NBProcess? 
        && (exists msg | msg in S[j].outbox :: msg.rnd == S[i].rnd))
  }

  predicate exists_quorum_with_msgs_to_deliver(S : seq<Process>, QS : QuorumSystem, i : nat)
    requires 0 <= i < |S|
    requires S[i].NBProcess?
  {
    exists q :: quorum_with_msgs_to_deliver(S, QS, i, q)
  }

	predicate no_one_left_behind(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
	{
		forall i :: 
      0 <= i < |S| 
      && S[i].NBProcess? 
      && i in QS.R 
      && S[i].rnd == min_rnd_subset(S, QS.R) ==>
			exists_quorum_with_msgs_to_deliver(S, QS, i)
	}

  lemma no_one_left_behind_lemma'(S : seq<Process>, QS : QuorumSystem, i : nat)
    returns (q : set<nat>)
    requires valid_distributed_system(S, QS)
    requires 0 <= i < |S|
    requires S[i].NBProcess?
    requires i in QS.R
    requires S[i].rnd == min_rnd_subset(S, QS.R)
    ensures quorum_with_msgs_to_deliver(S, QS, i, q)
  {
    q :| q in QS.C.Q && q <= QS.R; // q is qR
		forall j | j in q
      ensures 0 <= j < |S|
      ensures S[j].NBProcess?
		  ensures exists msg | msg in S[j].outbox :: msg.rnd == S[i].rnd
		{
      assert forall j :: j in q ==> 0 <= j < |S| && S[j].NBProcess?;
		  assert S[i].rnd <= S[j].rnd;
			assert Message(S[j].id, S[j].val_hist[S[i].rnd], S[i].rnd) in S[j].outbox;
		}
  }

	lemma 
  {:fuel quorum_with_msgs_to_deliver<T, S>, 0, 0}
  no_one_left_behind_lemma<T, S>(S : seq<Process>, QS : QuorumSystem)
		requires valid_distributed_system(S, QS)
    requires valid_distributed_system_impl(S, QS)
		ensures no_one_left_behind(S, QS)
	{
		forall i | 0 <= i < |S| && S[i].NBProcess? && i in QS.R && S[i].rnd == min_rnd_subset(S, QS.R)
			ensures exists_quorum_with_msgs_to_deliver(S, QS, i)
		{
			var q := no_one_left_behind_lemma'(S, QS, i);
      assert exists_quorum_with_msgs_to_deliver(S, QS, i);
		}
	}
}
