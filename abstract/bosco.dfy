include "../single-round/bosco.dfy"
  
module SingleRound {

  export Interface
    provides step_all, LBosco
    reveals Result, unanimous, single_round_agreement, single_round_unanimity, single_round_validity, single_round_correct_unanimous_proposals

  import opened LBosco = LBosco`Interface

  /* Result(v, S) represents the result of a step */  
  type Result<T(==)> = (T, Status)

  /* unanimous(pr, v) is true when every element in pr is v */
  predicate unanimous<T(==)>(pr : set<T>, v : T){
    forall p :: p in pr ==> p == v
  }

  predicate single_round_agreement<T(!new)>(re : set<Result<T>>)
  {
    forall v :: (v, D) in re ==> (forall v', s | (v', s) in re :: v' == v)
  }

  predicate single_round_unanimity<T(!new)>(pr : set<T>, re : set<Result<T>>)
  {
    forall v :: unanimous(pr, v) ==> (forall v', s :: (v', s) in re ==> v' == v && s == D)
  }

  predicate single_round_validity<T(!new)>(pr :  set<T>, re : set<Result<T>>)
  {
    forall v, s :: (v, s) in re ==> v in pr
  }

	predicate single_round_correct_unanimous_proposals<T(!new)>(pr_correct : set<T>, re : set<Result<T>>)
	{
		forall v :: unanimous(pr_correct, v) ==> (forall v', s :: (v', s) in re ==> v' == v)
	}

  method construct_system<T(==)>(pr : set<T>, pr_correct : set<T>, N : nat)
		returns (P : set<Proposal<T>>, Q : set<set<Proposal<T>>>, qR : set<Proposal<T>>)
    requires pr != {} && pr_correct != {}
		requires N != 0
		requires pr_correct <= pr
    ensures valid_system(P, Q)
		ensures qR in Q && (forall pr :: pr in qR ==> pr.value in pr_correct)
    ensures forall p, i :: Proposal(p, i) in P ==> p in pr
    ensures N == |P|
  {
    P := {};
    var i := 0;
    while i < N
      invariant forall p1, p2 | p1 in P && p2 in P :: p1 != p2 ==> p1.id != p2.id
      invariant forall p | p in P :: 0 <= p.id < |P|
      invariant |P| == i
      invariant forall p, i :: Proposal(p, i) in P ==> p in pr_correct
      invariant 0 <= i <= N
      decreases N - i
    {
      var p :| p in pr_correct;
      P := P + {Proposal(p, i)};
      i := i + 1;
    }
    Q := {P};
		qR := P;
  }

  method destruct_system<T(==)>(ghost P : set<Proposal<T>>, ghost Q : set<set<Proposal<T>>>, S : set<LBResult<T>>, ghost pr : set<T>, ghost pr_correct : set<T>, ghost qR : set<Proposal<T>>)
    returns (re : set<Result<T>>)
    requires valid_system(P, Q)
		requires qR in Q && (forall pr :: pr in qR ==> pr.value in pr_correct)
    requires forall v, i :: Proposal(v, i) in P ==> v in pr
    requires agreement(S)
    requires unanimity(P, S)
    requires validity(P, S)
		requires quorum_intersection_unanimity(P, Q, S)
    ensures single_round_agreement(re)
    ensures single_round_unanimity(pr, re)
    ensures single_round_validity(pr, re)
		ensures single_round_correct_unanimous_proposals(pr_correct, re)
     
  {
		re := set s | s in S :: (s.value, s.status);
    assert (forall v :: unanimous(pr, v) ==> unanimous_proposals(P, v));
		forall v | unanimous(pr_correct, v)
			ensures forall s :: s in S ==> s.value == v
		{
			assert qR != {};
			var pr :| pr in qR;
			assert forall q2 :: q2 in Q ==> unanimous_intersect(qR, q2, v);
			assert forall s :: s in S ==> s.value == v;
		}
  }
	
  method step_all<T(==)>(pr : set<T>, pr_correct : set<T>, N : nat) returns (re : set<Result<T>>)
		requires pr_correct <= pr
		ensures single_round_agreement(re)
    ensures single_round_unanimity(pr, re)
    ensures single_round_validity(pr, re)
		ensures single_round_correct_unanimous_proposals(pr_correct, re)
  {
    if pr != {} && pr_correct != {} && N != 0 {
      var P, Q, qR := construct_system(pr, pr_correct, N);
      var S := step_system(P, Q);
      re := destruct_system(P, Q, S, pr, pr_correct, qR);
    } else {
      re := {};
    }
  }
}


  
module UBosco {
  
  import opened SingleRound`Interface

  import opened LBosco`Types

  class UBosco<T(==)> {

		var pr_init : set<T>

		var pr_init_correct : set<T>

    // pr_hist[t] is the set of proposals made in round t
    var pr_hist : seq<set<T>>

    // re_hist[t] is the set of results after stepping in round t
    var re_hist : seq<set<Result<T>>>

    // T is the maximum number of rounds
    var T : nat

    // N is the maximum number of processes in a single round
    var N : nat
  
    predicate valid()
      reads *
    {
			1 <= |pr_hist|
        && |pr_hist| <= T + 1
				&& |re_hist| <= T
				&& pr_init_correct <= pr_init
				&& pr_init == pr_hist[0]
    }

    predicate agreement<T(!new)>(re_hist : seq<set<Result<T>>>)
    {
      forall t, t', v, v' :: 0 <= t <= t' < |re_hist| && (v, D) in re_hist[t] && (v', D) in re_hist[t'] ==> v == v'
    }

    predicate unanimity<T(!new)>(pr_init_correct : set<T>, re_hist : seq<set<Result<T>>>)
    {
      forall v :: unanimous(pr_init_correct, v) ==>
        forall t, v' :: 0 <= t < |re_hist| && (v', D) in re_hist[t] ==> v == v'
    }

    predicate validity<T(!new)>(pr_init : set<T>, re_hist : seq<set<Result<T>>>)
    {
      forall t, v :: 0 <= t < |re_hist| && (v, D) in re_hist[t] ==> v in pr_init
    }

    constructor(pr_init' : set<T>, pr_init_correct' : set<T>, max_rounds : nat, max_processes : nat)
			requires pr_init_correct' <= pr_init'
      ensures valid()
    {
			pr_init := pr_init';
			pr_init_correct := pr_init_correct';
      pr_hist := [pr_init'];
      re_hist := [];
      T := max_rounds;
      N := max_processes;
    }  

    /* update_proposals(re, pr_i) is a set of proposed values taken from the results in re, whose values must come from pr_i. The set of new proposals is a subset of pr_i. */
    method update_proposals(re : set<Result<T>>, ghost pr_i : set<T>) returns (pr : set<T>)
      requires (forall v, s :: (v, s) in re ==> v in pr_i)
      ensures forall p :: p in pr ==> p in pr_i
      ensures forall p :: p in pr ==> (exists s :: (p, s) in re)
    {
      pr := {};
      var i := 0;
      var j := |re|;
      while i < j
        invariant (forall p :: p in pr ==> (exists s :: (p, s) in re))
        decreases j - i
      {
        var r :| r in re;
        pr := pr + {r.0};
        i := i + 1;
      }
    }

    lemma decision_lemma(T : nat, t : nat, t' : nat, v : T)
      requires |re_hist| == T  && |pr_hist| == T + 1
      requires 0 <= t < t' <= T
      requires (v, D) in re_hist[t]
      requires forall t, p :: 0 < t < T + 1 && p in pr_hist[t] ==> (exists s :: (p, s) in re_hist[t-1])
      requires forall t, v :: 0 <= t < T && (v, D) in re_hist[t] ==> (forall v', s | (v', s) in re_hist[t] :: v' == v)
      requires forall t, v :: 0 <= t < T && unanimous(pr_hist[t], v) ==> (forall v', s :: (v', s) in re_hist[t] ==> v' == v && s == D)
      ensures unanimous(pr_hist[t'], v)
    {
      if (t' == t + 1)
      {
        assert unanimous(pr_hist[t+1], v);
      }
      else
      {
        decision_lemma(T, t, t'-1, v);
      }
    }

		lemma unanimous_proposals_stable(T : nat, t : nat, t' : nat, v : T)
			requires |re_hist| == T && |pr_hist| == T + 1
			requires 0 <= t <= t' <= T
			requires unanimous(pr_hist[t], v)
			requires forall t :: 0 <= t < T ==> single_round_validity(pr_hist[t], re_hist[t])
			requires forall t, p :: 0 < t < T + 1 && p in pr_hist[t] ==> (exists s :: (p, s) in re_hist[t - 1])
			ensures unanimous(pr_hist[t'], v)
			decreases t' - t
		{
			if (t == t') {
				
			}
			else if (t == t' - 1) {
				
			} else {
				unanimous_proposals_stable(T, t, t' - 1, v);
			}
		}
  
    method main() 
      requires valid()
			requires |re_hist| == 0 && |pr_hist| == 1
      modifies this
      ensures valid()
      ensures agreement(re_hist)
      ensures unanimity(pr_init_correct, re_hist)
      ensures validity(pr_init, re_hist)
    {
			if (T > 0) {

				// execute first round outside of the loop - easier to prove unanimity this way

				var pr := pr_init;
				var pr_correct := pr_init_correct;
				var N' :| 0 <= N' <= N;
				var re := SingleRound.step_all(pr, pr_correct, N');
				var pr_1 := update_proposals(re, pr_init);
				re_hist := [re];
				pr_hist := pr_hist[..1] + [pr_1];
				
				var t := 1;
				while t < T
					invariant 1 <= t <= T
					invariant valid()
					invariant |re_hist| == t && |pr_hist| == t + 1
					// proposals come from initial proposals
					invariant forall t', p :: 0 <= t' <= t && t' < T && p in pr_hist[t'] ==> p in pr_init
					// proposals come from last round's values
					invariant forall t', p :: 0 < t' < t + 1 && p in pr_hist[t'] ==> (exists s :: (p, s) in re_hist[t' - 1])
					// single-round agreement
					invariant forall t' :: 0 <= t' < t ==> single_round_agreement(re_hist[t'])
					// single-round unanimity
					invariant forall t' :: 0 <= t' < t ==> single_round_unanimity(pr_hist[t'], re_hist[t'])
					// single-round validity
					invariant forall t' :: 0 <= t' < t ==> single_round_validity(pr_hist[t'], re_hist[t'])
					// if all correct processes have same initial proposal, then results of first round are unanimous
					invariant single_round_correct_unanimous_proposals(pr_init_correct, re_hist[0])
					modifies this
					decreases T - t
				{
					var pr := pr_hist[t];
					var N' :| 0 <= N' <= N;
					var pr_correct := pr;
					var re := SingleRound.step_all(pr, pr_correct, N');
					var pr_n := update_proposals(re, pr_init);
					re_hist := re_hist[..t] + [re];
					pr_hist := pr_hist[..t+1] + [pr_n];
					t := t + 1;
				}
				forall t, v, s | 0 <= t < T && (v, s) in re_hist[t]
					ensures v in pr_init
				{
					assert v in pr_hist[t];
					assert v in pr_init;
				}
				forall t, t', v | 0 <= t < t' <= T && (v, D) in re_hist[t]
					ensures unanimous(pr_hist[t'], v)
				{
					decision_lemma(T, t, t', v);
				}
				forall t, v, v' | unanimous(pr_init_correct, v) && 0 <= t < T && (v', D) in re_hist[t]
					ensures v' == v
				{
					if (t == 0) {
						
					} else {
						assert unanimous(pr_hist[1], v);
						unanimous_proposals_stable(T, 1, t, v);
					}
				}
			}
    }
  }
}

  
  
