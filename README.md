# Verified Bosco
Formal models of [Bosco](https://link.springer.com/chapter/10.1007/978-3-540-87779-0_30) consensus protocol in Dafny. 

Authors: [Natalie Neamtu](https://nneamtu.github.io/), [Robbert van Renesse](https://www.cs.cornell.edu/home/rvr/).

We provide formal models at 3 levels of abstraction:
- `single-round`, a single round of the protocol (proves safety properties assuming crash failure model);
- `abstract`, an abstract protocol execution without processes (proves safety properties assuming crash failure model);
- `system`, a system with processes and a network interface (proves safety properties, and lemmas for proving some liveness properties, for both crash and Byzantine failure model).

## single-round
Model of a single round of the protocol execution.
Demonstrates that safety properties hold over all possible quorums (i.e., any possible set of proposals that a process could receive from a quorum)

## abstract
Model of protocol execution over arbitrary number of steps (i.e., rounds of the protocol). 
Processes are abstracted away to a set of proposals (inputs to the round) and results (outputs to the round). 
Reuses code from `single-round` to instantiate a set of processes and quorums to execute each round of the protocol.

## system
Models non-terminating execution of distributed system running the protocol as a sequence of atomic steps. 
Each of the processes and network are chosen to step in a non-deterministic order. 
Processes interface with the network by adding messages to their "outbox", which the network may deliver to the "inbox" of the corresponding recipient process.

Models crash tolerant, *weakly one-step* (Byzantine-fault tolerant), and *strongly one-step* (BFT) versions of the protocol. 
Demonstrates both safety properties as well as liveness properties that can be used to show that non-faulty processes will step infinitly often.
