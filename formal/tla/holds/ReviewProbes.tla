---------------------------- MODULE ReviewProbes ----------------------------
(* Reviewer probes on the T2 extension; nothing here changes the spec.      *)
EXTENDS AbsenceConnectorHolds

\* every state with no successor is quiescent with no pending hold
StuckOK == (~ENABLED NextH) => (Quiescent /\ NoPending)
\* sanity: must fail at the first terminal state
StuckSanity == ENABLED NextH
\* witness: two holds pending at once
WitTwoHolds == ~(Cardinality(holds) >= 2)
\* witness: two closed release units in one incarnation
WitTwoReleasesOneInc ==
  ~(\E r1, r2 \in 1..Len(rhist) : r1 < r2 /\ IsRUnit(Applied, r1) /\ IsRUnit(Applied, r2)
                                 /\ rhist[r1].inc = rhist[r2].inc)
\* witness: two holds pending at once, or two closed release units in one incarnation
WitMulti == WitTwoHolds /\ WitTwoReleasesOneInc
\* witness: two holds pending after a crash, at least one restored from the earlier incarnation
WitTwoHoldsAfterCrash ==
  ~(crashes = 1 /\ Cardinality(holds) >= 2 /\ \E hd \in holds : hist[hd.ex].inc = 0)
=============================================================================
