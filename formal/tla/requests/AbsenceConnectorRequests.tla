------------------------ MODULE AbsenceConnectorRequests ------------------------
(***************************************************************************)
(* An extension of the frozen core model AbsenceConnector.tla (sha256      *)
(* 4cbeac5962889914159a388f736422187cd1af51f75f4384401cbe44ebed9156) with   *)
(* the repair request verify-keys-absent (5.4), the drift process and its   *)
(* contract (5.5), the end-of-pass bounds hand-off (5.3), the end-of-pass   *)
(* key-list reads for candidates above the tail-read limit (5.6), and       *)
(* liveness under weak fairness.  For TLC.  Bounded evidence, never proof.  *)
(*                                                                         *)
(* CONSTRUCTION.  The module EXTENDS the core; the core file is not copied  *)
(* and not edited.  Every core action is used verbatim inside a wrapper     *)
(* that adds conjuncts only (no core conjunct is removed or replaced):      *)
(*  CWrite      = Write /\ rs # "close"  (writes do not interleave inside a *)
(*                request close block, the core's own reduction for close   *)
(*                blocks) /\ Grow /\ UNCHANGED new vars                     *)
(*  CStartPass  = StartPass /\ UNCHANGED new vars                           *)
(*  CWriteLW    = WriteLW /\ (rs = "none", the paper's serialization; under *)
(*                Interleave rs # "close") /\ UNCHANGED new vars            *)
(*  CQuery      = Query /\ rs # "close" (commutes with the entries of a     *)
(*                close block) /\ UNCHANGED new vars                        *)
(*  CWriteHW    = WriteHW /\ rs # "close" (close blocks never interleave)   *)
(*                /\ Grow /\ UNCHANGED new vars                             *)
(*  CEmitClose, CConsume = the core action /\ Grow /\ UNCHANGED new vars    *)
(*  CCrash(c), CCrashEarly(a) = the core action /\ ReqRestore: the request  *)
(*                part of the committed context is restored beside the      *)
(*                core's                                                    *)
(* Grow appends the in-memory request context (CtxNow) to outx for every    *)
(* item the core action appends to out, so outx[i] is the request part of   *)
(* out[i].ctx (the core's MkCtx cannot carry it without an edit).  With     *)
(* MaxCrashes = 0 no crash reads it and outx is not kept (dead state).      *)
(* RNext lists the core's disjuncts first, in the core's order, then the     *)
(* new actions.  With every new feature off (MaxReqs = 0, HandOff = "off",  *)
(* EndReads and every new mutation FALSE) the new variables are constant,  *)
(* every added guard holds, no new action is enabled, and the transition    *)
(* relation is the core's: the regression runs (prefix X_) reproduce the   *)
(* core's generated and distinct state counts and depths exactly, the       *)
(* mutation runs at -workers 1 included.                                    *)
(*                                                                         *)
(* Paper: 5.3 absence events ("Head, tail, and bounds hand-off", "Cost and *)
(* restarts"), 5.4 the request verify-keys-absent, 5.5 the drift process   *)
(* and its contract, 5.6 the tail-read limit and the visibility rule ("the *)
(* bracketed key-list read ... applies the same rule with its own window"),*)
(* 6 the baseline (the ordering condition), 8.  Theories: OA, OAR, OAC,    *)
(* OAI as in the core's header; OAI = Orphan_Absence_Interleaved.thy,      *)
(* OAC = Orphan_Absence_Composition.thy.                                    *)
(*                                                                         *)
(* MAPPING: spec object -> paper -> Isabelle                               *)
(*                                                                         *)
(*  Submit(K), reqs        5.5 the drift process: any key set, live keys   *)
(*                         included, at any step; its only output is the   *)
(*                         request (never a sink write, never a stream     *)
(*                         record).  reqs is the durable signal channel    *)
(*                         -> no counterpart (the theories take the        *)
(*                         request's units as given)                       *)
(*  rq, rs, rcur, rplan    5.4 "processes requested keys in bounded        *)
(*                         batches": the pending keys and the batch in     *)
(*                         flight                                          *)
(*  ReqLW, ReqQuery,       5.4 "queries those specific keys at the source  *)
(*  ReqHW, rhist[j]        between a fresh low and high watermark of its   *)
(*                         own"  -> OA absence_assertion_contract: a unit  *)
(*                         u_dom = the batch's keys the query did not      *)
(*                         return (without TrueGap), u_lo = lw, u_hi = hw, *)
(*                         u_refresh = None; the read coordinate qpos is   *)
(*                         OAI/OAC rc k (each batch its own coordinate)    *)
(*  ReqHW: chg, plan       5.4 "an absence event for every requested key   *)
(*                         that was neither returned by the query nor      *)
(*                         changed inside the watermark window"; 5.1       *)
(*                         changed keys; 5.6 the visibility rule with the  *)
(*                         read's own window  -> OA svl_ok2 with           *)
(*                         lists_absent (OAI/OAC: R.absent_untouched u     *)
(*                         subseteq svl2 u)                                *)
(*  ReqEmit, "rabs" items  5.3 absence events at the read's close, one     *)
(*                         entry per step  -> OAI R.closes_at (close       *)
(*                         entries at u_hi); OAC R.emission                *)
(*  ReqLW guard            5.4 "one bracketed read per batch serialized    *)
(*                         with ongoing chunk reads so their watermark     *)
(*                         windows never overlap"; Interleave = TRUE drops *)
(*                         it (the windows may overlap; OAI assumes        *)
(*                         nothing about them)                             *)
(*  outx, cmtx,            5.3 "retains any candidate keys submitted via a *)
(*  ReqRestore             signal request until their bracketed read       *)
(*                         completes"; R1 for batches  -> no counterpart:  *)
(*                         the theories have no restart with requests      *)
(*                         (EXTENSION)                                     *)
(*  HandOffStep, ho, hob,  5.3 the bounds hand-off: the pass's lowest      *)
(*  PaperBounds            returned key and highest returned key at or     *)
(*                         below the recorded maximum (or that maximum),   *)
(*                         empty for an empty table; the handler requests  *)
(*                         every key outside them (a superset of any       *)
(*                         sink's keys there, harmless: the request        *)
(*                         confirms at the source; the sink is quantified  *)
(*                         per key, not state)  -> no counterpart          *)
(*                         (EXTENSION); its request is an OAC/OAI R        *)
(*  EndReadsStep,          5.6 "checks any candidate keys in that          *)
(*  EndCands, erc          remaining tail using bracketed key-list reads   *)
(*                         at the end of the pass": the connector's own    *)
(*                         key-list reads of the supplier's candidates     *)
(*                         above the last returned key, served in batches  *)
(*                         like a request (not a signal: R14)  -> as the   *)
(*                         request's units                                 *)
(*  DriftCheck,            MUTATION (d), 6 "No position in the stream":    *)
(*  DriftDelete            the out-of-band delete                          *)
(*  Fairness, LSpec        liveness: weak fairness of every connector      *)
(*                         step, of request service, of the hand-off and   *)
(*                         end-of-pass reads (connector steps) and of the  *)
(*                         drift process  -> no counterpart (the theories  *)
(*                         speak about the sink after a finite stream)     *)
(*                                                                         *)
(* INVARIANTS AND PROPERTIES: invariant -> paper -> Isabelle counterpart   *)
(*                                                                         *)
(*  RTypeOK               the core's TypeOK with the request watermarks    *)
(*                        and "rabs" items admitted, plus the alignment of *)
(*                        outx with out and the exclusion of two close     *)
(*                        blocks; no counterpart                           *)
(*  CloseEntryTrue        (core operator, unchanged) now over chunk AND    *)
(*                        request entries, each at its own tag  -> OAI     *)
(*                        listed_entry_honest / inter_item_honest          *)
(*  SinkValueExisted      (core operator, unchanged), every state          *)
(*  RequestSafe           5.4 "a wrong or malicious request cannot delete  *)
(*                        a live row": every request entry is an absence   *)
(*                        that holds at its own position (the request      *)
(*                        half of CloseEntryTrue)  -> OAI                  *)
(*                        listed_entry_honest for R's units                *)
(*  RQuiescentSafe        8 safety with a request  -> OAI                  *)
(*                        pass_with_request_safe (_any), OAC               *)
(*                        pass_then_read_safe, over the contracts' scope:  *)
(*                        the chunk units' and the request units' domains  *)
(*                        (CScope \cup RCScope).  With a crash, or with    *)
(*                        two request units over one key: EXTENSION        *)
(*  RQuiescentConverges   8 convergence with a request  -> OAI             *)
(*                        pass_with_request_converges (_any), OAC         *)
(*                        pass_then_read_converges, OA absent_replay: over *)
(*                        the pass's claimed scope and the requested-and-  *)
(*                        confirmed keys (RCScope: requested, not returned *)
(*                        by the batch's query), the cover premise counting *)
(*                        request entries.  A consequence of the safety    *)
(*                        disjunction on the contracts' scope, as in the   *)
(*                        theories; operational on the claimed keys       *)
(*                        outside them                                     *)
(*  ReqCovers             5.4/5.5: once nothing is left to do, every       *)
(*                        requested key absent at the source ends absent   *)
(*                        at the sink from any initial value  -> the       *)
(*                        conclusion of OAI request_in_pass_converges and  *)
(*                        OAC request_after_pass_converges on the          *)
(*                        requested keys (their sc2_abs, lists_absent and  *)
(*                        asked premises met by construction, checked     *)
(*                        operationally); with a crash: EXTENSION          *)
(*  ReqServedAtQuiescence the safety form of RequestEventuallyServed:      *)
(*                        once nothing is left to do, every key submitted  *)
(*                        by the drift process or the handler (a signal)  *)
(*                        had a batch read that started after its          *)
(*                        submission; no counterpart (EXTENSION)           *)
(*  HandOffCovers         5.3 "Outside the key bounds that the pass        *)
(*                        publishes at its end, the bounds hand-off ...    *)
(*                        also finds such orphans": once nothing is left   *)
(*                        to do after a hand-off, every key outside the    *)
(*                        bounds AS THE PAPER DEFINES THEM (PaperBounds,   *)
(*                        computed from the pass's lineage, not the        *)
(*                        published value), absent at the source and with  *)
(*                        no log event since the pass started, ends absent *)
(*                        from any initial value; no counterpart           *)
(*                        (EXTENSION)                                      *)
(*  EndReadCovers         5.6: once nothing is left to do and the pass     *)
(*                        stopped at the tail-read limit, every candidate  *)
(*                        above the last returned key that is absent at    *)
(*                        the source ends absent from any initial value;   *)
(*                        as ReqCovers                                     *)
(*  BoundsOK              bookkeeping: the published bounds are the        *)
(*                        paper's (the mutation HiAtTail violates it; its  *)
(*                        consequence is checked without it)              *)
(*  TilingOK, ScopeBridge (core operators, unchanged): the chunk tiling   *)
(*                        and the pass's claimed coverage are untouched by *)
(*                        requests                                         *)
(*  RLocaleAssumptions    the bridge (see below)                           *)
(*  RequestEventually-    liveness: every key submitted by the drift       *)
(*  Served                process or the handler eventually has a batch    *)
(*                        read that started after its submission emit its  *)
(*                        whole close block                                *)
(*  EventuallyConverged   liveness: eventually and forever after, for     *)
(*                        every key and every initial sink value covered   *)
(*                        by a pass statement (PassCov: the claimed scope *)
(*                        with the core's cover premise over the chunk     *)
(*                        entries), a request (ReqCov: a requested key     *)
(*                        absent at the source), the hand-off (HOCov) or   *)
(*                        the end-of-pass reads (ERCov), the sink's replay *)
(*                        equals the source                                *)
(*  Both liveness properties are checked under LSpec = RSpec /\ Fairness:   *)
(*  weak fairness of StartPass, WriteLW, Query, WriteHW, EmitClose,         *)
(*  Consume (the connector), of ReqLW, ReqQuery, ReqHW, ReqEmit (request    *)
(*  service), of HandOffStep and EndReadsStep (connector steps), and of     *)
(*  Submit (the drift process: it keeps submitting until its bound).  No    *)
(*  fairness for Write and Crash: the environment may stop at any step,     *)
(*  and the bounds make writes and crashes finitely many.  The state graph  *)
(*  is finite and acyclic, so every fair behavior ends stuttering in a      *)
(*  state where no fair action is enabled; the properties are checked at    *)
(*  those states and on the way there.                                      *)
(*                                                                         *)
(* THE BRIDGE (RLocaleAssumptions), each conjunct and the clause it         *)
(* transcribes:                                                             *)
(*  RStreamShape   the core's StreamShape with request entries: per part,  *)
(*                 tag order, every data event from the part's start to its *)
(*                 crash coordinate exactly once and exact, every close     *)
(*                 entry (chunk or request) of the part's incarnation at    *)
(*                 its unit's u_hi.  With no crash this is the premise of  *)
(*                 OAI pass_with_request_safe_any/_converges_any: T_sorted  *)
(*                 and T_set (the stream carries the items of inter_t, in  *)
(*                 position order, whatever the tie order)                 *)
(*  UnitOK, O1OK,  (core operators, unchanged) P: capture_contract and     *)
(*  RestartOK      svl_ok2 for the chunk units, s0lo; one crash: the core's *)
(*                 pass_restart reading for the pass                       *)
(*  RUnitOK(j)     R: capture_contract for the request unit j (OA           *)
(*                 absence_assertion_contract): s0lo2 (s0 <= u_lo),         *)
(*                 R.bracket_lo_hi, R.bracket_hi_f (frontier the consumer's *)
(*                 position), R.O2_honest (every domain key absent at some  *)
(*                 coordinate of the bracket); R.svl_ok2 (listed keys in    *)
(*                 the domain, absent and untouched, distinct, entries =    *)
(*                 u_refresh = None at u_hi); lists_absent (a fully         *)
(*                 delivered batch lists every absent untouched key of its  *)
(*                 domain), the premise of OAI pass_with_listing_request_   *)
(*                 converges / request_in_pass_converges and OAC            *)
(*                 pass_then_request_converges / request_after_pass_        *)
(*                 converges                                               *)
(*  RO1OK          R.O1_disjoint for the request units of one incarnation, *)
(*                 asserted when no key was submitted twice (dbl FALSE).   *)
(*                 Two submissions of one key can give two units that both *)
(*                 list it: no single capture contract R holds them, and   *)
(*                 the theories compose ONE pass with ONE request contract  *)
(*                 (OAI) or one later read (OAC).  Those behaviors, and    *)
(*                 every behavior with a crash and a request, are checked  *)
(*                 per unit only; their composition is an EXTENSION with   *)
(*                 operational evidence (RQuiescentSafe, RQuiescent-       *)
(*                 Converges, ReqCovers checked directly)                  *)
(*  CompOK         OAC pass_then_read, for a crash-free behavior whose      *)
(*                 request units all open at or after the pass's last close *)
(*                 F1: f1_le_f2, s0f1, P.bracket_hi_f at F1; f1_le_lo2 is   *)
(*                 the antecedent; RStreamShape splits the stream at F1    *)
(*                 into P.emission s0..F1 and R.emission F1..frontier      *)
(* So, with no crash and no key submitted twice, every state's stream is an *)
(* instance of pass_with_request with f1 = the consumer's position (the     *)
(* request during or after the pass), and also of pass_then_read when every *)
(* request unit opens after the pass's last close.  Coverage premises       *)
(* (sc2_abs, asked, cover) are the antecedents of the convergence checks,   *)
(* not locale assumptions.                                                  *)
(*                                                                         *)
(* READINGS OF THE PAPER'S TEXT (named ambiguities; R1 to R5 are the       *)
(* core's):                                                                 *)
(*  R6  Batches.  The text fixes a bound, not a policy: a batch is any      *)
(*      nonempty set of at most BatchSize pending keys, chosen freely, so   *)
(*      keys of two requests may share a batch (this over-approximates any  *)
(*      batching policy, FIFO or per request).                              *)
(*  R7  Repeated keys.  A key submitted while pending is merged with the    *)
(*      pending one (the next read of it answers both); a key submitted     *)
(*      while its batch is in flight is pending again and read by a later   *)
(*      batch (the read in flight started before the submission).           *)
(*  R8  Retention ("retains any candidate keys submitted via a signal       *)
(*      request until their bracketed read completes").  The pending keys,  *)
(*      the keys of the batch in flight included, ride in the offset        *)
(*      context with a signal offset; at a restart the connector takes the  *)
(*      committed pending keys and re-reads from the durable channel every  *)
(*      signal after the committed offset.  Mutation DropReqsOnRestart      *)
(*      drops them.                                                         *)
(*  R9  Completion.  A batch is complete only once its last absence event   *)
(*      is committed (R1 for batches): every earlier entry's context        *)
(*      reports its keys pending.  An empty plan completes in memory; its   *)
(*      completion is committed by the next item or a heartbeat (Crash      *)
(*      with c = -1), and a crash before re-reads the batch.  Mutation      *)
(*      ReqDoneAtFirst commits the completion with the first entry.         *)
(*  R10 The visibility rule for a key-list read ("applies the same rule     *)
(*      with its own window").  The changed keys are the keys with an event *)
(*      in the batch's window plus the keys of every pending transaction    *)
(*      its query did not see, the pending set taken as of the batch's own *)
(*      low watermark together with its window's transactions; a request    *)
(*      never prunes the shared pending set (chunk closes do, as in the     *)
(*      core).  In the serialized default this equals the shared set at the *)
(*      close; under Interleave a chunk close inside the request's window   *)
(*      can prune it, which is what mutation SharedPend reads.              *)
(*  R11 Serialization ("serialized with ongoing chunk reads so their        *)
(*      watermark windows never overlap").  Default: a batch starts only    *)
(*      with no chunk in flight and a chunk only with no batch in flight.   *)
(*      Interleave: the windows may overlap; the two close blocks still     *)
(*      never interleave and writes wait during either (sound: a close      *)
(*      block appends nothing to the log).                                  *)
(*  R12 The bounds.  Computed over the pass's completed lineage (chain),    *)
(*      from the raw pages (the keys the SELECT returned, changed or not).  *)
(*      "Empty bounds for an empty table" is read as: the pass returned no  *)
(*      key.  When keys were returned but none at or below the recorded     *)
(*      maximum, the upper bound is that maximum, and 0 encodes "no         *)
(*      maximum" (empty at the start), so the bounds then contain no key    *)
(*      and the handler requests every key (safe, and a superset).          *)
(*  R13 The hand-off ("at the end of a full pass").  HandOff = "complete":  *)
(*      after a completed pass only; "end": after either terminal phase,    *)
(*      the tail-limit stop included.  The handler's request is submitted   *)
(*      in the publishing step (sound: its keys are fixed by the bounds and *)
(*      its service can be delayed arbitrarily); the published flag rides   *)
(*      in the offset context, so a restart from a context before the       *)
(*      publication publishes again (a second, identical request).          *)
(*  R14 End-of-pass reads (5.6).  The supplier's candidate list is any key  *)
(*      set, loaded once and reloaded unchanged at a restart (5.3 "it       *)
(*      simply reloads the candidates"); whenever an incarnation's pass     *)
(*      ends at "limit" the connector reads the candidates above the last   *)
(*      returned key, in batches, the issued keys riding in the offset      *)
(*      context.  They are NOT signal requests and not retained: a restart  *)
(*      from a context before the limit resumes the pass, and if the        *)
(*      resumed pass completes, its open last range covers the tail and no  *)
(*      end reads are issued.  (A first version owed these keys like a      *)
(*      signal; its green E2 run failed ReqServedAtQuiescence on exactly    *)
(*      that behavior, see the report.)                                     *)
(*  R15 Requests before the pass starts are not modelled: the connector is  *)
(*      not consuming in the core's "pre" phase; a request submitted then   *)
(*      is served after StartPass, which is a request submitted at the pass *)
(*      start (the drift's choice is free).                                 *)
(*  R16 The drift process's contract is structural: Submit is its only      *)
(*      action.  Mutation (d) gives it the Section 6 baseline's direct      *)
(*      delete, as an item appended to the stream when it decides.         *)
(*                                                                         *)
(* MUTATIONS (each expected to fail; the configurations named M):         *)
(*  (a) ReqDropChanged     a request's absence events ignore the changed   *)
(*      keys: a key inserted inside the batch's window is certified absent  *)
(*      (RequestSafe, CloseEntryTrue)                                       *)
(*  (b) HiAtTail           the published upper bound is the highest key    *)
(*      the tail reads returned: an orphan between the recorded maximum and *)
(*      rows inserted during the pass is inside the published bounds and is *)
(*      never requested (HandOffCovers: convergence, not safety)           *)
(*  (c) DropReqsOnRestart  requested keys dropped at a restart: the request *)
(*      is never served (ReqServedAtQuiescence, ReqCovers,                  *)
(*      RequestEventuallyServed: convergence, not safety)                  *)
(*  (d) DriftDirectDelete  the drift process deletes directly, decided on a *)
(*      source check at an earlier position: a live row re-created in       *)
(*      between is deleted (NoLiveRowDeleted, CloseEntryTrue): the Section *)
(*      6 baseline's unpositioned delete                                   *)
(*  (e) SharedPend         under Interleave, a request reads the shared     *)
(*      pending set at its close, which a chunk close inside its window has *)
(*      pruned: an insert the request's query did not see is certified     *)
(*      absent (RequestSafe).  Serialized, SharedPend is the same relation  *)
(*      (green control).  Not in the brief's list; it shows what R10 asks   *)
(*      the implementation to track.                                        *)
(*  (f) ReqDoneAtFirst     a batch's completion rides on its first absence  *)
(*      event (R9 broken, as the core's ProgressAtFirst breaks R1): a crash *)
(*      committed there drops the rest of the batch (ReqCovers: convergence)*)
(*                                                                         *)
(* SOUND REDUCTIONS (beyond the core's four):                              *)
(*  - a submission happens only with no read in flight (cs = rs = "none"): *)
(*    a submission made during a read is the same as one made just after   *)
(*    it (serialized: no batch can start before the read ends) or just     *)
(*    before it (Interleave: the batch may still start inside the chunk's  *)
(*    window, since ReqLW can be delayed); the only state it touches       *)
(*    before a batch starts is the pending set, whose restored value at a  *)
(*    crash is the same either way (context or re-read signal);            *)
(*  - with MaxCrashes = 0 the per-item request contexts are not kept (no   *)
(*    step reads them);                                                     *)
(*  - writes, chunk queries and the other read's watermarks do not         *)
(*    interleave inside a request close block (it appends nothing to the  *)
(*    log; as the core argues for chunk close blocks);                      *)
(*  - the handler's request is submitted in the publishing step (R13).     *)
(*                                                                         *)
(* Termination by construction (CHECK_DEADLOCK FALSE): on top of the       *)
(* core's bounds, submissions are bounded by MaxReqs, the hand-off and the *)
(* end-of-pass reads by one per incarnation, and every batch removes at    *)
(* least one key from the finite pending set.  The state graph is acyclic. *)
(*                                                                         *)
(* OUT OF THIS SLICE: held absence events and the safety cap (T2),         *)
(* table-level changes, transport partitions, the sidecar handler of 5.4   *)
(* (its request is a request; its scan is not modelled, as the sink is not *)
(* state), a lagging signal consumer (equivalent to a later submission),   *)
(* two crashes with requests, row-versioned sinks.                         *)
(***************************************************************************)
EXTENDS AbsenceConnector

CONSTANTS
  MaxReqs,           \* bound on the drift process's requests (and on its direct deletes, mutation d)
  BatchSize,         \* the request batch size
  Interleave,        \* TRUE: request windows may overlap chunk windows (the variant)
  HandOff,           \* "off" | "complete" (after a completed pass) | "end" (after either terminal phase)
  EndReads,          \* TRUE: the end-of-pass key-list reads for candidates above the tail limit (5.6)
  ReqDropChanged,    \* mutation (a): a request's absence events ignore the changed keys
  HiAtTail,          \* mutation (b): the published upper bound is the highest key the tail returned
  DropReqsOnRestart, \* mutation (c): requested keys are dropped at a restart
  DriftDirectDelete, \* mutation (d): the drift process deletes directly, an unpositioned delete
  SharedPend,        \* mutation (e): a request reads the shared pending set at its close
  ReqDoneAtFirst     \* mutation (f): a batch's completion rides on its first absence event

ASSUME MaxReqs \in Nat /\ BatchSize \in Nat /\ BatchSize >= 1
ASSUME HandOff \in {"off", "complete", "end"}
ASSUME \A b \in {Interleave, EndReads, ReqDropChanged, HiAtTail, DropReqsOnRestart,
                 DriftDirectDelete, SharedPend, ReqDoneAtFirst} : b \in BOOLEAN

VARIABLES
  reqs,          \* the signal channel: the submitted key sets, durable, in submission order
  rq,            \* the connector's pending requested keys, not in flight (in memory)
  rs, rcur,      \* the batch in flight: step ("none", "lw", "q", "close"), its rhist index
  rplan,         \* entries of the batch's close block still to emit
  outx,          \* the request part of the offset context of each item of out (aligned)
  cmtx,          \* the request part of the committed context
  ho, eq,        \* in memory: bounds published, end-of-pass reads issued
  rhist,         \* ghost: request batch executions
  hob,           \* ghost: the bounds as published
  owed, asked,   \* ghost: keys owed a read since their submission; keys ever requested
  dbl, ndr,      \* ghost: some key submitted twice; drift requests made
  erc,           \* the supplier's candidate list for the end-of-pass reads, once loaded (<<L>>)
  dck, ndd       \* mutation (d): keys the drift checked absent, direct deletes made

reqv  == <<reqs, rq, rs, rcur, rplan, outx, cmtx, ho, eq, rhist, hob, owed, asked, dbl, ndr,
           erc, dck, ndd>>
allvars == <<vars, reqv>>

-----------------------------------------------------------------------------
(* Helpers *)

Min(S) == CHOOSE m \in S : \A y \in S : m <= y
Bk == IF rcur = 0 THEN {} ELSE rhist[rcur].keys          \* the keys of the batch in flight
\* the request part of the in-memory context: the batch in flight is still pending (R1)
CtxNow  == [rq |-> rq \cup Bk, ns |-> Len(reqs), ho |-> ho, eq |-> eq]
CtxZero == [rq |-> {}, ns |-> 0, ho |-> FALSE, eq |-> FALSE]
\* every item a core action appends carries the in-memory request context
\* (kept only when a crash can read it: with MaxCrashes = 0 the contexts are dead state)
Grow == outx' = IF MaxCrashes = 0 THEN outx
                ELSE outx \o [i \in 1..(Len(out') - Len(out)) |-> CtxNow]
KeepR == UNCHANGED <<reqs, rq, rs, rcur, rplan, cmtx, ho, eq, rhist, hob, owed, asked, dbl,
                     ndr, erc, dck, ndd>>
\* the keys ever issued as end-of-pass reads (over-approximated by the loaded list)
EndIssued == IF erc = <<>> THEN {} ELSE erc[1]
\* a submission while a batch is in flight: its keys of that batch are owed a later read
MarkRe(K) == IF rcur = 0 THEN rhist ELSE [rhist EXCEPT ![rcur].re = @ \cup (K \cap Bk)]

\* the pass's returned keys over its completed lineage, and the published bounds
RetK == UNION {hist[chain[i]].page : i \in 1..Len(chain)}
EmptyB == [e |-> TRUE, lo |-> 0, hi |-> 0]
PaperBounds ==
  IF RetK = {} THEN EmptyB
  ELSE [e |-> FALSE, lo |-> Min(RetK),
        hi |-> IF {k \in RetK : k <= rmax} = {} THEN rmax ELSE Max({k \in RetK : k <= rmax})]
TailBounds == IF RetK = {} THEN EmptyB ELSE [e |-> FALSE, lo |-> Min(RetK), hi |-> Max(RetK)]
Outside(bd, k) == bd.e \/ k < bd.lo \/ k > bd.hi
HandOffPhases == IF HandOff = "end" THEN {"complete", "limit"} ELSE {"complete"}

-----------------------------------------------------------------------------
(* The core's actions, wrapped.  Each core action is used verbatim; the conjuncts added
   are the serialization guards, the request context of the items it appends, and
   UNCHANGED for the new variables. *)

RInit ==
  /\ Init
  /\ reqs = <<>> /\ rq = {} /\ rs = "none" /\ rcur = 0 /\ rplan = {}
  /\ outx = <<>> /\ cmtx = CtxZero /\ ho = FALSE /\ eq = FALSE
  /\ rhist = <<>> /\ hob = EmptyB /\ owed = {} /\ asked = {} /\ dbl = FALSE /\ ndr = 0
  /\ erc = <<>> /\ dck = {} /\ ndd = 0

CWrite(k, v)  == Write(k, v) /\ rs # "close" /\ Grow /\ KeepR
CStartPass(V) == StartPass(V) /\ UNCHANGED outx /\ KeepR
CWriteLW      == WriteLW /\ (IF Interleave THEN rs # "close" ELSE rs = "none")
                 /\ UNCHANGED outx /\ KeepR
CQuery(V)     == Query(V) /\ rs # "close" /\ UNCHANGED outx /\ KeepR
CWriteHW      == WriteHW /\ rs # "close" /\ Grow /\ KeepR
CEmitClose(k) == EmitClose(k) /\ Grow /\ KeepR
CConsume      == Consume /\ Grow /\ KeepR

(* The request part of a restart: the committed request context, plus every signal
   submitted after its signal offset, re-read from the channel.  The batch in flight is
   discarded; its keys are pending in the committed context (R1). *)
ReqRestore(nx) ==
  /\ cmtx' = nx
  /\ outx' = <<>>
  /\ rq' = IF DropReqsOnRestart THEN {}
           ELSE nx.rq \cup UNION {reqs[i] : i \in (nx.ns + 1)..Len(reqs)}
  /\ rs' = "none" /\ rcur' = 0 /\ rplan' = {}
  /\ ho' = nx.ho /\ eq' = nx.eq
  /\ UNCHANGED <<reqs, rhist, hob, owed, asked, dbl, ndr, erc, dck, ndd>>

CCrash(c) ==
  /\ Crash(c)
  /\ ReqRestore(CASE c = -1 -> CtxNow [] c = 0 -> cmtx [] OTHER -> outx[c])
CCrashEarly(a) == CrashEarly(a) /\ ReqRestore(CtxNow)

-----------------------------------------------------------------------------
(* The drift process: submits a request for any nonempty key set, live keys included,
   at any step once the connector runs.  It never writes to the sink or the stream. *)
Submit(K) ==
  /\ pst # "pre" /\ ndr < MaxReqs /\ K # {}
  /\ rs = "none" /\ cs = "none"   \* reduction: no read in flight (see SOUND REDUCTIONS)
  /\ reqs' = Append(reqs, K)
  /\ rq' = rq \cup K
  /\ ndr' = ndr + 1
  /\ owed' = owed \cup K /\ asked' = asked \cup K
  /\ dbl' = (dbl \/ K \cap (asked \cup EndIssued) # {})
  /\ rhist' = MarkRe(K)
  /\ UNCHANGED vars
  /\ UNCHANGED <<rs, rcur, rplan, outx, cmtx, ho, eq, hob, erc, dck, ndd>>

(* The request's bracketed key-list read, one batch: a low watermark, the key-list
   query, a high watermark, then the absence events one entry per step.  Serialized with
   the chunk reads (no chunk in flight) unless Interleave. *)
ReqLW(B) ==
  /\ rs = "none" /\ pst # "pre" /\ cpos = Len(log)
  /\ IF Interleave THEN cs # "close" ELSE cs = "none"
  /\ B \subseteq rq /\ B # {} /\ Cardinality(B) <= BatchSize
  /\ log' = Append(log, [t |-> "rlw", k |-> 0, v |-> NULL, x |-> Len(rhist) + 1])
  /\ cpos' = Len(log) + 1
  /\ rhist' = Append(rhist,
       [inc |-> crashes, lw |-> Len(log) + 1, hw |-> 0, qpos |-> 0, keys |-> B,
        page |-> {}, inv |-> {}, pd |-> pend, cl |-> FALSE, plan |-> {}, re |-> {}])
  /\ rcur' = Len(rhist) + 1 /\ rs' = "lw" /\ rq' = rq \ B
  /\ UNCHANGED <<vis, nW, progv, chkv, pend, out, topic, committed, crashes, s0, hist,
                 chain, crashrec>>
  /\ UNCHANGED <<reqs, rplan, outx, cmtx, ho, eq, hob, owed, asked, dbl, ndr, erc, dck, ndd>>

ReqQuery(V) ==
  /\ rs = "lw" /\ cs # "close"
  /\ V \subseteq (1..nW) \ vis
  /\ vis' = vis \cup V
  /\ VisRule = "wait" =>
       \A p \in 1..(rhist[rcur].lw - 1) : IsData(p) => log[p].x \in vis'
  /\ rhist' = [rhist EXCEPT ![rcur].qpos = Len(log),
                 ![rcur].page = {k \in rhist[rcur].keys : SnapK(vis', k) # NULL},
                 ![rcur].inv = (1..nW) \ vis']
  /\ rs' = "q"
  /\ UNCHANGED <<log, nW, progv, chkv, cpos, pend, out, topic, committed, crashes, s0,
                 hist, chain, crashrec>>
  /\ UNCHANGED <<reqs, rq, rcur, rplan, outx, cmtx, ho, eq, hob, owed, asked, dbl, ndr,
                 erc, dck, ndd>>

(* The high watermark is the batch's close: the changed keys are the keys with an event
   in the window plus the visibility rule's keys, from the pending set as of the batch's
   low watermark and the window's own transactions (its own view; mutation SharedPend:
   the shared set at the close).  The plan: every requested key neither returned nor
   changed.  An empty plan completes the batch at once. *)
ReqHW ==
  /\ rs = "q" /\ cpos = Len(log) /\ cs # "close"
  /\ log' = Append(log, [t |-> "rhw", k |-> 0, v |-> NULL, x |-> rcur])
  /\ cpos' = Len(log) + 1
  /\ LET p     == Len(log) + 1
         h     == rhist[rcur]
         winTx == {log[q].x : q \in {q \in (h.lw + 1)..Len(log) : IsData(q)}}
         wk    == {TxKey(x) : x \in winTx}
         notSeen(x) == x \in h.inv \/ TxPos(x) > h.qpos
         pv    == IF SharedPend THEN pend ELSE h.pd \cup winTx
         gp    == CASE VisRule \in {"changed", "chunk"} ->
                         {TxKey(x) : x \in {y \in pv : notSeen(y)}}
                    [] VisRule = "window" ->
                         {TxKey(x) : x \in {y \in winTx : notSeen(y)}}
                    [] OTHER -> {}
         chg   == (wk \cup gp) \cap h.keys
         plan  == (h.keys \ h.page) \ (IF ReqDropChanged THEN {} ELSE chg)
     IN /\ rhist' = [rhist EXCEPT ![rcur].hw = p, ![rcur].cl = TRUE, ![rcur].plan = plan]
        /\ IF plan = {}
           THEN /\ rs' = "none" /\ rcur' = 0 /\ rplan' = {}
                /\ owed' = owed \ (h.keys \ h.re)
           ELSE /\ rs' = "close" /\ rplan' = plan
                /\ UNCHANGED <<rcur, owed>>
  /\ UNCHANGED <<vis, nW, progv, chkv, pend, out, topic, committed, crashes, s0, hist,
                 chain, crashrec>>
  /\ UNCHANGED <<reqs, rq, outx, cmtx, ho, eq, hob, asked, dbl, ndr, erc, dck, ndd>>

(* One absence event per step.  Its offset context counts the batch complete only on the
   last entry (R1): before it, the batch's keys are still pending in the context.  The
   mutation ReqDoneAtFirst counts it complete from the first entry on. *)
ReqEmit(k) ==
  /\ rs = "close" /\ k \in rplan
  /\ LET h      == rhist[rcur]
         isLast == rplan = {k}
         done   == isLast \/ ReqDoneAtFirst
         it     == [kd |-> "rabs", key |-> k, v |-> NULL, tag |-> h.hw, ex |-> -rcur,
                    ctx |-> MkCtx(h.hw, Prog, PCtx(pend))]
     IN /\ out' = Append(out, it)
        /\ outx' = IF MaxCrashes = 0 THEN outx
                   ELSE Append(outx, [rq |-> IF done THEN rq ELSE rq \cup h.keys,
                                      ns |-> Len(reqs), ho |-> ho, eq |-> eq])
        /\ rplan' = rplan \ {k}
        /\ IF isLast
           THEN /\ rs' = "none" /\ rcur' = 0 /\ owed' = owed \ (h.keys \ h.re)
           ELSE UNCHANGED <<rs, rcur, owed>>
  /\ UNCHANGED <<srcv, progv, chkv, cpos, pend, topic, committed, crashes, s0, hist,
                 chain, crashrec>>
  /\ UNCHANGED <<reqs, rq, cmtx, ho, eq, rhist, hob, asked, dbl, ndr, erc, dck, ndd>>

(* The bounds hand-off: at the end of the pass the connector publishes the bounds; the
   handler submits a request for every key outside them (a superset of any sink's keys
   there).  The flag rides in the offset context; the request is a durable signal. *)
HandOffStep ==
  /\ HandOff # "off" /\ ~ho /\ cs = "none" /\ pst \in HandOffPhases
  /\ LET bd == IF HiAtTail THEN TailBounds ELSE PaperBounds
         K  == {k \in Keys : Outside(bd, k)}
     IN /\ ho' = TRUE /\ hob' = bd
        /\ IF K = {}
           THEN UNCHANGED <<reqs, rq, owed, asked, dbl, rhist>>
           ELSE /\ reqs' = Append(reqs, K) /\ rq' = rq \cup K
                /\ owed' = owed \cup K /\ asked' = asked \cup K
                /\ dbl' = (dbl \/ K \cap (asked \cup EndIssued) # {})
                /\ rhist' = MarkRe(K)
  /\ UNCHANGED vars
  /\ UNCHANGED <<rs, rcur, rplan, outx, cmtx, eq, ndr, erc, dck, ndd>>

(* 5.6: a pass stopped at the tail-read limit checks its candidate keys above the last
   returned key with bracketed key-list reads, the connector's own key-list reads served
   like a request's batches.  The candidate list L is any key set, loaded once (lazily
   here: nothing reads it before); a restart reloads the same list (5.3 "it simply
   reloads the candidates") and the reads are issued again whenever an incarnation's
   pass ends at the limit.  They are not signal requests: they are not retained across
   a restart (a resumed pass that completes covers the tail with its open last range),
   so they are not owed (R14).  The issued keys ride in the offset context like the
   pending requested keys. *)
EndCands == IF erc = <<>> THEN {} ELSE {k \in erc[1] : k > lob}
EndReadsStep(Lc) ==
  /\ EndReads /\ ~eq /\ pst = "limit" /\ cs = "none"
  /\ IF erc = <<>> THEN Lc \subseteq Keys ELSE Lc = erc[1]
  /\ erc' = <<Lc>>
  /\ eq' = TRUE
  /\ LET C == {k \in Lc : k > lob}
     IN /\ rq' = rq \cup C
        /\ dbl' = (dbl \/ C \cap asked # {} \/ erc # <<>>)
  /\ UNCHANGED vars
  /\ UNCHANGED <<reqs, rs, rcur, rplan, outx, cmtx, ho, hob, owed, asked, ndr, rhist, dck,
                 ndd>>

(* MUTATION (d), the Section 6 baseline: the drift process checks the source at one
   position and deletes at the sink later, modelled as a delete item appended to the
   stream at the moment of that decision. *)
DriftCheck(k) ==
  /\ DriftDirectDelete /\ pst # "pre" /\ ndd < MaxReqs /\ k \notin dck
  /\ SrcK(Len(log), k) = NULL
  /\ dck' = dck \cup {k}
  /\ UNCHANGED vars
  /\ UNCHANGED <<reqs, rq, rs, rcur, rplan, outx, cmtx, ho, eq, rhist, hob, owed, asked,
                 dbl, ndr, erc, ndd>>
DriftDelete(k) ==
  /\ DriftDirectDelete /\ k \in dck /\ ndd < MaxReqs
  /\ cpos = Len(log) /\ cs # "close" /\ rs # "close"
  /\ out' = Append(out, [kd |-> "ddel", key |-> k, v |-> NULL, tag |-> Len(log), ex |-> 0,
                         ctx |-> MkCtx(cpos, Prog, PCtx(pend))])
  /\ outx' = IF MaxCrashes = 0 THEN outx ELSE Append(outx, CtxNow)
  /\ dck' = dck \ {k} /\ ndd' = ndd + 1
  /\ UNCHANGED <<srcv, progv, chkv, cpos, pend, topic, committed, crashes, s0, hist,
                 chain, crashrec>>
  /\ UNCHANGED <<reqs, rq, rs, rcur, rplan, cmtx, ho, eq, rhist, hob, owed, asked, dbl,
                 ndr, erc>>

RNext ==
  \/ \E k \in Keys, v \in Img : CWrite(k, v)
  \/ \E V \in SUBSET (1..MaxWrites) : CStartPass(V)
  \/ CWriteLW
  \/ \E V \in SUBSET (1..MaxWrites) : CQuery(V)
  \/ CWriteHW
  \/ \E k \in Keys : CEmitClose(k)
  \/ CConsume
  \/ \E c \in -1..Len(out) : CCrash(c)
  \/ \E a \in 0..Len(out) : CCrashEarly(a)
  \/ \E K \in SUBSET Keys : Submit(K)
  \/ \E B \in SUBSET Keys : ReqLW(B)
  \/ \E V \in SUBSET (1..MaxWrites) : ReqQuery(V)
  \/ ReqHW
  \/ \E k \in Keys : ReqEmit(k)
  \/ HandOffStep
  \/ \E Lc \in SUBSET Keys : EndReadsStep(Lc)
  \/ \E k \in Keys : DriftCheck(k)
  \/ \E k \in Keys : DriftDelete(k)

RSpec == RInit /\ [][RNext]_allvars

-----------------------------------------------------------------------------
(* Liveness: weak fairness of every connector step, of request service and of the drift
   process (and of the hand-off and the end-of-pass reads, connector steps).  Writes and
   crashes are not fair: the environment may stop at any time; the bounds make them
   finitely many. *)
Fairness ==
  /\ WF_allvars(\E V \in SUBSET (1..MaxWrites) : CStartPass(V))
  /\ WF_allvars(CWriteLW)
  /\ WF_allvars(\E V \in SUBSET (1..MaxWrites) : CQuery(V))
  /\ WF_allvars(CWriteHW)
  /\ WF_allvars(\E k \in Keys : CEmitClose(k))
  /\ WF_allvars(CConsume)
  /\ WF_allvars(\E B \in SUBSET Keys : ReqLW(B))
  /\ WF_allvars(\E V \in SUBSET (1..MaxWrites) : ReqQuery(V))
  /\ WF_allvars(ReqHW)
  /\ WF_allvars(\E k \in Keys : ReqEmit(k))
  /\ WF_allvars(HandOffStep)
  /\ WF_allvars(\E Lc \in SUBSET Keys : EndReadsStep(Lc))
  /\ WF_allvars(\E K \in SUBSET Keys : Submit(K))
LSpec == RSpec /\ Fairness
\* vacuity control: the same fairness without request service (ReqLW, ReqQuery, ReqHW,
\* ReqEmit); RequestEventuallyServed must then fail
FairnessNoServe ==
  /\ WF_allvars(\E V \in SUBSET (1..MaxWrites) : CStartPass(V))
  /\ WF_allvars(CWriteLW)
  /\ WF_allvars(\E V \in SUBSET (1..MaxWrites) : CQuery(V))
  /\ WF_allvars(CWriteHW)
  /\ WF_allvars(\E k \in Keys : CEmitClose(k))
  /\ WF_allvars(CConsume)
  /\ WF_allvars(HandOffStep)
  /\ WF_allvars(\E Lc \in SUBSET Keys : EndReadsStep(Lc))
  /\ WF_allvars(\E K \in SUBSET Keys : Submit(K))
LSpecNoServe == RSpec /\ FairnessNoServe

-----------------------------------------------------------------------------
(* Properties *)

ListedC(S, k) == \E i \in 1..Len(S) : S[i].kd \in {"row", "abs"} /\ S[i].key = k
RQuiescent == Quiescent /\ rs = "none"
HandOffDue == HandOff # "off" /\ pst \in HandOffPhases
EndReadsDue == EndReads /\ pst = "limit"
\* nothing left to do: the pass ended, no read in flight, no requested key pending, the
\* hand-off and the end-of-pass reads issued where due
FullQuiescent == RQuiescent /\ rq = {} /\ (HandOffDue => ho) /\ (EndReadsDue => eq)

\* the request units (the bridge): absence_assertion_contract instances
RDelIdx(S, j) == {i \in 1..Len(S) : S[i].ex = -j}
RDelivered(S, j) == {S[i].key : i \in RDelIdx(S, j)}
RFullyDel(S, j) == rhist[j].cl /\ RDelivered(S, j) = rhist[j].plan
RIsUnit(S, j) == rhist[j].cl /\ (RFullyDel(S, j) \/ RDelivered(S, j) # {})
RTrueGap(j) == {TxKey(x) : x \in {y \in rhist[j].inv : TxPos(y) < rhist[j].lw}}
\* the domain: the requested keys the query did not return, without the TrueGap keys
\* (as the core's Dom); a partly delivered block is the sub-unit of its delivered keys
RDom(S, j) == (IF RFullyDel(S, j) THEN rhist[j].keys \ rhist[j].page ELSE RDelivered(S, j))
              \ RTrueGap(j)
RNoWin(j, k) == \A p \in (rhist[j].lw + 1)..rhist[j].hw : ~(IsData(p) /\ log[p].k = k)
RCScope(S) == {k \in Keys : \E j \in 1..Len(rhist) : RIsUnit(S, j) /\ k \in RDom(S, j)}

RTypeOK ==
  /\ nW \in 0..MaxWrites /\ vis \subseteq 1..nW
  /\ \A p \in 1..Len(log) :
       \/ (log[p].t = "d" /\ log[p].k \in Keys /\ log[p].v \in Img /\ log[p].x \in 1..nW)
       \/ (log[p].t \in {"lw", "hw"} /\ log[p].x \in 1..Len(hist))
       \/ (log[p].t \in {"rlw", "rhw"} /\ log[p].x \in 1..Len(rhist))
  /\ pst \in {"pre", "main", "tail", "complete", "limit"}
  /\ lob \in 0..N /\ rmax \in 0..N /\ tcnt \in 0..TailLimit
  /\ cs \in {"none", "lw", "q", "hw", "close"}
  /\ cpos \in 0..Len(log) /\ pend \subseteq 1..nW
  /\ crashes \in 0..MaxCrashes /\ s0 \in 0..Len(log)
  /\ \A i \in 1..Len(Stream) :
       /\ Stream[i].kd \in {"ev", "row", "abs", "rabs"} /\ Stream[i].key \in Keys
       /\ Stream[i].v \in Img /\ Stream[i].tag \in 1..Len(log)
  /\ rs \in {"none", "lw", "q", "close"} /\ (rs = "none") = (rcur = 0)
  /\ rq \subseteq Keys /\ rplan \subseteq Keys /\ owed \subseteq Keys /\ asked \subseteq Keys
  /\ MaxCrashes > 0 => Len(outx) = Len(out)
  /\ ~(cs = "close" /\ rs = "close")
  /\ ~Interleave => (cs = "none" \/ rs = "none")

(* 5.4 "a wrong or malicious request cannot delete a live row": every request entry is
   an absence that holds at the source at its own position.  The request half of
   CloseEntryTrue (OAI listed_entry_honest for R's units). *)
RequestSafe ==
  LET S == Stream IN
  \A i \in 1..Len(S) : S[i].kd = "rabs" => SrcK(S[i].tag, S[i].key) = NULL

\* every delete item in the stream holds at its position (catches mutation d)
NoLiveRowDeleted ==
  LET S == Stream IN
  \A i \in 1..Len(S) : (S[i].kd # "ev" /\ S[i].v = NULL) => SrcK(S[i].tag, S[i].key) = NULL

(* OAI pass_with_request_safe (no crash), OAC pass_then_read_safe (a request after the
   pass), over the contracts' scope: the chunk units' domains and the request units'
   domains.  One crash, or two requests with overlapping domains: EXTENSION. *)
RQuiescentSafe ==
  RQuiescent =>
    LET S == Stream IN
    \A k \in CScope(S) \cup RCScope(S), d \in Img :
      LET r == ReplayK(d, k, S) IN
      \/ r = SrcK(Frontier, k)
      \/ (r = d /\ SrcK(Frontier, k) = NULL /\ ~Listed(S, k) /\ NoEvents(k))

(* OAI pass_with_request_converges, OAC pass_then_read_converges, OA absent_replay: over
   the pass's claimed scope and the request contracts' scope (the requested keys a batch
   read found absent), the cover premise widened to the requested-and-confirmed keys
   (Listed counts request entries). *)
RQuiescentConverges ==
  RQuiescent =>
    LET S == Stream IN
    \A k \in Scope \cup RCScope(S), d \in Img :
      ((d # NULL /\ SrcK(Frontier, k) = NULL /\ NoEvents(k)) => Listed(S, k))
        => ReplayK(d, k, S) = SrcK(Frontier, k)

(* The safety form of RequestEventuallyServed: once nothing is left to do, every
   submitted key had a batch read that started after its submission. *)
ReqServedAtQuiescence == FullQuiescent => owed = {}

(* 5.4/5.5 the request removes the orphans it names: once nothing is left to do, every
   requested key that is absent at the source ends absent at the sink, from any initial
   value.  The conclusion of OAC request_after_pass_converges and OAI
   request_in_pass_converges for the requested keys (their sc2_abs and lists_absent;
   checked operationally; with a crash an EXTENSION). *)
ReqCovers ==
  FullQuiescent =>
    LET S == Stream IN
    \A k \in asked :
      SrcK(Frontier, k) = NULL => \A d \in Img : ReplayK(d, k, S) = NULL

(* 5.3 the bounds hand-off: once nothing is left to do after a hand-off, every key outside
   the bounds as the paper defines them, absent at the source and with no log event since
   the pass started, ends absent at the sink from any initial value.  The bounds are the
   paper's, computed from the pass's lineage, not the published ones. *)
HandOffCovers ==
  (FullQuiescent /\ ho) =>
    LET S == Stream IN
    \A k \in Keys :
      (Outside(PaperBounds, k) /\ NoEvents(k) /\ SrcK(Frontier, k) = NULL)
        => \A d \in Img : ReplayK(d, k, S) = NULL

(* 5.6 the end-of-pass key-list reads: once nothing is left to do and the pass stopped at
   the tail-read limit, every candidate above the last returned key that is absent at the
   source ends absent at the sink from any initial value. *)
EndReadCovers ==
  (FullQuiescent /\ EndReads /\ pst = "limit") =>
    LET S == Stream IN
    \A k \in EndCands :
      SrcK(Frontier, k) = NULL => \A d \in Img : ReplayK(d, k, S) = NULL

\* bookkeeping: the published bounds are the paper's (mutation HiAtTail violates it)
BoundsOK == ho => hob = PaperBounds

-----------------------------------------------------------------------------
(* The bridge with requests *)

\* a close item belongs to its unit's incarnation and sits at its unit's high edge
CloseOf(it, i) ==
  CASE it.ex > 0 -> hist[it.ex].inc = i /\ it.tag = hist[it.ex].hw
    [] it.ex < 0 -> rhist[-it.ex].inc = i /\ it.tag = rhist[-it.ex].hw
    [] OTHER -> FALSE
RPartOK(i, S) ==
  LET a   == PartLo(i)
      b   == PartHi(i, S)
      idx == a..b
      evx == {x \in idx : S[x].kd = "ev"}
      top == PartEnd(i)
  IN /\ \A x \in a..(b - 1) : S[x].tag <= S[x + 1].tag
     /\ \A x \in idx : S[x].tag > PartStart(i) /\ S[x].tag <= top
     /\ {S[x].tag : x \in evx} = {p \in (PartStart(i) + 1)..top : IsData(p)}
     /\ Cardinality(evx) = Cardinality({S[x].tag : x \in evx})
     /\ \A x \in evx : S[x].key = log[S[x].tag].k /\ S[x].v = log[S[x].tag].v
     /\ \A x \in idx \ evx : CloseOf(S[x], i)
RStreamShape == LET S == Stream IN \A i \in 0..Len(crashrec) : RPartOK(i, S)

(* A request unit is the one-unit contract of absence_assertion_contract with the
   listing of svl_ok2. *)
RUnitOK(S, j) ==
  LET h == rhist[j]
      D == RDom(S, j)
      L == RDelivered(S, j)
  IN /\ s0 <= h.lw                                              \* s0lo2
     /\ h.lw < h.hw /\ h.hw <= Len(log)                         \* R.bracket_lo_hi, R.bracket_hi_f
     /\ \A k \in D : \E c \in h.lw..h.hw : SrcK(c, k) = NULL    \* R.O2_honest, refresh None
     /\ L \subseteq D                                           \* svl_ok2: listed in the domain
     /\ \A k \in L : RNoWin(j, k)                               \* svl_ok2: listed absent untouched
     /\ \A i \in RDelIdx(S, j) : S[i].v = NULL /\ S[i].tag = h.hw  \* entry = u_refresh at u_hi
     /\ Cardinality(RDelIdx(S, j)) = Cardinality(L)             \* svl_ok2: distinct
     /\ RFullyDel(S, j) => {k \in D : RNoWin(j, k)} \subseteq L \* lists_absent

\* R.O1_disjoint: within an incarnation, when no key was submitted twice
RO1OK(S) ==
  ~dbl =>
    \A j1, j2 \in 1..Len(rhist) :
      (j1 < j2 /\ RIsUnit(S, j1) /\ RIsUnit(S, j2) /\ rhist[j1].inc = rhist[j2].inc)
        => RDom(S, j1) \cap RDom(S, j2) = {}

(* pass_then_read (OAC), for a crash-free behavior whose request units all open at or
   after the pass's last close F1: f1_le_f2, P.bracket_hi_f at F1, s0f1; f1_le_lo2 is the
   antecedent.  Sortedness (RStreamShape) splits the stream at F1 into P's emission and
   R's emission from F1. *)
CompOK(S) ==
  (crashes = 0 /\ pst \in {"complete", "limit"} /\ cs = "none" /\ Len(chain) > 0 /\
   \A j \in 1..Len(rhist) : RIsUnit(S, j) => rhist[j].lw >= hist[chain[Len(chain)]].hw)
    => LET F1 == hist[chain[Len(chain)]].hw IN
       /\ F1 <= Len(log)
       /\ s0 <= F1
       /\ \A e \in 1..Len(hist) : IsUnit(S, e) => hist[e].hw <= F1

RLocaleAssumptions ==
  LET S == Stream IN
  /\ RStreamShape
  /\ \A e \in 1..Len(hist) : IsUnit(S, e) => UnitOK(S, e)
  /\ O1OK(S)
  /\ RestartOK(S)
  /\ \A j \in 1..Len(rhist) : RIsUnit(S, j) => RUnitOK(S, j)
  /\ RO1OK(S)
  /\ CompOK(S)

-----------------------------------------------------------------------------
(* Liveness properties (checked with LSpec) *)

RequestEventuallyServed == \A k \in Keys : [](k \in owed => <>(k \notin owed))

PassCov(k, d) ==
  /\ pst \in {"complete", "limit"} /\ k \in Scope
  /\ (d # NULL /\ SrcK(Len(log), k) = NULL /\ NoEvents(k)) => ListedC(Stream, k)
ReqCov(k) == k \in asked /\ SrcK(Len(log), k) = NULL
HOCov(k) == ho /\ Outside(PaperBounds, k) /\ NoEvents(k) /\ SrcK(Len(log), k) = NULL
ERCov(k) == EndReads /\ pst = "limit" /\ eq /\ k \in EndCands /\ SrcK(Len(log), k) = NULL
ConvCovered ==
  \A k \in Keys, d \in Img :
    (PassCov(k, d) \/ ReqCov(k) \/ HOCov(k) \/ ERCov(k))
      => ReplayK(d, k, Stream) = SrcK(Len(log), k)
EventuallyConverged == <>[]ConvCovered

-----------------------------------------------------------------------------
(* Witness probes, EXPECTED TO BE VIOLATED where their comment says. *)

\* a request batch confirmed an absence while the pass was still running
WitReqDuringPass ==
  ~(\E j \in 1..Len(rhist), e \in 1..Len(hist) :
       RDelivered(Stream, j) # {} /\ hist[e].cl /\ hist[e].lw > rhist[j].hw)
\* a requested live key: the query returned it and no event was emitted for it
WitReqLiveKey == ~(RQuiescent /\ \E j \in 1..Len(rhist) : rhist[j].cl /\ rhist[j].page # {})
ListedR(k) == \E i \in 1..Len(Stream) : Stream[i].kd = "rabs" /\ Stream[i].key = k
\* an orphan outside the pass's claimed scope removed by a request
WitReqRepairsOutside ==
  ~(FullQuiescent /\ \E k \in Keys \ Scope :
       NoEvents(k) /\ SrcK(Frontier, k) = NULL /\ ListedR(k))
\* a request window overlapping a chunk window (Interleave only)
WitReqWindowOverlap ==
  ~(\E e \in 1..Len(hist), j \in 1..Len(rhist) :
       hist[e].cl /\ rhist[j].cl /\ hist[e].lw < rhist[j].hw /\ rhist[j].lw < hist[e].hw)
\* a batch re-run after a crash
WitReqRerun ==
  ~(\E j1, j2 \in 1..Len(rhist) :
       j1 < j2 /\ rhist[j1].inc < rhist[j2].inc /\ rhist[j1].keys \cap rhist[j2].keys # {})
\* two request units confirm the same key
WitReqOverlap ==
  ~(\E j1, j2 \in 1..Len(rhist) :
       j1 < j2 /\ RIsUnit(Stream, j1) /\ RIsUnit(Stream, j2) /\
       RDom(Stream, j1) \cap RDom(Stream, j2) # {})
\* the hand-off's request removes an orphan outside the bounds
WitHandOffRepair ==
  ~(FullQuiescent /\ ho /\ \E k \in Keys :
       Outside(PaperBounds, k) /\ NoEvents(k) /\ SrcK(Frontier, k) = NULL /\ ListedR(k))
\* an end-of-pass key-list read confirms a candidate above the last returned key
WitEndRead ==
  ~(FullQuiescent /\ pst = "limit" /\ \E k \in Keys : k > lob /\ ListedR(k))
=============================================================================
