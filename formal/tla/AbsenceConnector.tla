--------------------------- MODULE AbsenceConnector ---------------------------
(***************************************************************************)
(* The connector protocol of "Extending DBLog-Based Incremental Snapshots  *)
(* to Handle Orphan Rows in CDC Pipelines", Section 5, for the model       *)
(* checker TLC.  Bounded evidence, never proof.  The stream-level results  *)
(* are proved in Isabelle (session Orphan_Absence) for every history; this *)
(* model checks the operational protocol where the theories stop, and it   *)
(* checks on every behavior that the emitted stream meets the locale       *)
(* assumptions of those theories (the bridge: TLC checks the assumptions,  *)
(* the Isabelle theorem supplies the conclusion).                          *)
(*                                                                         *)
(* Paper sections: 2 the chunk read; 5.1 shared ground; 5.2 the chunk info *)
(* record; 5.3 absence events; 5.6 operational considerations; 8 what is   *)
(* formally verified.  Theory files: Orphan_Absence.thy (OA),              *)
(* Orphan_Absence_Restart.thy (OAR), Orphan_Absence_Tiling.thy (OAT),      *)
(* Orphan_Absence_Composition.thy (OAC), Orphan_Absence_Interleaved.thy    *)
(* (OAI), the core's Cut_Theorem.thy and Merge_Disciplines.thy (core).     *)
(*                                                                         *)
(* MAPPING: spec object -> paper -> Isabelle                               *)
(*                                                                         *)
(*  log, positions 1..Len(log)  2: committed changes in log order; the     *)
(*      watermarks are log entries  -> core: event list L, coordinates as  *)
(*      prefix lengths (den), pfx; watermark entries are not data          *)
(*  SrcK(n, k)            source value after the length-n prefix           *)
(*                        -> core: state_after sigma0 (pfx c) k            *)
(*  Write                 committed single-row insert, update, delete     *)
(*                        -> core: S-LOG, S-IMG (full row images)          *)
(*  vis, Query(V),        5.6 chunk query visibility, the PostgreSQL gap   *)
(*  StartPass(V), row     -> no counterpart: the theories assume the       *)
(*  lock in Write         visibility (README, "not covered").  EXTENSION.  *)
(*  WriteLW, Query,       2 the bracketed chunk read  -> cunit u_lo, u_hi, *)
(*  WriteHW, hist[e]      u_refresh; the read at qpos inside the bracket   *)
(*                        is the O2 coordinate (core O2_honest)            *)
(*  window (lw, hw]       2 the window  -> core: win lo hi (half-open)     *)
(*  wk, gp, chg           5.1 changed keys (window events), 5.6 the        *)
(*                        visibility rule (keys of transactions logged     *)
(*                        before the close that the query did not see)     *)
(*                        -> OA: evs_for k (win lo hi) # []; except_keys;  *)
(*                        gp has no counterpart (EXTENSION)                *)
(*  page, hi, nx          5.2 covering the key space: short-page rule,     *)
(*                        recorded maximum, tail reads with a limit        *)
(*                        -> OAT: page, bpage, bounded_scan, tail_scan,    *)
(*                        bounded_pass                                     *)
(*  plan, EmitClose       5.3 emission of rows and absence events at the   *)
(*                        close, one entry per step; a free candidate set  *)
(*                        (per-key absence events), or Dense: every absent *)
(*                        unchanged key, one entry per step, which is the  *)
(*                        per-key rendering of the chunk info record's key *)
(*                        set (a crash can cut it)  -> core: close_block   *)
(*                        svl u, closes_at, emission_t; OA: svl_ok2        *)
(*  Record (in WriteHW)   5.2 the chunk info record itself: the whole      *)
(*                        close block (the record's absence set and the    *)
(*                        surviving rows) is one atomic item with one      *)
(*                        offset context, delivered whole or not at all    *)
(*                        -> OA: record_enum, chunk_record_converges       *)
(*  out, topic, Stream    the output stream as the sink sees it  -> core:  *)
(*                        emission; OAR: restart_stream = cut_t ++ resumed *)
(*  committed, MkCtx      8 "resumes from its committed offset" with the   *)
(*                        pass context  -> OAR: cmt                        *)
(*  Crash, Consume,       5.6 restarts; 8 one restart  -> OAR: crash, the  *)
(*  Restart               re-delivered segment [cmt, crash), P2 = the      *)
(*                        re-executed chunks.  EXTENSIONS: two crashes     *)
(*                        (operational evidence only, no pass_restart      *)
(*                        reading), a crash inside a close block (OAR      *)
(*                        argues it in prose only), a crash during the     *)
(*                        re-delivery.  CrashEarly, ResetTailOnRestart and *)
(*                        ReRecordMax are mutations                        *)
(*  ReplayK(d, k, S)      the sink applies the stream in order from any    *)
(*                        initial value d  -> core: state_after D0 S k;    *)
(*                        OA: replay_per_key (so quantifying the initial  *)
(*                        sink per key is exact, the sink is not state)    *)
(*                                                                         *)
(* INVARIANTS: invariant -> paper -> Isabelle counterpart                  *)
(*                                                                         *)
(*  TypeOK                state-space sanity, no counterpart               *)
(*  CloseEntryTrue        5.1: a statement is true at the read's close     *)
(*                        -> OAI: listed_entry_honest (the close entry     *)
(*                        carries the source value at u_hi), the close     *)
(*                        half of OAR emission_item_honest                 *)
(*  SinkValueExisted      no paper statement; weaker than the above: every *)
(*                        sink value is the initial one or an earlier      *)
(*                        source value, at every state                     *)
(*  QuiescentSafe         8 safety  -> OA: absent_replay_safe with         *)
(*                        absent_replay_cut (no crash); OAR: restart_safe  *)
(*                        (one crash); two crashes: EXTENSION.  Over the   *)
(*                        contracts' scope CScope (the delivered units'    *)
(*                        domains, without TrueGap), as the theorems state *)
(*                        it                                               *)
(*  QuiescentConverges    8 convergence under coverage  -> OA:             *)
(*                        absent_replay (per key), self_stabilization;     *)
(*                        OAR: restart_converges (its cover premise).      *)
(*                        Over the claimed scope Scope, which is stronger  *)
(*                        than the theorems (keys outside every contract,  *)
(*                        see ScopeBridge)                                 *)
(*  RecordConverges       5.2 chunk info record, 8 "when applying chunk    *)
(*                        info records"  -> OA: chunk_record_converges,    *)
(*                        svl2_exists_covering (Dense or Record)           *)
(*  DeliveredRecordAbsence  5.2 the sink finishes a record's deletes       *)
(*                        "including across restarts"  -> OA: record_enum, *)
(*                        chunk_record_converges: once a record is in the  *)
(*                        stream, its absent unchanged keys stay deleted   *)
(*                        unless a later event changes them (Dense or      *)
(*                        Record; Record holds it, Dense fails it across   *)
(*                        a crash, which is why Dense is not the record)   *)
(*  TilingOK              5.2  -> OAT: range_rule, range_exact (with the  *)
(*                        query's snapshot as the read's source state),    *)
(*                        ranges_first_open_below, ranges_consecutive,     *)
(*                        ranges_disjoint, union_on_completion,            *)
(*                        completed_last_open_above,                       *)
(*                        union_on_limit_last_returned; across restarts    *)
(*                        (overlap only across incarnations, the recorded  *)
(*                        maximum and the tail count kept): EXTENSION.     *)
(*                        TailCountOK is exercised only at TailLimit >= 2  *)
(*                        with a crash (at 1 the first full tail page ends *)
(*                        the pass, so no restart can matter): it holds    *)
(*                        there and fails under ResetTailOnRestart.        *)
(*                        MaxPersisted holds by construction (the context  *)
(*                        restores the maximum); it is a bookkeeping check *)
(*                        that ReRecordMax violates, and the consequences  *)
(*                        of re-recording are checked without it           *)
(*  CScope, Dom           the contracts' scope: a unit's domain is its     *)
(*                        range without TrueGap (see the comment at Dom:   *)
(*                        the connector's rule makes those keys changed,   *)
(*                        the unit states nothing about them, and they get *)
(*                        their own log events, OAC emission_out_of_scope) *)
(*  LocaleAssumptions     the bridge  -> core capture_contract for each    *)
(*                        incarnation's part: O1_disjoint, bracket_lo_hi,  *)
(*                        bracket_hi_f, O2_honest (O1_cover holds by the   *)
(*                        scope's definition); OA: svl_ok2 (distinct,      *)
(*                        survivors listed, listed keys survivors or       *)
(*                        absent untouched, entry = u_refresh) and the     *)
(*                        premise s0lo; core emission_t and OAR            *)
(*                        restart_stream = cut_t ++ resumed_t (each part   *)
(*                        in tag order, every data event from its start    *)
(*                        to its crash coordinate exactly once: OAR        *)
(*                        cut_complete, resumed_complete; close entries at *)
(*                        u_hi); OAR pass_restart, for a behavior with     *)
(*                        exactly one crash only: s0cmt, cmt_le_crash,     *)
(*                        crash_le_f1 (the delivered units of incarnation  *)
(*                        0 close by the crash, pass_restart_after_        *)
(*                        frontier), crash_le_f2, crash_le_lo2; reexec is  *)
(*                        vacuous for that P1, and its operational content *)
(*                        (the undelivered parts are re-read) is           *)
(*                        ScopeBridge's clause.  With two                  *)
(*                        crashes the bridge checks the per-incarnation    *)
(*                        contracts only: no reading of the whole stream   *)
(*                        is one pass_restart instance (the incarnations   *)
(*                        after crash 1 can re-execute the same range, and *)
(*                        the stream steps back at each part boundary), so *)
(*                        the composition across two crashes is an         *)
(*                        EXTENSION.  A unit's domain is its range         *)
(*                        minus TrueGap (keys whose last transaction       *)
(*                        before the low watermark the query did not see,  *)
(*                        for which O2 can fail); a partly delivered block *)
(*                        is the sub-unit of its delivered keys (the       *)
(*                        sub-contract of OAR's prose).  The crash         *)
(*                        coordinate is the consumer's position.           *)
(*  ScopeBridge           5.2 the coverage the pass claims  -> core        *)
(*                        O1_cover of the contracts' scopes, with OAC      *)
(*                        emission_out_of_scope for a key outside them     *)
(*                        (with two crashes, a check of the per-           *)
(*                        incarnation scopes, not a theorem's premise)     *)
(*  Wit*                  witness probes, EXPECTED TO BE VIOLATED          *)
(*                                                                         *)
(* OUT OF THIS SLICE: held absence events under a cap, requests            *)
(* (verify-keys-absent), the drift process, the bounds hand-off, the       *)
(* end-of-pass key-list reads for candidates above the tail limit (5.6),   *)
(* liveness, transport partitions, compaction, multi-row transactions,     *)
(* primary-key updates (5.1 marks the old and the new key changed; here a  *)
(* key change is two single-key transactions, a delete and an insert, not  *)
(* one atomic change), table-level changes, a commit before the pass       *)
(* started, TailLimit = 0 (the Tiling theory's T = 0 case, which the       *)
(* design does not use: ASSUME TailLimit >= 1).                            *)
(*                                                                         *)
(* READINGS OF THE PAPER'S TEXT (named ambiguities):                       *)
(*  R1 A chunk counts as complete only once the last entry of its close    *)
(*     block is committed: the offset context of every earlier entry      *)
(*     reports the chunk open (8: "re-executes every chunk that had not    *)
(*     completed"; 5.6: an open chunk is discarded and re-read).           *)
(*     ProgressAtFirst is the mutation that persists it with the first.    *)
(*     An empty close block has no item: its completion is committed by    *)
(*     the next item or by a heartbeat commit of the in-memory context     *)
(*     (Crash with c = -1); a crash before either re-executes the chunk,   *)
(*     which delivered nothing.                                            *)
(*  R2 The recorded maximum, the phase, the tail count and the lower bound *)
(*     of the next chunk ride in the committed context (mutations:         *)
(*     ResetTailOnRestart, ReRecordMax).                                   *)
(*  R3 The visibility rule covers every transaction logged before the      *)
(*     close, including those decoded before the pass started; the         *)
(*     pending set rides in the committed context (PersistPend).  The      *)
(*     waiting variant ("wait") is a guard on Query.                       *)
(*  R4 A commit before the pass started is not modeled (StartPass          *)
(*     commits), as in OAR.                                                *)
(*  R5 Candidate keys (free lists): each chunk chooses any subset of its   *)
(*     absent unchanged keys, which over-approximates the paper's          *)
(*     pass-level list (a supplier's list at the pass start, reloaded at a *)
(*     restart): that list met with a chunk's range is one such subset, so *)
(*     every pass-level behavior is a behavior here; the safety checks     *)
(*     quantify over all behaviors, and convergence is checked under the   *)
(*     cover premise evaluated on what was actually listed.                *)
(*                                                                         *)
(* SOUND REDUCTIONS (each removes interleavings, not behaviors, up to      *)
(* watermark entries that no later step reads):                            *)
(*  - visibility is folded into its readers (Query, StartPass, the row     *)
(*    lock of Write); no property reads vis (TypeOK checks its range);     *)
(*  - the consumer is eager outside re-delivery: an append is consumed in  *)
(*    the step that makes it; a crash with a lagging consumer is an        *)
(*    earlier crash followed by the same writes; writes wait while the     *)
(*    re-delivery runs, which loses nothing, since a write appends at the  *)
(*    log end and commutes with the re-delivery steps;                     *)
(*  - acknowledgements and offset commits are resolved at the crash: a    *)
(*    lost unacknowledged item is an earlier crash; the commit point is   *)
(*    any delivered item; the sink's view of every prefix of the durable   *)
(*    stream is checked as the stream grows (one item per step, or one     *)
(*    whole record in Record mode);                                        *)
(*  - writes do not interleave inside a close block (they are logged       *)
(*    after the high watermark either way).                                *)
(*                                                                         *)
(* Termination by construction (CHECK_DEADLOCK FALSE): writes, crashes,    *)
(* and chunks per incarnation are bounded (the main loop advances its      *)
(* lower bound, the tail reads stop at the limit).                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
  N,                \* keys are 1..N, ordered by <
  Vals,             \* row values (a symmetry set of model values)
  NULL,             \* absence: the image of a delete, the refresh of an absent key
  MaxWrites,        \* bound on committed source transactions
  ChunkSize,        \* the chunk limit n
  TailLimit,        \* the tail-read limit T
  MaxCrashes,       \* bound on connector crashes
  VisGap,           \* TRUE: a logged transaction may stay invisible to new snapshots
  PrePassSettled,   \* TRUE: every transaction logged before the pass is visible at its start
  VisRule,          \* "changed" | "wait" | "off" | "window" | "chunk"
  PersistPend,      \* TRUE: the pending-visibility set rides in the committed context
  Dense,            \* TRUE: every absent unchanged key of a range is listed, one entry per step
                    \*       (the per-key rendering of the chunk info record's key set)
  Record,           \* TRUE: the chunk info record itself: the whole close block is one
                    \*       atomic stream item, delivered whole or not at all
  ProgressAtFirst,  \* mutation: chunk progress persisted with the first close entry
  FullPageOpen,     \* mutation: a full tail page left open above
  DropChanged,      \* mutation: the changed keys dropped from the absence computation
  CommitBeforeAck,  \* mutation: a crash may commit the in-memory context while the last
                    \*       emitted items are lost (the offset committed before the ack)
  ResetTailOnRestart, \* mutation: the tail count is reset to 0 at a restart
  ReRecordMax       \* mutation: the maximum key is queried again at a restart

ASSUME N \in Nat /\ N >= 1
ASSUME NULL \notin Vals
ASSUME MaxWrites \in Nat /\ MaxCrashes \in Nat
ASSUME TailLimit \in Nat /\ TailLimit >= 1   \* the design runs one or more tail reads
ASSUME ChunkSize \in Nat /\ ChunkSize >= 1
ASSUME VisRule \in {"changed", "wait", "off", "window", "chunk"}
ASSUME \A b \in {VisGap, PrePassSettled, PersistPend, Dense, Record,
                 ProgressAtFirst, FullPageOpen, DropChanged, CommitBeforeAck,
                 ResetTailOnRestart, ReRecordMax} : b \in BOOLEAN
ASSUME ~(Dense /\ Record)

Keys == 1..N
OPEN == N + 1                                \* an upper bound open above
Img  == Vals \cup {NULL}
Tracks == VisRule \in {"changed", "chunk"}   \* the connector keeps a pending set

VARIABLES
  log, vis, nW,                 \* source: committed log, visible transactions, write count
  pst, lob, rmax, tcnt, nch,    \* pass progress: status, lower bound, recorded max, tail reads, chunks done
  cs, cur, cplan,               \* chunk in flight: step, its history index, close entries still to emit
  cpos, pend,                   \* consumer position, pending-visibility set
  out, topic, committed,        \* this incarnation's items, durable items of earlier ones, committed context
  crashes, s0,                  \* crash count, consumption start of the pass
  hist, chain, crashrec         \* ghost: chunk executions, completed lineage, crash records

srcv  == <<log, vis, nW>>
progv == <<pst, lob, rmax, tcnt, nch>>
chkv  == <<cs, cur, cplan>>
vars  == <<log, vis, nW, pst, lob, rmax, tcnt, nch, cs, cur, cplan, cpos, pend,
           out, topic, committed, crashes, s0, hist, chain, crashrec>>

-----------------------------------------------------------------------------
(* Helpers *)

Max(S) == CHOOSE m \in S : \A y \in S : y <= m
IsData(p) == log[p].t = "d"
\* the source value of key k after the length-n prefix of the log
SrcK(n, k) ==
  LET ps == {p \in 1..n : IsData(p) /\ log[p].k = k}
  IN IF ps = {} THEN NULL ELSE log[Max(ps)].v
\* the value of key k in a snapshot that sees exactly the transactions in S
SnapK(S, k) ==
  LET ps == {p \in 1..Len(log) : IsData(p) /\ log[p].k = k /\ log[p].x \in S}
  IN IF ps = {} THEN NULL ELSE log[Max(ps)].v
TxPos(x) == CHOOSE p \in 1..Len(log) : IsData(p) /\ log[p].x = x
TxKey(x) == log[TxPos(x)].k
Smallest(n, A) == {a \in A : Cardinality({b \in A : b < a}) < n}
\* a finite set of keys as a sequence in key order
SeqOf(A) == [i \in 1..Cardinality(A) |-> CHOOSE a \in A : Cardinality({b \in A : b < a}) = i - 1]
\* the maximum key present in a snapshot that sees the transactions in S (0: none)
MaxPresent(S) == LET pres == {k \in Keys : SnapK(S, k) # NULL}
                 IN IF pres = {} THEN 0 ELSE Max(pres)
RangeKeys(lo, hi) == {k \in Keys : lo < k /\ k <= hi}

Prog == [lob |-> lob, pst |-> pst, tcnt |-> tcnt, nch |-> nch]
PCtx(pd) == IF PersistPend THEN pd ELSE {}
MkCtx(pos, pr, pd) ==
  [pos |-> pos, lob |-> pr.lob, rmax |-> rmax, pst |-> pr.pst,
   tcnt |-> pr.tcnt, nch |-> pr.nch, pend |-> pd]
EvItem(p, pd) ==
  [kd |-> "ev", key |-> log[p].k, v |-> log[p].v, tag |-> p, ex |-> 0,
   ctx |-> MkCtx(p, Prog, PCtx(pd))]
Strip(it) == [kd |-> it.kd, key |-> it.key, v |-> it.v, tag |-> it.tag, ex |-> it.ex]
NullRow == [k \in Keys |-> NULL]
NoNext == [lob |-> 0, pst |-> "none", tcnt |-> 0]

-----------------------------------------------------------------------------
(* Actions *)

Init ==
  /\ log = <<>> /\ vis = {} /\ nW = 0
  /\ pst = "pre" /\ lob = 0 /\ rmax = 0 /\ tcnt = 0 /\ nch = 0
  /\ cs = "none" /\ cur = 0 /\ cplan = {}
  /\ cpos = 0 /\ pend = {}
  /\ out = <<>> /\ topic = <<>>
  /\ committed = [pos |-> 0, lob |-> 0, rmax |-> 0, pst |-> "pre",
                  tcnt |-> 0, nch |-> 0, pend |-> {}]
  /\ crashes = 0 /\ s0 = 0
  /\ hist = <<>> /\ chain = <<>> /\ crashrec = <<>>

(* A committed single-row transaction on key k: an insert, an update or a
   delete (v = NULL).  Row locks: it commits only after every earlier
   transaction on k has ended, so those are visible by now; their
   visibility is folded into this step.  Once the pass runs, the connector
   consumes the new log event in the same step and emits it at its own
   position. *)
Write(k, v) ==
  /\ nW < MaxWrites
  /\ cs # "close"
  /\ pst = "pre" \/ cpos = Len(log)
  /\ v # SrcK(Len(log), k)
  /\ LET prev == {log[p].x : p \in {p \in 1..Len(log) : IsData(p) /\ log[p].k = k}}
     IN vis' = vis \cup prev \cup (IF VisGap THEN {} ELSE {nW + 1})
  /\ log' = Append(log, [t |-> "d", k |-> k, v |-> v, x |-> nW + 1])
  /\ nW' = nW + 1
  /\ IF pst = "pre"
     THEN UNCHANGED <<cpos, pend, out>>
     ELSE LET p  == Len(log) + 1
              pd == IF Tracks THEN pend \cup {nW + 1} ELSE pend
          IN /\ cpos' = p
             /\ pend' = pd
             /\ out' = Append(out, [kd |-> "ev", key |-> k, v |-> v, tag |-> p, ex |-> 0,
                                    ctx |-> MkCtx(p, Prog, PCtx(pd))])
  /\ UNCHANGED <<progv, chkv, topic, committed, crashes, s0, hist, chain, crashrec>>

(* The pass starts.  The transactions V become visible first.  The maximum
   key is read once in a snapshot, the consumer is at the log end, and the
   start is committed. *)
StartPass(V) ==
  /\ pst = "pre"
  /\ V \subseteq (1..nW) \ vis
  /\ PrePassSettled => vis \cup V = 1..nW
  /\ vis' = vis \cup V
  /\ LET m  == MaxPresent(vis')
         p0 == IF m = 0 THEN (IF TailLimit = 0 THEN "limit" ELSE "tail") ELSE "main"
         pd == IF Tracks THEN (1..nW) \ vis' ELSE {}
     IN /\ rmax' = m /\ pst' = p0 /\ lob' = 0 /\ tcnt' = 0 /\ nch' = 0
        /\ s0' = Len(log) /\ cpos' = Len(log) /\ pend' = pd
        /\ committed' = [pos |-> Len(log), lob |-> 0, rmax |-> m, pst |-> p0,
                         tcnt |-> 0, nch |-> 0, pend |-> PCtx(pd)]
  /\ UNCHANGED <<log, nW, chkv, out, topic, crashes, hist, chain, crashrec>>

(* The low watermark, consumed at once (watermarks are not emitted). *)
WriteLW ==
  /\ cs = "none" /\ pst \in {"main", "tail"}
  /\ cpos = Len(log)
  /\ log' = Append(log, [t |-> "lw", k |-> 0, v |-> NULL, x |-> Len(hist) + 1])
  /\ cpos' = Len(log) + 1
  /\ hist' = Append(hist,
       [inc |-> crashes, lw |-> Len(log) + 1, hw |-> 0, qpos |-> 0,
        lo |-> lob, hi |-> 0, tail |-> (pst = "tail"), rm |-> rmax,
        page |-> {}, val |-> NullRow, inv |-> {}, nxt |-> NoNext,
        cl |-> FALSE, plan |-> {}])
  /\ cur' = Len(hist) + 1
  /\ cs' = "lw"
  /\ UNCHANGED <<vis, nW, progv, cplan, pend, out, topic, committed,
                 crashes, s0, chain, crashrec>>

(* The chunk query.  The transactions V become visible first, then the
   query sees exactly the visible transactions.  Under the waiting variant
   it runs only once every transaction logged before the low watermark is
   visible.  The page is the n smallest present keys above the lower bound,
   bounded by the recorded maximum in the main loop; the range and the next
   progress follow the short-page rule. *)
Query(V) ==
  /\ cs = "lw"
  /\ V \subseteq (1..nW) \ vis
  /\ vis' = vis \cup V
  /\ VisRule = "wait" =>
       \A p \in 1..(hist[cur].lw - 1) : IsData(p) => log[p].x \in vis'
  /\ LET cand == {k \in Keys : k > lob /\ SnapK(vis', k) # NULL /\
                                (pst = "main" => k <= rmax)}
         pg   == Smallest(ChunkSize, cand)
         full == Cardinality(pg) = ChunkSize
         hi   == IF full THEN (IF pst = "tail" /\ FullPageOpen THEN OPEN ELSE Max(pg))
                 ELSE (IF pst = "main" THEN rmax ELSE OPEN)
         nx   == IF pst = "main"
                 THEN (IF full THEN [lob |-> Max(pg), pst |-> "main", tcnt |-> tcnt]
                       ELSE [lob |-> rmax,
                             pst |-> IF TailLimit = 0 THEN "limit" ELSE "tail",
                             tcnt |-> tcnt])
                 ELSE (IF ~full \/ FullPageOpen
                       THEN [lob |-> lob, pst |-> "complete", tcnt |-> tcnt + 1]
                       ELSE [lob |-> Max(pg),
                             pst |-> IF tcnt + 1 >= TailLimit THEN "limit" ELSE "tail",
                             tcnt |-> tcnt + 1])
     IN hist' = [hist EXCEPT ![cur].qpos = Len(log), ![cur].hi = hi, ![cur].page = pg,
                   ![cur].val = [k \in Keys |-> IF k \in pg THEN SnapK(vis', k) ELSE NULL],
                   ![cur].inv = (1..nW) \ vis', ![cur].nxt = nx]
  /\ cs' = "q"
  /\ UNCHANGED <<log, nW, progv, cur, cplan, cpos, pend, out, topic, committed,
                 crashes, s0, chain, crashrec>>

(* The high watermark, consumed at once, which is the chunk's close: the
   changed keys (window events, plus the visibility rule's keys), the
   survivors, the absence candidates, and the plan of the close block (the
   surviving rows plus a chosen candidate set).  In Record mode the whole
   block is emitted here, in this step, as one atomic item: its entries carry
   one offset context, the one that counts the chunk complete, so a crash
   delivers the record whole or not at all and the sink applies it whole
   (5.2, "including across restarts"). *)
WriteHW ==
  /\ cs = "q"
  /\ cpos = Len(log)
  /\ log' = Append(log, [t |-> "hw", k |-> 0, v |-> NULL, x |-> cur])
  /\ cpos' = Len(log) + 1
  /\ LET p     == Len(log) + 1
         h     == hist[cur]
         rng   == RangeKeys(h.lo, h.hi)
         winTx == {log[q].x : q \in {q \in (h.lw + 1)..Len(log) : IsData(q)}}
         wk    == {TxKey(x) : x \in winTx}
         notSeen(x) == x \in h.inv \/ TxPos(x) > h.qpos
         gp    == CASE VisRule \in {"changed", "chunk"} ->
                         {TxKey(x) : x \in {y \in pend : notSeen(y)}}
                    [] VisRule = "window" ->
                         {TxKey(x) : x \in {y \in winTx : notSeen(y)}}
                    [] OTHER -> {}
         chg   == (wk \cup gp) \cap rng
         rows  == h.page \ chg
         cands == (rng \ h.page) \ (IF DropChanged THEN {} ELSE chg)
         npend == CASE VisRule = "changed" -> {y \in pend : notSeen(y)}
                    [] OTHER -> {}
         aft   == [lob |-> h.nxt.lob, pst |-> h.nxt.pst, tcnt |-> h.nxt.tcnt, nch |-> nch + 1]
     IN \E A \in (IF Dense \/ Record THEN {cands} ELSE SUBSET cands) :
          LET plan  == rows \cup A
              ks    == SeqOf(plan)
              block == [i \in 1..Len(ks) |->
                         [kd |-> IF ks[i] \in h.page THEN "row" ELSE "abs", key |-> ks[i],
                          v |-> IF ks[i] \in h.page THEN h.val[ks[i]] ELSE NULL,
                          tag |-> p, ex |-> cur, ctx |-> MkCtx(p, aft, PCtx(npend))]]
          IN /\ hist' = [hist EXCEPT ![cur].hw = p, ![cur].cl = TRUE, ![cur].plan = plan]
             /\ pend' = npend
             /\ IF plan = {} \/ Record
                THEN /\ lob' = aft.lob /\ pst' = aft.pst /\ tcnt' = aft.tcnt
                     /\ nch' = aft.nch /\ chain' = Append(chain, cur)
                     /\ cs' = "none" /\ cur' = 0 /\ cplan' = {}
                     /\ out' = out \o block
                ELSE /\ cs' = "close" /\ cplan' = plan
                     /\ UNCHANGED <<lob, pst, tcnt, nch, chain, cur, out>>
  /\ UNCHANGED <<vis, nW, rmax, topic, committed, crashes, s0, crashrec>>

(* One close entry per step, in any order.  Its offset context counts the
   chunk as complete only on the last entry of the block (reading R1); the
   mutation ProgressAtFirst advances the progress on the first entry. *)
EmitClose(k) ==
  /\ cs = "close" /\ k \in cplan
  /\ LET h       == hist[cur]
         isFirst == cplan = h.plan
         isLast  == cplan = {k}
         adv     == IF ProgressAtFirst THEN isFirst ELSE isLast
         aft     == [lob |-> h.nxt.lob, pst |-> h.nxt.pst, tcnt |-> h.nxt.tcnt,
                     nch |-> nch + 1]
         pr      == IF adv THEN aft ELSE Prog
         row     == k \in h.page
         it      == [kd |-> IF row THEN "row" ELSE "abs", key |-> k,
                     v |-> IF row THEN h.val[k] ELSE NULL, tag |-> h.hw, ex |-> cur,
                     ctx |-> MkCtx(h.hw, pr, PCtx(pend))]
     IN /\ out' = Append(out, it)
        /\ cplan' = cplan \ {k}
        /\ IF adv
           THEN /\ lob' = aft.lob /\ pst' = aft.pst /\ tcnt' = aft.tcnt
                /\ nch' = aft.nch /\ chain' = Append(chain, cur)
           ELSE UNCHANGED <<lob, pst, tcnt, nch, chain>>
        /\ IF isLast THEN cs' = "none" /\ cur' = 0 ELSE UNCHANGED <<cs, cur>>
  /\ UNCHANGED <<srcv, rmax, cpos, pend, topic, committed, crashes, s0, hist,
                 crashrec>>

(* Re-delivery after a restart: the consumer re-reads the log from the
   committed offset, one entry per step.  Data events are emitted at their
   own position, watermarks of earlier executions are skipped.  Outside
   re-delivery every append is consumed in the step that makes it. *)
Consume ==
  /\ pst # "pre" /\ cs = "none" /\ cpos < Len(log)
  /\ LET p  == cpos + 1
         pd == IF IsData(p) /\ Tracks THEN pend \cup {log[p].x} ELSE pend
     IN /\ cpos' = p
        /\ pend' = pd
        /\ out' = IF IsData(p) THEN Append(out, EvItem(p, pd)) ELSE out
  /\ UNCHANGED <<srcv, progv, chkv, topic, committed, crashes, s0, hist, chain,
                 crashrec>>

(* The connector after a restart: the committed context, with the two
   restart mutations (the tail count reset, the maximum queried again). *)
Restart(nc) ==
  /\ cpos' = nc.pos /\ lob' = nc.lob /\ pst' = nc.pst /\ nch' = nc.nch
  /\ rmax' = IF ReRecordMax THEN MaxPresent(vis) ELSE nc.rmax
  /\ tcnt' = IF ResetTailOnRestart THEN 0 ELSE nc.tcnt
  /\ pend' = nc.pend
  /\ chain' = SubSeq(chain, 1, nc.nch)
  /\ cs' = "none" /\ cur' = 0 /\ cplan' = {}
  /\ crashes' = crashes + 1

(* A crash.  Everything emitted in this incarnation is durable (a lost
   unacknowledged item is the same as an earlier crash); the commit point
   is any of its items (c > 0), the previous commit (c = 0), or the
   connector's in-memory context (c = -1), as an acknowledged heartbeat, an
   offset-only record, commits it: that is how an empty close block's
   completion, which has no item of its own, gets committed.  The crash
   coordinate is the consumer's position: every data event up to it is
   emitted and every close block at or below it is complete, except a
   block being emitted at it.  The connector resumes from the committed
   context: offset, pass progress and, when persisted, the pending set. *)
Crash(c) ==
  /\ pst # "pre"
  /\ crashes < MaxCrashes
  /\ c \in -1..Len(out)
  /\ LET nc  == CASE c = -1 -> MkCtx(cpos, Prog, PCtx(pend))
                  [] c = 0  -> committed
                  [] OTHER  -> out[c].ctx
         cpt == cpos
     IN /\ topic' = topic \o [i \in 1..Len(out) |-> Strip(out[i])]
        /\ committed' = nc
        /\ out' = <<>>
        /\ crashrec' = Append(crashrec, [cmt |-> nc.pos, cpt |-> cpt,
                                         tl |-> Len(topic) + Len(out)])
        /\ Restart(nc)
  /\ UNCHANGED <<srcv, s0, hist>>

(* MUTATION CommitBeforeAck: the connector commits its in-memory context while
   the items after the first a are lost, as an offset committed before the
   records it covers are acknowledged.  In Record mode the cut lies between
   items, never inside one record. *)
ItemBoundary(i) ==
  IF i = 0 THEN TRUE ELSE ~(Record /\ out[i].ex # 0 /\ out[i].ex = out[i + 1].ex)
CrashEarly(a) ==
  /\ CommitBeforeAck
  /\ pst # "pre"
  /\ crashes < MaxCrashes
  /\ a \in 0..(Len(out) - 1)
  /\ ItemBoundary(a)
  /\ LET nc == MkCtx(cpos, Prog, PCtx(pend))
     IN /\ topic' = topic \o [i \in 1..a |-> Strip(out[i])]
        /\ committed' = nc
        /\ out' = <<>>
        /\ crashrec' = Append(crashrec, [cmt |-> nc.pos, cpt |-> cpos,
                                         tl |-> Len(topic) + a])
        /\ Restart(nc)
  /\ UNCHANGED <<srcv, s0, hist>>

Next ==
  \/ \E k \in Keys, v \in Img : Write(k, v)
  \/ \E V \in SUBSET (1..MaxWrites) : StartPass(V)
  \/ WriteLW
  \/ \E V \in SUBSET (1..MaxWrites) : Query(V)
  \/ WriteHW
  \/ \E k \in Keys : EmitClose(k)
  \/ Consume
  \/ \E c \in -1..Len(out) : Crash(c)
  \/ \E a \in 0..Len(out) : CrashEarly(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

Stream == topic \o [i \in 1..Len(out) |-> Strip(out[i])]
Frontier == Len(log)

\* the replay at key k of stream S from initial sink value d
ReplayK(d, k, S) ==
  LET js == {i \in 1..Len(S) : S[i].key = k}
  IN IF js = {} THEN d ELSE S[Max(js)].v

Quiescent == pst \in {"complete", "limit"} /\ cs = "none" /\ cpos = Len(log)
Scope == IF pst = "complete" THEN Keys ELSE {k \in Keys : k <= lob}
NoEvents(k) == \A p \in (s0 + 1)..Len(log) : ~(IsData(p) /\ log[p].k = k)
Listed(S, k) == \E i \in 1..Len(S) : S[i].kd # "ev" /\ S[i].key = k

TypeOK ==
  /\ nW \in 0..MaxWrites /\ vis \subseteq 1..nW
  /\ \A p \in 1..Len(log) :
       \/ (log[p].t = "d" /\ log[p].k \in Keys /\ log[p].v \in Img /\ log[p].x \in 1..nW)
       \/ (log[p].t \in {"lw", "hw"} /\ log[p].x \in 1..Len(hist))
  /\ pst \in {"pre", "main", "tail", "complete", "limit"}
  /\ lob \in 0..N /\ rmax \in 0..N /\ tcnt \in 0..TailLimit
  /\ cs \in {"none", "lw", "q", "hw", "close"}
  /\ cpos \in 0..Len(log) /\ pend \subseteq 1..nW
  /\ crashes \in 0..MaxCrashes /\ s0 \in 0..Len(log)
  /\ \A i \in 1..Len(Stream) :
       /\ Stream[i].kd \in {"ev", "row", "abs"} /\ Stream[i].key \in Keys
       /\ Stream[i].v \in Img /\ Stream[i].tag \in 1..Len(log)

(* listed_entry_honest in operational form: every emitted close entry is
   true of the source at its own position. *)
CloseEntryTrue ==
  LET S == Stream IN
  \A i \in 1..Len(S) : S[i].kd # "ev" => S[i].v = SrcK(S[i].tag, S[i].key)

\* every value key k has had at the source, {SrcK(p, k) : p \in 0..Len(log)}:
\* the table starts empty, and SrcK(p, k) is NULL or the image of a data entry
Existed(k) == {NULL} \cup {log[p].v : p \in {p \in 1..Len(log) : IsData(p) /\ log[p].k = k}}

SinkValueExisted ==
  LET S == Stream IN
  \A k \in Keys, d \in Img : ReplayK(d, k, S) \in {d} \cup Existed(k)

\* over the connector's claimed scope (operational: a key outside every
\* contract is covered only when the stream carries a log event for it, see
\* ScopeBridge); restricted to the contracts' scope it is absent_replay and
\* restart_converges, and there it follows from QuiescentSafe exactly as
\* restart_converges follows from restart_safe (a consequence, not independent
\* evidence); on the claimed keys outside the contracts it is an operational check
QuiescentConverges ==
  Quiescent =>
    LET S == Stream IN
    \A k \in Scope, d \in Img :
      ((d # NULL /\ SrcK(Frontier, k) = NULL /\ NoEvents(k)) => Listed(S, k))
        => ReplayK(d, k, S) = SrcK(Frontier, k)

RecordConverges ==
  ((Dense \/ Record) /\ Quiescent) =>
    LET S == Stream IN
    \A k \in Scope, d \in Img : ReplayK(d, k, S) = SrcK(Frontier, k)

-----------------------------------------------------------------------------
(* Tiling *)

Executed(e) == hist[e].qpos > 0
RangeOf(e) == RangeKeys(hist[e].lo, hist[e].hi)
SnapE(e, k) ==
  LET ps == {p \in 1..hist[e].qpos :
               IsData(p) /\ log[p].k = k /\ log[p].x \notin hist[e].inv}
  IN IF ps = {} THEN NULL ELSE log[Max(ps)].v

RangeRuleOK(e) ==
  LET h == hist[e] IN
  \/ (Cardinality(h.page) = ChunkSize /\ h.hi = Max(h.page))
  \/ (Cardinality(h.page) < ChunkSize /\ h.tail /\ h.hi = OPEN)
  \/ (Cardinality(h.page) < ChunkSize /\ ~h.tail /\ h.hi = h.rm)
PageExact(e) == hist[e].page = RangeOf(e) \cap {k \in Keys : SnapE(e, k) # NULL}
ChainOK ==
  /\ Len(chain) > 0 => hist[chain[1]].lo = 0
  /\ \A i \in 1..Len(chain) : hist[chain[i]].lo <= hist[chain[i]].hi
  /\ \A i \in 1..(Len(chain) - 1) :
       hist[chain[i]].hi # OPEN /\ hist[chain[i + 1]].lo = hist[chain[i]].hi
OverlapOK ==
  \A e1, e2 \in 1..Len(hist) :
    (e1 < e2 /\ Executed(e1) /\ Executed(e2) /\ RangeOf(e1) \cap RangeOf(e2) # {})
      => hist[e1].inc < hist[e2].inc
MaxPersisted == \A e \in 1..Len(hist) : hist[e].rm = rmax
TailCountOK == Cardinality({i \in 1..Len(chain) : hist[chain[i]].tail}) <= TailLimit
CoverOK ==
  Quiescent =>
    /\ UNION {RangeOf(chain[i]) : i \in 1..Len(chain)} = Scope
    /\ pst = "complete" => (Len(chain) > 0 /\ hist[chain[Len(chain)]].hi = OPEN /\
                            Cardinality(hist[chain[Len(chain)]].page) < ChunkSize)
    /\ (pst = "limit" /\ TailLimit > 0) =>
         (Len(chain) > 0 /\ hist[chain[Len(chain)]].page # {} /\
          lob = Max(hist[chain[Len(chain)]].page))

\* the tiling without the bookkeeping conjunct MaxPersisted (used to check the
\* consequences of the mutation ReRecordMax)
TilingChain ==
  /\ \A e \in 1..Len(hist) : Executed(e) => (RangeRuleOK(e) /\ PageExact(e))
  /\ ChainOK /\ OverlapOK /\ TailCountOK /\ CoverOK

TilingOK == TilingChain /\ MaxPersisted

-----------------------------------------------------------------------------
(* The bridge to the Isabelle locales *)

DelIdx(S, e) == {i \in 1..Len(S) : S[i].ex = e}
Delivered(S, e) == {S[i].key : i \in DelIdx(S, e)}
\* a unit is fully delivered when its close block is: in Dense and Record mode the
\* whole listing; with free candidate lists every surviving row, since any subset
\* of the absent untouched keys with all the survivors is a valid unit over the
\* whole range (svl_ok2)
FullyDel(S, e) ==
  /\ hist[e].cl
  /\ IF Dense \/ Record THEN Delivered(S, e) = hist[e].plan
     ELSE hist[e].plan \cap hist[e].page \subseteq Delivered(S, e)
\* keys whose last transaction before the low watermark the query did not see.
\* A unit's domain leaves them out: the connector's rule treats them as changed
\* and the unit states nothing about them (no row, no absence), and for them
\* O2 can fail; the core contract allows any domain, so the unit over the rest
\* of the range is a legitimate instance.  Such a key is outside every contract
\* and gets exactly its own log events in the stream (OAC
\* emission_out_of_scope): when it has none since the pass start, the pass does
\* not repair it, which is the coverage failure of F2 and F4.
TrueGap(e) == {TxKey(x) : x \in {y \in hist[e].inv : TxPos(y) < hist[e].lw}}
Dom(S, e) == (IF FullyDel(S, e) THEN RangeOf(e) ELSE Delivered(S, e)) \ TrueGap(e)
Refresh(e, k) == hist[e].val[k]
NoWin(e, k) == \A p \in (hist[e].lw + 1)..hist[e].hw : ~(IsData(p) /\ log[p].k = k)
IsUnit(S, e) == hist[e].cl /\ (FullyDel(S, e) \/ Delivered(S, e) # {})

UnitOK(S, e) ==
  LET h == hist[e]
      D == Dom(S, e)
      L == Delivered(S, e)
  IN /\ s0 <= h.lw /\ h.lw < h.hw /\ h.hw <= Len(log)
     /\ \A k \in D : \E c \in h.lw..h.hw : Refresh(e, k) = SrcK(c, k)
     /\ L \subseteq D
     /\ {k \in D : Refresh(e, k) # NULL /\ NoWin(e, k)} \subseteq L
     /\ \A k \in L : NoWin(e, k)
     /\ \A i \in DelIdx(S, e) : S[i].v = Refresh(e, S[i].key) /\ S[i].tag = h.hw
     /\ Cardinality(DelIdx(S, e)) = Cardinality(L)

O1OK(S) ==
  \A e1, e2 \in 1..Len(hist) :
    (e1 < e2 /\ IsUnit(S, e1) /\ IsUnit(S, e2) /\ hist[e1].inc = hist[e2].inc)
      => Dom(S, e1) \cap Dom(S, e2) = {}

\* pass_restart, asserted only for a behavior with exactly one crash: P1 = the
\* delivered units of incarnation 0 (frontier the crash, as in
\* pass_restart_after_frontier), P2 = the units of incarnation 1.  The premise
\* reexec holds vacuously for this P1 (none of its units closes after the
\* crash); its operational content, that the parts not delivered by the crash
\* are re-read, is ScopeBridge's clause.  With two
\* crashes no reading of the whole stream is one pass_restart instance (the
\* later incarnations can re-execute the same range, so they are not one
\* capture contract, and the stream steps back at each part boundary); the
\* composition across two crashes is an EXTENSION, checked operationally only.
RestartOK(S) ==
  Len(crashrec) = 1 =>
    /\ s0 <= crashrec[1].cmt                                        \* s0cmt
    /\ crashrec[1].cmt <= crashrec[1].cpt                           \* cmt_le_crash
    /\ crashrec[1].cpt <= Len(log)                                  \* crash_le_f2
    /\ \A e \in 1..Len(hist) :
         (hist[e].inc = 0 /\ IsUnit(S, e)) => hist[e].hw <= crashrec[1].cpt  \* crash_le_f1
    /\ \A e \in 1..Len(hist) : hist[e].inc >= 1 => hist[e].lw >= crashrec[1].cpt  \* crash_le_lo2

PartLo(i) == IF i = 0 THEN 1 ELSE crashrec[i].tl + 1
PartHi(i, S) == IF i = Len(crashrec) THEN Len(S) ELSE crashrec[i + 1].tl
PartStart(i) == IF i = 0 THEN s0 ELSE crashrec[i].cmt
\* the part's crash coordinate, or the consumer's position for the current part
PartEnd(i) == IF i = Len(crashrec) THEN cpos ELSE crashrec[i + 1].cpt
PartOK(i, S) ==
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
     /\ \A x \in idx \ evx : hist[S[x].ex].inc = i /\ S[x].tag = hist[S[x].ex].hw

StreamShape == LET S == Stream IN \A i \in 0..Len(crashrec) : PartOK(i, S)

\* every incarnation's part of the stream is the emission of its own capture
\* contract (its units, from its own start); at most one crash: the
\* pass_restart reading; two crashes: the per-incarnation contracts only
LocaleAssumptions ==
  LET S == Stream IN
  /\ StreamShape
  /\ \A e \in 1..Len(hist) : IsUnit(S, e) => UnitOK(S, e)
  /\ O1OK(S)
  /\ RestartOK(S)

(* The chunk info record across restarts (5.2: the sink finishes the record's
   deletes "including across restarts"): once any entry of a chunk's record
   is in the stream, every key of its range that the read found absent and
   unchanged stays deleted at the final replay, unless a later log event
   changes it.  Counterpart: OA record_enum and chunk_record_converges (the
   record deletes every absent untouched key the sink holds).  Holds for the
   atomic Record mode; the per-key Dense rendering violates it across a crash
   (the probe D1). *)
DeliveredRecordAbsence ==
  ((Dense \/ Record) /\ Quiescent) =>
    LET S == Stream IN
    \A e \in 1..Len(hist) :
      (hist[e].cl /\ Delivered(S, e) # {}) =>
        \A k \in RangeOf(e), d \in Img :
          (Refresh(e, k) = NULL /\ k \notin TrueGap(e) /\ NoWin(e, k) /\
           \A p \in (hist[e].hw + 1)..Len(log) : ~(IsData(p) /\ log[p].k = k))
          => ReplayK(d, k, S) = NULL

\* the contracts' scope: the domains of the delivered units, without the
\* TrueGap keys (OA: scope; OAR: sc1 \cup sc2)
CScope(S) == {k \in Keys : \E e \in 1..Len(hist) : IsUnit(S, e) /\ k \in Dom(S, e)}

(* The connector's claimed coverage lies in the scope of the contracts, or
   the key is outside every contract and the stream carries a log event
   for it since the pass started (emission_out_of_scope). *)
ScopeBridge ==
  Quiescent =>
    LET S == Stream IN
    \A k \in Scope : k \in CScope(S) \/ ~NoEvents(k)

(* absent_replay_safe (no crash) and restart_safe (one crash), transcribed
   over the contracts' scope, as the theorems state them: every key of a
   delivered unit's domain ends at the source state at the frontier, or it
   keeps its initial sink value, is absent at the source, no close entry lists
   it, and no log event since the pass start mentions it.  Two crashes: an
   EXTENSION.  The claimed scope is left to ScopeBridge and QuiescentConverges. *)
QuiescentSafe ==
  Quiescent =>
    LET S == Stream IN
    \A k \in CScope(S), d \in Img :
      LET r == ReplayK(d, k, S) IN
      \/ r = SrcK(Frontier, k)
      \/ (r = d /\ SrcK(Frontier, k) = NULL /\ ~Listed(S, k) /\ NoEvents(k))

-----------------------------------------------------------------------------
(* Witness probes.  Each is EXPECTED TO BE VIOLATED in the green
   configurations: a violation shows that the search reaches the scenario.
   They are run one per configuration and are not properties of the
   protocol. *)

PartialBlock(S, e) ==
  hist[e].cl /\ Delivered(S, e) # {} /\ Delivered(S, e) # hist[e].plan
WitTwoCrashesDone == ~(Quiescent /\ crashes = 2 /\ pst = "complete")
WitCrashInBlock ==
  ~(Quiescent /\ \E e \in 1..Len(hist) : PartialBlock(Stream, e))
\* strict: the second crash lands inside the re-delivered segment, after at
\* least one re-delivered item and before its end
WitCrashInRedelivery ==
  ~(\E j \in 2..Len(crashrec) :
       crashrec[j].cpt < crashrec[j - 1].cpt /\ crashrec[j].tl > crashrec[j - 1].tl)
\* a positive tail count in a committable context while tail reads remain
WitLiveTailCount ==
  ~(\E i \in 1..Len(out) : out[i].ctx.pst = "tail" /\ out[i].ctx.tcnt > 0)
\* two crashes, and two delivered units of the later incarnations with
\* overlapping domains: no single capture contract after crash 1
WitTwoCrashOverlap ==
  ~(Quiescent /\ crashes = 2 /\
    \E e1, e2 \in 1..Len(hist) :
       /\ e1 < e2 /\ hist[e1].inc >= 1 /\ hist[e2].inc >= 1
       /\ IsUnit(Stream, e1) /\ IsUnit(Stream, e2)
       /\ Dom(Stream, e1) \cap Dom(Stream, e2) # {})
WitGapExcluded ==
  ~(Quiescent /\ \E e \in 1..Len(hist) :
       IsUnit(Stream, e) /\ TrueGap(e) \cap RangeOf(e) # {})
WitOrphanKept ==
  ~(Quiescent /\ \E k \in Scope, d \in Vals :
       ReplayK(d, k, Stream) = d /\ SrcK(Frontier, k) = NULL)
WitOrphanRemoved ==
  ~(Quiescent /\ \E k \in Scope : NoEvents(k) /\ SrcK(Frontier, k) = NULL /\
       \E i \in 1..Len(Stream) : Stream[i].kd = "abs" /\ Stream[i].key = k)
WitTailLimit == ~(Quiescent /\ pst = "limit")
WitTailRows ==
  ~(\E i \in 1..Len(chain) : hist[chain[i]].tail /\ hist[chain[i]].page # {})
WitOverlap ==
  ~(\E e1, e2 \in 1..Len(hist) :
       e1 < e2 /\ Executed(e1) /\ Executed(e2) /\ RangeOf(e1) \cap RangeOf(e2) # {})

-----------------------------------------------------------------------------
(* Model values *)
ValPerms == Permutations(Vals)
=============================================================================
