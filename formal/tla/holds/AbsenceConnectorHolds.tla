----------------------- MODULE AbsenceConnectorHolds -----------------------
(***************************************************************************)
(* Held absence statements under a safety cap: an extension of the core    *)
(* model AbsenceConnector (paper "Extending DBLog-Based Incremental        *)
(* Snapshots to Handle Orphan Rows in CDC Pipelines", Section 5.6 "Safety  *)
(* caps"), for the model checker TLC.  Bounded evidence, never proof.      *)
(*                                                                         *)
(* The question: when a chunk's statement of absence is held back because  *)
(* it would delete more keys than a cap (and always for an empty table),   *)
(* and released later after an operator confirms, does the released        *)
(* statement stay true at its own position, and does the pass still        *)
(* converge once every hold is released?                                   *)
(*                                                                         *)
(* The paper's text (5.6): "a configurable safety cap applies to both      *)
(* representations, and an empty source table always calls for operator    *)
(* confirmation.  For chunk info records, a sink can refuse an unconfirmed *)
(* empty-table record or any record that would delete more rows than the   *)
(* cap.  For per-key absence events [...] the source connector holds back  *)
(* and reports any chunk [...] that exceeds the cap (and always an empty   *)
(* table).  Once an operator confirms via a signal, the connector runs a   *)
(* fresh bracketed read and emits the events or a confirmed chunk info     *)
(* record."  5.5: a pass can "hold back a statement at a safety cap".      *)
(*                                                                         *)
(* RELATION TO THE CORE.  This module EXTENDS AbsenceConnector, whose file *)
(* is not edited (sha256 4cbeac59...).  Every core operator is reused by   *)
(* name.  The new next-state relation NextH lists the core's disjuncts in  *)
(* the core's order, then the four release actions.  Core actions reused   *)
(* unchanged, each conjoined with UNCHANGED of the new variables and the   *)
(* extension of hctx for the items it appends: StartPass, WriteLW, Query,  *)
(* Consume, Crash, CrashEarly, and Write with one added guard.  Two core   *)
(* actions are replaced by copies with guarded changes, every changed      *)
(* line listed here (each change is the identity when Cap = 0):            *)
(*  WriteHW -> WriteHWH                                                    *)
(*   1 added "\E held \in HeldChoice(A, EmptyTab(h))" under the core's     *)
(*     "\E A": the hold decision ({FALSE} when Cap = 0);                   *)
(*   2 plan "rows \cup A" ->                                               *)
(*     "IF held /\ ~Record THEN rows ELSE rows \cup A"                     *)
(*     (per-key rendering: a held chunk emits its rows, not its absence    *)
(*     entries);                                                           *)
(*   3 kd "IF .. "row" ELSE "abs"" -> adds "ELSE IF held THEN "uabs""      *)
(*     (Record: the absence part of an unconfirmed record);                *)
(*   4 the context's progress "aft" -> "pr", which is the old progress     *)
(*     when the hold pauses the pass (reading "reexec");                   *)
(*   5 the completing branch gains the pause sub-branch (cs "held", the    *)
(*     progress and the lineage not advanced, reading "reexec");           *)
(*   6 added updates of hx, holds, hctx, cheld; the new variables added to *)
(*     its UNCHANGED.                                                      *)
(*  EmitClose -> EmitCloseH                                                *)
(*   7 adv "IF ProgressAtFirst THEN isFirst ELSE isLast" -> "IF pause THEN *)
(*     FALSE ELSE ..." (reading "reexec": a held chunk is not completed by *)
(*     its rows);                                                          *)
(*   8 at the last entry "cs' = "none" /\ cur' = 0" -> "IF pause THEN cs' =*)
(*     "held" (cur kept) ELSE as the core";                                *)
(*   9 added updates of holds (the hold recorded with the chunk's          *)
(*     completion, reading R1), hctx, cheld.                               *)
(*  Write -> WriteH                                                        *)
(*  10 added guard cs # "rclose": the core's reduction "writes do not      *)
(*     interleave inside a close block" extended to a release's block.     *)
(*  Crash -> CrashH                                                        *)
(*  11 conjoined: the holds restored with the committed context, the       *)
(*     release in flight discarded (it is an open read, 5.6).              *)
(* Regression: with Cap = 0 the extension reproduces the core's verdicts   *)
(* and distinct-state counts (configurations R_ and RH_).                  *)
(*                                                                         *)
(* MAPPING: spec object -> paper -> Isabelle (OA = Orphan_Absence.thy,     *)
(* OAI = Orphan_Absence_Interleaved.thy, OAC = Orphan_Absence_Composition, *)
(* OAR = Orphan_Absence_Restart.thy, core = Cut_Theorem.thy)               *)
(*                                                                         *)
(*  Cap               5.6 "a configurable safety cap"; Cap = 0 switches    *)
(*                    the whole feature off (no cap, no empty-table rule)  *)
(*                    -> no counterpart: the theories have no cap; a held  *)
(*                    chunk is a unit whose listing has no absence entry,  *)
(*                    which OA svl_ok2 admits (absence entries optional)   *)
(*  EmptyTab(h)       5.2 "An empty source table produces a single chunk   *)
(*                    info record with both bounds open and zero rows";    *)
(*                    5.6 "always calls for operator confirmation"         *)
(*                    -> no counterpart (reading H1)                       *)
(*  HeldChoice        5.6 per-key: "holds back [...] any chunk [...] that  *)
(*                    exceeds the cap (and always an empty table)"; Record:*)
(*                    "a sink can refuse an unconfirmed empty-table record *)
(*                    or any record that would delete more rows than the   *)
(*                    cap" (reading H2) -> no counterpart                  *)
(*  holds, hd         the pending holds, each with the held chunk's range  *)
(*                    5.6 "holds back and reports"; the report names the   *)
(*                    range -> no counterpart                              *)
(*  "uabs" items      Record: the absence part of an unconfirmed record,   *)
(*                    emitted, not applied by the sink (the rows apply)    *)
(*                    -> OA svl_ok2 with the refused unit's listing = its  *)
(*                    rows (the absence entries are optional)              *)
(*  Applied           the stream as the sink applies it: the emitted       *)
(*                    stream without the "uabs" items -> core emission     *)
(*                    svl s0 for that listing; OAI inter, OAC composed     *)
(*  hctx, chold,      reading "persist": the holds ride in the offset      *)
(*  PHolds, HoldRestore context of every item, restored at a restart with  *)
(*                    the committed context (like the pending set of R3)   *)
(*                    -> no counterpart (OAR models no hold)               *)
(*  cheld, cs "held"  the hold of the chunk in flight; reading "reexec":   *)
(*                    the pass waits at a held chunk -> no counterpart     *)
(*  RelLW, RelQuery,  5.6 "Once an operator confirms via a signal, the     *)
(*  RelHW, RelEmit,   connector runs a fresh bracketed read and emits the  *)
(*  rhist             events or a confirmed chunk info record": a unit of  *)
(*                    its own, low watermark, a query over the held range, *)
(*                    high watermark, the window rule and the visibility   *)
(*                    rule of 5.1 and 5.6, without the cap -> OAI          *)
(*                    pass_with_request: R = the release units (each a     *)
(*                    cunit with u_lo = its low watermark, u_hi = its high *)
(*                    watermark, u_refresh = its query); per key, a unit   *)
(*                    of OA absence_assertion_contract shape (domain = the *)
(*                    keys read absent, refresh None); in Record mode a    *)
(*                    full range unit with its rows; after the pass's last *)
(*                    close, OAC pass_then_read                            *)
(*  release items     ex = -r (r the release's index in rhist), tag = its  *)
(*                    high watermark -> OAI R.closes_at, R's close blocks  *)
(*                    at u_hi                                              *)
(*                                                                         *)
(* INVARIANTS: invariant -> paper -> Isabelle counterpart                  *)
(*                                                                         *)
(*  TypeOKH           sanity, no counterpart                               *)
(*  CloseEntryTrue    (the core's, unchanged) 5.1, over every emitted      *)
(*                    entry: chunk entries, the absence part of            *)
(*                    unconfirmed records, and the released entries at     *)
(*                    their own tag -> OAI listed_entry_honest for P and R *)
(*  HoldsSafe         no released absence entry deletes a key the source   *)
(*                    holds at the release's position: CloseEntryTrue      *)
(*                    restated for releases -> OAI listed_entry_honest     *)
(*                    for R (refresh None at u_hi)                         *)
(*  SinkValueExistedH the core's SinkValueExisted on Applied               *)
(*  QuiescentSafeH    8 safety -> OAI pass_with_request_safe (no crash),   *)
(*                    over sc1 \cup sc2 = CScopeH (the domains of the      *)
(*                    delivered chunk units and release units), on the     *)
(*                    applied stream; one crash without a release: OAR     *)
(*                    restart_safe; a crash with a release: EXTENSION      *)
(*                    (no theorem composes a restart with a request)       *)
(*  QuiescentConvergesH 8 convergence under coverage, the core's on        *)
(*                    Applied -> OAI pass_with_request_converges (cover    *)
(*                    premise), OA absent_replay, OAR restart_converges    *)
(*  ReleasedConverges at quiescence with no pending hold, every key of a   *)
(*                    released range converges under the same cover        *)
(*                    premise -> OAI pass_with_request_converges           *)
(*                    restricted to sc2; where a released range lies in    *)
(*                    the claimed scope it is implied by                   *)
(*                    QuiescentConvergesH, a restatement; in Record mode a *)
(*                    refused record of a discarded incarnation can name a *)
(*                    range beyond the claimed scope of a pass stopped by  *)
(*                    the tail limit, and there it is a check of its own   *)
(*  RecordConvergesH  5.2, 8 "when applying chunk info records": Dense or  *)
(*                    Record, at quiescence with no pending hold, every    *)
(*                    key of the claimed scope converges from any initial  *)
(*                    sink -> OA chunk_record_converges with OAI           *)
(*                    pass_with_listing_request_converges (the release     *)
(*                    lists every key it reads absent and untouched)       *)
(*  DeliveredRecordAbsenceH the core's, on Applied, with no pending hold:  *)
(*                    a delivered record's absent untouched keys stay      *)
(*                    deleted (a refused record's through its release)     *)
(*                    -> OA record_enum, chunk_record_converges            *)
(*  TilingOK          the core's, unchanged (releases are not chunks and   *)
(*                    live in rhist) -> OAT                                *)
(*  LocaleAssumptionsH the bridge, conjunct by conjunct:                   *)
(*                    StreamShapeH  core emission_t / OAI inter_t: every   *)
(*                      part in tag order, every data event from its start *)
(*                      to its crash coordinate once, every close entry,   *)
(*                      the released ones included, at its unit's u_hi     *)
(*                      (OAI inter_t_sorted, inter_t_mset; OAR cut_t ++    *)
(*                      resumed_t across a crash)                          *)
(*                    UnitOKH, O1OKH  P = the chunk units: capture_contract*)
(*                      (bracket_lo_hi, bracket_hi_f, O2_honest,           *)
(*                      O1_disjoint per incarnation), P.svl_ok2 on the     *)
(*                      applied stream, s0lo                               *)
(*                    RestartOKH  OAR pass_restart for one crash (the      *)
(*                      core's RestartOK over the units of Applied)        *)
(*                    RUnitOK  R = the release units: capture_contract     *)
(*                      (bracket_lo_hi, bracket_hi_f at f1 = the frontier, *)
(*                      O2_honest), R.svl_ok2, OAI s0lo2                   *)
(*                    RO1OK  R.O1_disjoint: the whole of R in a crash-free *)
(*                      behavior, as pass_with_request needs; with a crash *)
(*                      in per-key rendering per incarnation (EXTENSION);  *)
(*                      not asserted in Record mode with a crash, where    *)
(*                      two holds can name one range (reading H2,          *)
(*                      WitDuplicateHold)                                  *)
(*                    CompositionOK  OAC pass_then_read, for a crash-free  *)
(*                      behavior whose pass is done and whose release      *)
(*                      units all start at or after the pass's last close  *)
(*                      PassEnd: s0f1, f1_le_f2, P's bracket_hi_f at f1 =  *)
(*                      PassEnd, f1_le_lo2 (the order of the composed      *)
(*                      stream is StreamShapeH's tag order)                *)
(*                    A release that closes at or before PassEnd is OAI's  *)
(*                    case (R inside the pass); one that starts after it   *)
(*                    is OAC's case; windows are serialized, so no release *)
(*                    straddles a chunk's close.  OAI with f1 = the        *)
(*                    frontier also covers the second case                 *)
(*                    (contract_with_frontier).  With a crash the release  *)
(*                    units are checked per incarnation only: EXTENSION.   *)
(*  ScopeBridgeH      the core's ScopeBridge over CScopeH on Applied       *)
(*  CapGuard          the guard itself, no counterpart: the sink applies   *)
(*                    no unconfirmed absence entry, no applied absence     *)
(*                    entry comes from an empty-table chunk, and (per key) *)
(*                    no chunk emits more than Cap absence entries         *)
(*  Wit*              witness probes, EXPECTED TO BE VIOLATED              *)
(*                                                                         *)
(* READINGS OF THE PAPER'S TEXT (named ambiguities):                       *)
(*  H1 An empty table is a chunk whose range is open at both ends and      *)
(*     whose query returned no row (the shape of the empty-table record    *)
(*     of 5.2), whatever its changed list.                                 *)
(*  H2 Record mode: the refusal is the sink's.  An empty-table record is   *)
(*     always refused (the model's guard); any other record whose absence  *)
(*     set exceeds the cap may be refused or applied (the sink's count of  *)
(*     rows it would delete is at most that set's size, and the model does *)
(*     not store the sink, so both outcomes are behaviors); a record within*)
(*     the cap is applied.  The refused record stays in the durable stream *)
(*     and its hold survives every restart (HoldRestore keeps it); the     *)
(*     reading "reexec" is not offered for Record mode, since the          *)
(*     connector does not learn of a sink's refusal (ASSUME).  So a crash  *)
(*     whose committed context predates a refused record re-executes its   *)
(*     chunk, which can be refused again: two holds then name one range,   *)
(*     and both releases run in one incarnation (WitDuplicateHold).  Each  *)
(*     is true at its position; together they are not one capture          *)
(*     contract, so RO1OK is not asserted there.                           *)
(*  H3 A hold across a restart (per-key rendering), two readings, both     *)
(*     modelled: "persist", the held chunk counts as completed (its rows   *)
(*     and its read are done, 5.5 "hold back a statement"), the pass goes  *)
(*     on, and the hold rides in the committed context with its range,     *)
(*     recorded with the chunk's completion (R1); "reexec", the hold       *)
(*     pauses the pass at the held chunk, which counts as not completed    *)
(*     until its release completes, so a restart re-executes it from the   *)
(*     committed progress and it holds again; nothing new is persisted.    *)
(*  H4 What a release emits: per key, absence events only (5.6 "emits the  *)
(*     events"; the rows went out at the held chunk's close), so its unit's*)
(*     domain is the keys it read absent; Record, a confirmed record with  *)
(*     its surviving rows (the record format of 5.2), one atomic item.     *)
(*  H5 The release's query reads the whole held range (its own bounds, no  *)
(*     row limit), so its absence statement covers the range.              *)
(*  H6 The release's read is serialized with the chunk reads (one window   *)
(*     at a time, as 5.4 serializes request batches); it runs during the   *)
(*     pass between chunks or after the pass, whenever the connector is    *)
(*     not inside a window and has consumed the log.                       *)
(*  H7 Free candidate lists: the release lists any subset of the keys it   *)
(*     reads absent and unchanged (the core's R5 over-approximation of the *)
(*     supplier's list, reloaded at the release); Dense and Record list    *)
(*     every such key.  The cap does not apply to a release.               *)
(*                                                                         *)
(* SOUND REDUCTIONS (beyond the core's four):                              *)
(*  - the operator's confirmation and the release's low watermark are one  *)
(*    step (RelLW): a confirmation has no effect on the source or the      *)
(*    stream, and one lost at a crash before its read is the same as a     *)
(*    later confirmation, which RelLW allows at any later step;            *)
(*  - writes do not interleave inside a release's close block (logged      *)
(*    after its high watermark either way, as for chunks).                 *)
(*                                                                         *)
(* Termination by construction (CHECK_DEADLOCK FALSE): the core's argument,*)
(* plus: holds are created only by chunk executions (bounded), each        *)
(* release removes its hold, and a hold restored by a crash is released at *)
(* most once more per crash (crashes are bounded).                         *)
(*                                                                         *)
(* MUTATIONS: (a) StaleRelease: the release emits the absence set computed *)
(* at the original close, ignoring its own read; (b) RelNoWindow: the      *)
(* release's read without the window rule; (c) PersistHolds = FALSE: the   *)
(* holds do not ride in the committed context; (d) SinkAppliesUnconfirmed: *)
(* a sink applies the absence part of an unconfirmed record.  (a) is not   *)
(* offered in Record mode, and the core's mutations ProgressAtFirst and    *)
(* CommitBeforeAck are not combined with a cap: both move the commit point *)
(* the hold rides on (ASSUME).  Under the treat-as-changed variant (b)     *)
(* cannot fail: the visibility rule marks the key of every transaction the *)
(* release's query did not see, which covers every window event logged     *)
(* after the query, and a window event before the query is in its result.  *)
(***************************************************************************)

EXTENDS AbsenceConnector

CONSTANTS
  Cap,                    \* the safety cap of 5.6; 0 = no cap and no empty-table rule (the core)
  HoldMode,               \* "persist" | "reexec": the two readings of a hold across a restart
  PersistHolds,           \* FALSE = mutation (c): the holds do not ride in the committed context
  StaleRelease,           \* mutation (a): the release emits the absence set of the original close
  RelNoWindow,            \* mutation (b): the release's read without the window rule
  SinkAppliesUnconfirmed  \* mutation (d): a sink applies the absence part of an unconfirmed record

ASSUME Cap \in Nat
ASSUME HoldMode \in {"persist", "reexec"}
ASSUME \A b \in {PersistHolds, StaleRelease, RelNoWindow, SinkAppliesUnconfirmed} : b \in BOOLEAN
ASSUME HoldMode = "reexec" => ~Record
ASSUME StaleRelease => ~Record
ASSUME Cap > 0 => (~ProgressAtFirst /\ ~CommitBeforeAck)

VARIABLES
  holds,   \* the pending holds: [ex (the held chunk's execution), lo, hi, abs]
  hctx,    \* the holds in the offset context of each item of out (aligned with out)
  chold,   \* the holds in the committed context
  cheld,   \* the hold of the chunk in flight, recorded when the chunk completes
  hx,      \* ghost: the held chunk executions
  rhist,   \* ghost: the release executions
  rcur,    \* the release in flight (its index in rhist, 0: none)
  rplan    \* the release's close entries still to emit

hvars == <<holds, hctx, chold, cheld, hx, rhist, rcur, rplan>>
varsH == <<vars, hvars>>

NoHold == [ex |-> 0, lo |-> 0, hi |-> 0, abs |-> {}]
PHolds(hs) == IF HoldMode = "persist" /\ PersistHolds /\ ~Record THEN hs ELSE {}
EmptyTab(h) == h.lo = 0 /\ h.hi = OPEN /\ h.page = {}
HeldChoice(A, empt) ==
  IF Cap = 0 THEN {FALSE}
  ELSE IF Record
       THEN (IF empt THEN {TRUE} ELSE IF Cardinality(A) > Cap THEN {FALSE, TRUE} ELSE {FALSE})
       ELSE {empt \/ Cardinality(A) > Cap}
HctxNext(hs) == hctx' = hctx \o [i \in 1..(Len(out') - Len(out)) |-> PHolds(hs)]
AftOf(e) == [lob |-> hist[e].nxt.lob, pst |-> hist[e].nxt.pst, tcnt |-> hist[e].nxt.tcnt,
             nch |-> nch + 1]

-----------------------------------------------------------------------------
InitH ==
  /\ Init
  /\ holds = {} /\ hctx = <<>> /\ chold = {} /\ cheld = NoHold /\ hx = {}
  /\ rhist = <<>> /\ rcur = 0 /\ rplan = {}

WriteH(k, v) ==
  /\ cs # "rclose"
  /\ Write(k, v)
  /\ HctxNext(holds)
  /\ UNCHANGED <<holds, chold, cheld, hx, rhist, rcur, rplan>>

StartPassH(V) == StartPass(V) /\ UNCHANGED hvars
WriteLWH == WriteLW /\ UNCHANGED hvars
QueryH(V) == Query(V) /\ UNCHANGED hvars
ConsumeH ==
  /\ Consume
  /\ HctxNext(holds)
  /\ UNCHANGED <<holds, chold, cheld, hx, rhist, rcur, rplan>>

WriteHWH ==
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
        \E held \in HeldChoice(A, EmptyTab(h)) :
          LET plan   == IF held /\ ~Record THEN rows ELSE rows \cup A
              ks     == SeqOf(plan)
              pause  == held /\ HoldMode = "reexec"
              pr     == IF pause THEN Prog ELSE aft
              hd     == [ex |-> cur, lo |-> h.lo, hi |-> h.hi,
                         abs |-> IF StaleRelease THEN A ELSE {}]
              block  == [i \in 1..Len(ks) |->
                          [kd |-> IF ks[i] \in h.page THEN "row"
                                  ELSE IF held THEN "uabs" ELSE "abs",
                           key |-> ks[i],
                           v |-> IF ks[i] \in h.page THEN h.val[ks[i]] ELSE NULL,
                           tag |-> p, ex |-> cur, ctx |-> MkCtx(p, pr, PCtx(npend))]]
              nholds == IF held THEN holds \cup {hd} ELSE holds
          IN /\ hist' = [hist EXCEPT ![cur].hw = p, ![cur].cl = TRUE, ![cur].plan = plan]
             /\ pend' = npend
             /\ hx' = IF held THEN hx \cup {cur} ELSE hx
             /\ IF plan = {} \/ Record
                THEN /\ out' = out \o block
                     /\ holds' = nholds
                     /\ hctx' = hctx \o [i \in 1..Len(block) |-> PHolds(nholds)]
                     /\ IF pause
                        THEN /\ cs' = "held" /\ cheld' = hd /\ cplan' = {}
                             /\ UNCHANGED <<lob, pst, tcnt, nch, chain, cur>>
                        ELSE /\ lob' = aft.lob /\ pst' = aft.pst /\ tcnt' = aft.tcnt
                             /\ nch' = aft.nch /\ chain' = Append(chain, cur)
                             /\ cs' = "none" /\ cur' = 0 /\ cplan' = {}
                             /\ UNCHANGED cheld
                ELSE /\ cs' = "close" /\ cplan' = plan
                     /\ cheld' = IF held THEN hd ELSE NoHold
                     /\ UNCHANGED <<lob, pst, tcnt, nch, chain, cur, out, holds, hctx>>
  /\ UNCHANGED <<vis, nW, rmax, topic, committed, crashes, s0, crashrec,
                 chold, rhist, rcur, rplan>>

EmitCloseH(k) ==
  /\ cs = "close" /\ k \in cplan
  /\ LET h       == hist[cur]
         isFirst == cplan = h.plan
         isLast  == cplan = {k}
         pause   == cheld # NoHold /\ HoldMode = "reexec"
         adv     == IF pause THEN FALSE ELSE IF ProgressAtFirst THEN isFirst ELSE isLast
         aft     == [lob |-> h.nxt.lob, pst |-> h.nxt.pst, tcnt |-> h.nxt.tcnt,
                     nch |-> nch + 1]
         pr      == IF adv THEN aft ELSE Prog
         row     == k \in h.page
         it      == [kd |-> IF row THEN "row" ELSE "abs", key |-> k,
                     v |-> IF row THEN h.val[k] ELSE NULL, tag |-> h.hw, ex |-> cur,
                     ctx |-> MkCtx(h.hw, pr, PCtx(pend))]
         nholds  == IF isLast /\ cheld # NoHold THEN holds \cup {cheld} ELSE holds
     IN /\ out' = Append(out, it)
        /\ cplan' = cplan \ {k}
        /\ IF adv
           THEN /\ lob' = aft.lob /\ pst' = aft.pst /\ tcnt' = aft.tcnt
                /\ nch' = aft.nch /\ chain' = Append(chain, cur)
           ELSE UNCHANGED <<lob, pst, tcnt, nch, chain>>
        /\ IF isLast
           THEN IF pause THEN cs' = "held" /\ UNCHANGED <<cur, cheld>>
                ELSE cs' = "none" /\ cur' = 0 /\ cheld' = NoHold
           ELSE UNCHANGED <<cs, cur, cheld>>
        /\ holds' = nholds
        /\ hctx' = Append(hctx, PHolds(nholds))
  /\ UNCHANGED <<srcv, rmax, cpos, pend, topic, committed, crashes, s0, hist,
                 crashrec, chold, hx, rhist, rcur, rplan>>

HoldRestore(c) ==
  IF Record THEN holds
  ELSE IF HoldMode = "reexec" THEN {}
  ELSE CASE c = -1 -> PHolds(holds)
         [] c = 0  -> chold
         [] OTHER  -> hctx[c]

CrashH(c) ==
  /\ Crash(c)
  /\ holds' = HoldRestore(c)
  /\ chold' = HoldRestore(c)
  /\ hctx' = <<>>
  /\ cheld' = NoHold /\ rcur' = 0 /\ rplan' = {}
  /\ UNCHANGED <<hx, rhist>>

CrashEarlyH(a) ==
  /\ CrashEarly(a)
  /\ hctx' = <<>>
  /\ UNCHANGED <<holds, chold, cheld, hx, rhist, rcur, rplan>>

RelLW(hd) ==
  /\ Cap > 0
  /\ hd \in holds
  /\ IF HoldMode = "reexec" THEN cs = "held" ELSE cs = "none"
  /\ cpos = Len(log)
  /\ log' = Append(log, [t |-> "rlw", k |-> 0, v |-> NULL, x |-> Len(rhist) + 1])
  /\ cpos' = Len(log) + 1
  /\ rhist' = Append(rhist,
       [hd |-> hd, inc |-> crashes, lw |-> Len(log) + 1, hw |-> 0, qpos |-> 0,
        lo |-> hd.lo, hi |-> hd.hi, page |-> {}, val |-> NullRow, inv |-> {},
        cl |-> FALSE, plan |-> {}])
  /\ rcur' = Len(rhist) + 1
  /\ cs' = "rlw"
  /\ UNCHANGED <<vis, nW, progv, cur, cplan, pend, out, topic, committed, crashes,
                 s0, hist, chain, crashrec, holds, hctx, chold, cheld, hx, rplan>>

RelQuery(V) ==
  /\ cs = "rlw"
  /\ V \subseteq (1..nW) \ vis
  /\ vis' = vis \cup V
  /\ VisRule = "wait" =>
       \A p \in 1..(rhist[rcur].lw - 1) : IsData(p) => log[p].x \in vis'
  /\ LET r  == rhist[rcur]
         pg == {k \in RangeKeys(r.lo, r.hi) : SnapK(vis', k) # NULL}
     IN rhist' = [rhist EXCEPT ![rcur].qpos = Len(log), ![rcur].page = pg,
                    ![rcur].val = [k \in Keys |-> IF k \in pg THEN SnapK(vis', k) ELSE NULL],
                    ![rcur].inv = (1..nW) \ vis']
  /\ cs' = "rq"
  /\ UNCHANGED <<log, nW, progv, cur, cplan, cpos, pend, out, topic, committed,
                 crashes, s0, hist, chain, crashrec, holds, hctx, chold, cheld, hx,
                 rcur, rplan>>

RelHW ==
  /\ cs = "rq"
  /\ cpos = Len(log)
  /\ log' = Append(log, [t |-> "rhw", k |-> 0, v |-> NULL, x |-> rcur])
  /\ cpos' = Len(log) + 1
  /\ LET p     == Len(log) + 1
         r     == rhist[rcur]
         rng   == RangeKeys(r.lo, r.hi)
         winTx == {log[q].x : q \in {q \in (r.lw + 1)..Len(log) : IsData(q)}}
         wk    == {TxKey(x) : x \in winTx}
         notSeen(x) == x \in r.inv \/ TxPos(x) > r.qpos
         gp    == CASE VisRule \in {"changed", "chunk"} ->
                         {TxKey(x) : x \in {y \in pend : notSeen(y)}}
                    [] VisRule = "window" ->
                         {TxKey(x) : x \in {y \in winTx : notSeen(y)}}
                    [] OTHER -> {}
         chg   == ((IF RelNoWindow THEN {} ELSE wk) \cup gp) \cap rng
         rows  == r.page \ chg
         cands == (rng \ r.page) \ chg
         npend == CASE VisRule = "changed" -> {y \in pend : notSeen(y)}
                    [] OTHER -> {}
         pause == HoldMode = "reexec"
     IN \E A \in (IF StaleRelease THEN {r.hd.abs}
                  ELSE IF Dense \/ Record THEN {cands} ELSE SUBSET cands) :
          LET plan  == IF Record THEN rows \cup A ELSE A
              ks    == SeqOf(plan)
              done  == plan = {} \/ Record
              pr    == IF done /\ pause THEN AftOf(cur) ELSE Prog
              block == [i \in 1..Len(ks) |->
                         [kd |-> IF Record /\ ks[i] \in rows THEN "row" ELSE "abs",
                          key |-> ks[i],
                          v |-> IF Record /\ ks[i] \in rows THEN r.val[ks[i]] ELSE NULL,
                          tag |-> p, ex |-> 0 - rcur, ctx |-> MkCtx(p, pr, PCtx(npend))]]
          IN /\ rhist' = [rhist EXCEPT ![rcur].hw = p, ![rcur].cl = TRUE, ![rcur].plan = plan]
             /\ pend' = npend
             /\ IF done
                THEN /\ out' = out \o block
                     /\ holds' = holds \ {r.hd}
                     /\ hctx' = hctx \o [i \in 1..Len(block) |-> PHolds(holds \ {r.hd})]
                     /\ cs' = "none" /\ rcur' = 0 /\ rplan' = {}
                     /\ IF pause
                        THEN /\ lob' = AftOf(cur).lob /\ pst' = AftOf(cur).pst
                             /\ tcnt' = AftOf(cur).tcnt /\ nch' = AftOf(cur).nch
                             /\ chain' = Append(chain, cur) /\ cur' = 0 /\ cheld' = NoHold
                        ELSE UNCHANGED <<lob, pst, tcnt, nch, chain, cur, cheld>>
                ELSE /\ cs' = "rclose" /\ rplan' = plan
                     /\ UNCHANGED <<out, holds, hctx, rcur, lob, pst, tcnt, nch, chain,
                                    cur, cheld>>
  /\ UNCHANGED <<vis, nW, rmax, cplan, topic, committed, crashes, s0, hist, crashrec,
                 chold, hx>>

RelEmit(k) ==
  /\ cs = "rclose" /\ k \in rplan
  /\ LET r      == rhist[rcur]
         isLast == rplan = {k}
         pause  == HoldMode = "reexec"
         pr     == IF isLast /\ pause THEN AftOf(cur) ELSE Prog
         it     == [kd |-> "abs", key |-> k, v |-> NULL, tag |-> r.hw, ex |-> 0 - rcur,
                    ctx |-> MkCtx(r.hw, pr, PCtx(pend))]
         nholds == IF isLast THEN holds \ {r.hd} ELSE holds
     IN /\ out' = Append(out, it)
        /\ rplan' = rplan \ {k}
        /\ holds' = nholds
        /\ hctx' = Append(hctx, PHolds(nholds))
        /\ IF isLast
           THEN /\ cs' = "none" /\ rcur' = 0
                /\ IF pause
                   THEN /\ lob' = AftOf(cur).lob /\ pst' = AftOf(cur).pst
                        /\ tcnt' = AftOf(cur).tcnt /\ nch' = AftOf(cur).nch
                        /\ chain' = Append(chain, cur) /\ cur' = 0 /\ cheld' = NoHold
                   ELSE UNCHANGED <<lob, pst, tcnt, nch, chain, cur, cheld>>
           ELSE UNCHANGED <<cs, rcur, lob, pst, tcnt, nch, chain, cur, cheld>>
  /\ UNCHANGED <<srcv, rmax, cplan, cpos, pend, topic, committed, crashes, s0, hist,
                 crashrec, chold, hx, rhist>>

NextH ==
  \/ \E k \in Keys, v \in Img : WriteH(k, v)
  \/ \E V \in SUBSET (1..MaxWrites) : StartPassH(V)
  \/ WriteLWH
  \/ \E V \in SUBSET (1..MaxWrites) : QueryH(V)
  \/ WriteHWH
  \/ \E k \in Keys : EmitCloseH(k)
  \/ ConsumeH
  \/ \E c \in -1..Len(out) : CrashH(c)
  \/ \E a \in 0..Len(out) : CrashEarlyH(a)
  \/ \E hd \in holds : RelLW(hd)
  \/ \E V \in SUBSET (1..MaxWrites) : RelQuery(V)
  \/ RelHW
  \/ \E k \in Keys : RelEmit(k)

SpecH == InitH /\ [][NextH]_varsH

-----------------------------------------------------------------------------
(* Properties *)

NotRefused(it) == it.kd # "uabs"
Applied == IF SinkAppliesUnconfirmed THEN Stream ELSE SelectSeq(Stream, NotRefused)
NoPending == holds = {}

TypeOKH ==
  /\ nW \in 0..MaxWrites /\ vis \subseteq 1..nW
  /\ \A p \in 1..Len(log) :
       \/ (log[p].t = "d" /\ log[p].k \in Keys /\ log[p].v \in Img /\ log[p].x \in 1..nW)
       \/ (log[p].t \in {"lw", "hw"} /\ log[p].x \in 1..Len(hist))
       \/ (log[p].t \in {"rlw", "rhw"} /\ log[p].x \in 1..Len(rhist))
  /\ pst \in {"pre", "main", "tail", "complete", "limit"}
  /\ lob \in 0..N /\ rmax \in 0..N /\ tcnt \in 0..TailLimit
  /\ cs \in {"none", "lw", "q", "close", "held", "rlw", "rq", "rclose"}
  /\ cpos \in 0..Len(log) /\ pend \subseteq 1..nW
  /\ crashes \in 0..MaxCrashes /\ s0 \in 0..Len(log)
  /\ \A i \in 1..Len(Stream) :
       /\ Stream[i].kd \in {"ev", "row", "abs", "uabs"} /\ Stream[i].key \in Keys
       /\ Stream[i].v \in Img /\ Stream[i].tag \in 1..Len(log)
  /\ Len(hctx) = Len(out)
  /\ \A hd \in holds : hd.ex \in hx /\ hd.lo = hist[hd.ex].lo /\ hd.hi = hist[hd.ex].hi
  /\ (rcur # 0) <=> (cs \in {"rlw", "rq", "rclose"})
  /\ (cs = "held") => (HoldMode = "reexec" /\ holds = {cheld})
  /\ Cap = 0 => (holds = {} /\ hx = {} /\ rhist = <<>> /\ cheld = NoHold)

\* every released absence entry: the source holds no row at the release's own position
HoldsSafe ==
  \A i \in 1..Len(Stream) :
    (Stream[i].ex < 0 /\ Stream[i].kd = "abs") => SrcK(Stream[i].tag, Stream[i].key) = NULL

SinkValueExistedH ==
  LET S == Applied IN
  \A k \in Keys, d \in Img : ReplayK(d, k, S) \in {d} \cup Existed(k)

\* --- the bridge: chunk units (P) with the refusal of an unconfirmed record
RefusedE(e) == \E i \in 1..Len(Stream) : Stream[i].ex = e /\ Stream[i].kd = "uabs"
FullyDelH(S, e) ==
  /\ hist[e].cl
  /\ IF (Dense \/ Record) /\ ~RefusedE(e)
     THEN Delivered(S, e) = hist[e].plan
     ELSE hist[e].plan \cap hist[e].page \subseteq Delivered(S, e)
DomH(S, e) == (IF FullyDelH(S, e) THEN RangeOf(e) ELSE Delivered(S, e)) \ TrueGap(e)
IsUnitH(S, e) == hist[e].cl /\ (FullyDelH(S, e) \/ Delivered(S, e) # {})
UnitOKH(S, e) ==
  LET h == hist[e]
      D == DomH(S, e)
      L == Delivered(S, e)
  IN /\ s0 <= h.lw /\ h.lw < h.hw /\ h.hw <= Len(log)
     /\ \A k \in D : \E c \in h.lw..h.hw : Refresh(e, k) = SrcK(c, k)
     /\ L \subseteq D
     /\ {k \in D : Refresh(e, k) # NULL /\ NoWin(e, k)} \subseteq L
     /\ \A k \in L : NoWin(e, k)
     /\ \A i \in DelIdx(S, e) : S[i].v = Refresh(e, S[i].key) /\ S[i].tag = h.hw
     /\ Cardinality(DelIdx(S, e)) = Cardinality(L)
O1OKH(S) ==
  \A e1, e2 \in 1..Len(hist) :
    (e1 < e2 /\ IsUnitH(S, e1) /\ IsUnitH(S, e2) /\ hist[e1].inc = hist[e2].inc)
      => DomH(S, e1) \cap DomH(S, e2) = {}
RestartOKH(S) ==
  Len(crashrec) = 1 =>
    /\ s0 <= crashrec[1].cmt
    /\ crashrec[1].cmt <= crashrec[1].cpt
    /\ crashrec[1].cpt <= Len(log)
    /\ \A e \in 1..Len(hist) :
         (hist[e].inc = 0 /\ IsUnitH(S, e)) => hist[e].hw <= crashrec[1].cpt
    /\ \A e \in 1..Len(hist) : hist[e].inc >= 1 => hist[e].lw >= crashrec[1].cpt

\* --- the bridge: release units (R)
RDelIdx(S, r) == {i \in 1..Len(S) : S[i].ex = 0 - r}
RDelivered(S, r) == {S[i].key : i \in RDelIdx(S, r)}
RRange(r) == RangeKeys(rhist[r].lo, rhist[r].hi)
RTrueGap(r) == {TxKey(x) : x \in {y \in rhist[r].inv : TxPos(y) < rhist[r].lw}}
RNoWin(r, k) == \A p \in (rhist[r].lw + 1)..rhist[r].hw : ~(IsData(p) /\ log[p].k = k)
RFullyDel(S, r) ==
  /\ rhist[r].cl
  /\ (Dense \/ Record) => RDelivered(S, r) = rhist[r].plan
RDomBase(r) == IF Record THEN RRange(r) ELSE {k \in RRange(r) : rhist[r].val[k] = NULL}
RDom(S, r) == (IF RFullyDel(S, r) THEN RDomBase(r) ELSE RDelivered(S, r)) \ RTrueGap(r)
IsRUnit(S, r) == rhist[r].cl /\ (RFullyDel(S, r) \/ RDelivered(S, r) # {})
RUnitOK(S, r) ==
  LET h == rhist[r]
      D == RDom(S, r)
      L == RDelivered(S, r)
  IN /\ s0 <= h.lw
     /\ h.lw < h.hw /\ h.hw <= Len(log)
     /\ \A k \in D : \E c \in h.lw..h.hw : h.val[k] = SrcK(c, k)
     /\ L \subseteq D
     /\ {k \in D : h.val[k] # NULL /\ RNoWin(r, k)} \subseteq L
     /\ \A k \in L : RNoWin(r, k)
     /\ \A i \in RDelIdx(S, r) : S[i].v = h.val[S[i].key] /\ S[i].tag = h.hw
     /\ Cardinality(RDelIdx(S, r)) = Cardinality(L)
RO1OK(S) ==
  \A r1, r2 \in 1..Len(rhist) :
    (/\ r1 < r2 /\ IsRUnit(S, r1) /\ IsRUnit(S, r2) /\ rhist[r1].inc = rhist[r2].inc
     /\ ~(Record /\ crashes > 0))
      => RDom(S, r1) \cap RDom(S, r2) = {}

PartOKH(i, S) ==
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
     /\ \A x \in idx \ evx :
          IF S[x].ex > 0
          THEN hist[S[x].ex].inc = i /\ S[x].tag = hist[S[x].ex].hw
          ELSE rhist[0 - S[x].ex].inc = i /\ S[x].tag = rhist[0 - S[x].ex].hw
StreamShapeH == LET S == Stream IN \A i \in 0..Len(crashrec) : PartOKH(i, S)

PassEnd ==
  LET hs == {hist[e].hw : e \in {e \in 1..Len(hist) : hist[e].cl}}
  IN IF hs = {} THEN s0 ELSE Max(hs)
CompositionOK(S) ==
  (/\ crashes = 0 /\ pst \in {"complete", "limit"}
   /\ \E r \in 1..Len(rhist) : IsRUnit(S, r)
   /\ \A r \in 1..Len(rhist) : IsRUnit(S, r) => rhist[r].lw >= PassEnd)
  => /\ s0 <= PassEnd
     /\ PassEnd <= Len(log)
     /\ \A e \in 1..Len(hist) : IsUnitH(S, e) => hist[e].hw <= PassEnd
     /\ \A r \in 1..Len(rhist) : IsRUnit(S, r) => PassEnd <= rhist[r].lw

LocaleAssumptionsH ==
  LET A == Applied IN
  /\ StreamShapeH
  /\ \A e \in 1..Len(hist) : IsUnitH(A, e) => UnitOKH(A, e)
  /\ O1OKH(A)
  /\ RestartOKH(A)
  /\ \A r \in 1..Len(rhist) : IsRUnit(A, r) => RUnitOK(A, r)
  /\ RO1OK(A)
  /\ CompositionOK(A)

CScopeH(S) ==
  {k \in Keys : \/ \E e \in 1..Len(hist) : IsUnitH(S, e) /\ k \in DomH(S, e)
                \/ \E r \in 1..Len(rhist) : IsRUnit(S, r) /\ k \in RDom(S, r)}

ScopeBridgeH ==
  Quiescent =>
    LET S == Applied IN
    \A k \in Scope : k \in CScopeH(S) \/ ~NoEvents(k)

QuiescentSafeH ==
  Quiescent =>
    LET S == Applied IN
    \A k \in CScopeH(S), d \in Img :
      LET r == ReplayK(d, k, S) IN
      \/ r = SrcK(Frontier, k)
      \/ (r = d /\ SrcK(Frontier, k) = NULL /\ ~Listed(S, k) /\ NoEvents(k))

QuiescentConvergesH ==
  Quiescent =>
    LET S == Applied IN
    \A k \in Scope, d \in Img :
      ((d # NULL /\ SrcK(Frontier, k) = NULL /\ NoEvents(k)) => Listed(S, k))
        => ReplayK(d, k, S) = SrcK(Frontier, k)

ReleasedConverges ==
  (Quiescent /\ NoPending) =>
    LET S == Applied IN
    \A r \in 1..Len(rhist) :
      IsRUnit(S, r) =>
        \A k \in RRange(r), d \in Img :
          ((d # NULL /\ SrcK(Frontier, k) = NULL /\ NoEvents(k)) => Listed(S, k))
            => ReplayK(d, k, S) = SrcK(Frontier, k)

RecordConvergesH ==
  ((Dense \/ Record) /\ Quiescent /\ NoPending) =>
    LET S == Applied IN
    \A k \in Scope, d \in Img : ReplayK(d, k, S) = SrcK(Frontier, k)

DeliveredRecordAbsenceH ==
  ((Dense \/ Record) /\ Quiescent /\ NoPending) =>
    LET S == Applied IN
    \A e \in 1..Len(hist) :
      (hist[e].cl /\ Delivered(Stream, e) # {}) =>
        \A k \in RangeOf(e), d \in Img :
          (Refresh(e, k) = NULL /\ k \notin TrueGap(e) /\ NoWin(e, k) /\
           \A p \in (hist[e].hw + 1)..Len(log) : ~(IsData(p) /\ log[p].k = k))
          => ReplayK(d, k, S) = NULL

CapGuard ==
  LET S == Applied IN
  \A i \in 1..Len(S) :
    /\ S[i].kd # "uabs"
    /\ (S[i].kd = "abs" /\ S[i].ex > 0) =>
         /\ ~EmptyTab(hist[S[i].ex])
         /\ ~Record => Cardinality({j \in 1..Len(Stream) :
                                     Stream[j].ex = S[i].ex /\ Stream[j].kd = "abs"}) <= Cap

-----------------------------------------------------------------------------
(* Witness probes, EXPECTED TO BE VIOLATED *)

WitReleaseDone ==
  ~(Quiescent /\ NoPending /\
    \E r \in 1..Len(rhist) : IsRUnit(Applied, r) /\ RDelivered(Applied, r) # {})
WitReleaseInPass ==
  ~(\E r \in 1..Len(rhist), e \in 1..Len(hist) : rhist[r].cl /\ hist[e].lw > rhist[r].hw)
WitReleaseAfterPass ==
  ~(Quiescent /\ \E r \in 1..Len(rhist) : rhist[r].cl /\ rhist[r].lw > PassEnd)
WitInsertBeforeRelease ==
  ~(\E r \in 1..Len(rhist) :
      rhist[r].cl /\ \E k \in RRange(r) : k \in rhist[r].page /\ k \notin hist[rhist[r].hd.ex].page)
WitReleaseWindowChange ==
  ~(\E r \in 1..Len(rhist) :
      rhist[r].cl /\ \E k \in RRange(r) : ~RNoWin(r, k) /\ rhist[r].val[k] = NULL)
WitHoldAcrossCrash ==
  ~(\E r \in 1..Len(rhist) : rhist[r].cl /\ rhist[r].inc > hist[rhist[r].hd.ex].inc)
WitHeldAgain ==
  ~(\E e1, e2 \in hx : e1 < e2 /\ RangeOf(e1) = RangeOf(e2) /\ hist[e1].inc < hist[e2].inc)
WitEmptyTableRelease ==
  ~(\E r \in 1..Len(rhist) :
      rhist[r].cl /\ EmptyTab(hist[rhist[r].hd.ex]) /\ RDelivered(Applied, r) # {})
WitRefusedReleased ==
  ~(Quiescent /\ NoPending /\ \E i \in 1..Len(Stream) : Stream[i].kd = "uabs")
\* Record with a crash: two releases of one range in one incarnation (a refused record
\* stays in the stream while its chunk is re-executed and refused again)
WitDuplicateHold ==
  ~(\E r1, r2 \in 1..Len(rhist) :
       /\ r1 < r2 /\ rhist[r1].cl /\ rhist[r2].cl /\ rhist[r1].inc = rhist[r2].inc
       /\ RRange(r1) = RRange(r2))
=============================================================================
