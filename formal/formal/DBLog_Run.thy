(*  Title:   DBLog_Run.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory DBLog_Run
  imports DBLog_Run_Core
begin

section \<open>Layer 1: the DBLog run carrier, accessors, and wellformedness\<close>

text \<open>
  Layer 1 abstract DBLog run substrate.

  Layer 1 vocabulary:

    \<^item> chunks: the paper's @{text "('k, 'v) chunk"} carrier, modeled
        here concretely as the chunk index @{typ nat};
    \<^item> @{text "('k, 'v) chunk_read_record"}: Layer 0 self-contained
        chunk-read record carrying @{text "(domain, read_coord,
        observation)"}; the paper places this at Layer 0 inside the
        canonical-clean-prefix construction's input shape, and the
        Isabelle artifact lives in the imported theory
        @{text DBLog_Run_Core} (the carrier-independent Layer 0/1 core),
        consumed via the Layer 1 @{text clean_prefix_of} accessor's
        definitional equality;
    \<^item> @{text "('k, 'v) run"}: Layer 1 run carrier (a concrete
        single-constructor @{command datatype}, below);
    \<^item> Run accessors (paper "Run carrier and accessors", 7
        accessors): @{text scope_of} / @{text frontier_of} /
        @{text clean_prefix_of} / @{text chunks} /
        @{text src_history_of} / @{text chunk_read_result} /
        @{text cdc_events_of};
    \<^item> Chunk-plan accessors (paper "Chunk-plan accessors"):
        @{text chunk_domain} / @{text owns} /
        @{text responsible_chunk} /
        @{text canonical_chunk_ownership_domain};
    \<^item> Chunk watermarks (paper "Watermarks and Chunk-Read Coordinates"):
        @{text chunk_lower_watermark} /
        @{text chunk_upper_watermark} / @{text chunk_read_coordinate};
    \<^item> Coverage predicates (paper "Coverage predicates"):
        @{text covers_ordinary_cdc} / @{text row_absence_meaningful};
    \<^item> @{text canonical_clean_prefix}: Layer 0 building block paper
        "Auxiliary Layer 0 definitions" / "Canonical clean prefix";
        the paper places this at Layer 0 and the Isabelle artifact
        lives in the imported theory @{text DBLog_Run_Core}, with the
        Layer 1 @{text clean_prefix_of} accessor (below) its consumer;
    \<^item> @{text wellformed_dblog_run}: 3-argument predicate
        @{text "wellformed_dblog_run b0 R H"}; the body is the
        seven-clause conjunction WF0 / WF1 / WF2 / WF4 / WF5 / WF6 /
        WF7. There is no WF3 clause: the numbering carries a
        deliberate gap recording a clause that the model no longer
        uses.

  The run carrier and its accessors are defined here;
  @{text wellformed_dblog_run}, @{text covers_ordinary_cdc}, and
  @{text row_absence_meaningful} are real Isabelle definitions
  transliterating their paper bodies, and @{text clean_prefix_of} is
  determined by the canonical-clean-prefix construction in the imported
  theory @{text DBLog_Run_Core}.

  @{text owns} is an @{command abbreviation} over @{text chunk_domain}
  --- @{text "owns R ch k \<equiv> k \<in> chunk_domain R ch"} --- following the
  paper's reader-facing definitional equivalence; this rules out any
  gap where two independent accessors could disagree on a
  non-wellformed run.

  Run accessors use the @{text "_of"} suffix --- @{text "scope_of R"},
  @{text "frontier_of R"}, @{text "clean_prefix_of R"},
  @{text "src_history_of R"}, @{text "cdc_events_of R"}; certificate
  accessors live in @{text Virtual_Cut} with bare names.

  Naming note on the chunk-read record: the record-component selectors
  in Isabelle/HOL @{command record} blocks default to plain names
  ( @{text domain} / @{text read_coord} / @{text observation} );
  to avoid shadowing pre-existing Isabelle names (the standard
  @{text Domain} relation-domain projector lives in @{text Relation}),
  the selectors here are prefixed @{text "crr_"} ( @{text crr_domain}
  / @{text crr_read_coord} / @{text crr_observation} ). The
  paper-side names are unaffected.
\<close>

subsection \<open>Run carrier (concrete datatype)\<close>

text \<open>
  The run carrier is a concrete single-constructor @{command datatype} with
  named selectors (prefixed @{text "rr_"}). It is a @{command datatype} rather
  than a @{command record}: a record introduces an extensible @{text "_ext"}
  type and makes the bare name a type synonym, whereas the datatype keeps
  @{text run} a clean two-parameter type constructor. The
  @{text dblog_run_substrate} locale's canonical
  @{command global_interpretation} interprets the locale at this datatype via
  the global accessors below, so every locale-proved fact is available for
  the global headline theorems.

  Chunks are modeled as @{typ nat} (the chunk index): the chunk-plan accessors
  and watermarks are function fields keyed by the chunk index. The raw chunk
  enumeration @{text rr_chunks_list} is a @{typ "nat list"}; the public
  @{text chunks_list} accessor is @{term remdups} of it, so the two
  @{text chunks_list} facts below hold definitionally as lemmas.

  The Layer 0 self-contained @{type chunk_read_record} (selectors
  @{const crr_domain} / @{const crr_read_coord} / @{const crr_observation})
  is defined in theory @{text DBLog_Run_Core}, imported above: a
  carrier-independent building block shared by this global development and the
  @{text dblog_run_substrate} locale.
\<close>

datatype ('k, 'v) run =
  Run (rr_scope: "'k set")
      (rr_frontier: frontier)
      (rr_chunks_list: "nat list")
      (rr_src_history: "('k, 'v) src_history")
      (rr_cdc: "(src_coord \<times> ('k, 'v) source_event) list")
      (rr_rresult: "nat \<Rightarrow> 'k \<Rightarrow> 'v option option")
      (rr_dom: "nat \<Rightarrow> 'k set")
      (rr_resp: "'k \<Rightarrow> nat option")
      (rr_lwm: "nat \<Rightarrow> src_coord")
      (rr_uwm: "nat \<Rightarrow> src_coord")
      (rr_rcoord: "nat \<Rightarrow> src_coord")

subsection \<open>Run accessors (7 accessors)\<close>

text \<open>
  Paper "Run carrier and accessors". Seven accessors project the
  run-level structure that the rest of Layer 1 + the Layer 2 theorem
  range over. Chunk-plan accessors and watermarks live in their own
  subsections below; the @{text clean_prefix_of} accessor's
  definitional equality (paper "Clean-prefix construction at Layer
  1") is recorded at the @{text canonical_clean_prefix} subsection
  below.
\<close>

definition scope_of :: "('k, 'v) run \<Rightarrow> 'k set"
  where "scope_of R = rr_scope R"

definition frontier_of :: "('k, 'v) run \<Rightarrow> frontier"
  where "frontier_of R = rr_frontier R"

definition chunks :: "('k, 'v) run \<Rightarrow> nat set"
  where "chunks R = set (rr_chunks_list R)"

definition src_history_of :: "('k, 'v) run \<Rightarrow> ('k, 'v) src_history"
  where "src_history_of R = rr_src_history R"

definition chunk_read_result :: "('k, 'v) run \<Rightarrow> nat \<Rightarrow> 'k \<Rightarrow> 'v option option"
  where "chunk_read_result R = rr_rresult R"

definition cdc_events_of :: "('k, 'v) run \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
  where "cdc_events_of R = rr_cdc R"

text \<open>
  The @{text clean_prefix_of} accessor is not declared here. It is
  defined as the Layer 1 definitional equality (paper "Clean-prefix
  construction at Layer 1") below, after the @{text chunks_list}
  accessor and the @{text canonical_clean_prefix} construction have
  been introduced.
\<close>

subsection \<open>Chunks enumeration accessor\<close>

text \<open>
  The paper's clean-prefix construction at Layer 1 writes the
  chunk-reads input to @{text canonical_clean_prefix} as the list
  comprehension
  @{text "[ ChunkReadRecord(chunk_domain(R, ch),
  chunk_read_coordinate(R, ch), chunk_read_result(R, ch)) | ch \<in>
  chunks(R) ]"}. This requires enumerating the chunk set
  @{text "chunks(R)"} as a list in a deterministic order. The run
  carrier therefore stores a raw enumeration field
  @{text rr_chunks_list}; the public accessor @{text chunks_list}
  is its @{const remdups}, @{const chunks} is its set, and the two
  properties tying the enumeration to @{const chunks} are proved
  just below as lemmas:

    \<^item> @{text chunks_list_set}: @{text "set (chunks_list R) = chunks R"};
    \<^item> @{text chunks_list_distinct}: @{text "distinct (chunks_list R)"}.

  Two properties of this enumeration must be stated plainly,
  because they are easy to mistake for a harmless enumeration
  convenience.

  The first is global finiteness. @{text chunks_list_set}
  equates @{term "chunks R"} with the set of a list, so
  @{term "finite (chunks R)"} holds for every run, not only
  for wellformed ones. This is a genuine modeling decision
  baked into the carrier --- a run's chunk plan is stored as a
  finite list --- and it is intended and sound for the DBLog
  domain: a run's chunk plan is bounded by construction, because
  chunking proceeds over a determinable key range (a maximum
  primary key, or an equivalent keyspace bound, is fixed before
  chunking begins as the termination criterion), so the chunk
  plan is finite for every run. The lemma @{text chunks_finite}
  just below records this consequence as a named,
  machine-checked fact. The wellformed-run predicate's WF1 (f)
  clause separately requires @{term "finite (scope_of R)"} and
  finiteness of each chunk domain, but does not restate
  chunk-set finiteness --- that fact holds globally and is
  established here.

  The second is that the enumeration order is not canonical. The
  accessor returns the run's stored enumeration with duplicates
  removed, so two runs with the same chunk set may enumerate it
  in different orders. The Layer 2 source-side soundness theorem
  does not depend on the choice: at one source coordinate,
  cross-chunk-read Refresh events affect distinct keys (by the
  strict canonical partition), so the per-key replay semantics
  is invariant across enumeration choices.

  Pragmatic alternative considered + rejected: Hilbert epsilon
  @{text "(SOME xs. distinct xs \<and> set xs = chunks R)"} would avoid
  the stored enumeration field but would force every downstream
  proof to reason about non-determinism explicitly; a documented
  enumeration accessor over a stored field is cleaner.
\<close>

definition chunks_list :: "('k, 'v) run \<Rightarrow> nat list"
  where "chunks_list R = remdups (rr_chunks_list R)"

lemma chunks_list_set: "set (chunks_list R) = chunks R"
  by (simp add: chunks_list_def chunks_def)

lemma chunks_list_distinct: "distinct (chunks_list R)"
  by (simp add: chunks_list_def)

text \<open>
  The global finiteness documented above, recorded as a named
  fact. Since @{text chunks_list_set} equates @{term "chunks R"}
  with @{term "set (chunks_list R)"}, the set of a list,
  @{term "finite (chunks R)"} holds for every run. Stating it as
  a lemma keeps the global modeling assumption visible and
  machine-checked rather than left implicit in the carrier
  definition.
\<close>

lemma chunks_finite: "finite (chunks R)"
  by (metis chunks_list_set List.finite_set)

subsection \<open>Chunk-plan accessors\<close>

text \<open>
  Paper "Chunk-plan accessors". Naming: @{text chunk_domain} is the
  keys a chunk \<^emph>\<open>owns\<close>; @{text responsible_chunk} is the
  inverse projecting from a key to its owning chunk;
  @{text canonical_chunk_ownership_domain} is the union of chunk
  domains over all chunks of @{text R}.

  @{text owns} is an @{command abbreviation} over @{text chunk_domain}
  --- @{text "owns R ch k \<equiv> k \<in> chunk_domain R ch"} --- per the paper's
  reader-facing definitional equivalence (paper "Chunk-plan
  accessors": @{text "owns(R, ch, k) :: bool \<Leftrightarrow> k \<in> chunk_domain(R, ch)"}).
  Making it an abbreviation rather than an independent accessor rules
  out any gap where @{text owns} and @{text chunk_domain} could
  disagree on a non-wellformed run.
\<close>

definition chunk_domain :: "('k, 'v) run \<Rightarrow> nat \<Rightarrow> 'k set"
  where "chunk_domain R = rr_dom R"

definition responsible_chunk :: "('k, 'v) run \<Rightarrow> 'k \<Rightarrow> nat option"
  where "responsible_chunk R = rr_resp R"

abbreviation owns
  :: "('k, 'v) run \<Rightarrow> nat \<Rightarrow> 'k \<Rightarrow> bool"
where
  "owns R ch k \<equiv> k \<in> chunk_domain R ch"

definition canonical_chunk_ownership_domain
  :: "('k, 'v) run \<Rightarrow> 'k set"
where
  "canonical_chunk_ownership_domain R =
     (\<Union>ch \<in> chunks R. chunk_domain R ch)"

subsection \<open>Chunk watermarks and read coordinates\<close>

text \<open>
  Paper "Watermarks and Chunk-Read Coordinates". Three source-coordinate
  accessors per chunk: lower watermark, upper watermark, and the
  actual read coordinate. WF4 (clause body in the paper) requires
  @{text "lower \<le>\<^sub>src read \<le>\<^sub>src upper"}; WF5 additionally requires
  @{text "read \<le>\<^sub>src frontier_of(R)"}.
\<close>

definition chunk_lower_watermark :: "('k, 'v) run \<Rightarrow> nat \<Rightarrow> src_coord"
  where "chunk_lower_watermark R = rr_lwm R"

definition chunk_upper_watermark :: "('k, 'v) run \<Rightarrow> nat \<Rightarrow> src_coord"
  where "chunk_upper_watermark R = rr_uwm R"

definition chunk_read_coordinate :: "('k, 'v) run \<Rightarrow> nat \<Rightarrow> src_coord"
  where "chunk_read_coordinate R = rr_rcoord R"

text \<open>
  The Layer 0 canonical-clean-prefix construction --- @{const canonical_clean_prefix}
  with its builders @{const chunk_read_refreshes} / @{const cdc_event_replays},
  the @{const refresh_dominated} / @{const canonical_clean_prefix_normalized}
  normalized companion, and the Apply-equivalence theorem
  @{thm [source] apply_canonical_clean_prefix_normalized_eq} --- is defined in
  theory @{text DBLog_Run_Core}, imported above. It references no run/chunk
  accessor, so it is shared verbatim by this global theory and the
  @{text dblog_run_substrate} locale.
\<close>

subsection \<open>Layer 1 clean-prefix definitional equality (@{text clean_prefix_of})\<close>

text \<open>
  Paper "Clean-prefix construction at Layer 1": Layer 1's
  @{text "clean_prefix_of(R)"} is not a fresh primitive --- it is the
  Layer 0 @{text canonical_clean_prefix} building block instantiated
  for the run, with the chunk-read argument lifted out of an opaque
  "observed rows" assertion into per-chunk @{type chunk_read_record}
  values populated from the named accessors @{const chunk_domain},
  @{const chunk_read_coordinate}, and @{const chunk_read_result}, and
  with the CDC-side argument lifted out of "the source history's
  events" into the run-derived @{const cdc_events_of} accessor.

  @{text clean_prefix_of} is a real @{command definition} via this
  Layer 1 definitional equality. The signature carries a
  @{class linorder} constraint on @{text 'k} (propagated from
  @{text canonical_clean_prefix}); consumers (@{text wellformed_dblog_run},
  the Layer 2 source-side soundness theorem, downstream Layer 3
  certificate composition) inherit the constraint.

  Consequences:

    \<^item> the run carrier does not have to commit independently to a
        clean-prefix list shape; the wellformed-DBLog-run predicate's
        body constrains the run's @{const chunk_read_result},
        @{const chunks}, @{const scope_of}, @{const src_history_of},
        @{const cdc_events_of}, and @{const frontier_of} accessors,
        and @{text clean_prefix_of} is then determined by the
        construction;
    \<^item> the Layer 2 source-side soundness theorem can reason about
        @{text "clean_prefix_of(R)"} as a closed-form expression in
        the run's accessors, without needing a separate "clean prefix
        is some interleaving of chunk reads and CDC events"
        wellformedness clause;
    \<^item> the potential counterexample shape --- a
        @{text Cdc}-before-@{text Refresh} order at distinct source
        coordinates that satisfies all set-membership-shaped WF
        clauses but breaks the Layer 2 conclusion --- is structurally
        neutralized: under the construction body,
        @{text "clean_prefix_of(R)"} is sorted by source coordinate,
        so a low-coord @{text Cdc} cannot follow a high-coord
        @{text Refresh} for the same key.
\<close>

definition clean_prefix_of
  :: "('k :: linorder, 'v) run \<Rightarrow> ('k, 'v) replay_event list"
where
  "clean_prefix_of R =
     canonical_clean_prefix
       (map (\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                    crr_read_coord  = chunk_read_coordinate R ch,
                    crr_observation = chunk_read_result R ch \<rparr>)
            (chunks_list R))
       (cdc_events_of R)
       (scope_of R)
       (frontier_of R)"

subsection \<open>Coverage predicates\<close>

text \<open>
  Paper "Coverage predicates". @{text covers_ordinary_cdc} unwraps
  @{text responsible_chunk}'s @{text option} via an existential and
  compares against @{text cdc_events_of} (the run's observed CDC
  events) rather than @{text src_history_of} (the true source
  history); @{text row_absence_meaningful} is parameterized against
  @{text "Src b0 H (chunk_read_coordinate R ch) k = None"} rather
  than against an unstated "k was never inserted or deleted" reading.

  @{text covers_ordinary_cdc} is a real @{command definition}
  transliterating the paper "Coverage predicates" /
  "@{text "covers_ordinary_cdc(R, k, f)"}" body. The half-open interval
  @{text "(chunk_read_coordinate R ch, f]"} becomes
  @{text "src_lt (chunk_read_coordinate R ch) (hist_coord p)
  \<and> src_le (hist_coord p) f"} (strict on left, inclusive on right);
  the paper's "is reflected, with the same source coordinate, as a
  @{text "(c, e)"} pair in @{text "cdc_events_of(R)"}" becomes
  @{text "src_history_of R ! i \<in> set (cdc_events_of R)"} (the
  @{text "(c, e)"} pair preserved by element identity).

  @{text row_absence_meaningful} is a 5-argument predicate
  @{text "row_absence_meaningful b0 H R ch k"}, a real
  @{command definition} capturing the formalizable structural +
  source-state implication: if the key is in the chunk's domain and
  the chunk read for it produced an absence-Refresh in the clean
  prefix, then the source state at the chunk-read coordinate is
  absent (paper "Coverage predicates" / "@{text row_absence_meaningful}").
  WF6 (below) invokes it with the implication
  @{text "chunk_read_result R ch k = Some None \<longrightarrow>
  row_absence_meaningful b0 H R ch k"} on in-domain keys. That WF6
  implication is logically auto-satisfied under WF6 main alone: WF6
  main forces @{text "Src b0 H (chunk_read_coordinate R ch) k = None"},
  which discharges the predicate's body directly (machine-checked as
  @{text wf6_row_absence_redundant} in the redundancy section below).
  The predicate's role is structural rather than gating: the
  paper-side invocation exposes the deployment-level "no error / no
  partial result" obligation as reader-facing prose, and the
  formal-side predicate provides the type-level hook a deployment
  locale can state stronger assumptions against if a stronger
  operational obligation is to be expressed inside the formal model.
\<close>

definition covers_ordinary_cdc
  :: "('k, 'v) run \<Rightarrow> 'k \<Rightarrow> frontier \<Rightarrow> bool"
where
  "covers_ordinary_cdc R k f \<longleftrightarrow>
     (\<exists> ch. responsible_chunk R k = Some ch
            \<and> (\<forall> i. i < length (src_history_of R)
                     \<longrightarrow> src_lt (chunk_read_coordinate R ch)
                                (hist_coord (src_history_of R ! i))
                     \<longrightarrow> src_le (hist_coord (src_history_of R ! i)) f
                     \<longrightarrow> key_of (hist_event (src_history_of R ! i)) = k
                     \<longrightarrow> src_history_of R ! i \<in> set (cdc_events_of R)))"

text \<open>
  @{const source_key_coord_slice} (the per-key / per-coordinate filtering
  helper consumed by WF2 and the Layer 2 multiplicity lemmas) is defined in
  theory @{text DBLog_Run_Core}, imported above.
\<close>

definition row_absence_meaningful
  :: "('k :: linorder \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> ('k, 'v) run \<Rightarrow> nat \<Rightarrow> 'k \<Rightarrow> bool"
where
  "row_absence_meaningful b0 H R ch k \<longleftrightarrow>
     (k \<in> chunk_domain R ch
      \<and> Refresh k None (chunk_read_coordinate R ch) \<in> set (clean_prefix_of R)
      \<longrightarrow> Src b0 H (chunk_read_coordinate R ch) k = None)"

subsection \<open>The wellformed-DBLog-run predicate\<close>

text \<open>
  Paper "The @{text \<open>wellformed-DBLog-run\<close>} predicate". The
  three-argument signature @{text "wellformed_dblog_run b0 R H"}
  threads the source-side baseline @{text b0} through the predicate
  body, so chunk-read observations are checked against
  @{text "Src b0 H (chunk_read_coordinate R ch)"} (clause WF6). The
  7-clause body is:

  \<^item> WF0: source-history binding (@{text "src_history_of R = H"} +
    @{text "wellformed_src_history H"});
  \<^item> WF1: strict canonical chunk partition over scope +
    @{text responsible_chunk} coherence + finite-domain /
    finite-scope + non-empty-chunk-domain obligations (sub-clauses
    (a)@{text \<open>\<dots>\<close>}(g));
  \<^item> WF2 (four labeled sub-conjuncts): ordinary-CDC coverage on every
    key in scope (paper @{text covers_ordinary_cdc}) + observed-CDC
    membership faithfulness against @{text src_history_of} +
    observed-CDC order-preserving sublist coherence on the
    in-scope / at-or-before-frontier slice + post-read same-key /
    same-coordinate multiplicity. The order-preserving sublist
    condition strengthens the membership-only faithfulness conjunct
    with source-position-order preservation; this is what rules out
    a same-coordinate CDC-order reversal, where two source events at
    one coordinate appear in @{text cdc_events_of} in the opposite
    order to @{text src_history_of} and break the Layer 2 conclusion.
    The post-read multiplicity conjunct requires, for an in-scope
    key, that every source coordinate strictly after its responsible
    chunk read and at-or-before the frontier carries the same
    multiset of matching records in @{text cdc_events_of} as in
    @{text src_history_of}, closing the duplicate-record gap in the
    Cdc case of the per-key replay-equality lemma;
  \<^item> (no WF3 --- the numbering carries a deliberate gap recording a
    clause the model no longer uses);
  \<^item> WF4: chunk-read evidence (watermark bracketing +
    @{text chunk_read_result} totality on chunk domain +
    @{text Refresh}-event agreement with @{text chunk_read_result});
  \<^item> WF5: chunk-read coordinate at-or-before frontier;
  \<^item> WF6: refresh correctness against
    @{text "Src b0 H (chunk_read_coordinate R ch)"}; \<^emph>\<open>and\<close>, when
    @{text "chunk_read_result R ch k = Some None"} is observed for
    an in-domain key, @{text "row_absence_meaningful b0 H R ch k"}
    holds (the implication is auto-satisfied under WF6 main alone ---
    machine-checked as @{text wf6_row_absence_redundant}; see the
    Coverage predicates header above);
  \<^item> WF7: clean-prefix CDC coherence --- bidirectional coherence
    between @{text "cdc_events_of(R)"} and @{text Cdc} events in
    @{text "clean_prefix_of(R)"} on the in-scope /
    at-or-before-frontier filter.

  @{text wellformed_dblog_run} is a real @{command definition}
  transliterating the paper "wellformed-DBLog-run predicate" body.

  Two of the clauses warrant a closer note.

  WF7 (clean-prefix CDC coherence) makes explicit a fact that is
  otherwise only implicit in the paper's @{text covers_ordinary_cdc}
  parenthetical "so that @{text "Cdc c e"} appears in
  @{text "clean_prefix_of(R)"}". With WF7, the body enforces both
  directions --- forward: @{text cdc_events_of} @{text \<open>\<rightarrow>\<close>}
  @{text clean_prefix_of}; reverse: @{text clean_prefix_of} @{text \<open>\<rightarrow>\<close>}
  @{text cdc_events_of} --- on the in-scope / at-or-before-frontier
  filter.

  WF2's order-preservation conjunct is the order-preserving sublist
  condition: there exists a strictly increasing index function
  @{text \<iota>} from indices of (the in-scope, at-or-before-frontier
  filter on @{text "cdc_events_of(R)"}) into indices of (the same
  filter on @{text "src_history_of(R)"}) with elements matching
  pairwise. This is equivalent to "@{text "cdc_events_of(R)"} is an
  order-preserving sublist of @{text "src_history_of(R)"} on that
  slice". A bare membership condition would permit the
  same-coordinate reversal
  @{text "H = [(c, Update k v1), (c, Update k v2)]"} versus
  @{text "cdc_events_of(R) = [(c, Update k v2), (c, Update k v1)]"},
  where set membership holds both ways but the source-position order
  is reversed, causing @{text "Apply (clean_prefix_of R) k"} to
  disagree with @{text "Src b0 H (frontier_of R) k"} on the in-scope
  key @{text k}. The membership condition is kept as a separate
  conjunct alongside the order-preserving one (it is logically
  subsumed, but stating it explicitly keeps the extraction proofs
  simple). The @{text covers_ordinary_cdc} forward direction is
  independent and still requires coverage in the post-chunk-read
  interval.
\<close>

definition wellformed_dblog_run
  :: "('k :: linorder \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) run \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "wellformed_dblog_run b0 R H \<longleftrightarrow>
     \<comment> \<open>WF0: source-history binding\<close>
     src_history_of R = H \<and> wellformed_src_history H
   \<and>
     \<comment> \<open>WF1 (a): @{text \<open>\<exists>!\<close>} responsible chunk per in-scope key.
         Derivable from WF1 (b) + (c) ---
         @{text wf1a_unique_owner_redundant} below.\<close>
     (\<forall> k \<in> scope_of R. \<exists>! ch. ch \<in> chunks R \<and> owns R ch k)
   \<and>
     \<comment> \<open>WF1 (b): chunk domains are pairwise disjoint\<close>
     (\<forall> ch1 \<in> chunks R. \<forall> ch2 \<in> chunks R.
        ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R ch1 \<inter> chunk_domain R ch2 = {})
   \<and>
     \<comment> \<open>WF1 (c): canonical chunk-ownership domain equals scope\<close>
     canonical_chunk_ownership_domain R = scope_of R
   \<and>
     \<comment> \<open>WF1 (d): @{text responsible_chunk} @{text \<open>\<longleftrightarrow>\<close>} ownership predicate (in scope)\<close>
     (\<forall> k \<in> scope_of R. \<forall> ch.
        responsible_chunk R k = Some ch
          \<longleftrightarrow> ch \<in> chunks R \<and> owns R ch k)
   \<and>
     \<comment> \<open>WF1 (e): out-of-scope keys have no responsible chunk\<close>
     (\<forall> k. k \<notin> scope_of R \<longrightarrow> responsible_chunk R k = None)
   \<and>
     \<comment> \<open>WF1 (f): scope and chunk domains are finite\<close>
     finite (scope_of R)
   \<and> (\<forall> ch \<in> chunks R. finite (chunk_domain R ch))
   \<and>
     \<comment> \<open>WF1 (g): every chunk has a non-empty domain --- no
         inert dead chunks. With WF1 (a)-(f) this makes the chunks
         of R a strict partition of @{text \<open>scope_of R\<close>} (a partition has
         non-empty parts). An empty-domain chunk would be inert ---
         it owns no key and emits no Refresh events --- so this
         clause is not needed for the headline theorems; it is
         included so the formal body matches the paper's
         strict-partition wording.\<close>
     (\<forall> ch \<in> chunks R. chunk_domain R ch \<noteq> {})
   \<and>
     \<comment> \<open>WF2 (coverage): observed CDC reaches every in-scope key
         through the frontier (paper @{text covers_ordinary_cdc})\<close>
     (\<forall> k \<in> scope_of R. covers_ordinary_cdc R k (frontier_of R))
   \<and>
     \<comment> \<open>WF2 (faithfulness): observed CDC events that fall in scope
         and at-or-before frontier are real source events
         (membership condition). Logically subsumed by the
         order-preservation clause below (strict-monotonic indexing
         implies pairwise membership), but kept explicit as a
         separate conjunct so that the extraction proofs need not
         derive it from the embedding.\<close>
     (\<forall> p \<in> set (cdc_events_of R).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R)
        \<longrightarrow> p \<in> set (src_history_of R))
   \<and>
     \<comment> \<open>WF2 (order-preserving sublist): on the in-scope /
         at-or-before-frontier slice, @{text \<open>cdc_events_of(R)\<close>} is an
         order-preserving sublist of @{text \<open>src_history_of(R)\<close>}. The
         strict-monotonic indexing embedding strengthens the
         membership-only WF2 faithfulness clause above with
         source-position-order preservation, ruling out the
         same-coordinate CDC-order reversal. Consumed by the
         Layer 2 slice-subsequence supporting lemma (in theory
         @{text DBLog_Run_Substrate_Layer2}), which extracts this
         strict-monotonic embedding to show the per-key /
         per-coordinate CDC slice is an order-preserving
         subsequence of the source-history slice, and through it
         by the slice-equality lemma there.\<close>
     (\<exists> \<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
        \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R
                                 \<and> src_le (hist_coord p) (frontier_of R));
               cdc_in_slice  = filter in_slice (cdc_events_of R);
               hist_in_slice = filter in_slice (src_history_of R)
           in \<forall> i. i < length cdc_in_slice \<longrightarrow>
                   \<iota> i < length hist_in_slice
                 \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i))
   \<and>
     \<comment> \<open>WF2 (post-read same-key/same-coordinate multiplicity):
         for an in-scope key k, any source coordinate c strictly
         after k's responsible chunk read and at-or-before the run
         frontier has the same multiset of matching source records
         in @{text \<open>cdc_events_of(R)\<close>} as in @{text \<open>src_history_of(R)\<close>}. Together with
         the order-preserving sublist clause, this closes the
         duplicate-record gap in the Cdc case of the per-key
         replay-equality lemma without requiring global
         source-history distinctness. Multiset equality rather than
         set membership is essential: an [A, B, A] source slice
         versus an [A, B] CDC slice is rejected by multiplicity,
         while a same-multiset permutation such as [A, B, A] versus
         [A, A, B] is excluded instead by the order-preserving
         sublist clause above.\<close>
     (\<forall> k \<in> scope_of R. \<forall> ch c.
        responsible_chunk R k = Some ch
        \<and> src_lt (chunk_read_coordinate R ch) c
        \<and> src_le c (frontier_of R)
        \<longrightarrow>
          mset (source_key_coord_slice k c (cdc_events_of R))
          = mset (source_key_coord_slice k c (src_history_of R)))
   \<and>
     \<comment> \<open>(no WF3 --- the numbering carries a deliberate gap
         recording a clause the model no longer uses)\<close>
     \<comment> \<open>WF4: chunk-read evidence (watermark bracketing +
         @{text chunk_read_result} totality on domain + Refresh-event
         agreement with @{text chunk_read_result} on domain). The
         watermark-bracketing conjunct is not needed for the
         headline theorems; it is included so the formal body
         matches the paper's WF4 clause. The result/Refresh
         agreement biconditional is derivable from WF1 (b) + (f)
         and the @{text clean_prefix_of} construction ---
         @{text wf4_refresh_agreement_redundant} below.\<close>
     (\<forall> ch \<in> chunks R.
        src_le (chunk_lower_watermark R ch) (chunk_read_coordinate R ch)
      \<and> src_le (chunk_read_coordinate R ch) (chunk_upper_watermark R ch)
      \<and> (\<forall> k \<in> chunk_domain R ch.
           \<exists> m. chunk_read_result R ch k = Some m)
      \<and> (\<forall> k \<in> chunk_domain R ch. \<forall> m.
           chunk_read_result R ch k = Some m
             \<longleftrightarrow> Refresh k m (chunk_read_coordinate R ch)
                  \<in> set (clean_prefix_of R)))
   \<and>
     \<comment> \<open>WF5: chunk-read coordinate at-or-before frontier\<close>
     (\<forall> ch \<in> chunks R.
        src_le (chunk_read_coordinate R ch) (frontier_of R))
   \<and>
     \<comment> \<open>WF6 (main): refresh correctness against
         @{text \<open>Src b0 H (chunk_read_coordinate R ch) k\<close>}.\<close>
     (\<forall> ch \<in> chunks R. \<forall> k \<in> chunk_domain R ch. \<forall> m.
        chunk_read_result R ch k = Some m
          \<longrightarrow> m = Src b0 H (chunk_read_coordinate R ch) k)
   \<and>
     \<comment> \<open>WF6 (row-absence meaningfulness): when
         @{text \<open>chunk_read_result R ch k = Some None\<close>} is observed for an
         in-domain key, @{text \<open>row_absence_meaningful b0 H R ch k\<close>} holds.
         Auto-satisfied under WF6 main alone ---
         @{text wf6_row_absence_redundant} below; carries the paper's
         WF6 row-absence content into the formal body.\<close>
     (\<forall> ch \<in> chunks R. \<forall> k \<in> chunk_domain R ch.
        chunk_read_result R ch k = Some None
          \<longrightarrow> row_absence_meaningful b0 H R ch k)
   \<and>
     \<comment> \<open>WF7 (clean-prefix CDC coherence): forward direction ---
         every observed CDC event whose key is in scope and whose
         coordinate is at-or-before frontier appears as a Cdc replay
         event in @{text \<open>clean_prefix_of(R)\<close>}.\<close>
     (\<forall> p \<in> set (cdc_events_of R).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R)
        \<longrightarrow> Cdc (hist_coord p) (hist_event p)
              \<in> set (clean_prefix_of R))
   \<and>
     \<comment> \<open>WF7 (clean-prefix CDC coherence): reverse direction ---
         every Cdc replay event in @{text \<open>clean_prefix_of(R)\<close>} whose key is
         in scope and whose coordinate is at-or-before frontier is
         justified by the corresponding pair in @{text \<open>cdc_events_of(R)\<close>}.\<close>
     (\<forall> e c. Cdc c e \<in> set (clean_prefix_of R)
                \<and> key_of e \<in> scope_of R
                \<and> src_le c (frontier_of R)
                \<longrightarrow> (c, e) \<in> set (cdc_events_of R))"

section \<open>WF7 clean-prefix CDC coherence holds for every run\<close>

text \<open>The WF7 clean-prefix CDC-coherence conjunct of @{const wellformed_dblog_run} is
  provably redundant --- @{text wf7_clean_prefix_cdc_coherence_redundant} establishes it for
  \<^emph>\<open>every\<close> run, wellformed or not, because the @{const canonical_clean_prefix} construction
  emits its @{text Cdc} events exactly from the in-scope / at-or-before-frontier filter of
  @{const cdc_events_of}. The conjunct is retained in the predicate body for
  documentation: the formal body matches the paper's wellformedness clause list. The
  run-parametric meta-theorems live here alongside @{const wellformed_dblog_run} /
  @{const clean_prefix_of}.\<close>

lemma in_set_cdc_event_replaysI:
  fixes es :: "(src_coord \<times> ('k, 'v) source_event) list"
  assumes "(c, e) \<in> set es"
      and "key_of e \<in> scope"
      and "c \<le> frontier"
  shows "Cdc c e \<in> set (cdc_event_replays scope frontier es)"
  using assms(1)
proof (induction es)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "p = (c, e)")
    case True
    then show ?thesis
      using assms(2,3) by (simp add: cdc_event_replays_def)
  next
    case False
    with Cons.prems have "(c, e) \<in> set ps" by simp
    then have "Cdc c e \<in> set (cdc_event_replays scope frontier ps)"
      by (rule Cons.IH)
    then show ?thesis
      by (simp add: cdc_event_replays_def split: option.split)
  qed
qed

lemma wf7_forward_holds_for_all_runs:
  fixes R :: "('k :: linorder, 'v) run"
    and c :: src_coord
    and e :: "('k, 'v) source_event"
  assumes cdc_in:   "(c, e) \<in> set (cdc_events_of R)"
      and in_scope: "key_of e \<in> scope_of R"
      and le_front: "src_le c (frontier_of R)"
  shows "Cdc c e \<in> set (clean_prefix_of R)"
proof -
  have c_le: "c \<le> frontier_of R"
    using le_front by (simp add: less_eq_src_coord_def)
  have "Cdc c e \<in> set (cdc_event_replays (scope_of R) (frontier_of R)
                                          (cdc_events_of R))"
    using cdc_in in_scope c_le by (rule in_set_cdc_event_replaysI)
  thus ?thesis
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
qed

lemma wf7_reverse_holds_for_all_runs:
  fixes R :: "('k :: linorder, 'v) run"
    and c :: src_coord
    and e :: "('k, 'v) source_event"
  assumes e_in: "Cdc c e \<in> set (clean_prefix_of R)"
  shows "(c, e) \<in> set (cdc_events_of R)
       \<and> key_of e \<in> scope_of R
       \<and> src_le c (frontier_of R)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  \<comment> \<open>Cdc events cannot come from the @{text chunk_read_refreshes} branch,
      which emits only Refresh events.\<close>
  have not_refresh_branch:
    "\<forall> ch. Cdc c e \<notin> set (chunk_read_refreshes (?mkRec ch))"
    unfolding chunk_read_refreshes_def List.map_filter_def
    by (auto split: option.splits)
  have split:
    "Cdc c e \<in> set (cdc_event_replays (scope_of R)
                                       (frontier_of R)
                                       (cdc_events_of R))
   \<or> (\<exists> ch \<in> set (chunks_list R).
        Cdc c e \<in> set (chunk_read_refreshes (?mkRec ch)))"
    using e_in
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
  from split not_refresh_branch have in_cdc_replays:
    "Cdc c e \<in> set (cdc_event_replays (scope_of R)
                                       (frontier_of R)
                                       (cdc_events_of R))"
    by blast
  from in_cdc_replays show ?thesis
    unfolding cdc_event_replays_def List.map_filter_def
    by (auto split: if_splits simp: less_eq_src_coord_def)
qed

theorem wf7_clean_prefix_cdc_coherence_redundant:
  fixes R :: "('k :: linorder, 'v) run"
  shows "(\<forall> p \<in> set (cdc_events_of R).
            key_of (hist_event p) \<in> scope_of R
            \<and> src_le (hist_coord p) (frontier_of R)
            \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                  \<in> set (clean_prefix_of R))
       \<and> (\<forall> e c. Cdc c e \<in> set (clean_prefix_of R)
            \<and> key_of e \<in> scope_of R
            \<and> src_le c (frontier_of R)
            \<longrightarrow> (c, e) \<in> set (cdc_events_of R))"
proof
  show "\<forall> p \<in> set (cdc_events_of R).
          key_of (hist_event p) \<in> scope_of R
          \<and> src_le (hist_coord p) (frontier_of R)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (clean_prefix_of R)"
  proof (intro ballI impI)
    fix p
    assume p_in: "p \<in> set (cdc_events_of R)"
       and hyp: "key_of (hist_event p) \<in> scope_of R
                  \<and> src_le (hist_coord p) (frontier_of R)"
    have "(fst p, snd p) \<in> set (cdc_events_of R)" using p_in by simp
    moreover have "key_of (snd p) \<in> scope_of R" using hyp by simp
    moreover have "src_le (fst p) (frontier_of R)" using hyp by simp
    ultimately have "Cdc (fst p) (snd p) \<in> set (clean_prefix_of R)"
      by (rule wf7_forward_holds_for_all_runs)
    thus "Cdc (hist_coord p) (hist_event p) \<in> set (clean_prefix_of R)"
      by simp
  qed
next
  show "\<forall> e c. Cdc c e \<in> set (clean_prefix_of R)
                 \<and> key_of e \<in> scope_of R
                 \<and> src_le c (frontier_of R)
                 \<longrightarrow> (c, e) \<in> set (cdc_events_of R)"
  proof (intro allI impI)
    fix e c
    assume "Cdc c e \<in> set (clean_prefix_of R)
             \<and> key_of e \<in> scope_of R
             \<and> src_le c (frontier_of R)"
    from wf7_reverse_holds_for_all_runs[OF conjunct1[OF this]]
    show "(c, e) \<in> set (cdc_events_of R)" by simp
  qed
qed

section \<open>Further redundant conjuncts of the wellformed-run body\<close>

text \<open>Three further conjuncts of @{const wellformed_dblog_run} are provably
  redundant, completing the redundancy documentation that
  @{text wf7_clean_prefix_cdc_coherence_redundant} begins. Each is retained in
  the predicate body so the formal clause list matches the paper's; the lemmas
  here replace comment-level derivability claims with machine-checked facts.
  @{text wf1a_unique_owner_redundant}: the WF1 (a) unique-responsible-chunk
  clause follows from WF1 (b) disjointness and WF1 (c) ownership-domain
  coverage. @{text wf4_refresh_agreement_redundant}: the WF4 result/Refresh
  agreement biconditional follows from WF1 (b) + WF1 (f) and the
  @{const clean_prefix_of} construction. @{text wf6_row_absence_redundant}:
  the WF6 row-absence conjunct follows from WF6 main alone. The
  @{text in_set_chunk_read_refreshes_iff} membership characterization is the
  Refresh-side sibling of @{text in_set_cdc_event_replaysI} above.\<close>

lemma in_set_chunk_read_refreshes_aux:
  fixes r :: "('k :: linorder, 'v) chunk_read_record"
  shows "Refresh k m c
           \<in> set (List.map_filter
                    (\<lambda>k'. case crr_observation r k' of
                            Some m' \<Rightarrow> Some (Refresh k' m' (crr_read_coord r))
                          | None    \<Rightarrow> None)
                    xs)
           \<longleftrightarrow> k \<in> set xs
             \<and> crr_observation r k = Some m
             \<and> c = crr_read_coord r"
  by (induction xs)
     (auto simp: List.map_filter_simps split: option.splits)

lemma in_set_chunk_read_refreshes_iff:
  fixes r :: "('k :: linorder, 'v) chunk_read_record"
  shows "Refresh k m c \<in> set (chunk_read_refreshes r)
           \<longleftrightarrow> k \<in> set (sorted_list_of_set (crr_domain r))
             \<and> crr_observation r k = Some m
             \<and> c = crr_read_coord r"
  unfolding chunk_read_refreshes_def
  by (rule in_set_chunk_read_refreshes_aux)

lemma wf1a_unique_owner_redundant:
  fixes R :: "('k :: linorder, 'v) run"
  assumes disj: "\<forall> ch1 \<in> chunks R. \<forall> ch2 \<in> chunks R.
                   ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R ch1 \<inter> chunk_domain R ch2 = {}"
      and cov: "canonical_chunk_ownership_domain R = scope_of R"
  shows "\<forall> k \<in> scope_of R. \<exists>! ch. ch \<in> chunks R \<and> owns R ch k"
proof
  fix k assume "k \<in> scope_of R"
  with cov have "k \<in> (\<Union>ch \<in> chunks R. chunk_domain R ch)"
    by (simp add: canonical_chunk_ownership_domain_def)
  then obtain ch where ch_in: "ch \<in> chunks R" and k_dom: "k \<in> chunk_domain R ch"
    by blast
  show "\<exists>! ch. ch \<in> chunks R \<and> owns R ch k"
  proof
    show "ch \<in> chunks R \<and> owns R ch k" using ch_in k_dom by simp
  next
    fix ch' assume "ch' \<in> chunks R \<and> owns R ch' k"
    then have ch'_in: "ch' \<in> chunks R" and k_dom': "k \<in> chunk_domain R ch'" by auto
    show "ch' = ch"
    proof (rule ccontr)
      assume "ch' \<noteq> ch"
      then have "chunk_domain R ch' \<inter> chunk_domain R ch = {}"
        using disj ch'_in ch_in by blast
      with k_dom k_dom' show False by blast
    qed
  qed
qed

lemma wf4_refresh_agreement_redundant:
  fixes R :: "('k :: linorder, 'v) run"
  assumes disj: "\<forall> ch1 \<in> chunks R. \<forall> ch2 \<in> chunks R.
                   ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R ch1 \<inter> chunk_domain R ch2 = {}"
      and fin: "\<forall> ch \<in> chunks R. finite (chunk_domain R ch)"
      and ch_in: "ch \<in> chunks R"
      and k_dom: "k \<in> chunk_domain R ch"
  shows "chunk_read_result R ch k = Some m
           \<longleftrightarrow> Refresh k m (chunk_read_coordinate R ch) \<in> set (clean_prefix_of R)"
proof
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  assume obs: "chunk_read_result R ch k = Some m"
  have k_enum: "k \<in> set (sorted_list_of_set (chunk_domain R ch))"
    using fin ch_in k_dom by simp
  have "Refresh k m (chunk_read_coordinate R ch)
          \<in> set (chunk_read_refreshes (?mkRec ch))"
    using k_enum obs by (simp add: in_set_chunk_read_refreshes_iff)
  moreover have "ch \<in> set (chunks_list R)"
    using ch_in by (simp add: chunks_list_set)
  ultimately show "Refresh k m (chunk_read_coordinate R ch)
                     \<in> set (clean_prefix_of R)"
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
next
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  assume mem: "Refresh k m (chunk_read_coordinate R ch) \<in> set (clean_prefix_of R)"
  have not_cdc_branch:
    "Refresh k m (chunk_read_coordinate R ch)
       \<notin> set (cdc_event_replays (scope_of R) (frontier_of R) (cdc_events_of R))"
    unfolding cdc_event_replays_def List.map_filter_def
    by (auto split: if_splits)
  from mem not_cdc_branch have
    "\<exists> ch' \<in> set (chunks_list R).
       Refresh k m (chunk_read_coordinate R ch)
         \<in> set (chunk_read_refreshes (?mkRec ch'))"
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
  then obtain ch' where ch'_l: "ch' \<in> set (chunks_list R)"
    and r_mem: "Refresh k m (chunk_read_coordinate R ch)
                  \<in> set (chunk_read_refreshes (?mkRec ch'))"
    by blast
  have ch'_in: "ch' \<in> chunks R"
    using ch'_l by (simp add: chunks_list_set)
  from r_mem have k_enum': "k \<in> set (sorted_list_of_set (chunk_domain R ch'))"
    and obs': "chunk_read_result R ch' k = Some m"
    by (auto simp: in_set_chunk_read_refreshes_iff)
  have k_dom': "k \<in> chunk_domain R ch'"
    using k_enum' fin ch'_in by simp
  have "ch' = ch"
  proof (rule ccontr)
    assume "ch' \<noteq> ch"
    then have "chunk_domain R ch' \<inter> chunk_domain R ch = {}"
      using disj ch'_in ch_in by blast
    with k_dom k_dom' show False by blast
  qed
  with obs' show "chunk_read_result R ch k = Some m" by simp
qed

lemma wf6_row_absence_redundant:
  fixes R :: "('k :: linorder, 'v) run"
    and b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
  assumes main: "\<forall> ch \<in> chunks R. \<forall> k \<in> chunk_domain R ch. \<forall> m.
                   chunk_read_result R ch k = Some m
                     \<longrightarrow> m = Src b0 H (chunk_read_coordinate R ch) k"
      and ch_in: "ch \<in> chunks R"
      and k_dom: "k \<in> chunk_domain R ch"
      and obs: "chunk_read_result R ch k = Some None"
  shows "row_absence_meaningful b0 H R ch k"
proof -
  have "None = Src b0 H (chunk_read_coordinate R ch) k"
    using main[THEN bspec, OF ch_in, THEN bspec, OF k_dom,
               THEN spec, of None] obs
    by simp
  then have "Src b0 H (chunk_read_coordinate R ch) k = None" by simp
  thus ?thesis by (simp add: row_absence_meaningful_def)
qed

end
