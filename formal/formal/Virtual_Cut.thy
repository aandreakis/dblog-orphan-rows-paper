(*  Title:   Virtual_Cut.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Virtual_Cut
  imports
    Dual_Write_Layer0.Source_History
    Dual_Write_Layer0.Replay
    Dual_Write_Layer0.Scope
    DBLog_Run_Substrate_Layer2
begin

section \<open>Virtual cuts, certificates, and the Layer 2/3 theorems\<close>

text \<open>
  Central formal object of the paper: the @{text virtual_cut}
  predicate over certificates.

  The virtual cut is a three-argument predicate
  @{text "virtual_cut b0 C H"}: under a deployment base state
  @{text b0}, certificate @{text C}, and source history @{text H},
  the replay of @{text "clean_prefix C"} on @{text "scope C"} equals
  the source state at @{text "frontier C"}. It is the
  certificate-accessor instance of the factored source-side core
  predicate @{text virtual_cut_state} (below), which both this
  cert-side definition and the Layer 2 run-side soundness theorem
  reduce to.

  The reader-facing paper notation suppresses the
  universally-quantified base state: the paper writes
  @{text "virtual_cut(C, H)"} where the formal predicate is
  @{text "virtual_cut b0 C H"}.

  This theory also assembles the Layer 3 checker substrate: the
  certificate carrier and accessors, the @{text verify_result}
  enumeration (@{text "Accept | Reject | Unsupported"}), the
  evidence and observation primitives, and the
  @{text materializes_run} relation (the graph of the
  evidence-determined run) support the
  @{text layer3_checker_substrate} locale, under whose
  primitive checker obligations the composed soundness theorem
  @{text accepted_virtual_cut_sound} is proved.

  Certificate accessors are bare-named (@{text "scope C"},
  @{text "frontier C"}, @{text "clean_prefix C"}); run accessors, in
  @{text DBLog_Run}, carry the @{text "_of"} suffix.
\<close>

subsection \<open>Certificate carrier and accessors\<close>

text \<open>
  Certificate accessors are bare-named --- @{text "scope C"},
  @{text "frontier C"}, @{text "clean_prefix C"} --- to mirror the
  paper's notation. Run accessors live in @{text DBLog_Run} with the
  @{text "_of"} suffix.
\<close>

text \<open>
  The certificate carrier is a
  concrete single-constructor @{command datatype} with named selectors under the
  public name @{text cert}; the bare-named accessors are its field projections.
  (A @{command datatype} rather than a @{command record}, so @{text cert} stays a
  clean two-parameter type constructor rather
  than an extensible-record synonym. The Layer 3/4 substrate development
  abstracts the certificate over a locale parameter in
  @{text DBLog_Cert_Substrate}; this public datatype is the concrete carrier
  over which the headline theorems below are stated.)
\<close>

datatype ('k, 'v) cert =
  Cert (c_scope: "'k set")
       (c_frontier: frontier)
       (c_clean_prefix: "('k, 'v) replay_event list")

definition scope :: "('k, 'v) cert \<Rightarrow> 'k set"
  where "scope C = c_scope C"

definition frontier :: "('k, 'v) cert \<Rightarrow> frontier"
  where "frontier C = c_frontier C"

definition clean_prefix :: "('k, 'v) cert \<Rightarrow> ('k, 'v) replay_event list"
  where "clean_prefix C = c_clean_prefix C"

subsection \<open>Virtual cut state (shared Layer-0 predicate)\<close>

text \<open>
  @{text virtual_cut_state} is the source-side extensional-equality
  core that both Layer 2 (over runs) and the Layer 3 cert-side
  @{text virtual_cut} reduce to:

  @{text "virtual_cut_state b0 \<sigma> K f H
            \<longleftrightarrow>
          restrict (Apply \<sigma>) K = restrict (Src b0 H f) K"}.

  The factoring abstracts over how @{text \<sigma>}, @{text K}, and
  @{text f} are obtained: certificate accessors
  @{text "(clean_prefix C, scope C, frontier C)"} on the cert side;
  run accessors @{text "(clean_prefix_of R, scope_of R,
  frontier_of R)"} on the run side. Both reduce to the same
  @{text virtual_cut_state} conclusion under their respective
  context --- cert: faithful evidence, verifier accept, and cert/run
  coherence; run: a wellformed DBLog run.

  The reader-facing paper notation suppresses the
  universally-quantified base state: the paper writes
  @{text "virtual_cut_state(\<sigma>, K, f, H)"} where the formal
  predicate is @{text "virtual_cut_state b0 \<sigma> K f H"} --- the
  same suppression convention that @{text virtual_cut} and
  @{text Src} use.
\<close>

text \<open>
  WS4a moves @{const virtual_cut_state} to the shared Layer-0 theory
  @{theory Dual_Write_Layer0.Virtual_Cut_State}. The compatibility lemma below
  is now definitional reflexivity; it keeps older proof references stable while
  both DBLog and Dual-Write use the same imported HOL constant.
\<close>

lemma virtual_cut_state_eq_shared:
  "virtual_cut_state b0 \<sigma> K f H = virtual_cut_state b0 \<sigma> K f H"
  by simp

subsection \<open>Virtual cut (cert-side instance of virtual cut state)\<close>

text \<open>
  On @{text "scope C"}, the replay of @{text "clean_prefix C"}
  equals the source state at @{text "frontier C"} under base state
  @{text b0}. @{text virtual_cut} is expressed as the
  certificate-accessor instance of @{text virtual_cut_state}; the
  expanded form
    @{text "Apply (clean_prefix C) \<restriction> scope C
            = Src b0 H (frontier C) \<restriction> scope C"}
  is recovered by unfolding @{text virtual_cut_def} and
  @{text virtual_cut_state_def}.
\<close>

definition virtual_cut
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) cert \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "virtual_cut b0 C H \<longleftrightarrow>
     virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"

subsection \<open>Layer 2 source-side soundness (over runs)\<close>

text \<open>
  Layer 2 ranges over runs, not certificates. Its conclusion is the
  run-side instance of @{text virtual_cut_state}; the cert-side
  @{text virtual_cut} predicate is reserved for Layer 3 composition
  via @{text cert_run_coherence}. @{text wellformed_dblog_run}, in
  @{text DBLog_Run}, is a real @{command definition} with a
  three-argument signature and a seven-clause body (WF0 / WF1 with
  subclauses (a)-(g) / WF2 with coverage, faithfulness, order-
  preserving sublist, and post-read multiplicity conjuncts / WF4 /
  WF5 / WF6 main + row-absence / WF7 forward + reverse). See
  @{text DBLog_Run} for the authoritative clause list.

  The paper's wellformed-run replay equality on scope (the bridge
  lemma of "Layer 0 and Layer 1 Lemmas", stated as the Layer 2
  source-side soundness theorem):

  \<^verbatim>\<open>
    For any base state b0, any wellformed source history H, and any
    run R such that wellformed-DBLog-run(b0, R, H):

      Apply(clean_prefix_of(R)) \<restriction> scope_of(R)
        = Src(b0, H, frontier_of(R)) \<restriction> scope_of(R)
  \<close>

  The theorem below states this conclusion as
  @{text "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
  (frontier_of R) H"}; the expanded replay-equality form is
  recovered by unfolding @{thm virtual_cut_state_def}. It is proved
  as a wrapper over the locale theorem
  @{thm [source] dblog_run_substrate.wellformed_run_implies_virtual_cut},
  specialized through the canonical interpretation
  (@{theory DBLog_Virtual_Cuts.DBLog_Run_Substrate}) and rephrased from its
  @{const virtual_cut_state} conclusion to the public
  @{const virtual_cut_state} via @{thm [source] virtual_cut_state_eq_shared}.

  The result is \<^emph>\<open>Conditional\<close> at the paper level, on
  @{text "wellformed_dblog_run b0 R H"}; the Isabelle theorem is
  proved under that premise.
\<close>

theorem wellformed_run_implies_virtual_cut:
  assumes "wellformed_dblog_run b0 R H"
  shows
    "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                       (frontier_of R) H"
proof -
  from assms have "canonical.wellformed_dblog_run b0 R H"
    by (simp add: canonical_wellformed_dblog_run_eq)
  from canonical.wellformed_run_implies_virtual_cut[OF this]
  have "virtual_cut_state b0 (canonical.clean_prefix_of R) (scope_of R)
                              (frontier_of R) H" .
  thus ?thesis
    by (simp add: canonical_clean_prefix_of_eq)
qed

subsection \<open>Layer 3 checker substrate: cert/evidence bridge and soundness\<close>

text \<open>
  @{text materializes_run} witnesses that an accepted certificate,
  paired with faithful evidence, can be associated with an abstract
  DBLog run. The interface is stated relationally; the public model
  below instantiates it with the evidence-determined run (the run
  value the evidence bundle carries), and verifier acceptance plus
  coherence --- not the bare relation alone --- prevents an accepted
  proof from choosing an arbitrary convenient run.

  @{text raw_observation} is the interface slot for external
  source-side observations; the public model leaves it unconstrained
  (a one-value carrier), and the observation content lives in the
  evidence run. The predicate
  @{text "faithful_source_observation E b0 H Raw"} ties the evidence
  @{text E} to a fixed deployment base state @{text b0} and source
  history @{text H}; the @{text Raw} parameter is unconstrained in
  the public model, retained for statement-shape stability with the
  abstract substrate (@{text dblog_cert_substrate}, a later theory,
  abstracts the observation carrier as a genuine type parameter).
  The predicate asserts
  exactly the observation-channel facts that no checker can compute
  from @{text E} alone (the recorded source history \<^emph>\<open>is\<close> the true
  history; the recorded chunk reads reflect the true source state at
  their read coordinates), and the assumption is discharged at
  deployment, not inside the model.

  @{text verify_result} is the verifier's result enumeration. The
  headline theorem reads @{text "verify C E = Accept"}; the result
  type reserves @{text Reject} / @{text Unsupported} for the
  rejection and parser branches that a concrete verifier
  distinguishes.

  The Layer 3 development introduces three theorems:
    \<^item> the intermediate
      @{text accepted_certificate_implies_wellformed_run}
      stated below (cert + evidence yields an existentially
      witnessed run @{text R} with @{text wellformed_dblog_run});
    \<^item> the cert / run coherence predicate and bridge lemma
      stated below; @{text cert_run_coherent} packages
      @{text materializes_run} with accessor agreement so the
      evidence parameter is load-bearing;
    \<^item> the composed @{text accepted_virtual_cut_sound} (the
      paper headline, also stated below), whose proof composes
      @{text accepted_certificate_implies_wellformed_run}
      (existentially witnessed @{text R}) with Layer 2's
      @{text wellformed_run_implies_virtual_cut} on @{text "(R, b0)"}
      and @{text cert_run_coherence} to substitute run accessors
      back to certificate accessors.

  The non-circular proof substrate is made explicit by the
  @{text layer3_checker_substrate} locale below. The locale does not
  assume the accepted-certificate theorem; instead it separates four
  primitive checker obligations:
    \<^item> accepted input is bound to the certificate and belongs to
      the source-side checker schema;
    \<^item> accepted input has at least one materialized run witness;
    \<^item> accepted materializations agree with the certificate
      semantic accessors; and
    \<^item> faithful accepted materializations are wellformed runs
      against the same @{text b0}, @{text H}, and @{text Raw}.
  The theorem is then proved inside the locale from those primitive
  obligations.
\<close>

text \<open>
  The evidence and raw-observation carriers are concrete
  @{command datatype}s under the public names @{text evidence} /
  @{text raw_observation}: an evidence bundle carries the full observed
  @{type run} value (chunk plan, watermarks, read coordinates, chunk-read
  results, the captured CDC/source-history log) --- exactly the
  source-side artifacts a deployment hands the checker. The checker
  primitives (@{text verify}, @{text faithful_source_observation},
  @{text materializes_run}, @{text evidence_bound_to_cert},
  @{text source_side_schema_supported}) are genuine definitions over this
  carrier, factored along the paper's trust boundary:

    \<^item> @{text checker_run_wellformed} is the \<^emph>\<open>mechanical\<close> half of
      @{const wellformed_dblog_run}: every clause that is a property of
      the evidence run alone (chunk-partition structure WF1,
      observed-CDC coverage / faithfulness-to-the-recorded-log /
      order-preservation / multiplicity WF2, chunk-read evidence WF4,
      read-coordinate bound WF5, clean-prefix CDC coherence WF7, and
      internal wellformedness of the \<^emph>\<open>recorded\<close> source history).
      The verifier establishes all of it from @{text "(C, E)"} alone;
      no @{text b0} or @{text H} occurs in it. The checker is
      specification-level: its clauses contain unbounded
      quantification, and no executable refinement is provided or
      claimed --- the machine-checked content is the type-level fact
      that @{text checker_run_wellformed} cannot consult @{text b0}
      or @{text H} at all.

    \<^item> @{text run_reflects_source} is the \<^emph>\<open>external\<close> half: the recorded
      source history is the true deployment history (WF0 (a)) and the
      recorded chunk reads reflect the true source state at their read
      coordinates (WF6 main + row-absence). This is the content of
      @{text faithful_source_observation}: an observation-channel
      assumption, discharged at deployment, never computed by
      @{text verify}.

  The decomposition lemma @{text wellformed_dblog_run_decompose} proves
  that wellformedness is exactly the conjunction of the two halves ---
  a \<^emph>\<open>proved factoring\<close>, not a definition of either side as the whole,
  so the headline implication ``acceptance + faithful observation
  entails a wellformed materialized run'' combines two independent,
  individually insufficient premises (the witness theory
  @{text Public_Checker_Witness} exhibits an accepted-but-unfaithful
  pair and a faithful-but-not-accepted pair). The headline theorems
  below are conditional implications, proved from
  the locale's primitive checker obligations; the obligations hold
  for the public checker \<^emph>\<open>globally\<close>
  (@{text layer3_checker_substrate_holds} at the end of this theory),
  and the accepting public witness over the running example lives in
  @{text Public_Checker_Witness}.
\<close>

datatype ('k, 'v) evidence = Evidence (evidence_run: "('k, 'v) run")
datatype raw_observation = RawObservation

datatype verify_result = Accept | Reject | Unsupported

subsection \<open>Mechanical / external factoring of run wellformedness\<close>

text \<open>
  @{text checker_run_wellformed}: the conjuncts of
  @{const wellformed_dblog_run} that mention only the run value ---
  verbatim copies of the WF1 / WF2 / WF4 / WF5 / WF7 clauses, plus
  internal wellformedness of the \<^emph>\<open>recorded\<close> source history
  @{term "src_history_of R"} (WF0 (b) transported through WF0 (a)).
\<close>

definition checker_run_wellformed
  :: "('k :: linorder, 'v) run \<Rightarrow> bool"
where
  "checker_run_wellformed R \<longleftrightarrow>
     \<comment> \<open>WF0 (b), over the recorded history\<close>
     wellformed_src_history (src_history_of R)
   \<and>
     \<comment> \<open>WF1 (a)-(g), verbatim\<close>
     (\<forall> k \<in> scope_of R. \<exists>! ch. ch \<in> chunks R \<and> owns R ch k)
   \<and> (\<forall> ch1 \<in> chunks R. \<forall> ch2 \<in> chunks R.
        ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R ch1 \<inter> chunk_domain R ch2 = {})
   \<and> canonical_chunk_ownership_domain R = scope_of R
   \<and> (\<forall> k \<in> scope_of R. \<forall> ch.
        responsible_chunk R k = Some ch
          \<longleftrightarrow> ch \<in> chunks R \<and> owns R ch k)
   \<and> (\<forall> k. k \<notin> scope_of R \<longrightarrow> responsible_chunk R k = None)
   \<and> finite (scope_of R)
   \<and> (\<forall> ch \<in> chunks R. finite (chunk_domain R ch))
   \<and> (\<forall> ch \<in> chunks R. chunk_domain R ch \<noteq> {})
   \<and>
     \<comment> \<open>WF2 (coverage / faithfulness / order-preservation /
         multiplicity), verbatim --- all against the recorded
         history @{text \<open>src_history_of R\<close>}\<close>
     (\<forall> k \<in> scope_of R. covers_ordinary_cdc R k (frontier_of R))
   \<and> (\<forall> p \<in> set (cdc_events_of R).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R)
        \<longrightarrow> p \<in> set (src_history_of R))
   \<and> (\<exists> \<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
        \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R
                                 \<and> src_le (hist_coord p) (frontier_of R));
               cdc_in_slice  = filter in_slice (cdc_events_of R);
               hist_in_slice = filter in_slice (src_history_of R)
           in \<forall> i. i < length cdc_in_slice \<longrightarrow>
                   \<iota> i < length hist_in_slice
                 \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i))
   \<and> (\<forall> k \<in> scope_of R. \<forall> ch c.
        responsible_chunk R k = Some ch
        \<and> src_lt (chunk_read_coordinate R ch) c
        \<and> src_le c (frontier_of R)
        \<longrightarrow>
          mset (source_key_coord_slice k c (cdc_events_of R))
          = mset (source_key_coord_slice k c (src_history_of R)))
   \<and>
     \<comment> \<open>WF4, verbatim\<close>
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
     \<comment> \<open>WF5, verbatim\<close>
     (\<forall> ch \<in> chunks R.
        src_le (chunk_read_coordinate R ch) (frontier_of R))
   \<and>
     \<comment> \<open>WF7 forward + reverse, verbatim\<close>
     (\<forall> p \<in> set (cdc_events_of R).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R)
        \<longrightarrow> Cdc (hist_coord p) (hist_event p)
              \<in> set (clean_prefix_of R))
   \<and> (\<forall> e c. Cdc c e \<in> set (clean_prefix_of R)
                \<and> key_of e \<in> scope_of R
                \<and> src_le c (frontier_of R)
                \<longrightarrow> (c, e) \<in> set (cdc_events_of R))"

text \<open>
  @{text run_reflects_source}: the observation-channel conjuncts of
  @{const wellformed_dblog_run} --- WF0 (a) and WF6 (main +
  row-absence), verbatim. These are the only clauses in which the
  deployment base state @{text b0} or the true source history
  @{text H} occurs.
\<close>

definition run_reflects_source
  :: "('k :: linorder \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) run \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "run_reflects_source b0 R H \<longleftrightarrow>
     \<comment> \<open>WF0 (a): the recorded history is the true history\<close>
     src_history_of R = H
   \<and>
     \<comment> \<open>WF6 (main): recorded reads reflect the true source state\<close>
     (\<forall> ch \<in> chunks R. \<forall> k \<in> chunk_domain R ch. \<forall> m.
        chunk_read_result R ch k = Some m
          \<longrightarrow> m = Src b0 H (chunk_read_coordinate R ch) k)
   \<and>
     \<comment> \<open>WF6 (row-absence meaningfulness)\<close>
     (\<forall> ch \<in> chunks R. \<forall> k \<in> chunk_domain R ch.
        chunk_read_result R ch k = Some None
          \<longrightarrow> row_absence_meaningful b0 H R ch k)"

text \<open>
  The factoring is exact: wellformedness is the conjunction of the
  mechanical and the external half. The only non-verbatim step is
  transporting @{term "wellformed_src_history H"} across
  @{term "src_history_of R = H"}.
\<close>

lemma wellformed_dblog_run_decompose:
  "wellformed_dblog_run b0 R H \<longleftrightarrow>
     checker_run_wellformed R \<and> run_reflects_source b0 R H"
  unfolding wellformed_dblog_run_def checker_run_wellformed_def
            run_reflects_source_def
  by (rule iffI; elim conjE; intro conjI; (assumption | simp))

subsection \<open>The public checker primitives\<close>

definition cert_accessors_agree
  :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) run \<Rightarrow> bool"
where
  "cert_accessors_agree C R \<longleftrightarrow>
     scope C = scope_of R
   \<and> frontier C = frontier_of R
   \<and> clean_prefix C = clean_prefix_of R"

text \<open>
  The five checker primitives. @{text evidence_bound_to_cert} binds the
  evidence to \<^emph>\<open>this\<close> certificate: the certificate's semantic accessors
  agree with the evidence run's. @{text source_side_schema_supported}
  validates that the evidence run value is mechanically wellformed
  (@{const checker_run_wellformed}) --- the source-side shape the
  checker supports. @{text verify} is the composed verdict; all three
  @{type verify_result} values are reachable (@{const Unsupported} for
  out-of-schema evidence, @{const Reject} for in-schema evidence not
  bound to the certificate, @{const Accept} exactly on
  @{text checker_input_ok} inputs). @{text faithful_source_observation}
  is the external half (@{const run_reflects_source}), and
  @{text materializes_run} relates the pair to the evidence-determined
  run.
\<close>

definition evidence_bound_to_cert
  :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> bool"
  where "evidence_bound_to_cert C E \<longleftrightarrow> cert_accessors_agree C (evidence_run E)"

definition source_side_schema_supported
  :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> bool"
  where "source_side_schema_supported C E \<longleftrightarrow> checker_run_wellformed (evidence_run E)"

definition checker_input_ok
  :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> bool"
where
  "checker_input_ok C E \<longleftrightarrow>
     evidence_bound_to_cert C E \<and> source_side_schema_supported C E"

definition verify :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> verify_result"
  where "verify C E =
           (if source_side_schema_supported C E
            then if evidence_bound_to_cert C E then Accept else Reject
            else Unsupported)"

lemma verify_eq_Accept_iff:
  "verify C E = Accept \<longleftrightarrow> checker_input_ok C E"
  by (simp add: verify_def checker_input_ok_def)

text \<open>
  The @{text Raw} argument below is a deliberate placeholder: the
  body does not constrain it, and the public @{type raw_observation}
  carrier is single-valued --- the observation content lives in the
  evidence run (see the Layer 3 interface note above).
\<close>

definition faithful_source_observation
  :: "('k::linorder, 'v) evidence \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> raw_observation \<Rightarrow> bool"
  where "faithful_source_observation E b0 H Raw =
           run_reflects_source b0 (evidence_run E) H"

definition materializes_run
  :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> ('k, 'v) run \<Rightarrow> bool"
  where "materializes_run C E R = (R = evidence_run E)"

definition cert_run_coherent
  :: "('k::linorder, 'v) cert \<Rightarrow> ('k, 'v) evidence \<Rightarrow> ('k, 'v) run \<Rightarrow> bool"
where
  "cert_run_coherent C E R \<longleftrightarrow>
     materializes_run C E R \<and> cert_accessors_agree C R"

lemma cert_run_coherence:
  assumes "cert_run_coherent C E R"
  shows   "scope C = scope_of R
         \<and> frontier C = frontier_of R
         \<and> clean_prefix C = clean_prefix_of R"
  using assms
  unfolding cert_run_coherent_def cert_accessors_agree_def
  by blast

lemma cert_run_coherent_virtual_cut_state_subst:
  assumes "cert_accessors_agree C R"
      and "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                             (frontier_of R) H"
  shows   "virtual_cut_state b0 (clean_prefix C) (scope C)
                             (frontier C) H"
  using assms
  unfolding cert_accessors_agree_def
  by simp

subsection \<open>The four checker obligations hold globally for the public checker\<close>

text \<open>
  Each primitive checker obligation of the
  @{text layer3_checker_substrate} locale below is a global theorem of
  the public checker --- proved from the definitions, for \<^emph>\<open>every\<close>
  certificate / evidence pair. The composed obligation
  (@{text faithful_materialization_wellformed_global}) is where the
  factoring earns its keep: the mechanical half comes from the
  verifier's acceptance, the external half from faithful observation,
  and @{thm [source] wellformed_dblog_run_decompose} reassembles
  full wellformedness.
\<close>

lemma accepted_input_ok_global:
  "verify C E = Accept \<Longrightarrow> checker_input_ok C E"
  by (simp add: verify_eq_Accept_iff)

lemma accepted_has_materialization_global:
  "\<lbrakk>verify C E = Accept; checker_input_ok C E\<rbrakk>
    \<Longrightarrow> \<exists>R. materializes_run C E R"
  by (auto simp: materializes_run_def)

lemma accepted_materialization_agrees_global:
  "\<lbrakk>verify C E = Accept; checker_input_ok C E; materializes_run C E R\<rbrakk>
    \<Longrightarrow> cert_accessors_agree C R"
  by (simp add: checker_input_ok_def evidence_bound_to_cert_def
                materializes_run_def)

lemma faithful_materialization_wellformed_global:
  "\<lbrakk>verify C E = Accept; checker_input_ok C E; materializes_run C E R;
    faithful_source_observation E b0 H Raw\<rbrakk>
    \<Longrightarrow> wellformed_dblog_run b0 R H"
  by (simp add: checker_input_ok_def source_side_schema_supported_def
                materializes_run_def faithful_source_observation_def
                wellformed_dblog_run_decompose)

locale layer3_checker_substrate =
  fixes C :: "('k::linorder, 'v) cert"
    and E :: "('k, 'v) evidence"
  assumes accepted_input_ok:
    "verify C E = Accept \<Longrightarrow> checker_input_ok C E"
  and accepted_has_materialization:
    "\<lbrakk>verify C E = Accept; checker_input_ok C E\<rbrakk>
      \<Longrightarrow> \<exists>R. materializes_run C E R"
  and accepted_materialization_agrees:
    "\<And>R. \<lbrakk>verify C E = Accept; checker_input_ok C E;
      materializes_run C E R\<rbrakk>
      \<Longrightarrow> cert_accessors_agree C R"
  and faithful_materialization_wellformed:
    "\<And>R b0 H Raw. \<lbrakk>verify C E = Accept; checker_input_ok C E;
      materializes_run C E R; faithful_source_observation E b0 H Raw\<rbrakk>
      \<Longrightarrow> wellformed_dblog_run b0 R H"
begin

theorem accepted_certificate_implies_wellformed_run:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
  assumes accept: "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
  shows   "\<exists>R. wellformed_dblog_run b0 R H \<and> cert_run_coherent C E R"
proof -
  have input_ok: "checker_input_ok C E"
    by (rule accepted_input_ok[OF accept])
  then obtain R where mat: "materializes_run C E R"
    using accepted_has_materialization[OF accept input_ok] by blast
  have wf: "wellformed_dblog_run b0 R H"
    by (rule faithful_materialization_wellformed[OF accept input_ok mat faithful])
  have agree: "cert_accessors_agree C R"
    by (rule accepted_materialization_agrees[OF accept input_ok mat])
  have coherent: "cert_run_coherent C E R"
    using mat agree
    unfolding cert_run_coherent_def
    by blast
  show ?thesis
    using wf coherent by blast
qed

theorem accepted_virtual_cut_sound:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
  assumes accept: "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
  shows   "virtual_cut b0 C H"
proof -
  obtain R where wf: "wellformed_dblog_run b0 R H"
      and coherent: "cert_run_coherent C E R"
    using accepted_certificate_implies_wellformed_run[OF accept faithful]
    by blast
  have agree: "cert_accessors_agree C R"
    using coherent unfolding cert_run_coherent_def by blast
  have run_vcs:
    "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                       (frontier_of R) H"
    using wellformed_run_implies_virtual_cut[OF wf] .
  have cert_vcs:
    "virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"
    using cert_run_coherent_virtual_cut_state_subst[OF agree run_vcs] .
  show ?thesis
    unfolding virtual_cut_def
    using cert_vcs .
qed

end

subsection \<open>The locale holds for every public certificate / evidence pair\<close>

text \<open>
  Since the four primitive checker obligations are global theorems of
  the public checker, the @{locale layer3_checker_substrate} predicate
  holds for \<^emph>\<open>every\<close> @{text "(C, E)"} pair: the locale premise of the
  headline theorems stated inside the locale (e.g.
  @{text accepted_virtual_cut_sound}) discharges unconditionally, leaving
  @{text "verify C E = Accept"} and
  @{text "faithful_source_observation E b0 H Raw"} as the genuine
  premises. The witness theory @{text Public_Checker_Witness} exhibits
  a concrete pair satisfying both (theorem
  @{text public_checker_nonvacuous}), so the Layer 3 / Layer 4 /
  continuation headline implications are non-vacuous over the public
  surface.
\<close>

theorem layer3_checker_substrate_holds:
  "layer3_checker_substrate C E"
proof (unfold_locales, goal_cases)
  case 1
  then show ?case by (rule accepted_input_ok_global)
next
  case 2
  then show ?case by (rule accepted_has_materialization_global)
next
  case (3 R)
  then show ?case by (rule accepted_materialization_agrees_global)
next
  case (4 R b0 H Raw)
  then show ?case by (rule faithful_materialization_wellformed_global)
qed

end
