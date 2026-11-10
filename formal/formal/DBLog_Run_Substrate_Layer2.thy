(*  Title:   DBLog_Run_Substrate_Layer2.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory DBLog_Run_Substrate_Layer2
  imports DBLog_Run_Substrate Virtual_Cut_Core
begin

section \<open>Layer 2 source-side soundness in the run substrate locale\<close>

text \<open>
  The carrier-dependent Layer 2 supporting
  clean-prefix lemmas, the per-key replay-equality lemma, and the run-side
  soundness theorem @{text wellformed_run_implies_virtual_cut} are proved
  inside the @{locale dblog_run_substrate} locale, over the locale's
  fixed run/chunk accessors and its two @{text chunks_list}
  assumptions.

  Every proof step refers to the
  locale definitions (@{text clean_prefix_of}, @{text covers_ordinary_cdc},
  @{text wellformed_dblog_run}, ...) and the locale assumptions, or to the
  carrier-independent ``pure'' helpers (the @{text filter_take_nth} /
  @{text "subseq_*"} / @{text "last_filter_*"} list lemmas, @{text apply_at_latest_k_event},
  @{text src_eq_when_no_later_src_event_for_k},
  @{text src_frontier_eq_effect_of_last_key_coord_slice},
  @{text wellformed_src_history_coord_mono}) that live in
  @{text DBLog_Run_Core} and are reused directly via
  this theory's import. The @{text Virtual_Cut_Core} import supplies the
  carrier-independent state predicate @{const virtual_cut_state} for the
  concluding theorem.

  Under the canonical
  @{command global_interpretation} @{text canonical} (in
  @{text DBLog_Run_Substrate}) the locale results
  specialize to the concrete @{typ "('k, 'v) run"} carrier; the public
  headline theorem @{text "Virtual_Cut.wellformed_run_implies_virtual_cut"}
  is the canonical specialization of the locale theorem at the end of this
  theory, rephrased through the public state predicate.
\<close>

context dblog_run_substrate
begin

subsection \<open>Refresh-coordinate match and clean-prefix coordinate facts\<close>

theorem refresh_coordinate_match:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v" and R :: "'run"
    and H :: "('k, 'v) src_history" and ch :: "'chunk"
    and k :: 'k and m :: "'v option"
  assumes wf:  "wellformed_dblog_run b0 R H"
  assumes ch_in: "ch \<in> chunks R"
  assumes k_in:  "k \<in> chunk_domain R ch"
  assumes obs:   "chunk_read_result R ch k = Some m"
  shows "m = Src b0 H (chunk_read_coordinate R ch) k"
  using assms unfolding wellformed_dblog_run_def by blast


lemma clean_prefix_of_order_respects_coordinate:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "'run"
    and i j :: nat
  assumes "wellformed_dblog_run b0 R H"
      and "i < j"
      and "j < length (clean_prefix_of R)"
  shows "src_le (cdc_coord (clean_prefix_of R ! i))
                (cdc_coord (clean_prefix_of R ! j))"
proof -
  have sorted_cp: "sorted (map cdc_coord (clean_prefix_of R))"
    unfolding clean_prefix_of_def canonical_clean_prefix_def
    by (rule sorted_sort_key)
  from assms(2) have le_ij: "i \<le> j" by simp
  from assms(3) have j_bound:
    "j < length (map cdc_coord (clean_prefix_of R))" by simp
  from sorted_nth_mono[OF sorted_cp le_ij j_bound]
  have "map cdc_coord (clean_prefix_of R) ! i
          \<le> map cdc_coord (clean_prefix_of R) ! j" .
  hence "cdc_coord (clean_prefix_of R ! i)
           \<le> cdc_coord (clean_prefix_of R ! j)"
    using assms(2,3) by (simp add: nth_map)
  thus ?thesis by (simp add: less_eq_src_coord_def)
qed


lemma clean_prefix_of_no_future_in_scope_events:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "'run"
    and e :: "('k, 'v) replay_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and e_in: "e \<in> set (clean_prefix_of R)"
  shows "src_le (cdc_coord e) (frontier_of R)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  have split: "e \<in> set (cdc_event_replays (scope_of R) (frontier_of R)
                                          (cdc_events_of R))
             \<or> (\<exists> ch \<in> set (chunks_list R).
                  e \<in> set (chunk_read_refreshes (?mkRec ch)))"
    using e_in
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
  from split show ?thesis
  proof
    assume "e \<in> set (cdc_event_replays (scope_of R) (frontier_of R)
                                       (cdc_events_of R))"
    \<comment> \<open>Case A: e is a Cdc replay event whose coordinate is
        @{text \<open>\<le>\<close>} frontier by the @{text cdc_event_replays} filter. The
        @{text less_eq_src_coord_def} unfolding bridges
        @{text \<open>\<le>\<close>} on @{text src_coord} to @{text src_le}.\<close>
    then show ?thesis
      unfolding cdc_event_replays_def List.map_filter_def
      by (auto split: if_splits simp: less_eq_src_coord_def)
  next
    assume "\<exists> ch \<in> set (chunks_list R).
              e \<in> set (chunk_read_refreshes (?mkRec ch))"
    then obtain ch where
      ch_in: "ch \<in> set (chunks_list R)"
      and e_in_refs: "e \<in> set (chunk_read_refreshes (?mkRec ch))"
      by blast
    \<comment> \<open>Case B: e is a Refresh event whose coordinate equals
        @{text \<open>chunk_read_coordinate R ch\<close>} (by the @{text chunk_read_refreshes}
        construction), which is @{text \<open>\<le>\<close>} frontier by WF5.\<close>
    from ch_in have ch_in_chunks: "ch \<in> chunks R"
      using chunks_list_set by blast
    from e_in_refs have e_coord:
      "cdc_coord e = chunk_read_coordinate R ch"
      unfolding chunk_read_refreshes_def List.map_filter_def
      by (auto split: option.splits)
    from wf have wf5:
      "\<forall> ch \<in> chunks R.
          src_le (chunk_read_coordinate R ch) (frontier_of R)"
      unfolding wellformed_dblog_run_def by blast
    from wf5 ch_in_chunks
    have "src_le (chunk_read_coordinate R ch) (frontier_of R)" by blast
    with e_coord show ?thesis by simp
  qed
qed


subsection \<open>Provenance of clean-prefix events: responsible-chunk refreshes and observed CDC\<close>

lemma clean_prefix_of_refresh_generated_by_responsible_chunk:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "'run"
    and k :: 'k
    and m :: "'v option"
    and c :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and e_in: "Refresh k m c \<in> set (clean_prefix_of R)"
  shows "k \<in> scope_of R
       \<and> (\<exists> ch. responsible_chunk R k = Some ch
              \<and> chunk_read_coordinate R ch = c
              \<and> chunk_read_result R ch k = Some m)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  \<comment> \<open>Refresh events cannot come from the @{text cdc_event_replays}
      branch (which produces only Cdc events).\<close>
  have not_cdc:
    "Refresh k m c \<notin> set (cdc_event_replays (scope_of R)
                                            (frontier_of R)
                                            (cdc_events_of R))"
    unfolding cdc_event_replays_def List.map_filter_def
    by auto
  have split:
    "Refresh k m c \<in> set (cdc_event_replays (scope_of R)
                                            (frontier_of R)
                                            (cdc_events_of R))
   \<or> (\<exists> ch \<in> set (chunks_list R).
        Refresh k m c \<in> set (chunk_read_refreshes (?mkRec ch)))"
    using e_in
    by (auto simp: clean_prefix_of_def canonical_clean_prefix_def)
  from split not_cdc obtain ch where
    ch_in: "ch \<in> set (chunks_list R)" and
    refresh_in: "Refresh k m c \<in> set (chunk_read_refreshes (?mkRec ch))"
    by blast
  from ch_in have ch_in_chunks: "ch \<in> chunks R"
    using chunks_list_set by blast
  \<comment> \<open>Extract the conjuncts the downstream steps need: WF1
      (c), WF1 (d), and WF1 (f)'s chunk-domain finiteness.
      @{text blast} on the individual conjuncts can time out
      because of the WF2 @{text strict_mono} existential conjunct's
      complexity in the unfolded body; a single simp-based
      unfolding + elimination is faster.\<close>
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have wf1c: "canonical_chunk_ownership_domain R = scope_of R"
    by (elim conjE)
  from wf_body have wf1d:
    "\<forall> k \<in> scope_of R. \<forall> ch.
        responsible_chunk R k = Some ch
          \<longleftrightarrow> ch \<in> chunks R \<and> owns R ch k"
    by (elim conjE)
  from wf_body have wf1f_chunks:
    "\<forall> ch \<in> chunks R. finite (chunk_domain R ch)"
    by (elim conjE)
  from wf1f_chunks ch_in_chunks have fin_dom: "finite (chunk_domain R ch)"
    by blast
  \<comment> \<open>Pattern-match the Refresh against the @{text chunk_read_refreshes}
      emission to extract @{text \<open>k \<in> chunk_domain R ch\<close>},
      @{text \<open>chunk_read_result R ch k = Some m\<close>}, and
      @{text \<open>c = chunk_read_coordinate R ch\<close>}.\<close>
  from refresh_in fin_dom
  have k_props:
    "k \<in> chunk_domain R ch
   \<and> chunk_read_result R ch k = Some m
   \<and> c = chunk_read_coordinate R ch"
    unfolding chunk_read_refreshes_def List.map_filter_def
    by (auto split: option.splits)
  hence k_in_dom: "k \<in> chunk_domain R ch"
    and crr_res: "chunk_read_result R ch k = Some m"
    and c_eq: "c = chunk_read_coordinate R ch"
    by auto
  \<comment> \<open>Establish @{text \<open>k \<in> scope_of R\<close>} via WF1 (c) +
      @{text \<open>chunk_domain \<subseteq> canonical_chunk_ownership_domain\<close>}.\<close>
  from ch_in_chunks k_in_dom
  have "k \<in> canonical_chunk_ownership_domain R"
    unfolding canonical_chunk_ownership_domain_def by blast
  with wf1c have k_in_scope: "k \<in> scope_of R" by blast
  \<comment> \<open>Establish @{text \<open>responsible_chunk R k = Some ch\<close>} via WF1 (d).\<close>
  from wf1d k_in_scope ch_in_chunks k_in_dom
  have rc: "responsible_chunk R k = Some ch" by blast
  from k_in_scope rc c_eq crr_res show ?thesis by blast
qed


lemma clean_prefix_of_in_scope_responsible_chunk_refresh_exists:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "'run"
    and k :: 'k
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_in_scope: "k \<in> scope_of R"
  shows "\<exists> m c. Refresh k m c \<in> set (clean_prefix_of R)"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have wf1a:
    "\<forall> k \<in> scope_of R. \<exists>! ch. ch \<in> chunks R \<and> owns R ch k"
    by (elim conjE)
  from wf_body have wf4:
    "\<forall> ch \<in> chunks R.
       src_le (chunk_lower_watermark R ch) (chunk_read_coordinate R ch)
     \<and> src_le (chunk_read_coordinate R ch) (chunk_upper_watermark R ch)
     \<and> (\<forall> k \<in> chunk_domain R ch.
          \<exists> m. chunk_read_result R ch k = Some m)
     \<and> (\<forall> k \<in> chunk_domain R ch. \<forall> m.
          chunk_read_result R ch k = Some m
            \<longleftrightarrow> Refresh k m (chunk_read_coordinate R ch)
                 \<in> set (clean_prefix_of R))"
    by (elim conjE)
  \<comment> \<open>WF1 (a) extracts the responsible chunk.\<close>
  from wf1a k_in_scope obtain ch where
    ch_in_chunks: "ch \<in> chunks R" and
    k_in_dom: "k \<in> chunk_domain R ch"
    by blast
  \<comment> \<open>WF4 totality on @{text chunk_domain} produces the observation.\<close>
  from wf4 ch_in_chunks k_in_dom obtain m where
    crr_res: "chunk_read_result R ch k = Some m"
    by blast
  \<comment> \<open>WF4 iff (forward) lifts the observation into @{text clean_prefix_of}.\<close>
  from wf4 ch_in_chunks k_in_dom crr_res
  have "Refresh k m (chunk_read_coordinate R ch)
          \<in> set (clean_prefix_of R)"
    by blast
  thus ?thesis by blast
qed


lemma clean_prefix_of_cdc_generated_from_observed_cdc:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and R :: "'run"
    and c :: src_coord
    and e :: "('k, 'v) source_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and e_in: "Cdc c e \<in> set (clean_prefix_of R)"
  shows "(c, e) \<in> set (cdc_events_of R)
       \<and> key_of e \<in> scope_of R
       \<and> src_le c (frontier_of R)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  \<comment> \<open>Cdc events cannot come from the @{text chunk_read_refreshes}
      branch (which produces only Refresh events).\<close>
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
  \<comment> \<open>The @{text cdc_event_replays} filter directly yields the three
      conjuncts: @{text \<open>(c, e) \<in> cdc_events_of R\<close>} + @{text \<open>key_of e \<in> scope_of R\<close>}
      + @{text \<open>c \<le> frontier_of R\<close>} (bridged to @{text src_le} via
      @{text less_eq_src_coord_def}).\<close>
  from in_cdc_replays show ?thesis
    unfolding cdc_event_replays_def List.map_filter_def
    by (auto split: if_splits simp: less_eq_src_coord_def)
qed


subsection \<open>Clean-prefix CDC order respects source position\<close>

lemma clean_prefix_of_cdc_order_respects_source_position:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and c  :: src_coord
    and e1 e2 :: "('k, 'v) source_event"
    and i j :: nat
  assumes wf:       "wellformed_dblog_run b0 R H"
      and ij:       "i < j"
      and j_bound:  "j < length (clean_prefix_of R)"
      and at_i:     "clean_prefix_of R ! i = Cdc c e1"
      and at_j:     "clean_prefix_of R ! j = Cdc c e2"
  shows "\<exists> p q. p < q
              \<and> q < length (cdc_events_of R)
              \<and> cdc_events_of R ! p = (c, e1)
              \<and> cdc_events_of R ! q = (c, e2)"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  let ?cdc_part     = "cdc_event_replays (scope_of R) (frontier_of R) (cdc_events_of R)"
  let ?refresh_part = "concat (map chunk_read_refreshes (map ?mkRec (chunks_list R)))"
  let ?inp          = "?cdc_part @ ?refresh_part"
  let ?Pc = "\<lambda>x::('k, 'v) replay_event. \<exists> e. x = Cdc c e"
  let ?Qc = "\<lambda>x::('k, 'v) replay_event. cdc_coord x = c"
  let ?Qpair = "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
                  fst p = c
                  \<and> key_of (snd p) \<in> scope_of R
                  \<and> fst p \<le> frontier_of R"
  let ?in_filter = "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
                      key_of (snd p) \<in> scope_of R
                      \<and> fst p \<le> frontier_of R"
  define S where "S = filter ?Qpair (cdc_events_of R)"

  have i_lt_cp: "i < length (clean_prefix_of R)" using ij j_bound by simp
  have Pi: "?Pc (clean_prefix_of R ! i)" using at_i by auto
  have Pj: "?Pc (clean_prefix_of R ! j)" using at_j by auto

  \<comment> \<open>Step (a): @{const clean_prefix_of} as the @{text sort_key} over
      @{text \<open>cdc_part @ refresh_part\<close>}.\<close>
  have cp_eq: "clean_prefix_of R = sort_key cdc_coord ?inp"
    unfolding clean_prefix_of_def canonical_clean_prefix_def by simp

  \<comment> \<open>Step (b): @{text cdc_part} as map over a filter of
      @{text \<open>cdc_events_of R\<close>}.\<close>
  have cdc_part_eq:
    "?cdc_part = map (\<lambda>p. Cdc (fst p) (snd p)) (filter ?in_filter (cdc_events_of R))"
    unfolding cdc_event_replays_def
    by (simp add: map_filter_map_filter[symmetric])

  \<comment> \<open>Step (c): @{text refresh_part} contributes no Cdc events.\<close>
  have refresh_no_Cdc:
    "\<And> ch x. x \<in> set (chunk_read_refreshes (?mkRec ch)) \<Longrightarrow> \<not> ?Pc x"
    by (auto simp: chunk_read_refreshes_def List.map_filter_def split: option.splits)
  have refresh_filter_empty: "filter ?Pc ?refresh_part = []"
  proof -
    have "\<forall> x \<in> set ?refresh_part. \<not> ?Pc x"
      using refresh_no_Cdc by auto
    thus ?thesis by (simp add: filter_empty_conv)
  qed

  \<comment> \<open>Step (d): @{thm sort_key_stable} at coordinate c.\<close>
  have stab_Qc:
    "filter ?Qc (clean_prefix_of R) = filter ?Qc ?inp"
    using cp_eq sort_key_stable[of cdc_coord c ?inp] by simp

  \<comment> \<open>Chained filtering: ?Pc x implies ?Qc x, so filtering by ?Pc
      commutes with first filtering by ?Qc.\<close>
  have Pc_chain:
    "filter ?Pc xs = filter ?Pc (filter ?Qc xs)"
    for xs :: "('k, 'v) replay_event list"
    by (induction xs) auto

  \<comment> \<open>Composition: filter ?Pc collapses to the @{text cdc_part}
      contribution.\<close>
  have filter_Pc_cp:
    "filter ?Pc (clean_prefix_of R) = filter ?Pc ?cdc_part"
  proof -
    have "filter ?Pc (clean_prefix_of R) = filter ?Pc (filter ?Qc (clean_prefix_of R))"
      using Pc_chain by simp
    also have "\<dots> = filter ?Pc (filter ?Qc ?inp)"
      using stab_Qc by simp
    also have "\<dots> = filter ?Pc ?inp"
      using Pc_chain by simp
    also have "filter ?Pc ?inp
             = filter ?Pc ?cdc_part @ filter ?Pc ?refresh_part"
      by simp
    also have "\<dots> = filter ?Pc ?cdc_part"
      using refresh_filter_empty by simp
    finally show ?thesis .
  qed

  \<comment> \<open>@{text \<open>filter ?Pc cdc_part\<close>} as a map over S.\<close>
  have filter_Pc_cdc_part:
    "filter ?Pc ?cdc_part = map (\<lambda>p. Cdc c (snd p)) S"
  proof -
    have "filter ?Pc ?cdc_part
        = filter ?Pc (map (\<lambda>p. Cdc (fst p) (snd p))
                          (filter ?in_filter (cdc_events_of R)))"
      using cdc_part_eq by simp
    also have "\<dots> = map (\<lambda>p. Cdc (fst p) (snd p))
                         (filter (\<lambda>p. ?Pc (Cdc (fst p) (snd p)))
                                 (filter ?in_filter (cdc_events_of R)))"
      by (simp add: filter_map o_def)
    also have pred_simp:
      "(\<lambda>p::(src_coord \<times> ('k, 'v) source_event). ?Pc (Cdc (fst p) (snd p)))
         = (\<lambda>p. fst p = c)"
      by (auto intro: ext)
    also have "filter (\<lambda>p::(src_coord \<times> ('k, 'v) source_event). fst p = c)
                       (filter ?in_filter (cdc_events_of R))
             = filter ?Qpair (cdc_events_of R)"
      by (simp add: filter_filter conj_commute)
    also have "filter ?Qpair (cdc_events_of R) = S"
      unfolding S_def by simp
    finally have step:
      "filter ?Pc ?cdc_part = map (\<lambda>p. Cdc (fst p) (snd p)) S" by simp
    have rewrite_map:
      "map (\<lambda>p. Cdc (fst p) (snd p)) S = map (\<lambda>p. Cdc c (snd p)) S"
      by (rule map_cong[OF refl]) (auto simp: S_def)
    show ?thesis using step rewrite_map by simp
  qed

  have filter_Pc_eq_map:
    "filter ?Pc (clean_prefix_of R) = map (\<lambda>p. Cdc c (snd p)) S"
    using filter_Pc_cp filter_Pc_cdc_part by simp

  \<comment> \<open>Forward step: positions i, j in @{text \<open>clean_prefix_of R\<close>} lift to positions
      @{text \<open>n_i < n_j\<close>} in @{text \<open>filter ?Pc (clean_prefix_of R)\<close>} via
      @{text filter_take_nth} + @{text length_filter_take_strict_mono}.\<close>
  define n_i where "n_i = length (filter ?Pc (take i (clean_prefix_of R)))"
  define n_j where "n_j = length (filter ?Pc (take j (clean_prefix_of R)))"

  have nth_i_val_lt:
    "filter ?Pc (clean_prefix_of R) ! n_i = clean_prefix_of R ! i
   \<and> n_i < length (filter ?Pc (clean_prefix_of R))"
    using filter_take_nth[where xs = "clean_prefix_of R"
                            and P = "\<lambda>x::('k,'v) replay_event. \<exists>e. x = Cdc c e"
                            and i = i, OF i_lt_cp Pi]
    unfolding n_i_def by simp
  have nth_j_val_lt:
    "filter ?Pc (clean_prefix_of R) ! n_j = clean_prefix_of R ! j
   \<and> n_j < length (filter ?Pc (clean_prefix_of R))"
    using filter_take_nth[where xs = "clean_prefix_of R"
                            and P = "\<lambda>x::('k,'v) replay_event. \<exists>e. x = Cdc c e"
                            and i = j, OF j_bound Pj]
    unfolding n_j_def by simp
  have ni_lt_nj: "n_i < n_j"
    using length_filter_take_strict_mono[where xs = "clean_prefix_of R"
                                           and P = "\<lambda>x::('k,'v) replay_event. \<exists>e. x = Cdc c e"
                                           and i = i and j = j,
                                         OF ij _ Pi] j_bound
    unfolding n_i_def n_j_def by simp

  \<comment> \<open>S-positions at @{text n_i}, @{text n_j} carry (c, e1), (c, e2).\<close>
  have len_eq: "length (filter ?Pc (clean_prefix_of R)) = length S"
    using filter_Pc_eq_map by (simp add: length_map)
  have ni_lt_S: "n_i < length S" using nth_i_val_lt len_eq by simp
  have nj_lt_S: "n_j < length S" using nth_j_val_lt len_eq by simp
  have S_at_ni: "S ! n_i = (c, e1)"
  proof -
    have "(map (\<lambda>p. Cdc c (snd p)) S) ! n_i = Cdc c (snd (S ! n_i))"
      using ni_lt_S by simp
    moreover have "(map (\<lambda>p. Cdc c (snd p)) S) ! n_i = Cdc c e1"
      using filter_Pc_eq_map nth_i_val_lt at_i by simp
    ultimately have "Cdc c (snd (S ! n_i)) = Cdc c e1" by simp
    hence snd_eq: "snd (S ! n_i) = e1" by simp
    have "S ! n_i \<in> set S" using ni_lt_S nth_mem by blast
    hence fst_eq: "fst (S ! n_i) = c"
      using S_def by auto
    show "S ! n_i = (c, e1)" using snd_eq fst_eq by (cases "S ! n_i") simp
  qed
  have S_at_nj: "S ! n_j = (c, e2)"
  proof -
    have "(map (\<lambda>p. Cdc c (snd p)) S) ! n_j = Cdc c (snd (S ! n_j))"
      using nj_lt_S by simp
    moreover have "(map (\<lambda>p. Cdc c (snd p)) S) ! n_j = Cdc c e2"
      using filter_Pc_eq_map nth_j_val_lt at_j by simp
    ultimately have "Cdc c (snd (S ! n_j)) = Cdc c e2" by simp
    hence snd_eq: "snd (S ! n_j) = e2" by simp
    have "S ! n_j \<in> set S" using nj_lt_S nth_mem by blast
    hence fst_eq: "fst (S ! n_j) = c"
      using S_def by auto
    show "S ! n_j = (c, e2)" using snd_eq fst_eq by (cases "S ! n_j") simp
  qed

  \<comment> \<open>Backward step: positions @{text n_i}, @{text n_j} in S lift to positions
      p, q in @{text \<open>cdc_events_of R\<close>} via @{text filter_index_strict_mono} +
      @{text length_filter_take_mono} contrapositive.\<close>
  have ni_lt_S_filter: "n_i < length (filter ?Qpair (cdc_events_of R))"
    using ni_lt_S S_def by simp
  have nj_lt_S_filter: "n_j < length (filter ?Qpair (cdc_events_of R))"
    using nj_lt_S S_def by simp
  obtain p where p_props:
      "p < length (cdc_events_of R)"
      "?Qpair (cdc_events_of R ! p)"
      "cdc_events_of R ! p = filter ?Qpair (cdc_events_of R) ! n_i"
      "length (filter ?Qpair (take p (cdc_events_of R))) = n_i"
    using filter_index_strict_mono[OF ni_lt_S_filter] by blast
  obtain q where q_props:
      "q < length (cdc_events_of R)"
      "?Qpair (cdc_events_of R ! q)"
      "cdc_events_of R ! q = filter ?Qpair (cdc_events_of R) ! n_j"
      "length (filter ?Qpair (take q (cdc_events_of R))) = n_j"
    using filter_index_strict_mono[OF nj_lt_S_filter] by blast

  have p_val: "cdc_events_of R ! p = (c, e1)"
    using p_props S_at_ni S_def by simp
  have q_val: "cdc_events_of R ! q = (c, e2)"
    using q_props S_at_nj S_def by simp

  \<comment> \<open>p < q follows from monotonicity of @{text \<open>length \<circ> filter ?Qpair \<circ> take \<cdot>\<close>}
      composed with the contrapositive of @{text \<open>n_i < n_j\<close>}.\<close>
  have p_lt_q: "p < q"
  proof (rule ccontr)
    assume "\<not> p < q"
    hence q_le_p: "q \<le> p" by simp
    have "length (filter ?Qpair (take q (cdc_events_of R)))
        \<le> length (filter ?Qpair (take p (cdc_events_of R)))"
      using length_filter_take_mono[where xs = "cdc_events_of R"
                                      and P = ?Qpair
                                      and i = q and j = p,
                                    OF q_le_p]
      by simp
    hence "n_j \<le> n_i" using p_props q_props by simp
    thus False using ni_lt_nj by simp
  qed

  show ?thesis
  proof (intro exI conjI)
    show "p < q" by (rule p_lt_q)
    show "q < length (cdc_events_of R)" using q_props by simp
    show "cdc_events_of R ! p = (c, e1)" by (rule p_val)
    show "cdc_events_of R ! q = (c, e2)" by (rule q_val)
  qed
qed


subsection \<open>Latest per-key replay-event correspondence\<close>

lemma clean_prefix_of_latest_replay_correspondence:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and k  :: 'k
  assumes wf:          "wellformed_dblog_run b0 R H"
      and k_in_scope:  "k \<in> scope_of R"
  shows
    "(\<exists> i c e.
        i < length (clean_prefix_of R)
        \<and> clean_prefix_of R ! i = Cdc c e
        \<and> key_of e = k
        \<and> (\<forall> j. i < j \<and> j < length (clean_prefix_of R)
                  \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k)
        \<and> (c, e) \<in> set (cdc_events_of R)
        \<and> src_le c (frontier_of R))
   \<or>
    (\<exists> i ch m c_read.
        i < length (clean_prefix_of R)
        \<and> clean_prefix_of R ! i = Refresh k m c_read
        \<and> (\<forall> j. i < j \<and> j < length (clean_prefix_of R)
                  \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k)
        \<and> responsible_chunk R k = Some ch
        \<and> chunk_read_result R ch k = Some m
        \<and> chunk_read_coordinate R ch = c_read)"
proof -
  \<comment> \<open>Step 1: @{text clean_prefix_of_in_scope_responsible_chunk_refresh_exists}
      gives a Refresh event for k, yielding existence of an index.\<close>
  obtain m0 c0_read where refresh_exists:
    "Refresh k m0 c0_read \<in> set (clean_prefix_of R)"
    using clean_prefix_of_in_scope_responsible_chunk_refresh_exists[OF wf k_in_scope]
    by blast

  define event_indices where
    "event_indices =
       {i. i < length (clean_prefix_of R)
         \<and> event_key (clean_prefix_of R ! i) = k}"
  have event_indices_finite: "finite event_indices"
    unfolding event_indices_def by auto
  have event_indices_nonempty: "event_indices \<noteq> {}"
  proof -
    from refresh_exists obtain i where
      i_lt: "i < length (clean_prefix_of R)"
      and at_i: "clean_prefix_of R ! i = Refresh k m0 c0_read"
      by (auto simp: in_set_conv_nth)
    have "event_key (clean_prefix_of R ! i) = k"
      using at_i by simp
    hence "i \<in> event_indices"
      using i_lt unfolding event_indices_def by auto
    thus ?thesis by blast
  qed

  \<comment> \<open>Step 2: @{text \<open>i_max = Max event_indices\<close>} is the latest k-event
      position.\<close>
  define i_max where "i_max = Max event_indices"
  have i_max_in: "i_max \<in> event_indices"
    using event_indices_finite event_indices_nonempty
    unfolding i_max_def by (rule Max_in)
  have i_max_lt: "i_max < length (clean_prefix_of R)"
    using i_max_in unfolding event_indices_def by simp
  have i_max_event_key: "event_key (clean_prefix_of R ! i_max) = k"
    using i_max_in unfolding event_indices_def by simp
  have i_max_latest:
    "\<forall> j. i_max < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
  proof (intro allI impI)
    fix j
    assume j_assm: "i_max < j \<and> j < length (clean_prefix_of R)"
    hence j_props: "i_max < j" "j < length (clean_prefix_of R)" by auto
    show "event_key (clean_prefix_of R ! j) \<noteq> k"
    proof (rule ccontr)
      assume "\<not> event_key (clean_prefix_of R ! j) \<noteq> k"
      hence j_event_key: "event_key (clean_prefix_of R ! j) = k" by simp
      hence j_in: "j \<in> event_indices"
        unfolding event_indices_def using j_props by auto
      have "j \<le> i_max"
        unfolding i_max_def
        by (rule Max_ge[OF event_indices_finite j_in])
      with j_props show False by simp
    qed
  qed

  \<comment> \<open>Step 3: case-split on the shape of
      @{text \<open>clean_prefix_of R ! i_max\<close>}.\<close>
  show ?thesis
  proof (cases "clean_prefix_of R ! i_max")
    case (Cdc c e)
    \<comment> \<open>Cdc case: apply @{text clean_prefix_of_cdc_generated_from_observed_cdc}
        to extract the three correspondence conjuncts.\<close>
    have e_in_cp: "Cdc c e \<in> set (clean_prefix_of R)"
      using i_max_lt Cdc nth_mem by force
    have cdc_correspondence:
      "(c, e) \<in> set (cdc_events_of R)
       \<and> key_of e \<in> scope_of R
       \<and> src_le c (frontier_of R)"
      using clean_prefix_of_cdc_generated_from_observed_cdc[OF wf e_in_cp]
      by blast
    have key_eq: "key_of e = k"
      using i_max_event_key Cdc by simp
    show ?thesis
    proof (intro disjI1 exI[where x = i_max] exI[where x = c] exI[where x = e] conjI)
      show "i_max < length (clean_prefix_of R)" by (rule i_max_lt)
      show "clean_prefix_of R ! i_max = Cdc c e" by (rule Cdc)
      show "key_of e = k" by (rule key_eq)
      show "\<forall>j. i_max < j \<and> j < length (clean_prefix_of R)
                \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
        by (rule i_max_latest)
      show "(c, e) \<in> set (cdc_events_of R)" using cdc_correspondence by simp
      show "src_le c (frontier_of R)" using cdc_correspondence by simp
    qed
  next
    case (Refresh k' m' c_read)
    \<comment> \<open>Refresh case: @{text i_max_event_key} forces k' = k, then the
        responsible-chunk refresh-provenance lemma above applies (named in
        the @{text using} step just below).\<close>
    have k'_eq_k: "k' = k"
      using i_max_event_key Refresh by simp
    have refresh_in_cp: "Refresh k m' c_read \<in> set (clean_prefix_of R)"
      using i_max_lt Refresh k'_eq_k nth_mem by force
    obtain ch where ch_props:
      "responsible_chunk R k = Some ch"
      "chunk_read_coordinate R ch = c_read"
      "chunk_read_result R ch k = Some m'"
      using clean_prefix_of_refresh_generated_by_responsible_chunk[OF wf refresh_in_cp]
      by blast
    show ?thesis
    proof (intro disjI2 exI[where x = i_max] exI[where x = ch]
                       exI[where x = m'] exI[where x = c_read] conjI)
      show "i_max < length (clean_prefix_of R)" by (rule i_max_lt)
      show "clean_prefix_of R ! i_max = Refresh k m' c_read"
        using Refresh k'_eq_k by simp
      show "\<forall>j. i_max < j \<and> j < length (clean_prefix_of R)
                \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
        by (rule i_max_latest)
      show "responsible_chunk R k = Some ch" using ch_props by simp
      show "chunk_read_result R ch k = Some m'" using ch_props by simp
      show "chunk_read_coordinate R ch = c_read" using ch_props by simp
    qed
  qed
qed


subsection \<open>Per-key source/CDC coordinate-slice equalities\<close>

lemma cdc_events_key_coord_slice_mset_eq_source_history_slice:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and k  :: 'k
    and ch :: "'chunk"
    and c  :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and rc: "responsible_chunk R k = Some ch"
      and read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
      and c_le_f: "src_le c (frontier_of R)"
  shows "mset (source_key_coord_slice k c (cdc_events_of R))
       = mset (source_key_coord_slice k c (src_history_of R))"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have wf2_mset:
    "\<forall> k \<in> scope_of R. \<forall> ch c.
       responsible_chunk R k = Some ch
       \<and> src_lt (chunk_read_coordinate R ch) c
       \<and> src_le c (frontier_of R)
       \<longrightarrow>
         mset (source_key_coord_slice k c (cdc_events_of R))
         = mset (source_key_coord_slice k c (src_history_of R))"
    by (elim conjE)
  from wf2_mset k_scope rc read_lt_c c_le_f show ?thesis by blast
qed


lemma cdc_events_key_coord_slice_eq_source_history_slice:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and k  :: 'k
    and ch :: "'chunk"
    and c  :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and rc: "responsible_chunk R k = Some ch"
      and read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
      and c_le_f: "src_le c (frontier_of R)"
      and sub:
        "subseq (source_key_coord_slice k c (cdc_events_of R))
                (source_key_coord_slice k c (src_history_of R))"
  shows "source_key_coord_slice k c (cdc_events_of R)
       = source_key_coord_slice k c (src_history_of R)"
proof -
  have ms:
    "mset (source_key_coord_slice k c (cdc_events_of R))
     = mset (source_key_coord_slice k c (src_history_of R))"
    by (rule cdc_events_key_coord_slice_mset_eq_source_history_slice
          [OF wf k_scope rc read_lt_c c_le_f])
  show ?thesis by (rule subseq_mset_eq_imp_eq[OF sub ms])
qed


lemma cdc_events_key_coord_slice_subseq_source_history_slice:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and k  :: 'k
    and c  :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and c_le_f: "src_le c (frontier_of R)"
  shows "subseq (source_key_coord_slice k c (cdc_events_of R))
                (source_key_coord_slice k c (src_history_of R))"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  define in_slice
    where "in_slice =
      (\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R))"
  let ?Q =
    "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
       hist_coord p = c \<and> key_of (hist_event p) = k"

  from wf_body obtain \<iota> :: "nat \<Rightarrow> nat" where
    iota_mono: "strict_mono \<iota>" and
    iota_body:
      "(let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R
                              \<and> src_le (hist_coord p) (frontier_of R));
            cdc_in_slice = filter in_slice (cdc_events_of R);
            hist_in_slice = filter in_slice (src_history_of R)
        in \<forall>i. i < length cdc_in_slice
              \<longrightarrow> \<iota> i < length hist_in_slice
                    \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
    by (elim conjE exE)
  have iota_all:
    "\<forall>i. i < length (filter in_slice (cdc_events_of R))
      \<longrightarrow> \<iota> i < length (filter in_slice (src_history_of R))
            \<and> filter in_slice (cdc_events_of R) ! i
               = filter in_slice (src_history_of R) ! \<iota> i"
    using iota_body unfolding in_slice_def by (simp add: Let_def)

  have sub_in:
    "subseq (filter in_slice (cdc_events_of R))
            (filter in_slice (src_history_of R))"
  proof (rule subseq_from_strict_mono_nth[OF iota_mono])
    fix i
    assume i_lt: "i < length (filter in_slice (cdc_events_of R))"
    from iota_all i_lt
    show "\<iota> i < length (filter in_slice (src_history_of R))
          \<and> filter in_slice (cdc_events_of R) ! i
             = filter in_slice (src_history_of R) ! \<iota> i"
      by blast
  qed

  have sub_filtered:
    "subseq (filter ?Q (filter in_slice (cdc_events_of R)))
            (filter ?Q (filter in_slice (src_history_of R)))"
    by (rule subseq_filter[OF sub_in])

  have cdc_rewrite:
    "filter ?Q (filter in_slice (cdc_events_of R))
     = source_key_coord_slice k c (cdc_events_of R)"
    unfolding source_key_coord_slice_def in_slice_def
    by (simp add: filter_filter,
        rule filter_cong[OF refl],
        use k_scope c_le_f in auto)
  have hist_rewrite:
    "filter ?Q (filter in_slice (src_history_of R))
     = source_key_coord_slice k c (src_history_of R)"
    unfolding source_key_coord_slice_def in_slice_def
    by (simp add: filter_filter,
        rule filter_cong[OF refl],
        use k_scope c_le_f in auto)

  show ?thesis
    using sub_filtered by (simp only: cdc_rewrite hist_rewrite)
qed


lemma cdc_events_key_coord_slice_eq_source_history_slice_from_wf:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and k  :: 'k
    and ch :: "'chunk"
    and c  :: src_coord
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and rc: "responsible_chunk R k = Some ch"
      and read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
      and c_le_f: "src_le c (frontier_of R)"
  shows "source_key_coord_slice k c (cdc_events_of R)
       = source_key_coord_slice k c (src_history_of R)"
proof -
  have sub:
    "subseq (source_key_coord_slice k c (cdc_events_of R))
            (source_key_coord_slice k c (src_history_of R))"
    by (rule cdc_events_key_coord_slice_subseq_source_history_slice
          [OF wf k_scope c_le_f])
  show ?thesis
    by (rule cdc_events_key_coord_slice_eq_source_history_slice
          [OF wf k_scope rc read_lt_c c_le_f sub])
qed


subsection \<open>Clean-prefix structure at a fixed coordinate\<close>

lemma clean_prefix_cdc_key_coord_slice:
  fixes R :: "'run"
    and k :: 'k
    and c :: src_coord
  assumes k_scope: "k \<in> scope_of R"
      and c_le_f: "src_le c (frontier_of R)"
  shows "filter
          (\<lambda>x. case x of
                 Cdc c' e \<Rightarrow> c' = c \<and> key_of e = k
               | Refresh _ _ _ \<Rightarrow> False)
          (clean_prefix_of R)
       = map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
           (source_key_coord_slice k c (cdc_events_of R))"
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  let ?cdc_part = "cdc_event_replays (scope_of R) (frontier_of R) (cdc_events_of R)"
  let ?refresh_part = "concat (map chunk_read_refreshes (map ?mkRec (chunks_list R)))"
  let ?inp = "?cdc_part @ ?refresh_part"
  let ?P = "\<lambda>x::('k, 'v) replay_event.
              case x of Cdc c' e \<Rightarrow> c' = c \<and> key_of e = k
                      | Refresh _ _ _ \<Rightarrow> False"
  let ?Qc = "\<lambda>x::('k, 'v) replay_event. cdc_coord x = c"

  have cp_eq: "clean_prefix_of R = sort_key cdc_coord ?inp"
    unfolding clean_prefix_of_def canonical_clean_prefix_def by simp
  have refresh_no_cdc_slice:
    "\<And> ch x. x \<in> set (chunk_read_refreshes (?mkRec ch)) \<Longrightarrow> \<not> ?P x"
    by (auto simp: chunk_read_refreshes_def List.map_filter_def split: option.splits)
  have refresh_filter_empty: "filter ?P ?refresh_part = []"
  proof -
    have "\<forall> x \<in> set ?refresh_part. \<not> ?P x"
      using refresh_no_cdc_slice by auto
    thus ?thesis by (simp add: filter_empty_conv)
  qed
  have stab_Qc: "filter ?Qc (clean_prefix_of R) = filter ?Qc ?inp"
    using cp_eq sort_key_stable[of cdc_coord c ?inp] by simp
  have P_chain:
    "filter ?P xs = filter ?P (filter ?Qc xs)"
    for xs :: "('k, 'v) replay_event list"
    by (induction xs) (auto split: replay_event.splits)
  have filter_P_cp: "filter ?P (clean_prefix_of R) = filter ?P ?cdc_part"
  proof -
    have "filter ?P (clean_prefix_of R) = filter ?P (filter ?Qc (clean_prefix_of R))"
      using P_chain by simp
    also have "\<dots> = filter ?P (filter ?Qc ?inp)"
      using stab_Qc by simp
    also have "\<dots> = filter ?P ?inp"
      using P_chain by simp
    also have "\<dots> = filter ?P ?cdc_part @ filter ?P ?refresh_part"
      by simp
    also have "\<dots> = filter ?P ?cdc_part"
      using refresh_filter_empty by simp
    finally show ?thesis .
  qed
  have cdc_part_slice:
    "filter ?P ?cdc_part
       = map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
           (source_key_coord_slice k c (cdc_events_of R))"
  proof -
    let ?in_filter =
      "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
          key_of (snd p) \<in> scope_of R \<and> fst p \<le> frontier_of R"
    have cdc_part_eq:
      "?cdc_part =
         map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
           (filter ?in_filter (cdc_events_of R))"
      unfolding cdc_event_replays_def
      by (simp add: map_filter_map_filter[symmetric])
    have filter_collapse:
      "filter (\<lambda>p. hist_coord p = c \<and> key_of (hist_event p) = k)
              (filter ?in_filter (cdc_events_of R))
       = source_key_coord_slice k c (cdc_events_of R)"
      unfolding source_key_coord_slice_def
      by (simp add: filter_filter,
          rule filter_cong[OF refl],
          use k_scope c_le_f in \<open>auto simp: less_eq_src_coord_def\<close>)
    have "filter ?P ?cdc_part
        = filter ?P
            (map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
              (filter ?in_filter (cdc_events_of R)))"
      using cdc_part_eq by simp
    also have "\<dots>
        = map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
            (filter (\<lambda>p. hist_coord p = c \<and> key_of (hist_event p) = k)
              (filter ?in_filter (cdc_events_of R)))"
      by (simp add: filter_map o_def)
    also have "\<dots>
        = map (\<lambda>p. Cdc (hist_coord p) (hist_event p))
            (source_key_coord_slice k c (cdc_events_of R))"
      using filter_collapse by simp
    finally show ?thesis .
  qed
  show ?thesis using filter_P_cp cdc_part_slice by simp
qed


lemma clean_prefix_same_coord_refresh_before_cdc_false:
  fixes R :: "'run"
    and k :: 'k
    and m :: "'v option"
    and c :: src_coord
    and e :: "('k, 'v) source_event"
    and i j :: nat
  assumes ij: "i < j"
      and j_lt: "j < length (clean_prefix_of R)"
      and at_i: "clean_prefix_of R ! i = Refresh k m c"
      and at_j: "clean_prefix_of R ! j = Cdc c e"
  shows False
proof -
  let ?mkRec = "\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                       crr_read_coord  = chunk_read_coordinate R ch,
                       crr_observation = chunk_read_result R ch \<rparr>"
  let ?cdc_part = "cdc_event_replays (scope_of R) (frontier_of R) (cdc_events_of R)"
  let ?refresh_part = "concat (map chunk_read_refreshes (map ?mkRec (chunks_list R)))"
  let ?inp = "?cdc_part @ ?refresh_part"
  let ?Qc = "\<lambda>x::('k, 'v) replay_event. cdc_coord x = c"
  let ?A = "\<lambda>x::('k, 'v) replay_event. case x of Cdc _ _ \<Rightarrow> True | Refresh _ _ _ \<Rightarrow> False"
  let ?B = "\<lambda>x::('k, 'v) replay_event. case x of Refresh _ _ _ \<Rightarrow> True | Cdc _ _ \<Rightarrow> False"

  have i_lt: "i < length (clean_prefix_of R)" using ij j_lt by simp
  have Q_i: "?Qc (clean_prefix_of R ! i)" using at_i by simp
  have Q_j: "?Qc (clean_prefix_of R ! j)" using at_j by simp
  have cp_eq: "clean_prefix_of R = sort_key cdc_coord ?inp"
    unfolding clean_prefix_of_def canonical_clean_prefix_def by simp
  have stab_Qc: "filter ?Qc (clean_prefix_of R) = filter ?Qc ?inp"
    using cp_eq sort_key_stable[of cdc_coord c ?inp] by simp

  define n_i where "n_i = length (filter ?Qc (take i (clean_prefix_of R)))"
  define n_j where "n_j = length (filter ?Qc (take j (clean_prefix_of R)))"

  have nth_i:
    "filter ?Qc (clean_prefix_of R) ! n_i = clean_prefix_of R ! i
   \<and> n_i < length (filter ?Qc (clean_prefix_of R))"
    using filter_take_nth[where xs = "clean_prefix_of R" and P = ?Qc and i = i,
                          OF i_lt Q_i]
    unfolding n_i_def by simp
  have nth_j:
    "filter ?Qc (clean_prefix_of R) ! n_j = clean_prefix_of R ! j
   \<and> n_j < length (filter ?Qc (clean_prefix_of R))"
    using filter_take_nth[where xs = "clean_prefix_of R" and P = ?Qc and i = j,
                          OF j_lt Q_j]
    unfolding n_j_def by simp
  have ni_lt_nj: "n_i < n_j"
    using length_filter_take_strict_mono[where xs = "clean_prefix_of R"
                                           and P = ?Qc
                                           and i = i and j = j,
                                         OF ij _ Q_i] j_lt
    unfolding n_i_def n_j_def by simp
  have nj_lt_inp: "n_j < length (filter ?Qc ?inp)"
    using nth_j stab_Qc by simp
  have ni_B: "?B (filter ?Qc ?inp ! n_i)"
    using nth_i at_i stab_Qc by simp
  have nj_A: "?A (filter ?Qc ?inp ! n_j)"
    using nth_j at_j stab_Qc by simp

  have cdc_all_A: "\<forall>x \<in> set (filter ?Qc ?cdc_part). ?A x"
    unfolding cdc_event_replays_def List.map_filter_def
    by (auto split: if_splits)
  have refresh_all_B: "\<forall>y \<in> set (filter ?Qc ?refresh_part). ?B y"
    unfolding chunk_read_refreshes_def List.map_filter_def
    by (auto split: option.splits)
  have disj: "?A z \<Longrightarrow> ?B z \<Longrightarrow> False" for z
    by (cases z) auto

  show False
    by (rule append_no_B_before_A
          [where xs = "filter ?Qc ?cdc_part"
             and ys = "filter ?Qc ?refresh_part"
             and zs = "filter ?Qc ?inp"
             and A = ?A and B = ?B
             and i = n_i and j = n_j])
       (use cdc_all_A refresh_all_B disj ni_lt_nj nj_lt_inp ni_B nj_A in auto)
qed


subsection \<open>Consequences of a latest Cdc event for a key\<close>

lemma latest_cdc_for_key_implies_chunk_read_strictly_before:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and k  :: 'k
    and i  :: nat
    and c  :: src_coord
    and e  :: "('k, 'v) source_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and i_lt: "i < length (clean_prefix_of R)"
      and cp_i: "clean_prefix_of R ! i = Cdc c e"
      and key_e: "key_of e = k"
      and i_latest:
        "\<forall> j. i < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
  shows "\<exists>ch. responsible_chunk R k = Some ch
            \<and> src_lt (chunk_read_coordinate R ch) c"
proof -
  obtain m c_read where refresh_in:
    "Refresh k m c_read \<in> set (clean_prefix_of R)"
    using clean_prefix_of_in_scope_responsible_chunk_refresh_exists[OF wf k_scope]
    by blast
  then obtain i_r where
    i_r_lt: "i_r < length (clean_prefix_of R)" and
    i_r_at: "clean_prefix_of R ! i_r = Refresh k m c_read"
    by (auto simp: in_set_conv_nth)
  obtain ch where
    rc: "responsible_chunk R k = Some ch" and
    read_eq: "chunk_read_coordinate R ch = c_read"
    using clean_prefix_of_refresh_generated_by_responsible_chunk[OF wf refresh_in]
    by blast

  have i_r_key: "event_key (clean_prefix_of R ! i_r) = k"
    using i_r_at by simp
  have i_r_le_i: "i_r \<le> i"
  proof (rule ccontr)
    assume "\<not> i_r \<le> i"
    hence i_lt_ir: "i < i_r" by simp
    from i_latest i_lt_ir i_r_lt
    have "event_key (clean_prefix_of R ! i_r) \<noteq> k" by blast
    with i_r_key show False by simp
  qed
  have i_r_ne_i: "i_r \<noteq> i"
  proof
    assume "i_r = i"
    with i_r_at cp_i show False by simp
  qed
  have i_r_lt_i: "i_r < i"
    using i_r_le_i i_r_ne_i by linarith
  have coord_le: "src_le c_read c"
    using clean_prefix_of_order_respects_coordinate[OF wf i_r_lt_i i_lt]
          i_r_at cp_i
    by simp
  have c_read_ne_c: "c_read \<noteq> c"
  proof
    assume c_eq: "c_read = c"
    have "clean_prefix_of R ! i_r = Refresh k m c"
      using i_r_at c_eq by simp
    from clean_prefix_same_coord_refresh_before_cdc_false[OF i_r_lt_i i_lt this cp_i]
    show False .
  qed
  have read_lt: "src_lt (chunk_read_coordinate R ch) c"
    using coord_le c_read_ne_c read_eq
    unfolding src_lt_def by simp
  show ?thesis using rc read_lt by blast
qed


lemma latest_cdc_no_source_event_strictly_after_coord:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and k  :: 'k
    and ch :: "'chunk"
    and i  :: nat
    and c  :: src_coord
    and e  :: "('k, 'v) source_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_scope: "k \<in> scope_of R"
      and rc: "responsible_chunk R k = Some ch"
      and read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
      and i_lt: "i < length (clean_prefix_of R)"
      and cp_i: "clean_prefix_of R ! i = Cdc c e"
      and key_e: "key_of e = k"
      and i_latest:
        "\<forall> j. i < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
  shows "\<forall> j_src < length H.
           src_lt c (hist_coord (H ! j_src))
           \<and> src_le (hist_coord (H ! j_src)) (frontier_of R)
           \<longrightarrow> key_of (hist_event (H ! j_src)) \<noteq> k"
proof (intro allI impI)
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have src_hist_eq: "src_history_of R = H"
    by (elim conjE)
  from wf_body have wf2_cov_all:
    "\<forall> k \<in> scope_of R. covers_ordinary_cdc R k (frontier_of R)"
    by (elim conjE)
  from wf_body have wf7_fwd:
    "\<forall> p \<in> set (cdc_events_of R).
       key_of (hist_event p) \<in> scope_of R
       \<and> src_le (hist_coord p) (frontier_of R)
       \<longrightarrow> Cdc (hist_coord p) (hist_event p)
             \<in> set (clean_prefix_of R)"
    by (elim conjE)

  from wf2_cov_all k_scope
  have cov_k: "covers_ordinary_cdc R k (frontier_of R)" by blast
  then obtain ch_cov where
    rc_cov: "responsible_chunk R k = Some ch_cov" and
    cov_body:
      "\<forall> i. i < length (src_history_of R)
              \<longrightarrow> src_lt (chunk_read_coordinate R ch_cov)
                         (hist_coord (src_history_of R ! i))
              \<longrightarrow> src_le (hist_coord (src_history_of R ! i)) (frontier_of R)
              \<longrightarrow> key_of (hist_event (src_history_of R ! i)) = k
              \<longrightarrow> src_history_of R ! i \<in> set (cdc_events_of R)"
    unfolding covers_ordinary_cdc_def by blast
  have ch_cov_eq: "ch_cov = ch"
    using rc_cov rc by simp

  fix j_src
  assume j_lt: "j_src < length H"
  assume j_after_le_f:
    "src_lt c (hist_coord (H ! j_src))
     \<and> src_le (hist_coord (H ! j_src)) (frontier_of R)"
  hence j_after: "src_lt c (hist_coord (H ! j_src))"
    and j_le_f: "src_le (hist_coord (H ! j_src)) (frontier_of R)"
    by auto
  show "key_of (hist_event (H ! j_src)) \<noteq> k"
  proof (rule ccontr)
    assume "\<not> key_of (hist_event (H ! j_src)) \<noteq> k"
    hence j_key: "key_of (hist_event (H ! j_src)) = k" by simp

    have read_lt_j:
      "src_lt (chunk_read_coordinate R ch) (hist_coord (H ! j_src))"
    proof -
      have read_le_c: "src_le (chunk_read_coordinate R ch) c"
        using read_lt_c unfolding src_lt_def by simp
      have read_ne_c: "chunk_read_coordinate R ch \<noteq> c"
        using read_lt_c unfolding src_lt_def by simp
      have c_le_j: "src_le c (hist_coord (H ! j_src))"
        using j_after unfolding src_lt_def by simp
      have read_le_j: "src_le (chunk_read_coordinate R ch) (hist_coord (H ! j_src))"
        using read_le_c c_le_j src_le_trans by blast
      have read_ne_j: "chunk_read_coordinate R ch \<noteq> hist_coord (H ! j_src)"
      proof
        assume eq: "chunk_read_coordinate R ch = hist_coord (H ! j_src)"
        hence "src_le c (chunk_read_coordinate R ch)"
          using c_le_j by simp
        hence "chunk_read_coordinate R ch = c"
          using read_le_c src_le_antisym by blast
        with read_ne_c show False by simp
      qed
      show ?thesis unfolding src_lt_def using read_le_j read_ne_j by simp
    qed
    have j_lt_R: "j_src < length (src_history_of R)"
      using j_lt src_hist_eq by simp
    have j_after_R:
      "src_lt (chunk_read_coordinate R ch_cov)
              (hist_coord (src_history_of R ! j_src))"
      using read_lt_j ch_cov_eq src_hist_eq by simp
    have j_le_f_R:
      "src_le (hist_coord (src_history_of R ! j_src)) (frontier_of R)"
      using j_le_f src_hist_eq by simp
    have j_key_R:
      "key_of (hist_event (src_history_of R ! j_src)) = k"
      using j_key src_hist_eq by simp

    from cov_body j_lt_R j_after_R j_le_f_R j_key_R
    have hjs_in_cdc_R: "src_history_of R ! j_src \<in> set (cdc_events_of R)"
      by blast
    have hjs_in_cdc: "H ! j_src \<in> set (cdc_events_of R)"
      using hjs_in_cdc_R src_hist_eq by simp
    have key_in_scope_j: "key_of (hist_event (H ! j_src)) \<in> scope_of R"
      using j_key k_scope by simp
    from wf7_fwd hjs_in_cdc key_in_scope_j j_le_f
    have cdc_in_cp:
      "Cdc (hist_coord (H ! j_src)) (hist_event (H ! j_src))
         \<in> set (clean_prefix_of R)"
      by blast
    then obtain i_h where
      i_h_lt: "i_h < length (clean_prefix_of R)" and
      i_h_at:
        "clean_prefix_of R ! i_h
          = Cdc (hist_coord (H ! j_src)) (hist_event (H ! j_src))"
      by (auto simp: in_set_conv_nth)
    have i_h_key: "event_key (clean_prefix_of R ! i_h) = k"
      using i_h_at j_key by simp

    have i_h_le_i: "i_h \<le> i"
    proof (rule ccontr)
      assume "\<not> i_h \<le> i"
      hence i_lt_ih: "i < i_h" by simp
      from i_latest i_lt_ih i_h_lt
      have "event_key (clean_prefix_of R ! i_h) \<noteq> k" by blast
      with i_h_key show False by simp
    qed

    consider (eq) "i_h = i" | (lt) "i_h < i"
      using i_h_le_i by linarith
    thus False
    proof cases
      case eq
      have c_eq_j: "c = hist_coord (H ! j_src)"
        using cp_i i_h_at eq by simp
      with j_after show False
        unfolding src_lt_def by simp
    next
      case lt
      from clean_prefix_of_order_respects_coordinate[OF wf lt i_lt]
      have "src_le (cdc_coord (clean_prefix_of R ! i_h))
                   (cdc_coord (clean_prefix_of R ! i))" .
      hence "src_le (hist_coord (H ! j_src)) c"
        using i_h_at cp_i by simp
      with j_after show False
        unfolding src_lt_def
        using src_le_antisym by blast
    qed
  qed
qed


lemma latest_cdc_event_last_in_clean_prefix_key_coord_slice:
  fixes R :: "'run"
    and k :: 'k
    and i :: nat
    and c :: src_coord
    and e :: "('k, 'v) source_event"
  assumes i_lt: "i < length (clean_prefix_of R)"
      and cp_i: "clean_prefix_of R ! i = Cdc c e"
      and key_e: "key_of e = k"
      and i_latest:
        "\<forall> j. i < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
  shows "let slice =
           filter
             (\<lambda>x. case x of
                    Cdc c' e' \<Rightarrow> c' = c \<and> key_of e' = k
                  | Refresh _ _ _ \<Rightarrow> False)
             (clean_prefix_of R)
         in slice \<noteq> [] \<and> last slice = Cdc c e"
proof -
  let ?P = "\<lambda>x::('k, 'v) replay_event.
              case x of Cdc c' e' \<Rightarrow> c' = c \<and> key_of e' = k
                      | Refresh _ _ _ \<Rightarrow> False"
  have P_i: "?P (clean_prefix_of R ! i)"
    using cp_i key_e by simp
  have decomp:
    "clean_prefix_of R =
       take i (clean_prefix_of R)
       @ [clean_prefix_of R ! i]
       @ drop (Suc i) (clean_prefix_of R)"
    using i_lt
    by (metis Cons_nth_drop_Suc append_Cons append_Nil append_take_drop_id)
  have drop_no_P: "filter ?P (drop (Suc i) (clean_prefix_of R)) = []"
  proof -
    have "\<forall> x \<in> set (drop (Suc i) (clean_prefix_of R)). \<not> ?P x"
    proof
      fix x
      assume x_in: "x \<in> set (drop (Suc i) (clean_prefix_of R))"
      then obtain j where
        j_lt_drop: "j < length (drop (Suc i) (clean_prefix_of R))"
        and x_at: "drop (Suc i) (clean_prefix_of R) ! j = x"
        by (auto simp: in_set_conv_nth)
      let ?j' = "Suc (i + j)"
      have j'_lt: "?j' < length (clean_prefix_of R)"
        using j_lt_drop by simp
      have x_eq: "x = clean_prefix_of R ! ?j'"
        using x_at j_lt_drop by (simp add: add.commute)
      have i_lt_j': "i < ?j'" by simp
      from i_latest i_lt_j' j'_lt
      have later_not_k: "event_key (clean_prefix_of R ! ?j') \<noteq> k" by blast
      show "\<not> ?P x"
      proof
        assume Px: "?P x"
        hence "event_key x = k"
          by (cases x) auto
        hence "event_key (clean_prefix_of R ! ?j') = k"
          using x_eq by simp
        with later_not_k show False by simp
      qed
    qed
    thus ?thesis by (simp add: filter_empty_conv)
  qed
  have slice_eq:
    "filter ?P (clean_prefix_of R)
     = filter ?P (take i (clean_prefix_of R)) @ [Cdc c e]"
  proof -
    have "filter ?P (clean_prefix_of R)
        = filter ?P
            (take i (clean_prefix_of R)
             @ [clean_prefix_of R ! i]
             @ drop (Suc i) (clean_prefix_of R))"
      using decomp by simp
    also have "\<dots>
        = filter ?P (take i (clean_prefix_of R))
          @ filter ?P [clean_prefix_of R ! i]
          @ filter ?P (drop (Suc i) (clean_prefix_of R))"
      by simp
    also have "\<dots> = filter ?P (take i (clean_prefix_of R)) @ [Cdc c e]"
      using P_i cp_i drop_no_P by simp
    finally show ?thesis .
  qed
  show ?thesis
    using slice_eq by simp
qed


subsection \<open>Per-key replay equality: the Cdc case\<close>

lemma clean_prefix_of_per_key_replay_equals_source_cdc_case:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and k  :: 'k
    and i_max :: nat
    and c  :: src_coord
    and e  :: "('k, 'v) source_event"
  assumes wf: "wellformed_dblog_run b0 R H"
      and k_in_scope: "k \<in> scope_of R"
      and i_max_lt: "i_max < length (clean_prefix_of R)"
      and cp_at_imax: "clean_prefix_of R ! i_max = Cdc c e"
      and key_e: "key_of e = k"
      and i_max_latest:
        "\<forall>j. i_max < j \<and> j < length (clean_prefix_of R)
              \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k"
      and c_le_f: "src_le c (frontier_of R)"
  shows "Apply (clean_prefix_of R) k = Src b0 H (frontier_of R) k"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have src_hist_eq: "src_history_of R = H"
    by (elim conjE)
  from wf_body have wf_h: "wellformed_src_history H"
    by (elim conjE)

  let ?E =
    "(case e of Insert _ v \<Rightarrow> Some v
              | Update _ v \<Rightarrow> Some v
              | Delete _   \<Rightarrow> None)"

  have ev_key_imax: "event_key (clean_prefix_of R ! i_max) = k"
    using cp_at_imax key_e by simp
  have apply_val: "Apply (clean_prefix_of R) k = ?E"
  proof -
    have "Apply (clean_prefix_of R) k =
            (case clean_prefix_of R ! i_max of
               Cdc _ (Insert _ v) \<Rightarrow> Some v
             | Cdc _ (Update _ v) \<Rightarrow> Some v
             | Cdc _ (Delete _)   \<Rightarrow> None
             | Refresh _ m_obs _  \<Rightarrow> m_obs)"
      by (rule apply_at_latest_k_event[OF i_max_lt ev_key_imax i_max_latest])
    also have "\<dots> = ?E"
      using cp_at_imax by (cases e) auto
    finally show ?thesis .
  qed

  obtain ch where
    rc: "responsible_chunk R k = Some ch" and
    read_lt_c: "src_lt (chunk_read_coordinate R ch) c"
    using latest_cdc_for_key_implies_chunk_read_strictly_before
            [OF wf k_in_scope i_max_lt cp_at_imax key_e i_max_latest]
    by blast

  have no_later_src:
    "\<forall>j < length H.
       src_lt c (hist_coord (H ! j))
       \<and> src_le (hist_coord (H ! j)) (frontier_of R)
       \<longrightarrow> key_of (hist_event (H ! j)) \<noteq> k"
    by (rule latest_cdc_no_source_event_strictly_after_coord
          [OF wf k_in_scope rc read_lt_c i_max_lt cp_at_imax key_e i_max_latest])

  have slice_eq_R:
    "source_key_coord_slice k c (cdc_events_of R)
     = source_key_coord_slice k c (src_history_of R)"
    by (rule cdc_events_key_coord_slice_eq_source_history_slice_from_wf
          [OF wf k_in_scope rc read_lt_c c_le_f])

  let ?cp_slice =
    "filter
       (\<lambda>x::('k, 'v) replay_event.
          case x of
            Cdc c' e' \<Rightarrow> c' = c \<and> key_of e' = k
          | Refresh _ _ _ \<Rightarrow> False)
       (clean_prefix_of R)"
  let ?cdc_slice = "source_key_coord_slice k c (cdc_events_of R)"
  let ?hist_R_slice = "source_key_coord_slice k c (src_history_of R)"
  let ?hist_H_slice = "source_key_coord_slice k c H"

  have cp_slice_nonempty: "?cp_slice \<noteq> []"
    and cp_slice_last: "last ?cp_slice = Cdc c e"
    using latest_cdc_event_last_in_clean_prefix_key_coord_slice
            [OF i_max_lt cp_at_imax key_e i_max_latest]
    by (simp_all add: Let_def)
  have cp_slice_map:
    "?cp_slice =
       map (\<lambda>p. Cdc (hist_coord p) (hist_event p)) ?cdc_slice"
    by (rule clean_prefix_cdc_key_coord_slice[OF k_in_scope c_le_f])
  have cdc_slice_nonempty: "?cdc_slice \<noteq> []"
    using cp_slice_nonempty cp_slice_map by auto
  have last_map:
    "last ?cp_slice =
       Cdc (hist_coord (last ?cdc_slice)) (hist_event (last ?cdc_slice))"
  proof -
    let ?f = "\<lambda>p. Cdc (hist_coord p) (hist_event p)"
    have cdc_decomp: "?cdc_slice = butlast ?cdc_slice @ [last ?cdc_slice]"
      using cdc_slice_nonempty by simp
    have map_decomp:
      "map ?f ?cdc_slice = map ?f (butlast ?cdc_slice) @ [?f (last ?cdc_slice)]"
      by (subst cdc_decomp, simp)
    have "last ?cp_slice = last (map ?f ?cdc_slice)"
      using cp_slice_map by simp
    also have "\<dots> = last (map ?f (butlast ?cdc_slice) @ [?f (last ?cdc_slice)])"
      using map_decomp by simp
    also have "\<dots> = ?f (last ?cdc_slice)"
      by simp
    finally show ?thesis .
  qed
  have last_cdc_slice: "last ?cdc_slice = (c, e)"
  proof -
    have coord_eq: "hist_coord (last ?cdc_slice) = c"
      and event_eq: "hist_event (last ?cdc_slice) = e"
      using last_map cp_slice_last by simp_all
    show ?thesis
      using coord_eq event_eq by (cases "last ?cdc_slice") simp
  qed

  have hist_R_nonempty: "?hist_R_slice \<noteq> []"
    using slice_eq_R cdc_slice_nonempty by simp
  have hist_R_last: "last ?hist_R_slice = (c, e)"
    using slice_eq_R last_cdc_slice by simp
  have hist_H_nonempty: "?hist_H_slice \<noteq> []"
    using hist_R_nonempty src_hist_eq by simp
  have hist_H_last: "last ?hist_H_slice = (c, e)"
    using hist_R_last src_hist_eq by simp

  have src_val: "Src b0 H (frontier_of R) k = ?E"
    by (rule src_frontier_eq_effect_of_last_key_coord_slice
          [OF wf_h c_le_f no_later_src hist_H_nonempty hist_H_last])

  show ?thesis using apply_val src_val by simp
qed


subsection \<open>Per-key replay equality: main lemma and the Refresh case\<close>

lemma clean_prefix_of_per_key_replay_equals_source:
  fixes b0 :: "'k :: linorder \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and R  :: "'run"
    and k  :: 'k
  assumes wf:          "wellformed_dblog_run b0 R H"
      and k_in_scope:  "k \<in> scope_of R"
  shows "Apply (clean_prefix_of R) k = Src b0 H (frontier_of R) k"
proof -
  \<comment> \<open>Step 1: extract the WF body conjuncts this lemma consumes.
      Using the pattern @{text \<open>wf_body = wf[unfolded ...] + (elim conjE)\<close>},
      individual conjuncts are extracted one by one rather than as a
      compound --- a single @{text "elim conjE"} pass per conjunct
      suffices, since it also breaks inner conjunctions such as WF0's
      @{text \<open>src_history_of R = H \<and> wellformed_src_history H\<close>}.\<close>
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body have src_hist_eq: "src_history_of R = H"
    by (elim conjE)
  from wf_body have wf2_cov_all:
    "\<forall> k \<in> scope_of R. covers_ordinary_cdc R k (frontier_of R)"
    by (elim conjE)
  from wf_body have wf5:
    "\<forall> ch \<in> chunks R.
        src_le (chunk_read_coordinate R ch) (frontier_of R)"
    by (elim conjE)
  from wf_body have wf7_fwd:
    "\<forall> p \<in> set (cdc_events_of R).
       key_of (hist_event p) \<in> scope_of R
       \<and> src_le (hist_coord p) (frontier_of R)
       \<longrightarrow> Cdc (hist_coord p) (hist_event p)
             \<in> set (clean_prefix_of R)"
    by (elim conjE)

  \<comment> \<open>Extract @{text \<open>covers_ordinary_cdc R k (frontier_of R)\<close>} for \<^emph>\<open>this\<close> k.\<close>
  from wf2_cov_all k_in_scope
  have cov_k: "covers_ordinary_cdc R k (frontier_of R)" by blast
  then obtain ch_k where
    rc_k: "responsible_chunk R k = Some ch_k" and
    cov_k_body:
      "\<forall> i. i < length (src_history_of R)
              \<longrightarrow> src_lt (chunk_read_coordinate R ch_k)
                         (hist_coord (src_history_of R ! i))
              \<longrightarrow> src_le (hist_coord (src_history_of R ! i)) (frontier_of R)
              \<longrightarrow> key_of (hist_event (src_history_of R ! i)) = k
              \<longrightarrow> src_history_of R ! i \<in> set (cdc_events_of R)"
    unfolding covers_ordinary_cdc_def by blast

  \<comment> \<open>Step 2: invoke @{text clean_prefix_of_latest_replay_correspondence}
      to obtain the Cdc-or-Refresh disjunction at the latest k-event
      position in @{text \<open>clean_prefix_of(R)\<close>}.\<close>
  note latest_replay_disj = clean_prefix_of_latest_replay_correspondence[OF wf k_in_scope]

  \<comment> \<open>Step 3: case-split on the
      @{text clean_prefix_of_latest_replay_correspondence} disjunction.\<close>
  show ?thesis
  proof (rule disjE[OF latest_replay_disj])
    \<comment> \<open>\<^bold>\<open>Cdc case\<close>: latest k-event is a Cdc(c, e).\<close>
    assume cdc_disj:
      "\<exists> i c e. i < length (clean_prefix_of R)
              \<and> clean_prefix_of R ! i = Cdc c e
              \<and> key_of e = k
              \<and> (\<forall> j. i < j \<and> j < length (clean_prefix_of R)
                        \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k)
              \<and> (c, e) \<in> set (cdc_events_of R)
              \<and> src_le c (frontier_of R)"
    then obtain i_max c e where
      i_max_lt:    "i_max < length (clean_prefix_of R)" and
      cp_at_imax:  "clean_prefix_of R ! i_max = Cdc c e" and
      key_e:       "key_of e = k" and
      i_max_latest:
                   "\<forall> j. i_max < j \<and> j < length (clean_prefix_of R)
                          \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k" and
      ce_in_cdc:   "(c, e) \<in> set (cdc_events_of R)" and
      c_le_f:      "src_le c (frontier_of R)"
      by blast

    \<comment> \<open>Cdc case: delegated to the standalone helper lemma above.\<close>
    show "Apply (clean_prefix_of R) k = Src b0 H (frontier_of R) k"
      by (rule clean_prefix_of_per_key_replay_equals_source_cdc_case
            [OF wf k_in_scope i_max_lt cp_at_imax key_e i_max_latest
                c_le_f])
  next
    \<comment> \<open>\<^bold>\<open>Refresh case\<close>: latest k-event is a
        @{text \<open>Refresh(k, m, c_read)\<close>}.\<close>
    assume refresh_disj:
      "\<exists> i ch m c_read.
          i < length (clean_prefix_of R)
          \<and> clean_prefix_of R ! i = Refresh k m c_read
          \<and> (\<forall> j. i < j \<and> j < length (clean_prefix_of R)
                    \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k)
          \<and> responsible_chunk R k = Some ch
          \<and> chunk_read_result R ch k = Some m
          \<and> chunk_read_coordinate R ch = c_read"
    then obtain i_max ch m c_read where
      i_max_lt:    "i_max < length (clean_prefix_of R)" and
      cp_at_imax:  "clean_prefix_of R ! i_max = Refresh k m c_read" and
      i_max_latest:
                   "\<forall> j. i_max < j \<and> j < length (clean_prefix_of R)
                          \<longrightarrow> event_key (clean_prefix_of R ! j) \<noteq> k" and
      rc_eq:       "responsible_chunk R k = Some ch" and
      crr_res:     "chunk_read_result R ch k = Some m" and
      cr_eq:       "chunk_read_coordinate R ch = c_read"
      by blast

    \<comment> \<open>Refresh case Step 1: @{text \<open>ch_k = ch\<close>} (uniqueness via
        Some-injectivity).\<close>
    have ch_eq: "ch = ch_k"
      using rc_eq rc_k by simp

    \<comment> \<open>Refresh case Step 2: @{text \<open>ch \<in> chunks R\<close>} + @{text \<open>k \<in> chunk_domain R ch\<close>}
        via WF1 (d) (with the responsible-chunk fact from the case split).\<close>
    from wf_body have wf1d:
      "\<forall> k \<in> scope_of R. \<forall> ch.
         responsible_chunk R k = Some ch
           \<longleftrightarrow> ch \<in> chunks R \<and> owns R ch k"
      by (elim conjE)
    from wf1d k_in_scope rc_eq
    have ch_props: "ch \<in> chunks R \<and> owns R ch k" by blast
    hence ch_in_chunks: "ch \<in> chunks R" and k_in_dom: "k \<in> chunk_domain R ch"
      by auto

    \<comment> \<open>Refresh case Step 3: Apply value via
        @{text apply_at_latest_k_event}.\<close>
    have ev_key_imax: "event_key (clean_prefix_of R ! i_max) = k"
      using cp_at_imax by simp
    have apply_val: "Apply (clean_prefix_of R) k = m"
    proof -
      have "Apply (clean_prefix_of R) k =
              (case clean_prefix_of R ! i_max of
                 Cdc _ (Insert _ v) \<Rightarrow> Some v
               | Cdc _ (Update _ v) \<Rightarrow> Some v
               | Cdc _ (Delete _)   \<Rightarrow> None
               | Refresh _ m_obs _  \<Rightarrow> m_obs)"
        by (rule apply_at_latest_k_event[OF i_max_lt ev_key_imax i_max_latest])
      also have "\<dots> = m"
        using cp_at_imax by simp
      finally show ?thesis .
    qed

    \<comment> \<open>Refresh case Step 4: @{text \<open>m = Src b0 H c_read k\<close>} via
        @{text refresh_coordinate_match}.\<close>
    have m_eq_src_at_cr: "m = Src b0 H c_read k"
    proof -
      from refresh_coordinate_match[OF wf ch_in_chunks k_in_dom crr_res]
      have "m = Src b0 H (chunk_read_coordinate R ch) k" .
      thus ?thesis using cr_eq by simp
    qed

    \<comment> \<open>Refresh case Step 5: no source event for k in
        @{text \<open>(c_read, frontier]\<close>}.\<close>
    have no_later_src:
      "\<forall> j_src < length H. src_lt c_read (hist_coord (H ! j_src))
                            \<and> src_le (hist_coord (H ! j_src)) (frontier_of R)
                            \<longrightarrow> key_of (hist_event (H ! j_src)) \<noteq> k"
    proof (intro allI impI)
      fix j_src
      assume j_lt: "j_src < length H"
      assume j_after_le_f:
        "src_lt c_read (hist_coord (H ! j_src))
         \<and> src_le (hist_coord (H ! j_src)) (frontier_of R)"
      hence j_after: "src_lt c_read (hist_coord (H ! j_src))"
        and j_le_f: "src_le (hist_coord (H ! j_src)) (frontier_of R)"
        by auto
      show "key_of (hist_event (H ! j_src)) \<noteq> k"
      proof (rule ccontr)
        assume "\<not> key_of (hist_event (H ! j_src)) \<noteq> k"
        hence j_key: "key_of (hist_event (H ! j_src)) = k" by simp

        \<comment> \<open>@{text \<open>chunk_read_coordinate R ch_k = chunk_read_coordinate R ch\<close>}
            = @{text c_read}.\<close>
        have crk_eq: "chunk_read_coordinate R ch_k = c_read"
          using ch_eq cr_eq by simp
        have j_after_crk:
          "src_lt (chunk_read_coordinate R ch_k) (hist_coord (H ! j_src))"
          using crk_eq j_after by simp

        \<comment> \<open>Translate @{text j_src}'s H properties to @{text \<open>src_history_of R\<close>}
            via @{text src_hist_eq}.\<close>
        have j_lt_R: "j_src < length (src_history_of R)"
          using j_lt src_hist_eq by simp
        have j_after_R:
          "src_lt (chunk_read_coordinate R ch_k)
                  (hist_coord (src_history_of R ! j_src))"
          using j_after_crk src_hist_eq by simp
        have j_le_f_R:
          "src_le (hist_coord (src_history_of R ! j_src)) (frontier_of R)"
          using j_le_f src_hist_eq by simp
        have j_key_R:
          "key_of (hist_event (src_history_of R ! j_src)) = k"
          using j_key src_hist_eq by simp

        \<comment> \<open>@{text covers_ordinary_cdc}:
            @{text \<open>H!j_src \<in> cdc_events_of R\<close>}.\<close>
        from cov_k_body j_lt_R j_after_R j_le_f_R j_key_R
        have hjs_in_cdc_R:
          "src_history_of R ! j_src \<in> set (cdc_events_of R)" by blast
        have hjs_in_cdc: "H ! j_src \<in> set (cdc_events_of R)"
          using hjs_in_cdc_R src_hist_eq by simp

        \<comment> \<open>WF7 forward: @{text \<open>Cdc (hist_coord (H!j_src)) (hist_event (H!j_src))\<close>}
            @{text \<open>\<in> clean_prefix_of R\<close>}.\<close>
        have key_in_scope_j:
          "key_of (hist_event (H ! j_src)) \<in> scope_of R"
          using j_key k_in_scope by simp
        from wf7_fwd hjs_in_cdc key_in_scope_j j_le_f
        have cdc_in_cp:
          "Cdc (hist_coord (H ! j_src)) (hist_event (H ! j_src))
             \<in> set (clean_prefix_of R)"
          by blast
        then obtain i_h where
          i_h_lt: "i_h < length (clean_prefix_of R)" and
          i_h_at: "clean_prefix_of R ! i_h
                     = Cdc (hist_coord (H ! j_src)) (hist_event (H ! j_src))"
          by (auto simp: in_set_conv_nth)

        have i_h_key: "event_key (clean_prefix_of R ! i_h) = k"
          using i_h_at j_key by simp

        \<comment> \<open>@{text \<open>i_h \<le> i_max\<close>} (else contradicts @{text i_max_latest}).\<close>
        have i_h_le_imax: "i_h \<le> i_max"
        proof (rule ccontr)
          assume "\<not> i_h \<le> i_max"
          hence imax_lt_ih: "i_max < i_h" by simp
          from i_max_latest imax_lt_ih i_h_lt have "event_key (clean_prefix_of R ! i_h) \<noteq> k"
            by blast
          with i_h_key show False by simp
        qed

        \<comment> \<open>Three sub-cases on @{text i_h} vs @{text i_max}.\<close>
        consider (eq) "i_h = i_max" | (lt) "i_h < i_max"
          using i_h_le_imax by linarith
        thus False
        proof cases
          case eq
          \<comment> \<open>@{text \<open>clean_prefix_of R ! i_max = Refresh k m c_read\<close>} \<^emph>\<open>and\<close>
              @{text \<open>= Cdc (...)\<close>}. Distinct constructors, contradiction.\<close>
          from cp_at_imax i_h_at eq show False by simp
        next
          case lt
          \<comment> \<open>By @{text clean_prefix_of_order_respects_coordinate}
              + @{text cdc_coord}, @{text \<open>src_le (hist_coord (H!j_src)) c_read\<close>}.
              But @{text \<open>src_lt c_read (hist_coord (H!j_src))\<close>}. Antisymmetry.\<close>
          from clean_prefix_of_order_respects_coordinate[OF wf lt i_max_lt]
          have "src_le (cdc_coord (clean_prefix_of R ! i_h))
                       (cdc_coord (clean_prefix_of R ! i_max))" .
          hence "src_le (hist_coord (H ! j_src)) c_read"
            using i_h_at cp_at_imax by simp
          with j_after show False
            unfolding src_lt_def
            using src_le_antisym by blast
        qed
      qed
    qed

    \<comment> \<open>Refresh case Step 6: @{text \<open>c_read \<le> frontier\<close>} via WF5.\<close>
    have c_read_le_f: "src_le c_read (frontier_of R)"
    proof -
      from wf5 ch_in_chunks
      have "src_le (chunk_read_coordinate R ch) (frontier_of R)" by blast
      thus ?thesis using cr_eq by simp
    qed

    \<comment> \<open>Refresh case Step 7:
        @{text \<open>Src b0 H frontier k = Src b0 H c_read k\<close>}.\<close>
    have src_eq:
      "Src b0 H (frontier_of R) k = Src b0 H c_read k"
      by (rule src_eq_when_no_later_src_event_for_k[OF c_read_le_f no_later_src])

    \<comment> \<open>Refresh case Step 8: assemble
        @{text \<open>Apply = m = Src b0 H c_read k = Src b0 H frontier k\<close>}.\<close>
    show "Apply (clean_prefix_of R) k = Src b0 H (frontier_of R) k"
      using apply_val m_eq_src_at_cr src_eq by simp
  qed
qed


subsection \<open>Layer 2 run-side soundness (locale form of the paper's bridge lemma)\<close>

text \<open>
  The run-side instance of @{const virtual_cut_state}: a wellformed DBLog
  run replays its clean prefix to the source state at its frontier on its scope.
  The public theorem @{text "Virtual_Cut.wellformed_run_implies_virtual_cut"}
  is this theorem specialized through the canonical interpretation (its
  conclusion uses the public @{text "Virtual_Cut.virtual_cut_state"}, which
  coincides with the body-identical @{const virtual_cut_state} used
  here). Proved by
  unfolding @{const virtual_cut_state} and applying the locale per-key
  equality @{thm [source] clean_prefix_of_per_key_replay_equals_source}
  pointwise.
\<close>

theorem wellformed_run_implies_virtual_cut:
  assumes "wellformed_dblog_run b0 R H"
  shows
    "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                       (frontier_of R) H"
  unfolding virtual_cut_state_def restrict_def
  by (intro ext)
     (auto intro: clean_prefix_of_per_key_replay_equals_source[OF assms])

end

end
