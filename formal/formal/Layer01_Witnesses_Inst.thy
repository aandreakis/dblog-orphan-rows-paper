(*  Title:   Layer01_Witnesses_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Witnesses_Inst
  imports Layer01_Witnesses_Model DBLog_Run_Substrate_Layer2
begin

section \<open>Constructed interpretation for the minimum-viable wellformed-run
  witness\<close>

text \<open>
  Constructs an explicit model of the minimum-viable wellformed-run positive
  witness and interprets the Layer 1 locale @{locale dblog_run_substrate} at
  it, establishing the witness facts with no axioms. The model is that of
  @{text Layer01_Witnesses_Model}
  (the @{typ unit} run carrier, the @{type wit_cchunk} two-element chunk type,
  and the definitional accessors).

  Structure:

    \<^item> \<^bold>\<open>Constructed interpretation.\<close> We instantiate
        @{locale dblog_run_substrate} at the model carrier
        (@{typ unit} run, @{type wit_cchunk} chunks, the @{text "wit_c\<dots>"}
        accessors). @{locale dblog_run_substrate} assumes only the two
        @{text chunks_list} obligations, which hold definitionally for the
        model enumeration @{term "[WCh1, WCh2]"}, so the interpretation
        discharges them with @{method simp} --- no axiom.

    \<^item> \<^bold>\<open>Accessor-value lemmas.\<close> The @{text "wm_\<dots>"} lemmas read off the
        model's definitional accessor values pointwise --- the conjuncts of
        @{thm [source] wit_model_accessor_values} --- in exactly the
        shape used as rewrite facts by the determinate clean-prefix
        computation and the seven-clause wellformedness discharge below.
        The carrier-independent witness data they refer to (@{const b0_w},
        @{const H_w}, the @{const Src} / @{const latest_src_event}
        computation lemmas, @{thm [source] wf_h_w}) lives in
        @{text Layer01_Witnesses_Core}.

  The constructed witness needs the key/value carrier fixed to concrete
  @{typ nat} (the witness keys and values are literal naturals); a lemma inside
  the locale context cannot do this, because the locale type parameter
  @{typ "'k"} is rigid there. The constructed wellformed-run fact
  @{text wit_model_wellformed} and the constructed positive witness
  @{text wellformed_run_positive_witness_constructed} therefore live in
  the global context over the interpretation, neither resting on any run/chunk
  axiom.

  The witness source coordinates @{const c1_w} / @{const c2_w} are
  @{const coord_of_nat} definitions from
  @{text Source_Coordinates}
  (@{text "c1_w = coord_of_nat 6"}, @{text "c2_w = coord_of_nat 7"}); the
  strict chain @{thm [source] c0_lt_c1_w} / @{thm [source] c1_w_lt_c2_w} and
  its basic consequences are proved there by @{method simp} from @{typ nat}
  arithmetic, and further derived ordering facts on the witness data
  (e.g. @{thm [source] not_src_lt_c2_w_c1_w}) live in
  @{text Layer01_Witnesses_Core}.
\<close>

subsection \<open>Constructed interpretation at the witness model\<close>

text \<open>
  Instantiate @{locale dblog_run_substrate} at the model carrier: the
  @{typ unit} run, the @{type wit_cchunk} chunks, and the definitional
  @{text "wit_c\<dots>"} accessors of
  @{text Layer01_Witnesses_Model}. The two
  @{text chunks_list} obligations reduce to
  @{term "set [WCh1, WCh2] = {WCh1, WCh2}"} and @{term "distinct [WCh1, WCh2]"},
  discharged by @{method simp} --- no axiom.
\<close>

global_interpretation wit_model: dblog_run_substrate
  wit_cscope
  wit_cfrontier
  wit_cchunks
  wit_csrc_history_of
  wit_cchunk_read_result
  wit_ccdc_events_of
  wit_cchunks_list
  wit_cchunk_domain
  wit_cresponsible_chunk
  wit_cchunk_lower_watermark
  wit_cchunk_upper_watermark
  wit_cchunk_read_coordinate
  by unfold_locales (simp_all add: wit_cchunks_def wit_cchunks_list_def)


subsection \<open>Model accessor-value lemmas\<close>

text \<open>
  Each @{text "wm_\<dots>"} lemma reads off one model accessor value from its
  definitional equation. Together they are the
  conjuncts of @{thm [source] wit_model_accessor_values}, used as the
  rewrite facts that drive the proofs below.
\<close>

lemma wm_distinct: "WCh1 \<noteq> WCh2" by simp
lemma wm_scope: "wit_cscope () = {0, 1}" by (simp add: wit_cscope_def)
lemma wm_frontier: "wit_cfrontier () = c2_w" by (simp add: wit_cfrontier_def)
lemma wm_chunks: "wit_cchunks () = {WCh1, WCh2}" by (simp add: wit_cchunks_def)
lemma wm_dom_1: "wit_cchunk_domain () WCh1 = {0}"
  by (simp add: wit_cchunk_domain_def)
lemma wm_dom_2: "wit_cchunk_domain () WCh2 = {1}"
  by (simp add: wit_cchunk_domain_def)
lemma wm_resp_0: "wit_cresponsible_chunk () 0 = Some WCh1"
  by (simp add: wit_cresponsible_chunk_def)
lemma wm_resp_1: "wit_cresponsible_chunk () 1 = Some WCh2"
  by (simp add: wit_cresponsible_chunk_def)
lemma wm_resp_else:
  "k \<noteq> 0 \<Longrightarrow> k \<noteq> 1 \<Longrightarrow> wit_cresponsible_chunk () k = None"
  by (simp add: wit_cresponsible_chunk_def)
lemma wm_rcoord_1: "wit_cchunk_read_coordinate () WCh1 = c0"
  by (simp add: wit_cchunk_read_coordinate_def)
lemma wm_rcoord_2: "wit_cchunk_read_coordinate () WCh2 = c2_w"
  by (simp add: wit_cchunk_read_coordinate_def)
lemma wm_lwm_1: "wit_cchunk_lower_watermark () WCh1 = c0"
  by (simp add: wit_cchunk_lower_watermark_def)
lemma wm_uwm_1: "wit_cchunk_upper_watermark () WCh1 = c0"
  by (simp add: wit_cchunk_upper_watermark_def)
lemma wm_lwm_2: "wit_cchunk_lower_watermark () WCh2 = c2_w"
  by (simp add: wit_cchunk_lower_watermark_def)
lemma wm_uwm_2: "wit_cchunk_upper_watermark () WCh2 = c2_w"
  by (simp add: wit_cchunk_upper_watermark_def)
lemma wm_src_history: "wit_csrc_history_of () = H_w"
  by (simp add: wit_csrc_history_of_def)
lemma wm_crr_1_0: "wit_cchunk_read_result () WCh1 0 = Some None"
  by (simp add: wit_cchunk_read_result_def)
lemma wm_crr_2_1: "wit_cchunk_read_result () WCh2 1 = Some None"
  by (simp add: wit_cchunk_read_result_def)
lemma wm_cdc:
  "wit_ccdc_events_of () = [(c1_w, Insert 0 42), (c2_w, Delete 1)]"
  by (simp add: wit_ccdc_events_of_def H_w_def)
lemma wm_chunks_list: "wit_cchunks_list () = [WCh1, WCh2]"
  by (simp add: wit_cchunks_list_def)

lemma wm_chunks_eq:
  "(ch \<in> wit_cchunks ()) \<longleftrightarrow> (ch = WCh1 \<or> ch = WCh2)"
  using wm_chunks by simp


subsection \<open>Determinate clean prefix and Apply over the model\<close>

text \<open>The determinate clean prefix of the witness run, computed over the
  model carrier as an explicit four-event list.\<close>

lemma wm_clean_prefix:
  "wit_model.clean_prefix_of ()
     = [ Refresh (0::nat) (None::nat option) c0,
         Cdc c1_w (Insert 0 42),
         Cdc c2_w (Delete 1),
         Refresh 1 None c2_w ]"
proof -
  have d0: "sorted_list_of_set {0::nat} = [0]" by simp
  have d1: "sorted_list_of_set {Suc 0} = [Suc 0]" by simp
  have le12: "src_le c1_w c2_w"
    using c1_w_lt_c2_w by (simp add: src_lt_def)
  have le02: "src_le c0 c2_w"
    using c0_le_c1_w le12 src_le_trans by blast
  have n10: "\<not> src_le c1_w c0"
    using c0_le_c1_w c0_neq_c1_w src_le_antisym by blast
  have n20: "\<not> src_le c2_w c0"
    using le02 c0_neq_c2_w src_le_antisym by blast
  have n21: "\<not> src_le c2_w c1_w"
    using le12 c1_w_neq_c2_w src_le_antisym by blast
  show ?thesis
    unfolding wit_model.clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: wm_chunks_list wm_dom_1 wm_dom_2
                  wm_rcoord_1 wm_rcoord_2
                  wm_crr_1_0 wm_crr_2_1[unfolded One_nat_def]
                  wm_cdc wm_scope wm_frontier d0 d1 One_nat_def
                  List.map_filter_simps sort_key_def
                  c0_le_c1_w[unfolded src_le_eq_less_eq]
                  le02[unfolded src_le_eq_less_eq]
                  le12[unfolded src_le_eq_less_eq]
                  n10[unfolded src_le_eq_less_eq]
                  n20[unfolded src_le_eq_less_eq]
                  n21[unfolded src_le_eq_less_eq])
qed

text \<open>Replaying the witness clean prefix: @{const Apply} yields the map
  sending key \<open>0\<close> to \<open>42\<close> and every other key to @{const None}.\<close>

lemma wm_apply:
  "Apply (wit_model.clean_prefix_of ())
     = (\<lambda>k. if k = (0::nat) then Some (42::nat) else None)"
proof -
  have "Apply (wit_model.clean_prefix_of ())
          = foldl apply_step (\<lambda>_. None)
              [ Refresh (0::nat) (None::nat option) c0,
                Cdc c1_w (Insert 0 42),
                Cdc c2_w (Delete 1),
                Refresh 1 None c2_w ]"
    unfolding Apply_def wm_clean_prefix by (rule refl)
  also have "\<dots> = (\<lambda>k. if k = (0::nat) then Some (42::nat) else None)"
    by (auto simp: fun_eq_iff fun_upd_def)
  finally show ?thesis .
qed


subsection \<open>Constructed wellformed-run fact\<close>

text \<open>
  The minimum-viable witness is wellformed, proved over the constructed carrier
  with no run/chunk axiom: a clause-by-clause discharge of the seven-clause
  @{text wellformed_dblog_run} definition, driven by the @{text "wm_\<dots>"}
  accessor-value lemmas together with the
  @{text Layer01_Witnesses_Core} facts about
  @{const b0_w} / @{const H_w}.
\<close>

theorem wit_model_wellformed:
  "wit_model.wellformed_dblog_run b0_w () H_w"
  unfolding wit_model.wellformed_dblog_run_def
proof (intro conjI)
  \<comment> \<open>WF0 part 1: source-history binding.\<close>
  show "wit_csrc_history_of () = H_w" by (rule wm_src_history)
next
  \<comment> \<open>WF0 part 2: source-history wellformedness.\<close>
  show "wellformed_src_history H_w" by (rule wf_h_w)
next
  \<comment> \<open>WF1 (a): unique responsible chunk per in-scope key.\<close>
  show "\<forall>k\<in>wit_cscope (). \<exists>!ch. ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch"
  proof
    fix k :: nat
    assume "k \<in> wit_cscope ()"
    hence k_cases: "k = 0 \<or> k = 1" using wm_scope by simp
    show "\<exists>!ch. ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch"
    proof (cases "k = 0")
      case True
      have "WCh1 \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () WCh1"
        using wm_chunks wm_dom_1 True by simp
      moreover have "\<And>ch. ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch \<Longrightarrow> ch = WCh1"
        using wm_chunks_eq wm_dom_1 wm_dom_2 True by auto
      ultimately show ?thesis by blast
    next
      case False
      hence k1: "k = 1" using k_cases by simp
      have "WCh2 \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () WCh2"
        using wm_chunks wm_dom_2 k1 by simp
      moreover have "\<And>ch. ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch \<Longrightarrow> ch = WCh2"
        using wm_chunks_eq wm_dom_1 wm_dom_2 k1 by auto
      ultimately show ?thesis by blast
    qed
  qed
next
  \<comment> \<open>WF1 (b): chunk domains pairwise disjoint.\<close>
  show "\<forall>ch1\<in>wit_cchunks (). \<forall>ch2\<in>wit_cchunks ().
          ch1 \<noteq> ch2 \<longrightarrow> wit_cchunk_domain () ch1 \<inter> wit_cchunk_domain () ch2 = {}"
    using wm_chunks_eq wm_dom_1 wm_dom_2 by auto
next
  \<comment> \<open>WF1 (c): canonical chunk-ownership domain equals scope.\<close>
  show "wit_model.canonical_chunk_ownership_domain () = wit_cscope ()"
    unfolding wit_model.canonical_chunk_ownership_domain_def
    using wm_chunks wm_dom_1 wm_dom_2 wm_scope by auto
next
  \<comment> \<open>WF1 (d): @{text responsible_chunk} @{text \<open>\<longleftrightarrow>\<close>} ownership predicate (in scope).\<close>
  show "\<forall>k\<in>wit_cscope (). \<forall>ch.
          wit_cresponsible_chunk () k = Some ch
            \<longleftrightarrow> ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch"
  proof (intro ballI allI)
    fix k :: nat and ch :: wit_cchunk
    assume "k \<in> wit_cscope ()"
    hence k_cases: "k = 0 \<or> k = 1" using wm_scope by simp
    show "wit_cresponsible_chunk () k = Some ch
            \<longleftrightarrow> ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch"
    proof (cases "k = 0")
      case True
      then have rc: "wit_cresponsible_chunk () k = Some WCh1"
        using wm_resp_0 by simp
      show ?thesis
      proof
        assume "wit_cresponsible_chunk () k = Some ch"
        with rc have "ch = WCh1" by simp
        thus "ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch"
          using wm_chunks wm_dom_1 True by simp
      next
        assume A: "ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch"
        have "ch = WCh1"
          using A wm_chunks_eq wm_dom_1 wm_dom_2 True by auto
        with rc show "wit_cresponsible_chunk () k = Some ch" by simp
      qed
    next
      case False
      hence k1: "k = 1" using k_cases by simp
      then have rc: "wit_cresponsible_chunk () k = Some WCh2"
        using wm_resp_1 by simp
      show ?thesis
      proof
        assume "wit_cresponsible_chunk () k = Some ch"
        with rc have "ch = WCh2" by simp
        thus "ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch"
          using wm_chunks wm_dom_2 k1 by simp
      next
        assume A: "ch \<in> wit_cchunks () \<and> k \<in> wit_cchunk_domain () ch"
        have "ch = WCh2"
          using A wm_chunks_eq wm_dom_1 wm_dom_2 k1 by auto
        with rc show "wit_cresponsible_chunk () k = Some ch" by simp
      qed
    qed
  qed
next
  \<comment> \<open>WF1 (e): out-of-scope keys have no responsible chunk.\<close>
  show "\<forall>k. k \<notin> wit_cscope () \<longrightarrow> wit_cresponsible_chunk () k = None"
    using wm_scope wm_resp_else by auto
next
  \<comment> \<open>WF1 (f) part 1: scope is finite.\<close>
  show "finite (wit_cscope ())" using wm_scope by simp
next
  \<comment> \<open>WF1 (f) part 2: chunk domains are finite.\<close>
  show "\<forall>ch\<in>wit_cchunks (). finite (wit_cchunk_domain () ch)"
    using wm_chunks_eq wm_dom_1 wm_dom_2 by auto
next
  \<comment> \<open>WF1 (g): every chunk has a non-empty domain.\<close>
  show "\<forall>ch\<in>wit_cchunks (). wit_cchunk_domain () ch \<noteq> {}"
    using wm_chunks_eq wm_dom_1 wm_dom_2 by auto
next
  \<comment> \<open>WF2 coverage: observed CDC reaches every in-scope key.\<close>
  show "\<forall>k\<in>wit_cscope (). wit_model.covers_ordinary_cdc () k (wit_cfrontier ())"
  proof
    fix k :: nat assume "k \<in> wit_cscope ()"
    hence k_cases: "k = 0 \<or> k = 1" using wm_scope by simp
    show "wit_model.covers_ordinary_cdc () k (wit_cfrontier ())"
    proof (cases "k = 0")
      case True
      show ?thesis
        unfolding wit_model.covers_ordinary_cdc_def
      proof (intro exI[where x = WCh1] conjI allI impI)
        show "wit_cresponsible_chunk () k = Some WCh1"
          using wm_resp_0 True by simp
      next
        fix i assume i_lt: "i < length (wit_csrc_history_of ())"
           and chunk_lt: "src_lt (wit_cchunk_read_coordinate () WCh1)
                                  (hist_coord (wit_csrc_history_of () ! i))"
           and to_f: "src_le (hist_coord (wit_csrc_history_of () ! i))
                              (wit_cfrontier ())"
           and key_eq: "key_of (hist_event (wit_csrc_history_of () ! i)) = k"
        show "wit_csrc_history_of () ! i \<in> set (wit_ccdc_events_of ())"
          using i_lt chunk_lt to_f key_eq True
                wm_src_history wm_cdc length_H_w
                H_w_nth_0 H_w_nth_1
          by (cases "i = 0"; cases "i = 1"; auto simp: numeral_2_eq_2 set_H_w)
      qed
    next
      case False
      hence k1: "k = 1" using k_cases by simp
      show ?thesis
        unfolding wit_model.covers_ordinary_cdc_def
      proof (intro exI[where x = WCh2] conjI allI impI)
        show "wit_cresponsible_chunk () k = Some WCh2"
          using wm_resp_1 k1 by simp
      next
        fix i assume i_lt: "i < length (wit_csrc_history_of ())"
           and chunk_lt: "src_lt (wit_cchunk_read_coordinate () WCh2)
                                  (hist_coord (wit_csrc_history_of () ! i))"
           and to_f: "src_le (hist_coord (wit_csrc_history_of () ! i))
                              (wit_cfrontier ())"
           and key_eq: "key_of (hist_event (wit_csrc_history_of () ! i)) = k"
        have False
          using i_lt chunk_lt
                wm_src_history wm_rcoord_2 length_H_w
                H_w_nth_0 H_w_nth_1
                not_src_lt_c2_w_c1_w not_src_lt_c2_w_c2_w
          by (cases "i = 0"; cases "i = 1"; auto simp: numeral_2_eq_2)
        thus "wit_csrc_history_of () ! i \<in> set (wit_ccdc_events_of ())" ..
      qed
    qed
  qed
next
  \<comment> \<open>WF2 faithfulness.\<close>
  show "\<forall>p\<in>set (wit_ccdc_events_of ()).
          key_of (hist_event p) \<in> wit_cscope ()
          \<and> src_le (hist_coord p) (wit_cfrontier ())
          \<longrightarrow> p \<in> set (wit_csrc_history_of ())"
    using wm_cdc wm_src_history set_H_w by auto
next
  \<comment> \<open>WF2 order-preserving sublist.\<close>
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> wit_cscope ()
                                   \<and> src_le (hist_coord p) (wit_cfrontier ()));
                 cdc_in_slice  = filter in_slice (wit_ccdc_events_of ());
                 hist_in_slice = filter in_slice (wit_csrc_history_of ())
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    have eq: "wit_ccdc_events_of () = wit_csrc_history_of ()"
      using wm_cdc wm_src_history H_w_def by simp
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> wit_cscope ()
                                \<and> src_le (hist_coord p) (wit_cfrontier ()));
              cdc_in_slice  = filter in_slice (wit_ccdc_events_of ());
              hist_in_slice = filter in_slice (wit_csrc_history_of ())
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      using eq by (simp add: Let_def)
  qed
next
  \<comment> \<open>WF2 post-read same-key/same-coordinate multiplicity.\<close>
  show "\<forall>k\<in>wit_cscope (). \<forall>ch c.
          wit_cresponsible_chunk () k = Some ch
          \<and> src_lt (wit_cchunk_read_coordinate () ch) c
          \<and> src_le c (wit_cfrontier ())
          \<longrightarrow>
            mset (source_key_coord_slice k c (wit_ccdc_events_of ()))
            = mset (source_key_coord_slice k c (wit_csrc_history_of ()))"
  proof (intro ballI allI impI)
    fix k :: nat and ch :: wit_cchunk and c :: src_coord
    have eq: "wit_ccdc_events_of () = wit_csrc_history_of ()"
      using wm_cdc wm_src_history H_w_def by simp
    show "mset (source_key_coord_slice k c (wit_ccdc_events_of ()))
          = mset (source_key_coord_slice k c (wit_csrc_history_of ()))"
      using eq by simp
  qed
next
  \<comment> \<open>WF4: chunk-read evidence.\<close>
  show "\<forall>ch\<in>wit_cchunks ().
          src_le (wit_cchunk_lower_watermark () ch) (wit_cchunk_read_coordinate () ch)
        \<and> src_le (wit_cchunk_read_coordinate () ch) (wit_cchunk_upper_watermark () ch)
        \<and> (\<forall>k\<in>wit_cchunk_domain () ch. \<exists>m. wit_cchunk_read_result () ch k = Some m)
        \<and> (\<forall>k\<in>wit_cchunk_domain () ch. \<forall>m.
             wit_cchunk_read_result () ch k = Some m
               \<longleftrightarrow> Refresh k m (wit_cchunk_read_coordinate () ch)
                    \<in> set (wit_model.clean_prefix_of ()))"
  proof
    fix ch :: wit_cchunk
    assume ch_in: "ch \<in> wit_cchunks ()"
    hence ch_cases: "ch = WCh1 \<or> ch = WCh2"
      using wm_chunks_eq by simp
    show "src_le (wit_cchunk_lower_watermark () ch) (wit_cchunk_read_coordinate () ch)
        \<and> src_le (wit_cchunk_read_coordinate () ch) (wit_cchunk_upper_watermark () ch)
        \<and> (\<forall>k\<in>wit_cchunk_domain () ch. \<exists>m. wit_cchunk_read_result () ch k = Some m)
        \<and> (\<forall>k\<in>wit_cchunk_domain () ch. \<forall>m.
             wit_cchunk_read_result () ch k = Some m
               \<longleftrightarrow> Refresh k m (wit_cchunk_read_coordinate () ch)
                    \<in> set (wit_model.clean_prefix_of ()))"
    proof (cases "ch = WCh1")
      case True
      show ?thesis
        using True wm_lwm_1 wm_uwm_1 wm_rcoord_1 src_le_refl
              wm_dom_1 wm_crr_1_0 wm_clean_prefix
        by auto
    next
      case False
      hence "ch = WCh2" using ch_cases by simp
      show ?thesis
        using \<open>ch = WCh2\<close> wm_lwm_2 wm_uwm_2 wm_rcoord_2 src_le_refl
              wm_dom_2 wm_crr_2_1 wm_clean_prefix
              c0_neq_c2_w c1_w_neq_c2_w
        by auto
    qed
  qed
next
  \<comment> \<open>WF5: chunk-read coordinate at-or-before frontier.\<close>
  show "\<forall>ch\<in>wit_cchunks ().
          src_le (wit_cchunk_read_coordinate () ch) (wit_cfrontier ())"
    using wm_chunks_eq wm_rcoord_1 wm_rcoord_2 wm_frontier
          src_le_c0_c2_w src_le_refl
    by auto
next
  \<comment> \<open>WF6 main: refresh correctness against Src.\<close>
  show "\<forall>ch\<in>wit_cchunks (). \<forall>k\<in>wit_cchunk_domain () ch. \<forall>m.
          wit_cchunk_read_result () ch k = Some m
            \<longrightarrow> m = Src b0_w H_w (wit_cchunk_read_coordinate () ch) k"
  proof
    fix ch :: wit_cchunk assume ch_in: "ch \<in> wit_cchunks ()"
    hence ch_cases: "ch = WCh1 \<or> ch = WCh2"
      using wm_chunks_eq by simp
    show "\<forall>k\<in>wit_cchunk_domain () ch. \<forall>m.
            wit_cchunk_read_result () ch k = Some m
              \<longrightarrow> m = Src b0_w H_w (wit_cchunk_read_coordinate () ch) k"
    proof (cases "ch = WCh1")
      case True
      show ?thesis
        using True wm_dom_1 wm_crr_1_0
              wm_rcoord_1 Src_b0_w_H_w_c0_0
        by auto
    next
      case False
      hence "ch = WCh2" using ch_cases by simp
      show ?thesis
        using \<open>ch = WCh2\<close> wm_dom_2 wm_crr_2_1
              wm_rcoord_2 Src_b0_w_H_w_c2_w_1
        by auto
    qed
  qed
next
  \<comment> \<open>WF6 row-absence.\<close>
  show "\<forall>ch\<in>wit_cchunks (). \<forall>k\<in>wit_cchunk_domain () ch.
          wit_cchunk_read_result () ch k = Some None
            \<longrightarrow> wit_model.row_absence_meaningful b0_w H_w () ch k"
  proof (intro ballI impI)
    fix ch :: wit_cchunk and k :: nat
    assume ch_in: "ch \<in> wit_cchunks ()"
       and k_in: "k \<in> wit_cchunk_domain () ch"
       and crr: "wit_cchunk_read_result () ch k = Some None"
    from ch_in wm_chunks_eq
      have ch_cases: "ch = WCh1 \<or> ch = WCh2" by simp
    show "wit_model.row_absence_meaningful b0_w H_w () ch k"
    proof (cases "ch = WCh1")
      case True
      with k_in wm_dom_1 have k0: "k = 0" by simp
      show ?thesis
        unfolding wit_model.row_absence_meaningful_def
        using True k0 wm_dom_1 wm_rcoord_1 Src_b0_w_H_w_c0_0
        by simp
    next
      case False
      with ch_cases have ch_2: "ch = WCh2" by simp
      with k_in wm_dom_2 have k1: "k = 1" by simp
      show ?thesis
        unfolding wit_model.row_absence_meaningful_def
        using ch_2 k1 wm_dom_2 wm_rcoord_2 Src_b0_w_H_w_c2_w_1
        by simp
    qed
  qed
next
  \<comment> \<open>WF7 forward (clean-prefix CDC coherence).\<close>
  show "\<forall>p \<in> set (wit_ccdc_events_of ()).
          key_of (hist_event p) \<in> wit_cscope ()
          \<and> src_le (hist_coord p) (wit_cfrontier ())
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (wit_model.clean_prefix_of ())"
  proof (intro ballI impI)
    fix p :: "src_coord \<times> (nat, nat) source_event"
    assume p_in: "p \<in> set (wit_ccdc_events_of ())"
    hence p_cases: "p = (c1_w, Insert 0 42) \<or> p = (c2_w, Delete 1)"
      using wm_cdc by simp
    show "Cdc (hist_coord p) (hist_event p)
            \<in> set (wit_model.clean_prefix_of ())"
      using p_cases wm_clean_prefix by fastforce
  qed
next
  \<comment> \<open>WF7 reverse (clean-prefix CDC coherence).\<close>
  show "\<forall>e c. Cdc c e \<in> set (wit_model.clean_prefix_of ())
                 \<and> key_of e \<in> wit_cscope ()
                 \<and> src_le c (wit_cfrontier ())
                 \<longrightarrow> (c, e) \<in> set (wit_ccdc_events_of ())"
  proof (intro allI impI)
    fix e :: "(nat, nat) source_event" and c :: src_coord
    assume "Cdc c e \<in> set (wit_model.clean_prefix_of ())
              \<and> key_of e \<in> wit_cscope ()
              \<and> src_le c (wit_cfrontier ())"
    hence cdc_in: "Cdc c e \<in> set (wit_model.clean_prefix_of ())" by simp
    have list_eq: "Cdc c e \<in> set [Refresh (0::nat) (None::nat option) c0,
                                    Cdc c1_w (Insert 0 42),
                                    Cdc c2_w (Delete 1),
                                    Refresh 1 None c2_w]"
      using cdc_in wm_clean_prefix by simp
    hence "(c = c1_w \<and> e = Insert 0 42)
            \<or> (c = c2_w \<and> e = Delete 1)"
      by auto
    thus "(c, e) \<in> set (wit_ccdc_events_of ())"
      using wm_cdc by auto
  qed
qed


subsection \<open>Constructed positive witness\<close>

text \<open>
  The Layer 1 wellformed-run non-vacuity statement, established over the
  constructed model with no run/chunk axiom: a wellformed run exists, and the
  eight side conjuncts pin down why the witness is minimum-viable rather than
  degenerate --- non-empty base state and scope, at least two chunks, a chunk
  read at the base coordinate, a CDC event strictly past some chunk's read
  coordinate, a delete or an absence @{const Refresh}, and a replay that is
  non-empty and differs from the base state on the scope.
\<close>

theorem wellformed_run_positive_witness_constructed:
  "\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: unit) (H :: (nat, nat) src_history).
        wit_model.wellformed_dblog_run b0 R H
      \<and> b0 \<noteq> Map.empty
      \<and> wit_cscope R \<noteq> {}
      \<and> 2 \<le> card (wit_cchunks R)
      \<and> (\<exists> ch \<in> wit_cchunks R. wit_cchunk_read_coordinate R ch = c0)
      \<and> (\<exists> ch \<in> wit_cchunks R. \<exists> c e.
              Cdc c e \<in> set (wit_model.clean_prefix_of R)
            \<and> src_lt (wit_cchunk_read_coordinate R ch) c)
      \<and> ( (\<exists> c k. Cdc c (Delete k) \<in> set (wit_model.clean_prefix_of R))
        \<or> (\<exists> k c. Refresh k None c \<in> set (wit_model.clean_prefix_of R)) )
      \<and> restrict (Apply (wit_model.clean_prefix_of R)) (wit_cscope R)
          \<noteq> Map.empty
      \<and> restrict (Apply (wit_model.clean_prefix_of R)) (wit_cscope R)
          \<noteq> restrict b0 (wit_cscope R)"
proof (intro exI[where x = b0_w] exI[where x = "()"] exI[where x = H_w] conjI)
  show "wit_model.wellformed_dblog_run b0_w () H_w"
    by (rule wit_model_wellformed)
next
  show "b0_w \<noteq> Map.empty"
  proof -
    have "b0_w 7 \<noteq> Map.empty 7" by (simp add: b0_w_def)
    thus ?thesis by metis
  qed
next
  show "wit_cscope () \<noteq> {}" using wm_scope by simp
next
  show "2 \<le> card (wit_cchunks ())" using wm_chunks wm_distinct by simp
next
  show "\<exists> ch \<in> wit_cchunks (). wit_cchunk_read_coordinate () ch = c0"
    using wm_chunks wm_rcoord_1 by blast
next
  show "\<exists> ch \<in> wit_cchunks (). \<exists> c e.
          Cdc c e \<in> set (wit_model.clean_prefix_of ())
        \<and> src_lt (wit_cchunk_read_coordinate () ch) c"
    using wm_clean_prefix wm_rcoord_1 c0_lt_c1_w wm_chunks by fastforce
next
  show "(\<exists> c k. Cdc c (Delete k) \<in> set (wit_model.clean_prefix_of ()))
          \<or> (\<exists> k c. Refresh k None c \<in> set (wit_model.clean_prefix_of ()))"
    using wm_clean_prefix by fastforce
next
  show "restrict (Apply (wit_model.clean_prefix_of ())) (wit_cscope ())
          \<noteq> Map.empty"
  proof
    assume H: "restrict (Apply (wit_model.clean_prefix_of ())) (wit_cscope ())
                = Map.empty"
    hence "restrict (Apply (wit_model.clean_prefix_of ())) (wit_cscope ()) 0
             = Map.empty 0" by simp
    hence "(if (0::nat) \<in> wit_cscope ()
              then Apply (wit_model.clean_prefix_of ()) 0 else None) = None"
      unfolding restrict_def by simp
    moreover have "(0::nat) \<in> wit_cscope ()" using wm_scope by simp
    ultimately have "Apply (wit_model.clean_prefix_of ()) 0 = None" by simp
    thus False using wm_apply by simp
  qed
next
  show "restrict (Apply (wit_model.clean_prefix_of ())) (wit_cscope ())
          \<noteq> restrict b0_w (wit_cscope ())"
  proof
    assume H: "restrict (Apply (wit_model.clean_prefix_of ())) (wit_cscope ())
                = restrict b0_w (wit_cscope ())"
    hence "restrict (Apply (wit_model.clean_prefix_of ())) (wit_cscope ()) 0
             = restrict b0_w (wit_cscope ()) 0" by simp
    moreover have "(0::nat) \<in> wit_cscope ()" using wm_scope by simp
    ultimately have "Apply (wit_model.clean_prefix_of ()) 0 = b0_w 0"
      unfolding restrict_def by simp
    thus False using wm_apply unfolding b0_w_def by simp
  qed
qed

text \<open>
  A model exists for the @{locale dblog_run_substrate} interface that realizes
  the minimum-viable wellformed-run witness, so the Layer 1 positive-witness
  result holds by construction --- consistency-by-construction, resting on no
  axiom.
\<close>

end
