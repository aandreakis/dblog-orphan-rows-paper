(*  Title:   Layer01_Witness_Topics_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Witness_Topics_Inst
  imports Layer01_Witness_Topics_Model DBLog_Run_Substrate_Layer2
begin

section \<open>Constructed interpretations for the Topic 1 and Topic 2 witnesses\<close>

text \<open>
  Constructs the Topic 1 (clean-prefix-carrier) and Topic 2 (multi-chunk
  partition) positive witnesses as explicit interpretations of the Layer 1
  locale @{locale dblog_run_substrate} at the concrete models of
  @{theory DBLog_Virtual_Cuts.Layer01_Witness_Topics_Model}
  (the @{typ unit} run carriers, the @{type t1_cchunk} / @{type t2_cchunk} chunk
  datatypes, and the definitional accessors), establishing both witness facts
  with no axioms.

  Method (the @{text Layer01_Witnesses_Inst} pattern,
  applied to both topics). For each topic: instantiate
  @{locale dblog_run_substrate} at the model carrier (the two inherited
  @{text chunks_list} obligations discharge by @{method simp}, no axiom); read
  off the model's definitional accessor values pointwise as the
  @{text "t1m_\<dots>"} / @{text "t2m_\<dots>"} lemmas (the conjuncts of
  @{thm [source] t1_model_accessor_values} /
  @{thm [source] t2_model_accessor_values}); and prove the
  determinate clean-prefix shape, the wellformedness, and the topic's
  positive-witness statement from those rewrite facts plus the
  carrier-independent topic data of
  @{theory DBLog_Virtual_Cuts.Layer01_Witness_Topics_Core} (the base states,
  the source histories, and the @{const Src} / @{const latest_src_event}
  computation lemmas). As in @{text Layer01_Witnesses_Inst} the
  concrete-@{typ nat}
  wellformedness is proved at the interpretation in the global context (the
  locale type parameter @{typ "'k"} is rigid inside the locale context), not as
  an in-locale lemma.

  The Topic 1 source coordinate @{const ct1} is a @{const coord_of_nat}
  definition from @{theory Dual_Write_Layer0.Source_Coordinates}, with its
  order facts proved there; Topic 2 uses only the base coordinate @{const c0}.
\<close>


section \<open>Topic 1: constructed interpretation\<close>

text \<open>
  Instantiate @{locale dblog_run_substrate} at the Topic 1 model carrier
  (@{typ unit} run, the single-constructor @{type t1_cchunk}); the two
  @{text chunks_list} obligations reduce to @{term "set [T1Ch] = {T1Ch}"} and
  @{term "distinct [T1Ch]"}, discharged by @{method simp} --- no axiom.
\<close>

global_interpretation t1_model: dblog_run_substrate
  t1_cscope
  t1_cfrontier
  t1_cchunks
  t1_csrc_history_of
  t1_cchunk_read_result
  t1_ccdc_events_of
  t1_cchunks_list
  t1_cchunk_domain
  t1_cresponsible_chunk
  t1_cchunk_lower_watermark
  t1_cchunk_upper_watermark
  t1_cchunk_read_coordinate
  by unfold_locales (simp_all add: t1_cchunks_def t1_cchunks_list_def)

subsection \<open>Topic 1 model accessor-value lemmas\<close>

lemma t1m_scope: "t1_cscope () = {1}" by (simp add: t1_cscope_def)
lemma t1m_frontier: "t1_cfrontier () = ct1" by (simp add: t1_cfrontier_def)
lemma t1m_chunks: "t1_cchunks () = {T1Ch}" by (simp add: t1_cchunks_def)
lemma t1m_dom: "t1_cchunk_domain () T1Ch = {1}"
  by (simp add: t1_cchunk_domain_def)
lemma t1m_resp_1: "t1_cresponsible_chunk () 1 = Some T1Ch"
  by (simp add: t1_cresponsible_chunk_def)
lemma t1m_resp_else: "k \<noteq> 1 \<Longrightarrow> t1_cresponsible_chunk () k = None"
  by (simp add: t1_cresponsible_chunk_def)
lemma t1m_rcoord: "t1_cchunk_read_coordinate () T1Ch = c0"
  by (simp add: t1_cchunk_read_coordinate_def)
lemma t1m_lwm: "t1_cchunk_lower_watermark () T1Ch = c0"
  by (simp add: t1_cchunk_lower_watermark_def)
lemma t1m_uwm: "t1_cchunk_upper_watermark () T1Ch = c0"
  by (simp add: t1_cchunk_upper_watermark_def)
lemma t1m_src_history: "t1_csrc_history_of () = H_t1"
  by (simp add: t1_csrc_history_of_def)
lemma t1m_crr_1: "t1_cchunk_read_result () T1Ch 1 = Some (Some 5)"
  by (simp add: t1_cchunk_read_result_def)
lemma t1m_cdc: "t1_ccdc_events_of () = [(ct1, Update 1 7)]"
  by (simp add: t1_ccdc_events_of_def H_t1_def)
lemma t1m_chunks_list: "t1_cchunks_list () = [T1Ch]"
  by (simp add: t1_cchunks_list_def)

lemma t1m_chunks_eq:
  "(ch \<in> t1_cchunks ()) \<longleftrightarrow> (ch = T1Ch)"
  using t1m_chunks by simp

subsection \<open>Topic 1 determinate clean prefix and Apply over the model\<close>

lemma t1m_clean_prefix:
  "t1_model.clean_prefix_of ()
     = [ Refresh (1::nat) (Some (5::nat)) c0,
         Cdc ct1 (Update 1 7) ]"
proof -
  have d1: "sorted_list_of_set {Suc 0} = [Suc 0]" by simp
  show ?thesis
    unfolding t1_model.clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: t1m_chunks_list t1m_dom t1m_rcoord
                  t1m_crr_1[unfolded One_nat_def]
                  t1m_cdc t1m_scope t1m_frontier d1 One_nat_def
                  List.map_filter_simps sort_key_def
                  c0_le_ct1[unfolded src_le_eq_less_eq]
                  not_src_le_ct1_c0[unfolded src_le_eq_less_eq])
qed

lemma t1m_apply:
  "Apply (t1_model.clean_prefix_of ())
     = (\<lambda>k. if k = (1::nat) then Some (7::nat) else None)"
proof -
  have "Apply (t1_model.clean_prefix_of ())
          = foldl apply_step (\<lambda>_. None)
              [ Refresh (1::nat) (Some (5::nat)) c0,
                Cdc ct1 (Update 1 7) ]"
    unfolding Apply_def t1m_clean_prefix by (rule refl)
  also have "\<dots> = (\<lambda>k. if k = (1::nat) then Some (7::nat) else None)"
    by (auto simp: fun_eq_iff fun_upd_def)
  finally show ?thesis .
qed

subsection \<open>Topic 1 constructed wellformed-run fact\<close>

theorem t1_model_wellformed:
  "t1_model.wellformed_dblog_run b0_t1 () H_t1"
  unfolding t1_model.wellformed_dblog_run_def
proof (intro conjI)
  show "t1_csrc_history_of () = H_t1" by (rule t1m_src_history)
next
  show "wellformed_src_history H_t1" by (rule wf_h_t1)
next
  show "\<forall>k\<in>t1_cscope (). \<exists>!ch. ch \<in> t1_cchunks () \<and> k \<in> t1_cchunk_domain () ch"
  proof
    fix k :: nat assume "k \<in> t1_cscope ()"
    hence k1: "k = 1" using t1m_scope by simp
    show "\<exists>!ch. ch \<in> t1_cchunks () \<and> k \<in> t1_cchunk_domain () ch"
    proof
      show "T1Ch \<in> t1_cchunks () \<and> k \<in> t1_cchunk_domain () T1Ch"
        using t1m_chunks t1m_dom k1 by simp
    next
      fix ch assume "ch \<in> t1_cchunks () \<and> k \<in> t1_cchunk_domain () ch"
      thus "ch = T1Ch" using t1m_chunks_eq by blast
    qed
  qed
next
  show "\<forall>ch1\<in>t1_cchunks (). \<forall>ch2\<in>t1_cchunks ().
          ch1 \<noteq> ch2 \<longrightarrow> t1_cchunk_domain () ch1 \<inter> t1_cchunk_domain () ch2 = {}"
    using t1m_chunks_eq by auto
next
  show "t1_model.canonical_chunk_ownership_domain () = t1_cscope ()"
    unfolding t1_model.canonical_chunk_ownership_domain_def
    using t1m_chunks t1m_dom t1m_scope by auto
next
  show "\<forall>k\<in>t1_cscope (). \<forall>ch.
          t1_cresponsible_chunk () k = Some ch
            \<longleftrightarrow> ch \<in> t1_cchunks () \<and> k \<in> t1_cchunk_domain () ch"
  proof (intro ballI allI)
    fix k :: nat and ch :: t1_cchunk
    assume "k \<in> t1_cscope ()"
    hence k1: "k = 1" using t1m_scope by simp
    show "t1_cresponsible_chunk () k = Some ch
            \<longleftrightarrow> ch \<in> t1_cchunks () \<and> k \<in> t1_cchunk_domain () ch"
    proof
      assume "t1_cresponsible_chunk () k = Some ch"
      with t1m_resp_1 k1 have "ch = T1Ch" by simp
      thus "ch \<in> t1_cchunks () \<and> k \<in> t1_cchunk_domain () ch"
        using t1m_chunks t1m_dom k1 by simp
    next
      assume A: "ch \<in> t1_cchunks () \<and> k \<in> t1_cchunk_domain () ch"
      have "ch = T1Ch" using A t1m_chunks_eq by blast
      with t1m_resp_1 k1 show "t1_cresponsible_chunk () k = Some ch" by simp
    qed
  qed
next
  show "\<forall>k. k \<notin> t1_cscope () \<longrightarrow> t1_cresponsible_chunk () k = None"
    using t1m_scope t1m_resp_else by auto
next
  show "finite (t1_cscope ())" using t1m_scope by simp
next
  show "\<forall>ch\<in>t1_cchunks (). finite (t1_cchunk_domain () ch)"
    using t1m_chunks_eq t1m_dom by auto
next
  show "\<forall>ch\<in>t1_cchunks (). t1_cchunk_domain () ch \<noteq> {}"
    using t1m_chunks_eq t1m_dom by auto
next
  show "\<forall>k\<in>t1_cscope (). t1_model.covers_ordinary_cdc () k (t1_cfrontier ())"
  proof
    fix k :: nat assume "k \<in> t1_cscope ()"
    hence k1: "k = 1" using t1m_scope by simp
    show "t1_model.covers_ordinary_cdc () k (t1_cfrontier ())"
      unfolding t1_model.covers_ordinary_cdc_def
    proof (intro exI[where x = T1Ch] conjI allI impI)
      show "t1_cresponsible_chunk () k = Some T1Ch"
        using t1m_resp_1 k1 by simp
    next
      fix i assume i_lt: "i < length (t1_csrc_history_of ())"
        and chunk_lt: "src_lt (t1_cchunk_read_coordinate () T1Ch)
                              (hist_coord (t1_csrc_history_of () ! i))"
        and to_f: "src_le (hist_coord (t1_csrc_history_of () ! i))
                          (t1_cfrontier ())"
        and key_eq: "key_of (hist_event (t1_csrc_history_of () ! i)) = k"
      have i0: "i = 0"
        using i_lt t1m_src_history length_H_t1 by simp
      show "t1_csrc_history_of () ! i \<in> set (t1_ccdc_events_of ())"
        using i0 t1m_src_history t1m_cdc H_t1_nth_0
        by (simp add: H_t1_def)
    qed
  qed
next
  show "\<forall>p\<in>set (t1_ccdc_events_of ()).
          key_of (hist_event p) \<in> t1_cscope ()
          \<and> src_le (hist_coord p) (t1_cfrontier ())
          \<longrightarrow> p \<in> set (t1_csrc_history_of ())"
    using t1m_cdc t1m_src_history set_H_t1 H_t1_def by auto
next
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> t1_cscope ()
                                   \<and> src_le (hist_coord p) (t1_cfrontier ()));
                 cdc_in_slice  = filter in_slice (t1_ccdc_events_of ());
                 hist_in_slice = filter in_slice (t1_csrc_history_of ())
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    have eq: "t1_ccdc_events_of () = t1_csrc_history_of ()"
      using t1m_cdc t1m_src_history H_t1_def by simp
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> t1_cscope ()
                                \<and> src_le (hist_coord p) (t1_cfrontier ()));
              cdc_in_slice  = filter in_slice (t1_ccdc_events_of ());
              hist_in_slice = filter in_slice (t1_csrc_history_of ())
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      using eq by (simp add: Let_def)
  qed
next
  show "\<forall>k\<in>t1_cscope (). \<forall>ch c.
          t1_cresponsible_chunk () k = Some ch
          \<and> src_lt (t1_cchunk_read_coordinate () ch) c
          \<and> src_le c (t1_cfrontier ())
          \<longrightarrow>
            mset (source_key_coord_slice k c (t1_ccdc_events_of ()))
            = mset (source_key_coord_slice k c (t1_csrc_history_of ()))"
  proof (intro ballI allI impI)
    fix k :: nat and ch :: t1_cchunk and c :: src_coord
    have eq: "t1_ccdc_events_of () = t1_csrc_history_of ()"
      using t1m_cdc t1m_src_history H_t1_def by simp
    show "mset (source_key_coord_slice k c (t1_ccdc_events_of ()))
          = mset (source_key_coord_slice k c (t1_csrc_history_of ()))"
      using eq by simp
  qed
next
  show "\<forall>ch\<in>t1_cchunks ().
          src_le (t1_cchunk_lower_watermark () ch) (t1_cchunk_read_coordinate () ch)
        \<and> src_le (t1_cchunk_read_coordinate () ch) (t1_cchunk_upper_watermark () ch)
        \<and> (\<forall>k\<in>t1_cchunk_domain () ch. \<exists>m. t1_cchunk_read_result () ch k = Some m)
        \<and> (\<forall>k\<in>t1_cchunk_domain () ch. \<forall>m.
             t1_cchunk_read_result () ch k = Some m
               \<longleftrightarrow> Refresh k m (t1_cchunk_read_coordinate () ch)
                    \<in> set (t1_model.clean_prefix_of ()))"
  proof
    fix ch :: t1_cchunk assume "ch \<in> t1_cchunks ()"
    hence ch_eq: "ch = T1Ch" using t1m_chunks_eq by simp
    show "src_le (t1_cchunk_lower_watermark () ch) (t1_cchunk_read_coordinate () ch)
        \<and> src_le (t1_cchunk_read_coordinate () ch) (t1_cchunk_upper_watermark () ch)
        \<and> (\<forall>k\<in>t1_cchunk_domain () ch. \<exists>m. t1_cchunk_read_result () ch k = Some m)
        \<and> (\<forall>k\<in>t1_cchunk_domain () ch. \<forall>m.
             t1_cchunk_read_result () ch k = Some m
               \<longleftrightarrow> Refresh k m (t1_cchunk_read_coordinate () ch)
                    \<in> set (t1_model.clean_prefix_of ()))"
      using ch_eq t1m_lwm t1m_uwm t1m_rcoord src_le_refl
            t1m_dom t1m_crr_1 t1m_clean_prefix
      by auto
  qed
next
  show "\<forall>ch\<in>t1_cchunks ().
          src_le (t1_cchunk_read_coordinate () ch) (t1_cfrontier ())"
    using t1m_chunks_eq t1m_rcoord t1m_frontier c0_le_ct1 by auto
next
  show "\<forall>ch\<in>t1_cchunks (). \<forall>k\<in>t1_cchunk_domain () ch. \<forall>m.
          t1_cchunk_read_result () ch k = Some m
            \<longrightarrow> m = Src b0_t1 H_t1 (t1_cchunk_read_coordinate () ch) k"
  proof
    fix ch :: t1_cchunk assume "ch \<in> t1_cchunks ()"
    hence ch_eq: "ch = T1Ch" using t1m_chunks_eq by simp
    show "\<forall>k\<in>t1_cchunk_domain () ch. \<forall>m.
            t1_cchunk_read_result () ch k = Some m
              \<longrightarrow> m = Src b0_t1 H_t1 (t1_cchunk_read_coordinate () ch) k"
      using ch_eq t1m_dom t1m_crr_1 t1m_rcoord
            Src_b0_t1_H_t1_c0_1
      by auto
  qed
next
  show "\<forall>ch\<in>t1_cchunks (). \<forall>k\<in>t1_cchunk_domain () ch.
          t1_cchunk_read_result () ch k = Some None
            \<longrightarrow> t1_model.row_absence_meaningful b0_t1 H_t1 () ch k"
  proof (intro ballI impI)
    fix ch :: t1_cchunk and k :: nat
    assume ch_in: "ch \<in> t1_cchunks ()"
       and k_in: "k \<in> t1_cchunk_domain () ch"
       and crr: "t1_cchunk_read_result () ch k = Some None"
    from ch_in t1m_chunks_eq have ch_eq: "ch = T1Ch" by simp
    with k_in t1m_dom have k1: "k = 1" by simp
    from ch_eq k1 crr t1m_crr_1 have False by simp
    thus "t1_model.row_absence_meaningful b0_t1 H_t1 () ch k" ..
  qed
next
  show "\<forall>p \<in> set (t1_ccdc_events_of ()).
          key_of (hist_event p) \<in> t1_cscope ()
          \<and> src_le (hist_coord p) (t1_cfrontier ())
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (t1_model.clean_prefix_of ())"
  proof (intro ballI impI)
    fix p :: "src_coord \<times> (nat, nat) source_event"
    assume p_in: "p \<in> set (t1_ccdc_events_of ())"
    hence "p = (ct1, Update 1 7)" using t1m_cdc by simp
    thus "Cdc (hist_coord p) (hist_event p)
            \<in> set (t1_model.clean_prefix_of ())"
      using t1m_clean_prefix by simp
  qed
next
  show "\<forall>e c. Cdc c e \<in> set (t1_model.clean_prefix_of ())
                 \<and> key_of e \<in> t1_cscope ()
                 \<and> src_le c (t1_cfrontier ())
                 \<longrightarrow> (c, e) \<in> set (t1_ccdc_events_of ())"
  proof (intro allI impI)
    fix e :: "(nat, nat) source_event" and c :: src_coord
    assume "Cdc c e \<in> set (t1_model.clean_prefix_of ())
              \<and> key_of e \<in> t1_cscope ()
              \<and> src_le c (t1_cfrontier ())"
    hence cdc_in: "Cdc c e \<in> set (t1_model.clean_prefix_of ())" by simp
    have "Cdc c e \<in> set [Refresh (1::nat) (Some (5::nat)) c0,
                          Cdc ct1 (Update 1 7)]"
      using cdc_in t1m_clean_prefix by simp
    hence "c = ct1 \<and> e = Update 1 7" by auto
    thus "(c, e) \<in> set (t1_ccdc_events_of ())"
      using t1m_cdc by simp
  qed
qed

subsection \<open>Topic 1 constructed replay-equality conclusion (non-trivial)\<close>

lemma t1_model_virtual_cut_holds:
  "restrict (Apply (t1_model.clean_prefix_of ())) (t1_cscope ())
     = restrict (Src b0_t1 H_t1 (t1_cfrontier ())) (t1_cscope ())"
proof
  fix k :: nat
  show "restrict (Apply (t1_model.clean_prefix_of ())) (t1_cscope ()) k
          = restrict (Src b0_t1 H_t1 (t1_cfrontier ())) (t1_cscope ()) k"
  proof (cases "k \<in> t1_cscope ()")
    case True
    hence k1: "k = 1" using t1m_scope by simp
    then show ?thesis
      unfolding restrict_def
      using \<open>k \<in> t1_cscope ()\<close>
            t1m_apply Src_b0_t1_H_t1_ct1_1 t1m_frontier
      by simp
  next
    case False
    show ?thesis
      unfolding restrict_def using False by simp
  qed
qed

lemma t1_model_virtual_cut_non_trivial:
  "restrict (Apply (t1_model.clean_prefix_of ())) (t1_cscope ())
     \<noteq> restrict b0_t1 (t1_cscope ())"
proof
  assume H: "restrict (Apply (t1_model.clean_prefix_of ())) (t1_cscope ())
              = restrict b0_t1 (t1_cscope ())"
  hence "restrict (Apply (t1_model.clean_prefix_of ())) (t1_cscope ()) 1
           = restrict b0_t1 (t1_cscope ()) 1" by simp
  moreover have "(1::nat) \<in> t1_cscope ()" using t1m_scope by simp
  ultimately have "Apply (t1_model.clean_prefix_of ()) 1 = b0_t1 1"
    unfolding restrict_def by simp
  thus False
    using t1m_apply unfolding b0_t1_def by simp
qed

subsection \<open>Topic 1 constructed positive witness\<close>

theorem topic1_positive_witness_constructed:
  "\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: unit) (H :: (nat, nat) src_history).
        t1_model.wellformed_dblog_run b0 R H
      \<and> t1_cchunks R \<noteq> {}
      \<and> (\<exists> c e. Cdc c e \<in> set (t1_model.clean_prefix_of R))
      \<and> restrict (Apply (t1_model.clean_prefix_of R)) (t1_cscope R)
          = restrict (Src b0 H (t1_cfrontier R)) (t1_cscope R)
      \<and> restrict (Apply (t1_model.clean_prefix_of R)) (t1_cscope R)
          \<noteq> restrict b0 (t1_cscope R)"
proof (intro exI[where x = b0_t1] exI[where x = "()"] exI[where x = H_t1] conjI)
  show "t1_model.wellformed_dblog_run b0_t1 () H_t1"
    by (rule t1_model_wellformed)
next
  show "t1_cchunks () \<noteq> {}" using t1m_chunks by simp
next
  show "\<exists> c e. Cdc c e \<in> set (t1_model.clean_prefix_of ())"
    using t1m_clean_prefix by auto
next
  show "restrict (Apply (t1_model.clean_prefix_of ())) (t1_cscope ())
          = restrict (Src b0_t1 H_t1 (t1_cfrontier ())) (t1_cscope ())"
    by (rule t1_model_virtual_cut_holds)
next
  show "restrict (Apply (t1_model.clean_prefix_of ())) (t1_cscope ())
          \<noteq> restrict b0_t1 (t1_cscope ())"
    by (rule t1_model_virtual_cut_non_trivial)
qed


section \<open>Topic 2: constructed interpretation\<close>

text \<open>
  Instantiate @{locale dblog_run_substrate} at the Topic 2 model carrier
  (@{typ unit} run, the two-constructor @{type t2_cchunk}); the two
  @{text chunks_list} obligations reduce to
  @{term "set [T2ChA, T2ChB] = {T2ChA, T2ChB}"} and
  @{term "distinct [T2ChA, T2ChB]"}, discharged by @{method simp} --- no axiom.
\<close>

global_interpretation t2_model: dblog_run_substrate
  t2_cscope
  t2_cfrontier
  t2_cchunks
  t2_csrc_history_of
  t2_cchunk_read_result
  t2_ccdc_events_of
  t2_cchunks_list
  t2_cchunk_domain
  t2_cresponsible_chunk
  t2_cchunk_lower_watermark
  t2_cchunk_upper_watermark
  t2_cchunk_read_coordinate
  by unfold_locales (simp_all add: t2_cchunks_def t2_cchunks_list_def)

subsection \<open>Topic 2 model accessor-value lemmas\<close>

lemma t2m_distinct: "T2ChA \<noteq> T2ChB" by simp
lemma t2m_scope: "t2_cscope () = {10, 20}" by (simp add: t2_cscope_def)
lemma t2m_frontier: "t2_cfrontier () = c0" by (simp add: t2_cfrontier_def)
lemma t2m_chunks: "t2_cchunks () = {T2ChA, T2ChB}" by (simp add: t2_cchunks_def)
lemma t2m_dom_A: "t2_cchunk_domain () T2ChA = {10}"
  by (simp add: t2_cchunk_domain_def)
lemma t2m_dom_B: "t2_cchunk_domain () T2ChB = {20}"
  by (simp add: t2_cchunk_domain_def)
lemma t2m_resp_10: "t2_cresponsible_chunk () 10 = Some T2ChA"
  by (simp add: t2_cresponsible_chunk_def)
lemma t2m_resp_20: "t2_cresponsible_chunk () 20 = Some T2ChB"
  by (simp add: t2_cresponsible_chunk_def)
lemma t2m_resp_else:
  "k \<noteq> 10 \<Longrightarrow> k \<noteq> 20 \<Longrightarrow> t2_cresponsible_chunk () k = None"
  by (simp add: t2_cresponsible_chunk_def)
lemma t2m_rcoord_A: "t2_cchunk_read_coordinate () T2ChA = c0"
  by (simp add: t2_cchunk_read_coordinate_def)
lemma t2m_rcoord_B: "t2_cchunk_read_coordinate () T2ChB = c0"
  by (simp add: t2_cchunk_read_coordinate_def)
lemma t2m_lwm_A: "t2_cchunk_lower_watermark () T2ChA = c0"
  by (simp add: t2_cchunk_lower_watermark_def)
lemma t2m_uwm_A: "t2_cchunk_upper_watermark () T2ChA = c0"
  by (simp add: t2_cchunk_upper_watermark_def)
lemma t2m_lwm_B: "t2_cchunk_lower_watermark () T2ChB = c0"
  by (simp add: t2_cchunk_lower_watermark_def)
lemma t2m_uwm_B: "t2_cchunk_upper_watermark () T2ChB = c0"
  by (simp add: t2_cchunk_upper_watermark_def)
lemma t2m_src_history: "t2_csrc_history_of () = H_t2"
  by (simp add: t2_csrc_history_of_def)
lemma t2m_crr_A_10: "t2_cchunk_read_result () T2ChA 10 = Some (Some 100)"
  by (simp add: t2_cchunk_read_result_def)
lemma t2m_crr_B_20: "t2_cchunk_read_result () T2ChB 20 = Some (Some 200)"
  by (simp add: t2_cchunk_read_result_def)
lemma t2m_cdc: "t2_ccdc_events_of () = []"
  by (simp add: t2_ccdc_events_of_def H_t2_def)
lemma t2m_chunks_list: "t2_cchunks_list () = [T2ChA, T2ChB]"
  by (simp add: t2_cchunks_list_def)

lemma t2m_chunks_eq:
  "(ch \<in> t2_cchunks ()) \<longleftrightarrow> (ch = T2ChA \<or> ch = T2ChB)"
  using t2m_chunks by simp

subsection \<open>Topic 2 determinate clean prefix over the model\<close>

lemma t2m_clean_prefix:
  "t2_model.clean_prefix_of ()
     = [ Refresh (10::nat) (Some (100::nat)) c0,
         Refresh 20 (Some 200) c0 ]"
proof -
  have dA: "sorted_list_of_set {10::nat} = [10]" by simp
  have dB: "sorted_list_of_set {20::nat} = [20]" by simp
  show ?thesis
    unfolding t2_model.clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: t2m_chunks_list t2m_dom_A t2m_dom_B
                  t2m_rcoord_A t2m_rcoord_B
                  t2m_crr_A_10 t2m_crr_B_20
                  t2m_cdc t2m_scope t2m_frontier dA dB
                  List.map_filter_simps sort_key_def)
qed

subsection \<open>Topic 2 constructed wellformed-run fact\<close>

theorem t2_model_wellformed:
  "t2_model.wellformed_dblog_run b0_t2 () H_t2"
  unfolding t2_model.wellformed_dblog_run_def
proof (intro conjI)
  show "t2_csrc_history_of () = H_t2" by (rule t2m_src_history)
next
  show "wellformed_src_history H_t2" by (rule wf_h_t2)
next
  show "\<forall>k\<in>t2_cscope (). \<exists>!ch. ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch"
  proof
    fix k :: nat assume "k \<in> t2_cscope ()"
    hence k_cases: "k = 10 \<or> k = 20" using t2m_scope by simp
    show "\<exists>!ch. ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch"
    proof (cases "k = 10")
      case True
      have "T2ChA \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () T2ChA"
        using t2m_chunks t2m_dom_A True by simp
      moreover have "\<And>ch. ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch \<Longrightarrow> ch = T2ChA"
        using t2m_chunks_eq t2m_dom_A t2m_dom_B True by auto
      ultimately show ?thesis by blast
    next
      case False
      hence k20: "k = 20" using k_cases by simp
      have "T2ChB \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () T2ChB"
        using t2m_chunks t2m_dom_B k20 by simp
      moreover have "\<And>ch. ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch \<Longrightarrow> ch = T2ChB"
        using t2m_chunks_eq t2m_dom_A t2m_dom_B k20 by auto
      ultimately show ?thesis by blast
    qed
  qed
next
  show "\<forall>ch1\<in>t2_cchunks (). \<forall>ch2\<in>t2_cchunks ().
          ch1 \<noteq> ch2 \<longrightarrow> t2_cchunk_domain () ch1 \<inter> t2_cchunk_domain () ch2 = {}"
    using t2m_chunks_eq t2m_dom_A t2m_dom_B by auto
next
  show "t2_model.canonical_chunk_ownership_domain () = t2_cscope ()"
    unfolding t2_model.canonical_chunk_ownership_domain_def
    using t2m_chunks t2m_dom_A t2m_dom_B t2m_scope by auto
next
  show "\<forall>k\<in>t2_cscope (). \<forall>ch.
          t2_cresponsible_chunk () k = Some ch
            \<longleftrightarrow> ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch"
  proof (intro ballI allI)
    fix k :: nat and ch :: t2_cchunk
    assume "k \<in> t2_cscope ()"
    hence k_cases: "k = 10 \<or> k = 20" using t2m_scope by simp
    show "t2_cresponsible_chunk () k = Some ch
            \<longleftrightarrow> ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch"
    proof (cases "k = 10")
      case True
      then have rc: "t2_cresponsible_chunk () k = Some T2ChA"
        using t2m_resp_10 by simp
      show ?thesis
      proof
        assume "t2_cresponsible_chunk () k = Some ch"
        with rc have "ch = T2ChA" by simp
        thus "ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch"
          using t2m_chunks t2m_dom_A True by simp
      next
        assume A: "ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch"
        have "ch = T2ChA"
          using A t2m_chunks_eq t2m_dom_A t2m_dom_B True by auto
        with rc show "t2_cresponsible_chunk () k = Some ch" by simp
      qed
    next
      case False
      hence k20: "k = 20" using k_cases by simp
      then have rc: "t2_cresponsible_chunk () k = Some T2ChB"
        using t2m_resp_20 by simp
      show ?thesis
      proof
        assume "t2_cresponsible_chunk () k = Some ch"
        with rc have "ch = T2ChB" by simp
        thus "ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch"
          using t2m_chunks t2m_dom_B k20 by simp
      next
        assume A: "ch \<in> t2_cchunks () \<and> k \<in> t2_cchunk_domain () ch"
        have "ch = T2ChB"
          using A t2m_chunks_eq t2m_dom_A t2m_dom_B k20 by auto
        with rc show "t2_cresponsible_chunk () k = Some ch" by simp
      qed
    qed
  qed
next
  show "\<forall>k. k \<notin> t2_cscope () \<longrightarrow> t2_cresponsible_chunk () k = None"
    using t2m_scope t2m_resp_else by auto
next
  show "finite (t2_cscope ())" using t2m_scope by simp
next
  show "\<forall>ch\<in>t2_cchunks (). finite (t2_cchunk_domain () ch)"
    using t2m_chunks_eq t2m_dom_A t2m_dom_B by auto
next
  show "\<forall>ch\<in>t2_cchunks (). t2_cchunk_domain () ch \<noteq> {}"
    using t2m_chunks_eq t2m_dom_A t2m_dom_B by auto
next
  show "\<forall>k\<in>t2_cscope (). t2_model.covers_ordinary_cdc () k (t2_cfrontier ())"
  proof
    fix k :: nat assume "k \<in> t2_cscope ()"
    hence k_cases: "k = 10 \<or> k = 20" using t2m_scope by simp
    show "t2_model.covers_ordinary_cdc () k (t2_cfrontier ())"
    proof (cases "k = 10")
      case True
      show ?thesis
        unfolding t2_model.covers_ordinary_cdc_def
      proof (intro exI[where x = T2ChA] conjI allI impI)
        show "t2_cresponsible_chunk () k = Some T2ChA"
          using t2m_resp_10 True by simp
      next
        fix i assume "i < length (t2_csrc_history_of ())"
        with t2m_src_history length_H_t2 have False by simp
        thus "t2_csrc_history_of () ! i \<in> set (t2_ccdc_events_of ())" ..
      qed
    next
      case False
      hence k20: "k = 20" using k_cases by simp
      show ?thesis
        unfolding t2_model.covers_ordinary_cdc_def
      proof (intro exI[where x = T2ChB] conjI allI impI)
        show "t2_cresponsible_chunk () k = Some T2ChB"
          using t2m_resp_20 k20 by simp
      next
        fix i assume "i < length (t2_csrc_history_of ())"
        with t2m_src_history length_H_t2 have False by simp
        thus "t2_csrc_history_of () ! i \<in> set (t2_ccdc_events_of ())" ..
      qed
    qed
  qed
next
  show "\<forall>p\<in>set (t2_ccdc_events_of ()).
          key_of (hist_event p) \<in> t2_cscope ()
          \<and> src_le (hist_coord p) (t2_cfrontier ())
          \<longrightarrow> p \<in> set (t2_csrc_history_of ())"
    using t2m_cdc by simp
next
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> t2_cscope ()
                                   \<and> src_le (hist_coord p) (t2_cfrontier ()));
                 cdc_in_slice  = filter in_slice (t2_ccdc_events_of ());
                 hist_in_slice = filter in_slice (t2_csrc_history_of ())
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> t2_cscope ()
                                \<and> src_le (hist_coord p) (t2_cfrontier ()));
              cdc_in_slice  = filter in_slice (t2_ccdc_events_of ());
              hist_in_slice = filter in_slice (t2_csrc_history_of ())
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      using t2m_cdc by (simp add: Let_def)
  qed
next
  show "\<forall>k\<in>t2_cscope (). \<forall>ch c.
          t2_cresponsible_chunk () k = Some ch
          \<and> src_lt (t2_cchunk_read_coordinate () ch) c
          \<and> src_le c (t2_cfrontier ())
          \<longrightarrow>
            mset (source_key_coord_slice k c (t2_ccdc_events_of ()))
            = mset (source_key_coord_slice k c (t2_csrc_history_of ()))"
    using t2m_cdc t2m_src_history H_t2_def
    by (simp add: source_key_coord_slice_def)
next
  show "\<forall>ch\<in>t2_cchunks ().
          src_le (t2_cchunk_lower_watermark () ch) (t2_cchunk_read_coordinate () ch)
        \<and> src_le (t2_cchunk_read_coordinate () ch) (t2_cchunk_upper_watermark () ch)
        \<and> (\<forall>k\<in>t2_cchunk_domain () ch. \<exists>m. t2_cchunk_read_result () ch k = Some m)
        \<and> (\<forall>k\<in>t2_cchunk_domain () ch. \<forall>m.
             t2_cchunk_read_result () ch k = Some m
               \<longleftrightarrow> Refresh k m (t2_cchunk_read_coordinate () ch)
                    \<in> set (t2_model.clean_prefix_of ()))"
  proof
    fix ch :: t2_cchunk assume "ch \<in> t2_cchunks ()"
    hence ch_cases: "ch = T2ChA \<or> ch = T2ChB"
      using t2m_chunks_eq by simp
    show "src_le (t2_cchunk_lower_watermark () ch) (t2_cchunk_read_coordinate () ch)
        \<and> src_le (t2_cchunk_read_coordinate () ch) (t2_cchunk_upper_watermark () ch)
        \<and> (\<forall>k\<in>t2_cchunk_domain () ch. \<exists>m. t2_cchunk_read_result () ch k = Some m)
        \<and> (\<forall>k\<in>t2_cchunk_domain () ch. \<forall>m.
             t2_cchunk_read_result () ch k = Some m
               \<longleftrightarrow> Refresh k m (t2_cchunk_read_coordinate () ch)
                    \<in> set (t2_model.clean_prefix_of ()))"
    proof (cases "ch = T2ChA")
      case True
      show ?thesis
        using True t2m_lwm_A t2m_uwm_A t2m_rcoord_A src_le_refl
              t2m_dom_A t2m_crr_A_10 t2m_clean_prefix
        by auto
    next
      case False
      hence "ch = T2ChB" using ch_cases by simp
      show ?thesis
        using \<open>ch = T2ChB\<close> t2m_lwm_B t2m_uwm_B t2m_rcoord_B src_le_refl
              t2m_dom_B t2m_crr_B_20 t2m_clean_prefix
        by auto
    qed
  qed
next
  show "\<forall>ch\<in>t2_cchunks ().
          src_le (t2_cchunk_read_coordinate () ch) (t2_cfrontier ())"
    using t2m_chunks_eq t2m_rcoord_A t2m_rcoord_B
          t2m_frontier src_le_refl
    by auto
next
  show "\<forall>ch\<in>t2_cchunks (). \<forall>k\<in>t2_cchunk_domain () ch. \<forall>m.
          t2_cchunk_read_result () ch k = Some m
            \<longrightarrow> m = Src b0_t2 H_t2 (t2_cchunk_read_coordinate () ch) k"
  proof
    fix ch :: t2_cchunk assume "ch \<in> t2_cchunks ()"
    hence ch_cases: "ch = T2ChA \<or> ch = T2ChB"
      using t2m_chunks_eq by simp
    show "\<forall>k\<in>t2_cchunk_domain () ch. \<forall>m.
            t2_cchunk_read_result () ch k = Some m
              \<longrightarrow> m = Src b0_t2 H_t2 (t2_cchunk_read_coordinate () ch) k"
    proof (cases "ch = T2ChA")
      case True
      show ?thesis
        using True t2m_dom_A t2m_crr_A_10
              t2m_rcoord_A Src_b0_t2_H_t2_c0_10
        by auto
    next
      case False
      hence "ch = T2ChB" using ch_cases by simp
      show ?thesis
        using \<open>ch = T2ChB\<close> t2m_dom_B t2m_crr_B_20
              t2m_rcoord_B Src_b0_t2_H_t2_c0_20
        by auto
    qed
  qed
next
  show "\<forall>ch\<in>t2_cchunks (). \<forall>k\<in>t2_cchunk_domain () ch.
          t2_cchunk_read_result () ch k = Some None
            \<longrightarrow> t2_model.row_absence_meaningful b0_t2 H_t2 () ch k"
  proof (intro ballI impI)
    fix ch :: t2_cchunk and k :: nat
    assume ch_in: "ch \<in> t2_cchunks ()"
       and k_in: "k \<in> t2_cchunk_domain () ch"
       and crr: "t2_cchunk_read_result () ch k = Some None"
    from ch_in t2m_chunks_eq
      have ch_cases: "ch = T2ChA \<or> ch = T2ChB" by simp
    have False
    proof (cases "ch = T2ChA")
      case True
      with k_in t2m_dom_A have "k = 10" by simp
      with True crr t2m_crr_A_10 show False by simp
    next
      case False
      with ch_cases have ch_B: "ch = T2ChB" by simp
      with k_in t2m_dom_B have "k = 20" by simp
      with ch_B crr t2m_crr_B_20 show False by simp
    qed
    thus "t2_model.row_absence_meaningful b0_t2 H_t2 () ch k" ..
  qed
next
  show "\<forall>p \<in> set (t2_ccdc_events_of ()).
          key_of (hist_event p) \<in> t2_cscope ()
          \<and> src_le (hist_coord p) (t2_cfrontier ())
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (t2_model.clean_prefix_of ())"
    using t2m_cdc by simp
next
  show "\<forall>e c. Cdc c e \<in> set (t2_model.clean_prefix_of ())
                 \<and> key_of e \<in> t2_cscope ()
                 \<and> src_le c (t2_cfrontier ())
                 \<longrightarrow> (c, e) \<in> set (t2_ccdc_events_of ())"
  proof (intro allI impI)
    fix e :: "(nat, nat) source_event" and c :: src_coord
    assume "Cdc c e \<in> set (t2_model.clean_prefix_of ())
              \<and> key_of e \<in> t2_cscope ()
              \<and> src_le c (t2_cfrontier ())"
    hence cdc_in: "Cdc c e \<in> set (t2_model.clean_prefix_of ())" by simp
    have "Cdc c e \<in> set [Refresh (10::nat) (Some (100::nat)) c0,
                          Refresh 20 (Some 200) c0]"
      using cdc_in t2m_clean_prefix by simp
    hence False by simp
    thus "(c, e) \<in> set (t2_ccdc_events_of ())" ..
  qed
qed

subsection \<open>Topic 2 constructed positive witness\<close>

theorem topic2_positive_witness_constructed:
  "\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: unit) (H :: (nat, nat) src_history).
        t2_model.wellformed_dblog_run b0 R H
      \<and> t2_cscope R \<noteq> {}
      \<and> 2 \<le> card (t2_cchunks R)
      \<and> (\<forall> ch1 \<in> t2_cchunks R. \<forall> ch2 \<in> t2_cchunks R.
            ch1 \<noteq> ch2 \<longrightarrow> t2_cchunk_domain R ch1 \<inter> t2_cchunk_domain R ch2 = {})
      \<and> t2_model.canonical_chunk_ownership_domain R = t2_cscope R"
proof (intro exI[where x = b0_t2] exI[where x = "()"] exI[where x = H_t2] conjI)
  show "t2_model.wellformed_dblog_run b0_t2 () H_t2"
    by (rule t2_model_wellformed)
next
  show "t2_cscope () \<noteq> {}" using t2m_scope by simp
next
  show "2 \<le> card (t2_cchunks ())" using t2m_chunks t2m_distinct by simp
next
  show "\<forall> ch1 \<in> t2_cchunks (). \<forall> ch2 \<in> t2_cchunks ().
          ch1 \<noteq> ch2 \<longrightarrow> t2_cchunk_domain () ch1 \<inter> t2_cchunk_domain () ch2 = {}"
    using t2m_chunks_eq t2m_dom_A t2m_dom_B by auto
next
  show "t2_model.canonical_chunk_ownership_domain () = t2_cscope ()"
    unfolding t2_model.canonical_chunk_ownership_domain_def
    using t2m_chunks t2m_dom_A t2m_dom_B t2m_scope by auto
qed

text \<open>
  Models exist for the @{locale dblog_run_substrate} interface realizing the
  Topic 1 (clean-prefix-carrier) and Topic 2 (multi-chunk partition) witnesses,
  so both Layer 1 positive-witness results hold by construction, resting on no
  axiom.
\<close>

end
