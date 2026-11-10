(*  Title:   Layer01_Virtual_Cut_Example_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Virtual_Cut_Example_Inst
  imports Layer01_Virtual_Cut_Example_Model DBLog_Run_Substrate_Layer2
begin

section \<open>Constructed interpretation for the running-example virtual cut\<close>

text \<open>
  Constructs the paper's running example (the accounts-table
  backfill: three in-scope keys, two chunks, four CDC events, a seven-event
  clean prefix, and the full per-key replay equality) as an explicit
  interpretation of the Layer 1 locale @{locale dblog_run_substrate} at the
  concrete model of
  @{theory DBLog_Virtual_Cuts.Layer01_Virtual_Cut_Example_Model} (the @{typ unit}
  run carrier, the @{type cchunk} two-element chunk datatype, the @{text "c\<dots>"}
  definitional accessors), establishing the example facts with no axioms.

  Method (the @{text Layer01_Witnesses_Inst} pattern): instantiate
  @{locale dblog_run_substrate} at the model carrier (the two inherited
  @{text chunks_list} obligations discharge by @{method simp}, no axiom); read
  off the model's definitional accessor values pointwise as the
  @{text "exm_\<dots>"} lemmas (the conjuncts of
  @{thm [source] running_example_model_accessor_values}); and prove
  the determinate seven-event clean-prefix shape, the @{const Apply}
  computation, the seven-clause wellformedness, and the virtual-cut
  replay equality from those rewrite facts. As in @{text Layer01_Witnesses_Inst} the
  concrete-@{typ nat} wellformedness is proved at the interpretation in the
  global context (the locale type parameter @{typ "'k"} is rigid inside the
  locale context).

  The example source coordinates @{text "ec1..ec4"} are @{const coord_of_nat}
  definitions from @{theory Dual_Write_Layer0.Source_Coordinates}, with their
  order facts proved there; the carrier-independent example data
  (@{const b0_ex}, @{const H_ex}, the @{const Src} / @{const latest_src_event}
  computation lemmas, @{thm [source] wf_h_ex}, and further coordinate order
  lemmas) lives in
  @{theory DBLog_Virtual_Cuts.Layer01_Virtual_Cut_Example_Core}.
\<close>

subsection \<open>Constructed interpretation at the running-example model\<close>

global_interpretation ex_model: dblog_run_substrate
  cscope_of
  cfrontier_of
  cchunks
  csrc_history_of
  cchunk_read_result
  ccdc_events_of
  cchunks_list
  cchunk_domain
  cresponsible_chunk
  cchunk_lower_watermark
  cchunk_upper_watermark
  cchunk_read_coordinate
  by unfold_locales (simp_all add: cchunks_def cchunks_list_def)

subsection \<open>Model accessor-value lemmas\<close>

lemma exm_distinct: "ChA \<noteq> ChB" by simp
lemma exm_scope: "cscope_of () = {100, 200, 300}" by (simp add: cscope_of_def)
lemma exm_frontier: "cfrontier_of () = ec4" by (simp add: cfrontier_of_def)
lemma exm_chunks: "cchunks () = {ChA, ChB}" by (simp add: cchunks_def)
lemma exm_dom_A: "cchunk_domain () ChA = {100, 200}"
  by (simp add: cchunk_domain_def)
lemma exm_dom_B: "cchunk_domain () ChB = {300}"
  by (simp add: cchunk_domain_def)
lemma exm_resp_100: "cresponsible_chunk () 100 = Some ChA"
  by (simp add: cresponsible_chunk_def)
lemma exm_resp_200: "cresponsible_chunk () 200 = Some ChA"
  by (simp add: cresponsible_chunk_def)
lemma exm_resp_300: "cresponsible_chunk () 300 = Some ChB"
  by (simp add: cresponsible_chunk_def)
lemma exm_resp_else:
  "k \<noteq> 100 \<Longrightarrow> k \<noteq> 200 \<Longrightarrow> k \<noteq> 300
     \<Longrightarrow> cresponsible_chunk () k = None"
  by (simp add: cresponsible_chunk_def)
lemma exm_rcoord_A: "cchunk_read_coordinate () ChA = ec1"
  by (simp add: cchunk_read_coordinate_def)
lemma exm_rcoord_B: "cchunk_read_coordinate () ChB = ec3"
  by (simp add: cchunk_read_coordinate_def)
lemma exm_lwm_A: "cchunk_lower_watermark () ChA = ec1"
  by (simp add: cchunk_lower_watermark_def)
lemma exm_uwm_A: "cchunk_upper_watermark () ChA = ec1"
  by (simp add: cchunk_upper_watermark_def)
lemma exm_lwm_B: "cchunk_lower_watermark () ChB = ec3"
  by (simp add: cchunk_lower_watermark_def)
lemma exm_uwm_B: "cchunk_upper_watermark () ChB = ec3"
  by (simp add: cchunk_upper_watermark_def)
lemma exm_src_history: "csrc_history_of () = H_ex"
  by (simp add: csrc_history_of_def)
lemma exm_crr_A_100: "cchunk_read_result () ChA 100 = Some (Some 3000)"
  by (simp add: cchunk_read_result_def)
lemma exm_crr_A_200: "cchunk_read_result () ChA 200 = Some (Some 10000)"
  by (simp add: cchunk_read_result_def)
lemma exm_crr_B_300: "cchunk_read_result () ChB 300 = Some (Some 2500)"
  by (simp add: cchunk_read_result_def)
lemma exm_cdc: "ccdc_events_of () = H_ex"
  by (simp add: ccdc_events_of_def)
lemma exm_chunks_list: "cchunks_list () = [ChA, ChB]"
  by (simp add: cchunks_list_def)

lemma exm_chunks_eq:
  "(ch \<in> cchunks ()) \<longleftrightarrow> (ch = ChA \<or> ch = ChB)"
  using exm_chunks by simp

subsection \<open>Determinate clean prefix and Apply over the model\<close>

lemma exm_clean_prefix:
  "ex_model.clean_prefix_of ()
     = [ Cdc ec1 (Update 100 3000),
         Refresh (100::nat) (Some (3000::nat))  ec1,
         Refresh 200 (Some 10000) ec1,
         Cdc ec2 (Insert 300 2500),
         Cdc ec3 (Update 200 12000),
         Refresh 300 (Some 2500) ec3,
         Cdc ec4 (Update 300 3500) ]"
proof -
  have dA: "sorted_list_of_set {100::nat, 200} = [100, 200]" by simp
  have dB: "sorted_list_of_set {300::nat} = [300]" by simp
  show ?thesis
    unfolding ex_model.clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: exm_chunks_list exm_dom_A exm_dom_B
                  exm_rcoord_A exm_rcoord_B
                  exm_crr_A_100 exm_crr_A_200
                  exm_crr_B_300
                  exm_cdc exm_scope exm_frontier H_ex_def dA dB
                  List.map_filter_simps sort_key_def
                  ec1_le_ec2[unfolded src_le_eq_less_eq]
                  ec1_le_ec3[unfolded src_le_eq_less_eq]
                  ec1_le_ec4[unfolded src_le_eq_less_eq]
                  ec2_le_ec3[unfolded src_le_eq_less_eq]
                  ec2_le_ec4[unfolded src_le_eq_less_eq]
                  ec3_le_ec4[unfolded src_le_eq_less_eq]
                  not_src_le_ec2_ec1[unfolded src_le_eq_less_eq]
                  not_src_le_ec3_ec1[unfolded src_le_eq_less_eq]
                  not_src_le_ec4_ec1[unfolded src_le_eq_less_eq]
                  not_src_le_ec3_ec2[unfolded src_le_eq_less_eq]
                  not_src_le_ec4_ec2[unfolded src_le_eq_less_eq]
                  not_src_le_ec4_ec3[unfolded src_le_eq_less_eq])
qed

lemma exm_apply:
  "Apply (ex_model.clean_prefix_of ())
     = (\<lambda>k. if k = (100::nat) then Some (3000::nat)
            else if k = 200 then Some 12000
            else if k = 300 then Some 3500
            else None)"
proof -
  have step:
    "Apply (ex_model.clean_prefix_of ())
       = foldl apply_step (\<lambda>_. None)
           [ Cdc ec1 (Update 100 3000),
             Refresh (100::nat) (Some (3000::nat)) ec1,
             Refresh 200 (Some 10000) ec1,
             Cdc ec2 (Insert 300 2500),
             Cdc ec3 (Update 200 12000),
             Refresh 300 (Some 2500) ec3,
             Cdc ec4 (Update 300 3500) ]"
    unfolding Apply_def exm_clean_prefix by (rule refl)
  show ?thesis
    unfolding step by (auto simp: fun_eq_iff fun_upd_def)
qed

subsection \<open>Constructed wellformed-run fact\<close>

theorem ex_model_wellformed:
  "ex_model.wellformed_dblog_run b0_ex () H_ex"
  unfolding ex_model.wellformed_dblog_run_def
proof (intro conjI)
  show "csrc_history_of () = H_ex" by (rule exm_src_history)
next
  show "wellformed_src_history H_ex" by (rule wf_h_ex)
next
  show "\<forall>k\<in>cscope_of (). \<exists>!ch. ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
  proof
    fix k :: nat assume "k \<in> cscope_of ()"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using exm_scope by simp
    show "\<exists>!ch. ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
    proof (cases "k = 100")
      case True
      have "ChA \<in> cchunks () \<and> k \<in> cchunk_domain () ChA"
        using exm_chunks exm_dom_A True by simp
      moreover have "\<And>ch. ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch
                            \<Longrightarrow> ch = ChA"
        using exm_chunks_eq exm_dom_A exm_dom_B True by auto
      ultimately show ?thesis by blast
    next
      case False
      hence k_or: "k = 200 \<or> k = 300" using k_cases by simp
      show ?thesis
      proof (cases "k = 200")
        case True
        have "ChA \<in> cchunks () \<and> k \<in> cchunk_domain () ChA"
          using exm_chunks exm_dom_A True by simp
        moreover have "\<And>ch. ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch
                              \<Longrightarrow> ch = ChA"
          using exm_chunks_eq exm_dom_A exm_dom_B True by auto
        ultimately show ?thesis by blast
      next
        case False
        hence k300: "k = 300" using k_or by simp
        have "ChB \<in> cchunks () \<and> k \<in> cchunk_domain () ChB"
          using exm_chunks exm_dom_B k300 by simp
        moreover have "\<And>ch. ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch
                              \<Longrightarrow> ch = ChB"
          using exm_chunks_eq exm_dom_A exm_dom_B k300 by auto
        ultimately show ?thesis by blast
      qed
    qed
  qed
next
  show "\<forall>ch1\<in>cchunks (). \<forall>ch2\<in>cchunks ().
          ch1 \<noteq> ch2
            \<longrightarrow> cchunk_domain () ch1 \<inter> cchunk_domain () ch2 = {}"
    using exm_chunks_eq exm_dom_A exm_dom_B by auto
next
  show "ex_model.canonical_chunk_ownership_domain () = cscope_of ()"
    unfolding ex_model.canonical_chunk_ownership_domain_def
    using exm_chunks exm_dom_A exm_dom_B exm_scope by auto
next
  show "\<forall>k\<in>cscope_of (). \<forall>ch.
          cresponsible_chunk () k = Some ch
            \<longleftrightarrow> ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
  proof (intro ballI allI)
    fix k :: nat and ch :: cchunk
    assume "k \<in> cscope_of ()"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using exm_scope by simp
    show "cresponsible_chunk () k = Some ch
            \<longleftrightarrow> ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
    proof (cases "k = 100")
      case True
      then have rc: "cresponsible_chunk () k = Some ChA"
        using exm_resp_100 by simp
      show ?thesis
      proof
        assume "cresponsible_chunk () k = Some ch"
        with rc have "ch = ChA" by simp
        thus "ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
          using exm_chunks exm_dom_A True by simp
      next
        assume A: "ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
        have "ch = ChA"
          using A exm_chunks_eq exm_dom_A exm_dom_B True by auto
        with rc show "cresponsible_chunk () k = Some ch" by simp
      qed
    next
      case False
      hence k_or: "k = 200 \<or> k = 300" using k_cases by simp
      show ?thesis
      proof (cases "k = 200")
        case True
        then have rc: "cresponsible_chunk () k = Some ChA"
          using exm_resp_200 by simp
        show ?thesis
        proof
          assume "cresponsible_chunk () k = Some ch"
          with rc have "ch = ChA" by simp
          thus "ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
            using exm_chunks exm_dom_A True by simp
        next
          assume A: "ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
          have "ch = ChA"
            using A exm_chunks_eq exm_dom_A exm_dom_B True by auto
          with rc show "cresponsible_chunk () k = Some ch" by simp
        qed
      next
        case False
        hence k300: "k = 300" using k_or by simp
        then have rc: "cresponsible_chunk () k = Some ChB"
          using exm_resp_300 by simp
        show ?thesis
        proof
          assume "cresponsible_chunk () k = Some ch"
          with rc have "ch = ChB" by simp
          thus "ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
            using exm_chunks exm_dom_B k300 by simp
        next
          assume A: "ch \<in> cchunks () \<and> k \<in> cchunk_domain () ch"
          have "ch = ChB"
            using A exm_chunks_eq exm_dom_A exm_dom_B k300 by auto
          with rc show "cresponsible_chunk () k = Some ch" by simp
        qed
      qed
    qed
  qed
next
  show "\<forall>k. k \<notin> cscope_of () \<longrightarrow> cresponsible_chunk () k = None"
    using exm_scope exm_resp_else by auto
next
  show "finite (cscope_of ())" using exm_scope by simp
next
  show "\<forall>ch\<in>cchunks (). finite (cchunk_domain () ch)"
    using exm_chunks_eq exm_dom_A exm_dom_B by auto
next
  show "\<forall>ch\<in>cchunks (). cchunk_domain () ch \<noteq> {}"
    using exm_chunks_eq exm_dom_A exm_dom_B by auto
next
  show "\<forall>k\<in>cscope_of ().
          ex_model.covers_ordinary_cdc () k (cfrontier_of ())"
  proof
    fix k :: nat assume "k \<in> cscope_of ()"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using exm_scope by simp
    show "ex_model.covers_ordinary_cdc () k (cfrontier_of ())"
    proof (cases "k = 100")
      case True
      show ?thesis
        unfolding ex_model.covers_ordinary_cdc_def
      proof (intro exI[where x = ChA] conjI allI impI)
        show "cresponsible_chunk () k = Some ChA"
          using exm_resp_100 True by simp
      next
        fix i
        assume i_lt: "i < length (csrc_history_of ())"
           and chunk_lt: "src_lt (cchunk_read_coordinate () ChA)
                                  (hist_coord (csrc_history_of () ! i))"
           and to_f: "src_le (hist_coord (csrc_history_of () ! i))
                              (cfrontier_of ())"
           and key_eq: "key_of (hist_event (csrc_history_of () ! i)) = k"
        have i_lt4: "i < 4"
          using i_lt exm_src_history length_H_ex by simp
        have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
          using i_lt4 by (rule less_4_cases)
        have False
        proof -
          consider (a) "i = 0" | (b) "i = 1"
                 | (c) "i = 2" | (d) "i = 3"
            using i_cases by blast
          thus False
          proof cases
            case a
            then show False using chunk_lt exm_src_history
                                  exm_rcoord_A H_ex_nth_0
                                  not_src_lt_ec1_ec1 by simp
          next
            case b
            then show False using key_eq exm_src_history
                                  H_ex_nth_1 True by simp
          next
            case c
            then show False using key_eq exm_src_history
                                  H_ex_nth_2 True by simp
          next
            case d
            then show False using key_eq exm_src_history
                                  H_ex_nth_3 True by simp
          qed
        qed
        thus "csrc_history_of () ! i \<in> set (ccdc_events_of ())"
          ..
      qed
    next
      case False
      hence k_or: "k = 200 \<or> k = 300" using k_cases by simp
      show ?thesis
      proof (cases "k = 200")
        case True
        show ?thesis
          unfolding ex_model.covers_ordinary_cdc_def
        proof (intro exI[where x = ChA] conjI allI impI)
          show "cresponsible_chunk () k = Some ChA"
            using exm_resp_200 True by simp
        next
          fix i
          assume i_lt: "i < length (csrc_history_of ())"
             and chunk_lt: "src_lt (cchunk_read_coordinate () ChA)
                                    (hist_coord (csrc_history_of () ! i))"
             and to_f: "src_le (hist_coord (csrc_history_of () ! i))
                                (cfrontier_of ())"
             and key_eq: "key_of (hist_event (csrc_history_of () ! i)) = k"
          have i_lt4: "i < 4"
            using i_lt exm_src_history length_H_ex by simp
          have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
            using i_lt4 by (rule less_4_cases)
          consider (a) "i = 0" | (b) "i = 1"
                 | (c) "i = 2" | (d) "i = 3"
            using i_cases by blast
          thus "csrc_history_of () ! i \<in> set (ccdc_events_of ())"
          proof cases
            case a
            then show ?thesis using chunk_lt exm_src_history
                                    exm_rcoord_A H_ex_nth_0
                                    not_src_lt_ec1_ec1 by simp
          next
            case b
            then show ?thesis using key_eq exm_src_history
                                    H_ex_nth_1 True by simp
          next
            case c
            then show ?thesis using exm_src_history exm_cdc
                                    H_ex_nth_2 set_H_ex c by simp
          next
            case d
            then show ?thesis using key_eq exm_src_history
                                    H_ex_nth_3 True by simp
          qed
        qed
      next
        case False
        hence k300: "k = 300" using k_or by simp
        show ?thesis
          unfolding ex_model.covers_ordinary_cdc_def
        proof (intro exI[where x = ChB] conjI allI impI)
          show "cresponsible_chunk () k = Some ChB"
            using exm_resp_300 k300 by simp
        next
          fix i
          assume i_lt: "i < length (csrc_history_of ())"
             and chunk_lt: "src_lt (cchunk_read_coordinate () ChB)
                                    (hist_coord (csrc_history_of () ! i))"
             and to_f: "src_le (hist_coord (csrc_history_of () ! i))
                                (cfrontier_of ())"
             and key_eq: "key_of (hist_event (csrc_history_of () ! i)) = k"
          have i_lt4: "i < 4"
            using i_lt exm_src_history length_H_ex by simp
          have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
            using i_lt4 by (rule less_4_cases)
          consider (a) "i = 0" | (b) "i = 1"
                 | (c) "i = 2" | (d) "i = 3"
            using i_cases by blast
          thus "csrc_history_of () ! i \<in> set (ccdc_events_of ())"
          proof cases
            case a
            then show ?thesis using key_eq exm_src_history
                                    H_ex_nth_0 k300 by simp
          next
            case b
            then show ?thesis using chunk_lt exm_src_history
                                    exm_rcoord_B H_ex_nth_1
                                    not_src_lt_ec3_ec2 by simp
          next
            case c
            then show ?thesis using chunk_lt exm_src_history
                                    exm_rcoord_B H_ex_nth_2
                                    not_src_lt_ec3_ec3 by simp
          next
            case d
            then show ?thesis using exm_src_history exm_cdc
                                    H_ex_nth_3 set_H_ex d by simp
          qed
        qed
      qed
    qed
  qed
next
  show "\<forall>p\<in>set (ccdc_events_of ()).
          key_of (hist_event p) \<in> cscope_of ()
          \<and> src_le (hist_coord p) (cfrontier_of ())
          \<longrightarrow> p \<in> set (csrc_history_of ())"
    using exm_cdc exm_src_history by auto
next
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> cscope_of ()
                                   \<and> src_le (hist_coord p) (cfrontier_of ()));
                 cdc_in_slice  = filter in_slice (ccdc_events_of ());
                 hist_in_slice = filter in_slice (csrc_history_of ())
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    have eq: "ccdc_events_of () = csrc_history_of ()"
      using exm_cdc exm_src_history by simp
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> cscope_of ()
                                \<and> src_le (hist_coord p) (cfrontier_of ()));
              cdc_in_slice  = filter in_slice (ccdc_events_of ());
              hist_in_slice = filter in_slice (csrc_history_of ())
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      using eq by (simp add: Let_def)
  qed
next
  show "\<forall>k\<in>cscope_of (). \<forall>ch c.
          cresponsible_chunk () k = Some ch
          \<and> src_lt (cchunk_read_coordinate () ch) c
          \<and> src_le c (cfrontier_of ())
          \<longrightarrow>
            mset (source_key_coord_slice k c (ccdc_events_of ()))
            = mset (source_key_coord_slice k c (csrc_history_of ()))"
  proof (intro ballI allI impI)
    fix k :: nat and ch :: cchunk and c :: src_coord
    have eq: "ccdc_events_of () = csrc_history_of ()"
      using exm_cdc exm_src_history by simp
    show "mset (source_key_coord_slice k c (ccdc_events_of ()))
          = mset (source_key_coord_slice k c (csrc_history_of ()))"
      using eq by simp
  qed
next
  show "\<forall>ch\<in>cchunks ().
          src_le (cchunk_lower_watermark () ch)
                  (cchunk_read_coordinate () ch)
        \<and> src_le (cchunk_read_coordinate () ch)
                  (cchunk_upper_watermark () ch)
        \<and> (\<forall>k\<in>cchunk_domain () ch.
             \<exists>m. cchunk_read_result () ch k = Some m)
        \<and> (\<forall>k\<in>cchunk_domain () ch. \<forall>m.
             cchunk_read_result () ch k = Some m
               \<longleftrightarrow> Refresh k m (cchunk_read_coordinate () ch)
                    \<in> set (ex_model.clean_prefix_of ()))"
  proof
    fix ch :: cchunk
    assume ch_in: "ch \<in> cchunks ()"
    hence ch_cases: "ch = ChA \<or> ch = ChB"
      using exm_chunks_eq by simp
    show "src_le (cchunk_lower_watermark () ch)
                  (cchunk_read_coordinate () ch)
        \<and> src_le (cchunk_read_coordinate () ch)
                  (cchunk_upper_watermark () ch)
        \<and> (\<forall>k\<in>cchunk_domain () ch.
             \<exists>m. cchunk_read_result () ch k = Some m)
        \<and> (\<forall>k\<in>cchunk_domain () ch. \<forall>m.
             cchunk_read_result () ch k = Some m
               \<longleftrightarrow> Refresh k m (cchunk_read_coordinate () ch)
                    \<in> set (ex_model.clean_prefix_of ()))"
    proof (cases "ch = ChA")
      case True
      show ?thesis
        using True exm_lwm_A exm_uwm_A exm_rcoord_A
              src_le_refl
              exm_dom_A
              exm_crr_A_100
              exm_crr_A_200
              exm_clean_prefix
        by auto
    next
      case False
      hence ch_B: "ch = ChB" using ch_cases by simp
      show ?thesis
        using ch_B exm_lwm_B exm_uwm_B exm_rcoord_B
              src_le_refl
              exm_dom_B
              exm_crr_B_300
              exm_clean_prefix
              ec1_neq_ec3 ec1_neq_ec2 ec2_neq_ec3
        by auto
    qed
  qed
next
  show "\<forall>ch\<in>cchunks ().
          src_le (cchunk_read_coordinate () ch) (cfrontier_of ())"
    using exm_chunks_eq exm_rcoord_A exm_rcoord_B
          exm_frontier ec1_le_ec4 ec3_le_ec4
    by auto
next
  show "\<forall>ch\<in>cchunks (). \<forall>k\<in>cchunk_domain () ch. \<forall>m.
          cchunk_read_result () ch k = Some m
            \<longrightarrow> m = Src b0_ex H_ex (cchunk_read_coordinate () ch) k"
  proof
    fix ch :: cchunk
    assume ch_in: "ch \<in> cchunks ()"
    hence ch_cases: "ch = ChA \<or> ch = ChB"
      using exm_chunks_eq by simp
    show "\<forall>k\<in>cchunk_domain () ch. \<forall>m.
            cchunk_read_result () ch k = Some m
              \<longrightarrow> m = Src b0_ex H_ex (cchunk_read_coordinate () ch) k"
    proof (cases "ch = ChA")
      case True
      show ?thesis
        using True exm_dom_A
              exm_crr_A_100
              exm_crr_A_200
              exm_rcoord_A
              Src_b0_ex_H_ex_ec1_100
              Src_b0_ex_H_ex_ec1_200
        by auto
    next
      case False
      hence ch_B: "ch = ChB" using ch_cases by simp
      show ?thesis
        using ch_B exm_dom_B
              exm_crr_B_300
              exm_rcoord_B
              Src_b0_ex_H_ex_ec3_300
        by auto
    qed
  qed
next
  show "\<forall>ch\<in>cchunks (). \<forall>k\<in>cchunk_domain () ch.
          cchunk_read_result () ch k = Some None
            \<longrightarrow> ex_model.row_absence_meaningful b0_ex H_ex () ch k"
  proof (intro ballI impI)
    fix ch :: cchunk and k :: nat
    assume ch_in: "ch \<in> cchunks ()"
       and k_in: "k \<in> cchunk_domain () ch"
       and crr: "cchunk_read_result () ch k = Some None"
    from ch_in exm_chunks_eq
      have ch_cases: "ch = ChA \<or> ch = ChB" by simp
    have False
    proof (cases "ch = ChA")
      case True
      with k_in exm_dom_A have "k = 100 \<or> k = 200" by simp
      with True crr exm_crr_A_100
            exm_crr_A_200 show False by auto
    next
      case False
      with ch_cases have ch_B: "ch = ChB" by simp
      with k_in exm_dom_B have "k = 300" by simp
      with ch_B crr exm_crr_B_300 show False by simp
    qed
    thus "ex_model.row_absence_meaningful b0_ex H_ex () ch k" ..
  qed
next
  show "\<forall>p \<in> set (ccdc_events_of ()).
          key_of (hist_event p) \<in> cscope_of ()
          \<and> src_le (hist_coord p) (cfrontier_of ())
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (ex_model.clean_prefix_of ())"
  proof (intro ballI impI)
    fix p :: "src_coord \<times> (nat, nat) source_event"
    assume p_in: "p \<in> set (ccdc_events_of ())"
    hence p_cases: "p = (ec1, Update 100 3000)
                    \<or> p = (ec2, Insert 300 2500)
                    \<or> p = (ec3, Update 200 12000)
                    \<or> p = (ec4, Update 300 3500)"
      using exm_cdc set_H_ex by simp
    show "Cdc (hist_coord p) (hist_event p)
            \<in> set (ex_model.clean_prefix_of ())"
      using p_cases exm_clean_prefix by fastforce
  qed
next
  show "\<forall>e c. Cdc c e \<in> set (ex_model.clean_prefix_of ())
                 \<and> key_of e \<in> cscope_of ()
                 \<and> src_le c (cfrontier_of ())
                 \<longrightarrow> (c, e) \<in> set (ccdc_events_of ())"
  proof (intro allI impI)
    fix e :: "(nat, nat) source_event" and c :: src_coord
    assume "Cdc c e \<in> set (ex_model.clean_prefix_of ())
              \<and> key_of e \<in> cscope_of ()
              \<and> src_le c (cfrontier_of ())"
    hence cdc_in: "Cdc c e \<in> set (ex_model.clean_prefix_of ())" by simp
    have list_eq: "Cdc c e \<in> set [ Cdc ec1 (Update 100 3000),
                                    Refresh (100::nat) (Some (3000::nat)) ec1,
                                    Refresh 200 (Some 10000) ec1,
                                    Cdc ec2 (Insert 300 2500),
                                    Cdc ec3 (Update 200 12000),
                                    Refresh 300 (Some 2500) ec3,
                                    Cdc ec4 (Update 300 3500) ]"
      using cdc_in exm_clean_prefix by simp
    hence "(c = ec1 \<and> e = Update 100 3000)
            \<or> (c = ec2 \<and> e = Insert 300 2500)
            \<or> (c = ec3 \<and> e = Update 200 12000)
            \<or> (c = ec4 \<and> e = Update 300 3500)"
      by auto
    thus "(c, e) \<in> set (ccdc_events_of ())"
      using exm_cdc set_H_ex by auto
  qed
qed

subsection \<open>Constructed virtual-cut replay equality\<close>

theorem ex_model_virtual_cut_holds:
  "restrict (Apply (ex_model.clean_prefix_of ())) (cscope_of ())
     = restrict (Src b0_ex H_ex (cfrontier_of ())) (cscope_of ())"
proof
  fix k :: nat
  show "restrict (Apply (ex_model.clean_prefix_of ())) (cscope_of ()) k
          = restrict (Src b0_ex H_ex (cfrontier_of ())) (cscope_of ()) k"
  proof (cases "k \<in> cscope_of ()")
    case True
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using exm_scope by simp
    show ?thesis
    proof (cases "k = 100")
      case True
      then show ?thesis
        unfolding restrict_def
        using \<open>k \<in> cscope_of ()\<close>
              exm_apply
              Src_b0_ex_H_ex_ec4_100
              exm_frontier
        by simp
    next
      case False
      hence "k = 200 \<or> k = 300" using k_cases by simp
      show ?thesis
      proof (cases "k = 200")
        case True
        then show ?thesis
          unfolding restrict_def
          using \<open>k \<in> cscope_of ()\<close>
                exm_apply
                Src_b0_ex_H_ex_ec4_200
                exm_frontier
          by simp
      next
        case False
        hence k300: "k = 300" using \<open>k = 200 \<or> k = 300\<close> by simp
        then show ?thesis
          unfolding restrict_def
          using \<open>k \<in> cscope_of ()\<close>
                exm_apply
                Src_b0_ex_H_ex_ec4_300
                exm_frontier
          by simp
      qed
    qed
  next
    case False
    show ?thesis
      unfolding restrict_def using False by simp
  qed
qed

text \<open>
  Composite constructed result: the running example, realized by a concrete
  interpretation of @{locale dblog_run_substrate}, is wellformed and its
  assembled replay equals the source state at the frontier on the chunk-covered
  scope --- the Layer 2 source-side soundness conclusion (the paper's
  bridge lemma) on the running-example instance, backed by construction
  and resting on no axiom.
\<close>

theorem ex_model_wellformed_and_virtual_cut:
  "ex_model.wellformed_dblog_run b0_ex () H_ex
    \<and> restrict (Apply (ex_model.clean_prefix_of ())) (cscope_of ())
        = restrict (Src b0_ex H_ex (cfrontier_of ())) (cscope_of ())"
  using ex_model_wellformed ex_model_virtual_cut_holds by blast

end
