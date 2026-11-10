(*  Title:   Public_Checker_Witness.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Public_Checker_Witness
  imports Layer4_Whole_Table Continuation Layer4_Witnesses_Core
begin

section \<open>Public accepting witness for the Layer 3 checker (non-vacuity gate)\<close>

text \<open>
  This theory exhibits a concrete certificate / evidence pair over the
  \<^emph>\<open>public\<close> carriers (@{type cert}, @{type evidence}, the concrete
  @{type run} datatype) that the public verifier @{const verify}
  genuinely accepts, together with a deployment environment
  (@{const b0_ex}, @{const H_ex}) under which
  @{const faithful_source_observation} genuinely holds. It then exercises
  the Layer 3 / Layer 4 / continuation headline theorems at that
  pair, so the public headline implications are demonstrably
  non-vacuous --- with no axiom and no locale-instance detour.

  The construction is the paper's running example (the accounts-table
  backfill: three in-scope keys, two chunks, four CDC events, a
  seven-event clean prefix), realized as a value @{text ex_run} of the
  concrete @{type run} datatype --- the global-carrier sibling of the
  @{text ex_model} interpretation in
  @{text Layer01_Virtual_Cut_Example_Inst}.

  Two \<^emph>\<open>independence exhibits\<close> close the theory: an accepted pair whose
  observation is unfaithful (against a wrong deployment base state) and
  a faithful evidence bundle the verifier does not accept (a broken
  chunk plan). Together they certify that the two headline premises
  @{text "verify C E = Accept"} and
  @{text "faithful_source_observation E b0 H Raw"} are logically
  independent --- neither subsumes the other, and neither alone entails
  the wellformed-run conclusion --- which is the formal non-circularity
  of the mechanical / external factoring in
  @{theory DBLog_Virtual_Cuts.Virtual_Cut}.

  \<^bold>\<open>Regression gate.\<close> The capstone theorem
  @{text public_checker_nonvacuous} keeps this non-vacuity
  machine-checked:
  any change that degenerates the public checker (e.g. into
  @{text "verify C E = Reject"} or
  @{text "faithful_source_observation E b0 H Raw = False"}), or that
  weakens it until acceptance or faithfulness is unsatisfiable or the
  checker obligations fail, breaks this theory and hence the build.
\<close>

subsection \<open>The running-example run over the concrete run datatype\<close>

text \<open>Chunk plan: chunk @{term "0::nat"} owns @{term "{100::nat, 200}"}
  and reads at @{const ec1}; chunk @{term "1::nat"} owns
  @{term "{300::nat}"} and reads at @{const ec3}. Watermarks coincide
  with the read coordinates, as in the running example.\<close>

definition exr_dom :: "nat \<Rightarrow> nat set" where
  "exr_dom ch = (if ch = 0 then {100, 200} else if ch = 1 then {300} else {})"

definition exr_resp :: "nat \<Rightarrow> nat option" where
  "exr_resp k =
     (if k = 100 \<or> k = 200 then Some 0
      else if k = 300 then Some 1 else None)"

definition exr_coord :: "nat \<Rightarrow> src_coord" where
  "exr_coord ch = (if ch = 0 then ec1 else ec3)"

definition exr_read :: "nat \<Rightarrow> nat \<Rightarrow> nat option option" where
  "exr_read ch k =
     (if ch = 0 \<and> k = 100 then Some (Some 3000)
      else if ch = 0 \<and> k = 200 then Some (Some 10000)
      else if ch = 1 \<and> k = 300 then Some (Some 2500)
      else None)"

definition ex_run :: "(nat, nat) run" where
  "ex_run =
     Run {100, 200, 300} ec4 [0, 1] H_ex H_ex
         exr_read exr_dom exr_resp exr_coord exr_coord exr_coord"

subsection \<open>Accessor values\<close>

lemma exr_scope: "scope_of ex_run = {100, 200, 300}"
  by (simp add: scope_of_def ex_run_def)

lemma exr_frontier: "frontier_of ex_run = ec4"
  by (simp add: frontier_of_def ex_run_def)

lemma exr_chunks: "chunks ex_run = {0, 1}"
  by (simp add: chunks_def ex_run_def)

lemma exr_chunks_list: "chunks_list ex_run = [0, 1]"
  by (simp add: chunks_list_def ex_run_def)

lemma exr_hist: "src_history_of ex_run = H_ex"
  by (simp add: src_history_of_def ex_run_def)

lemma exr_cdc: "cdc_events_of ex_run = H_ex"
  by (simp add: cdc_events_of_def ex_run_def)

lemma exr_chunk_domain: "chunk_domain ex_run = exr_dom"
  by (simp add: chunk_domain_def ex_run_def)

lemma exr_responsible: "responsible_chunk ex_run = exr_resp"
  by (simp add: responsible_chunk_def ex_run_def)

lemma exr_rcoord: "chunk_read_coordinate ex_run = exr_coord"
  by (simp add: chunk_read_coordinate_def ex_run_def)

lemma exr_lwm: "chunk_lower_watermark ex_run = exr_coord"
  by (simp add: chunk_lower_watermark_def ex_run_def)

lemma exr_uwm: "chunk_upper_watermark ex_run = exr_coord"
  by (simp add: chunk_upper_watermark_def ex_run_def)

lemma exr_rresult: "chunk_read_result ex_run = exr_read"
  by (simp add: chunk_read_result_def ex_run_def)

subsection \<open>Determinate clean prefix and Apply\<close>

lemma exr_clean_prefix:
  "clean_prefix_of ex_run
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
    unfolding clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: exr_chunks_list exr_chunk_domain exr_rcoord exr_rresult
                  exr_dom_def exr_coord_def exr_read_def
                  exr_cdc exr_scope exr_frontier H_ex_def dA dB
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

lemma exr_apply:
  "Apply (clean_prefix_of ex_run)
     = (\<lambda>k. if k = (100::nat) then Some (3000::nat)
            else if k = 200 then Some 12000
            else if k = 300 then Some 3500
            else None)"
proof -
  have step:
    "Apply (clean_prefix_of ex_run)
       = foldl apply_step (\<lambda>_. None)
           [ Cdc ec1 (Update 100 3000),
             Refresh (100::nat) (Some (3000::nat)) ec1,
             Refresh 200 (Some 10000) ec1,
             Cdc ec2 (Insert 300 2500),
             Cdc ec3 (Update 200 12000),
             Refresh 300 (Some 2500) ec3,
             Cdc ec4 (Update 300 3500) ]"
    unfolding Apply_def exr_clean_prefix by (rule refl)
  show ?thesis
    unfolding step by (auto simp: fun_eq_iff fun_upd_def)
qed

subsection \<open>The running-example run is wellformed (global carrier)\<close>

theorem ex_run_wellformed:
  "wellformed_dblog_run b0_ex ex_run H_ex"
  unfolding wellformed_dblog_run_def
proof (intro conjI)
  show "src_history_of ex_run = H_ex" by (rule exr_hist)
next
  show "wellformed_src_history H_ex" by (rule wf_h_ex)
next
  show "\<forall>k\<in>scope_of ex_run.
          \<exists>!ch. ch \<in> chunks ex_run \<and> k \<in> chunk_domain ex_run ch"
  proof
    fix k :: nat assume "k \<in> scope_of ex_run"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using exr_scope by auto
    show "\<exists>!ch. ch \<in> chunks ex_run \<and> k \<in> chunk_domain ex_run ch"
    proof (rule ex1I[of _ "if k = 300 then 1 else (0::nat)"])
      show "(if k = 300 then 1 else (0::nat)) \<in> chunks ex_run
              \<and> k \<in> chunk_domain ex_run (if k = 300 then 1 else 0)"
        using k_cases
        by (auto simp: exr_chunks exr_chunk_domain exr_dom_def)
    next
      fix ch
      assume "ch \<in> chunks ex_run \<and> k \<in> chunk_domain ex_run ch"
      thus "ch = (if k = 300 then 1 else 0)"
        using k_cases
        by (auto simp: exr_chunks exr_chunk_domain exr_dom_def
                 split: if_split_asm)
    qed
  qed
next
  show "\<forall>ch1\<in>chunks ex_run. \<forall>ch2\<in>chunks ex_run.
          ch1 \<noteq> ch2
            \<longrightarrow> chunk_domain ex_run ch1 \<inter> chunk_domain ex_run ch2 = {}"
    by (auto simp: exr_chunks exr_chunk_domain exr_dom_def)
next
  show "canonical_chunk_ownership_domain ex_run = scope_of ex_run"
    unfolding canonical_chunk_ownership_domain_def
    by (auto simp: exr_chunks exr_chunk_domain exr_dom_def exr_scope)
next
  show "\<forall>k\<in>scope_of ex_run. \<forall>ch.
          responsible_chunk ex_run k = Some ch
            \<longleftrightarrow> ch \<in> chunks ex_run \<and> k \<in> chunk_domain ex_run ch"
  proof (intro ballI allI)
    fix k :: nat and ch :: nat
    assume "k \<in> scope_of ex_run"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using exr_scope by auto
    show "responsible_chunk ex_run k = Some ch
            \<longleftrightarrow> ch \<in> chunks ex_run \<and> k \<in> chunk_domain ex_run ch"
      using k_cases
      by (auto simp: exr_responsible exr_resp_def exr_chunks
                     exr_chunk_domain exr_dom_def
               split: if_split_asm)
  qed
next
  show "\<forall>k. k \<notin> scope_of ex_run \<longrightarrow> responsible_chunk ex_run k = None"
    by (auto simp: exr_scope exr_responsible exr_resp_def)
next
  show "finite (scope_of ex_run)" by (simp add: exr_scope)
next
  show "\<forall>ch\<in>chunks ex_run. finite (chunk_domain ex_run ch)"
    by (auto simp: exr_chunks exr_chunk_domain exr_dom_def)
next
  show "\<forall>ch\<in>chunks ex_run. chunk_domain ex_run ch \<noteq> {}"
    by (auto simp: exr_chunks exr_chunk_domain exr_dom_def)
next
  show "\<forall>k\<in>scope_of ex_run.
          covers_ordinary_cdc ex_run k (frontier_of ex_run)"
  proof
    fix k :: nat assume "k \<in> scope_of ex_run"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using exr_scope by auto
    show "covers_ordinary_cdc ex_run k (frontier_of ex_run)"
      unfolding covers_ordinary_cdc_def
    proof (intro exI[where x = "if k = 300 then 1 else (0::nat)"]
                 conjI allI impI)
      show "responsible_chunk ex_run k = Some (if k = 300 then 1 else 0)"
        using k_cases by (auto simp: exr_responsible exr_resp_def)
    next
      \<comment> \<open>The observed CDC log is the full recorded history, so every
          history entry is trivially present in it.\<close>
      fix i
      assume "i < length (src_history_of ex_run)"
      thus "src_history_of ex_run ! i \<in> set (cdc_events_of ex_run)"
        by (simp add: exr_hist exr_cdc)
    qed
  qed
next
  show "\<forall>p\<in>set (cdc_events_of ex_run).
          key_of (hist_event p) \<in> scope_of ex_run
          \<and> src_le (hist_coord p) (frontier_of ex_run)
          \<longrightarrow> p \<in> set (src_history_of ex_run)"
    by (simp add: exr_cdc exr_hist)
next
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of ex_run
                                   \<and> src_le (hist_coord p) (frontier_of ex_run));
                 cdc_in_slice  = filter in_slice (cdc_events_of ex_run);
                 hist_in_slice = filter in_slice (src_history_of ex_run)
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x = "\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of ex_run
                                \<and> src_le (hist_coord p) (frontier_of ex_run));
              cdc_in_slice  = filter in_slice (cdc_events_of ex_run);
              hist_in_slice = filter in_slice (src_history_of ex_run)
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      by (simp add: Let_def exr_cdc exr_hist)
  qed
next
  show "\<forall>k\<in>scope_of ex_run. \<forall>ch c.
          responsible_chunk ex_run k = Some ch
          \<and> src_lt (chunk_read_coordinate ex_run ch) c
          \<and> src_le c (frontier_of ex_run)
          \<longrightarrow>
            mset (source_key_coord_slice k c (cdc_events_of ex_run))
            = mset (source_key_coord_slice k c (src_history_of ex_run))"
    by (simp add: exr_cdc exr_hist)
next
  show "\<forall>ch\<in>chunks ex_run.
          src_le (chunk_lower_watermark ex_run ch)
                  (chunk_read_coordinate ex_run ch)
        \<and> src_le (chunk_read_coordinate ex_run ch)
                  (chunk_upper_watermark ex_run ch)
        \<and> (\<forall>k\<in>chunk_domain ex_run ch.
             \<exists>m. chunk_read_result ex_run ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain ex_run ch. \<forall>m.
             chunk_read_result ex_run ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate ex_run ch)
                    \<in> set (clean_prefix_of ex_run))"
  proof
    fix ch :: nat
    assume "ch \<in> chunks ex_run"
    hence ch_cases: "ch = 0 \<or> ch = 1" by (auto simp: exr_chunks)
    show "src_le (chunk_lower_watermark ex_run ch)
                  (chunk_read_coordinate ex_run ch)
        \<and> src_le (chunk_read_coordinate ex_run ch)
                  (chunk_upper_watermark ex_run ch)
        \<and> (\<forall>k\<in>chunk_domain ex_run ch.
             \<exists>m. chunk_read_result ex_run ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain ex_run ch. \<forall>m.
             chunk_read_result ex_run ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate ex_run ch)
                    \<in> set (clean_prefix_of ex_run))"
    proof (cases "ch = 0")
      case True
      show ?thesis
        using True exr_lwm exr_uwm exr_rcoord
              src_le_refl
              exr_chunk_domain exr_rresult
              exr_clean_prefix
        by (auto simp: exr_coord_def exr_dom_def exr_read_def
                       ec1_neq_ec3 ec1_neq_ec2 ec2_neq_ec3)
    next
      case False
      hence ch_1: "ch = 1" using ch_cases by simp
      show ?thesis
        using ch_1 exr_lwm exr_uwm exr_rcoord
              src_le_refl
              exr_chunk_domain exr_rresult
              exr_clean_prefix
        by (auto simp: exr_coord_def exr_dom_def exr_read_def
                       ec1_neq_ec3 ec1_neq_ec2 ec2_neq_ec3)
    qed
  qed
next
  show "\<forall>ch\<in>chunks ex_run.
          src_le (chunk_read_coordinate ex_run ch) (frontier_of ex_run)"
    by (auto simp: exr_chunks exr_rcoord exr_coord_def exr_frontier
                   ec1_le_ec4 ec3_le_ec4)
next
  show "\<forall>ch\<in>chunks ex_run. \<forall>k\<in>chunk_domain ex_run ch. \<forall>m.
          chunk_read_result ex_run ch k = Some m
            \<longrightarrow> m = Src b0_ex H_ex (chunk_read_coordinate ex_run ch) k"
    by (auto simp: exr_chunks exr_chunk_domain exr_dom_def
                   exr_rresult exr_read_def exr_rcoord exr_coord_def
                   Src_b0_ex_H_ex_ec1_100 Src_b0_ex_H_ex_ec1_200
                   Src_b0_ex_H_ex_ec3_300
             split: if_split_asm)
next
  show "\<forall>ch\<in>chunks ex_run. \<forall>k\<in>chunk_domain ex_run ch.
          chunk_read_result ex_run ch k = Some None
            \<longrightarrow> row_absence_meaningful b0_ex H_ex ex_run ch k"
    by (auto simp: exr_chunks exr_chunk_domain exr_dom_def
                   exr_rresult exr_read_def
             split: if_split_asm)
next
  show "\<forall>p \<in> set (cdc_events_of ex_run).
          key_of (hist_event p) \<in> scope_of ex_run
          \<and> src_le (hist_coord p) (frontier_of ex_run)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (clean_prefix_of ex_run)"
    using wf7_clean_prefix_cdc_coherence_redundant[of ex_run] by blast
next
  show "\<forall>e c. Cdc c e \<in> set (clean_prefix_of ex_run)
                 \<and> key_of e \<in> scope_of ex_run
                 \<and> src_le c (frontier_of ex_run)
                 \<longrightarrow> (c, e) \<in> set (cdc_events_of ex_run)"
    using wf7_clean_prefix_cdc_coherence_redundant[of ex_run] by blast
qed

text \<open>The two halves of the factoring, extracted once for reuse.\<close>

lemma ex_run_checker_wellformed: "checker_run_wellformed ex_run"
  using ex_run_wellformed wellformed_dblog_run_decompose by blast

lemma ex_run_reflects_source: "run_reflects_source b0_ex ex_run H_ex"
  using ex_run_wellformed wellformed_dblog_run_decompose by blast

subsection \<open>The accepting public certificate / evidence pair\<close>

definition ex_cert :: "(nat, nat) cert" where
  "ex_cert = Cert {100, 200, 300} ec4 (clean_prefix_of ex_run)"

definition ex_evidence :: "(nat, nat) evidence" where
  "ex_evidence = Evidence ex_run"

lemma ex_cert_scope: "scope ex_cert = {100, 200, 300}"
  by (simp add: scope_def ex_cert_def)

lemma ex_cert_frontier: "frontier ex_cert = ec4"
  by (simp add: frontier_def ex_cert_def)

lemma ex_cert_clean_prefix: "clean_prefix ex_cert = clean_prefix_of ex_run"
  by (simp add: clean_prefix_def ex_cert_def)

lemma ex_evidence_bound: "evidence_bound_to_cert ex_cert ex_evidence"
  by (simp add: evidence_bound_to_cert_def cert_accessors_agree_def
                ex_evidence_def ex_cert_scope ex_cert_frontier
                ex_cert_clean_prefix exr_scope exr_frontier)

lemma ex_evidence_schema: "source_side_schema_supported ex_cert ex_evidence"
  by (simp add: source_side_schema_supported_def ex_evidence_def
                ex_run_checker_wellformed)

theorem ex_verify_accept: "verify ex_cert ex_evidence = Accept"
  by (simp add: verify_def ex_evidence_schema ex_evidence_bound)

theorem ex_faithful:
  "faithful_source_observation ex_evidence b0_ex H_ex RawObservation"
  by (simp add: faithful_source_observation_def ex_evidence_def
                ex_run_reflects_source)

subsection \<open>Exercising the headline theorems at the public witness\<close>

text \<open>Layer 3 intermediate theorem
  @{text accepted_certificate_implies_wellformed_run} at the public
  witness: the accepted pair has a
  wellformed, coherent materialized run.\<close>

theorem public_accepted_certificate_wellformed_run:
  "\<exists>R. wellformed_dblog_run b0_ex R H_ex \<and> cert_run_coherent ex_cert ex_evidence R"
  by (rule layer3_checker_substrate.accepted_certificate_implies_wellformed_run
        [OF layer3_checker_substrate_holds ex_verify_accept ex_faithful])

text \<open>Layer 3 headline @{text accepted_virtual_cut_sound} at the public
  witness: the accepted certificate's
  virtual cut holds.\<close>

theorem public_accepted_virtual_cut:
  "virtual_cut b0_ex ex_cert H_ex"
  by (rule layer3_checker_substrate.accepted_virtual_cut_sound
        [OF layer3_checker_substrate_holds ex_verify_accept ex_faithful])

text \<open>Layer 4 whole-table side conditions at anchor @{const ec1}, over the
  pure @{theory DBLog_Virtual_Cuts.Virtual_Cut_Core} predicates.\<close>

lemma ex_whole_table_claim_scope:
  "whole_table_claim_scope b0_ex ex_cert H_ex ec1"
  unfolding whole_table_claim_scope_def
proof (intro conjI)
  show "ec1 \<le> frontier ex_cert"
    using ec1_le_ec4 by (simp add: ex_cert_frontier less_eq_src_coord_def)
next
  show "anchor_complete_at_boundary b0_ex H_ex ec1 (scope ex_cert)"
    unfolding anchor_complete_at_boundary_def
    using l4_anchor_domain[unfolded l4_anchor_def]
    by (simp add: ex_cert_scope)
next
  show "all_post_anchor_changes_covered H_ex ec1 (frontier ex_cert) (scope ex_cert)"
    unfolding all_post_anchor_changes_covered_def touched_between_def
    by (auto simp: ex_cert_scope H_ex_def)
next
  show "no_unclaimed_replay_keys (clean_prefix ex_cert) (scope ex_cert)"
    unfolding no_unclaimed_replay_keys_def replay_keys_def
    by (auto simp: ex_cert_clean_prefix ex_cert_scope exr_clean_prefix)
qed

text \<open>Layer 4 specialization
  @{text accepted_whole_table_anchor_domain_specialization}: unrestricted
  whole-table
  equality at the accepted certificate.\<close>

theorem public_accepted_whole_table_equality:
  "Apply (clean_prefix ex_cert) = Src b0_ex H_ex (frontier ex_cert)"
  by (rule layer3_checker_substrate.accepted_whole_table_anchor_domain_specialization
        [OF layer3_checker_substrate_holds ex_verify_accept ex_faithful
            ex_whole_table_claim_scope])

text \<open>Continuation corollary
  @{text accepted_certificate_continuation_sound}: the accepted
  certificate's cut extends to the strictly later frontier
  @{term "coord_of_nat 5"} by the (here empty) faithful continuation
  segment for the half-open interval.\<close>

lemma ex_cdc_segment_to_later_frontier:
  "cdc_segment_between H_ex (scope ex_cert) (frontier ex_cert) (coord_of_nat 5) []"
  unfolding cdc_segment_between_def ex_cert_frontier
  by (simp add: H_ex_def ec_defs)

theorem public_accepted_continuation:
  "virtual_cut_state b0_ex (clean_prefix ex_cert @ []) (scope ex_cert)
                     (coord_of_nat 5) H_ex"
  by (rule layer3_checker_substrate.accepted_certificate_continuation_sound
        [OF layer3_checker_substrate_holds ex_verify_accept ex_faithful
            wf_h_ex ex_cdc_segment_to_later_frontier])

subsection \<open>Exercising the remaining state-level headlines: Layer 2 and
  sub-scope restriction\<close>

text \<open>Layer 2 (@{text wellformed_run_implies_virtual_cut}) exercised at the
  running-example run: the
  wellformed public run replays, on its scope, to the source state
  at its frontier.\<close>

theorem public_wellformed_run_virtual_cut:
  "virtual_cut_state b0_ex (clean_prefix_of ex_run) (scope_of ex_run)
                     (frontier_of ex_run) H_ex"
  by (rule wellformed_run_implies_virtual_cut[OF ex_run_wellformed])

text \<open>Sub-scope restriction over the accepted certificate
  (@{text virtual_cut_restrict_to_subscope}), exercised at the \<^emph>\<open>proper\<close>,
  non-empty sub-scope @{term "{100::nat, 300}"}
  of the certified scope: the accepted certificate's cut restricts to the
  sub-scope that drops key @{term "200::nat"}. Non-degeneracy is part of
  the statement: the sub-scope is neither empty nor the whole certified
  scope.\<close>

theorem public_accepted_subscope_restriction:
  "{100, 300} \<noteq> ({} :: nat set)
   \<and> {100, 300} \<subset> scope ex_cert
   \<and> virtual_cut_state b0_ex (clean_prefix ex_cert) {100, 300}
                       (frontier ex_cert) H_ex"
proof (intro conjI)
  show "{100, 300} \<noteq> ({} :: nat set)" by simp
next
  show "{100, 300} \<subset> scope ex_cert"
  proof (rule psubsetI)
    show "{100, 300} \<subseteq> scope ex_cert"
      unfolding ex_cert_scope by simp
  next
    show "{100, 300} \<noteq> scope ex_cert"
    proof
      assume eq: "{100, 300} = scope ex_cert"
      have "(200::nat) \<in> scope ex_cert"
        unfolding ex_cert_scope by simp
      with eq have "(200::nat) \<in> {100, 300}" by simp
      thus False by simp
    qed
  qed
next
  have "{100, 300} \<subseteq> scope ex_cert"
    unfolding ex_cert_scope by simp
  thus "virtual_cut_state b0_ex (clean_prefix ex_cert) {100, 300}
                          (frontier ex_cert) H_ex"
    by (rule virtual_cut_restrict_to_subscope[OF public_accepted_virtual_cut])
qed

text \<open>State-level sub-scope restriction
  (@{text virtual_cut_state_restrict_scope}), exercised at the
  same accepted cut --- @{text public_accepted_virtual_cut} unfolded through
  @{thm [source] virtual_cut_def} --- and the proper, non-empty singleton
  sub-scope @{term "{200::nat}"}.\<close>

theorem public_state_restrict_scope_singleton:
  "{200} \<noteq> ({} :: nat set)
   \<and> {200} \<subset> scope ex_cert
   \<and> virtual_cut_state b0_ex (clean_prefix ex_cert) {200}
                       (frontier ex_cert) H_ex"
proof (intro conjI)
  show "{200} \<noteq> ({} :: nat set)" by simp
next
  show "{200} \<subset> scope ex_cert"
  proof (rule psubsetI)
    show "{200} \<subseteq> scope ex_cert"
      unfolding ex_cert_scope by simp
  next
    show "{200} \<noteq> scope ex_cert"
    proof
      assume eq: "{200} = scope ex_cert"
      have "(100::nat) \<in> scope ex_cert"
        unfolding ex_cert_scope by simp
      with eq have "(100::nat) \<in> {200}" by simp
      thus False by simp
    qed
  qed
next
  have cut: "virtual_cut_state b0_ex (clean_prefix ex_cert) (scope ex_cert)
                               (frontier ex_cert) H_ex"
    using public_accepted_virtual_cut unfolding virtual_cut_def .
  have "{200} \<subseteq> scope ex_cert"
    unfolding ex_cert_scope by simp
  with cut show "virtual_cut_state b0_ex (clean_prefix ex_cert) {200}
                                   (frontier ex_cert) H_ex"
    by (rule virtual_cut_state_restrict_scope)
qed

subsection \<open>A mid-frontier accepted certificate and non-empty continuation
  segments (the active-interval continuation case)\<close>

text \<open>
  @{thm [source] public_accepted_continuation} above exercises
  @{text accepted_certificate_continuation_sound}
  with the \<^emph>\<open>empty\<close> continuation segment --- the quiescent-interval case
  of continuation (no in-scope source event lies in the half-open
  interval, and the certified cut persists at the strictly later
  frontier). The theorems below exercise the continuation headlines in their
  \<^emph>\<open>active-interval\<close> case, with a non-empty segment that genuinely replays
  a post-frontier source event.

  The witness is a second accepted certificate over the \<^emph>\<open>same\<close> running
  example: the same source history @{const H_ex}, the same chunk plan,
  chunk reads, and watermarks, but certified at the \<^emph>\<open>mid\<close> frontier
  @{const ec3} --- so the recorded history genuinely extends past the
  certified frontier, and the faithful continuation segment for
  @{text "(ec3, ec4]"} on the certified scope is the non-empty singleton
  @{term "[Cdc ec4 (Update (300::nat) (3500::nat))]"}. Its canonical
  clean prefix is the running example's first six replay events (the
  @{const ec4} CDC event now lies beyond the certified frontier).
  Continuation then lands exactly on the state that the full-frontier
  certificate @{const ex_cert} certifies directly
  (@{text public_continuation_meets_direct_certification} below).
\<close>

definition ex_run_mid :: "(nat, nat) run" where
  "ex_run_mid =
     Run {100, 200, 300} ec3 [0, 1] H_ex H_ex
         exr_read exr_dom exr_resp exr_coord exr_coord exr_coord"

lemma mid_scope: "scope_of ex_run_mid = {100, 200, 300}"
  by (simp add: scope_of_def ex_run_mid_def)

lemma mid_frontier: "frontier_of ex_run_mid = ec3"
  by (simp add: frontier_of_def ex_run_mid_def)

lemma mid_chunks: "chunks ex_run_mid = {0, 1}"
  by (simp add: chunks_def ex_run_mid_def)

lemma mid_chunks_list: "chunks_list ex_run_mid = [0, 1]"
  by (simp add: chunks_list_def ex_run_mid_def)

lemma mid_hist: "src_history_of ex_run_mid = H_ex"
  by (simp add: src_history_of_def ex_run_mid_def)

lemma mid_cdc: "cdc_events_of ex_run_mid = H_ex"
  by (simp add: cdc_events_of_def ex_run_mid_def)

lemma mid_chunk_domain: "chunk_domain ex_run_mid = exr_dom"
  by (simp add: chunk_domain_def ex_run_mid_def)

lemma mid_responsible: "responsible_chunk ex_run_mid = exr_resp"
  by (simp add: responsible_chunk_def ex_run_mid_def)

lemma mid_rcoord: "chunk_read_coordinate ex_run_mid = exr_coord"
  by (simp add: chunk_read_coordinate_def ex_run_mid_def)

lemma mid_lwm: "chunk_lower_watermark ex_run_mid = exr_coord"
  by (simp add: chunk_lower_watermark_def ex_run_mid_def)

lemma mid_uwm: "chunk_upper_watermark ex_run_mid = exr_coord"
  by (simp add: chunk_upper_watermark_def ex_run_mid_def)

lemma mid_rresult: "chunk_read_result ex_run_mid = exr_read"
  by (simp add: chunk_read_result_def ex_run_mid_def)

lemma mid_clean_prefix:
  "clean_prefix_of ex_run_mid
     = [ Cdc ec1 (Update 100 3000),
         Refresh (100::nat) (Some (3000::nat))  ec1,
         Refresh 200 (Some 10000) ec1,
         Cdc ec2 (Insert 300 2500),
         Cdc ec3 (Update 200 12000),
         Refresh 300 (Some 2500) ec3 ]"
proof -
  have dA: "sorted_list_of_set {100::nat, 200} = [100, 200]" by simp
  have dB: "sorted_list_of_set {300::nat} = [300]" by simp
  show ?thesis
    unfolding clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: mid_chunks_list mid_chunk_domain mid_rcoord mid_rresult
                  exr_dom_def exr_coord_def exr_read_def
                  mid_cdc mid_scope mid_frontier H_ex_def dA dB
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

theorem ex_run_mid_wellformed:
  "wellformed_dblog_run b0_ex ex_run_mid H_ex"
  unfolding wellformed_dblog_run_def
proof (intro conjI)
  show "src_history_of ex_run_mid = H_ex" by (rule mid_hist)
next
  show "wellformed_src_history H_ex" by (rule wf_h_ex)
next
  show "\<forall>k\<in>scope_of ex_run_mid.
          \<exists>!ch. ch \<in> chunks ex_run_mid \<and> k \<in> chunk_domain ex_run_mid ch"
  proof
    fix k :: nat assume "k \<in> scope_of ex_run_mid"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using mid_scope by auto
    show "\<exists>!ch. ch \<in> chunks ex_run_mid \<and> k \<in> chunk_domain ex_run_mid ch"
    proof (rule ex1I[of _ "if k = 300 then 1 else (0::nat)"])
      show "(if k = 300 then 1 else (0::nat)) \<in> chunks ex_run_mid
              \<and> k \<in> chunk_domain ex_run_mid (if k = 300 then 1 else 0)"
        using k_cases
        by (auto simp: mid_chunks mid_chunk_domain exr_dom_def)
    next
      fix ch
      assume "ch \<in> chunks ex_run_mid \<and> k \<in> chunk_domain ex_run_mid ch"
      thus "ch = (if k = 300 then 1 else 0)"
        using k_cases
        by (auto simp: mid_chunks mid_chunk_domain exr_dom_def
                 split: if_split_asm)
    qed
  qed
next
  show "\<forall>ch1\<in>chunks ex_run_mid. \<forall>ch2\<in>chunks ex_run_mid.
          ch1 \<noteq> ch2
            \<longrightarrow> chunk_domain ex_run_mid ch1 \<inter> chunk_domain ex_run_mid ch2 = {}"
    by (auto simp: mid_chunks mid_chunk_domain exr_dom_def)
next
  show "canonical_chunk_ownership_domain ex_run_mid = scope_of ex_run_mid"
    unfolding canonical_chunk_ownership_domain_def
    by (auto simp: mid_chunks mid_chunk_domain exr_dom_def mid_scope)
next
  show "\<forall>k\<in>scope_of ex_run_mid. \<forall>ch.
          responsible_chunk ex_run_mid k = Some ch
            \<longleftrightarrow> ch \<in> chunks ex_run_mid \<and> k \<in> chunk_domain ex_run_mid ch"
  proof (intro ballI allI)
    fix k :: nat and ch :: nat
    assume "k \<in> scope_of ex_run_mid"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using mid_scope by auto
    show "responsible_chunk ex_run_mid k = Some ch
            \<longleftrightarrow> ch \<in> chunks ex_run_mid \<and> k \<in> chunk_domain ex_run_mid ch"
      using k_cases
      by (auto simp: mid_responsible exr_resp_def mid_chunks
                     mid_chunk_domain exr_dom_def
               split: if_split_asm)
  qed
next
  show "\<forall>k. k \<notin> scope_of ex_run_mid \<longrightarrow> responsible_chunk ex_run_mid k = None"
    by (auto simp: mid_scope mid_responsible exr_resp_def)
next
  show "finite (scope_of ex_run_mid)" by (simp add: mid_scope)
next
  show "\<forall>ch\<in>chunks ex_run_mid. finite (chunk_domain ex_run_mid ch)"
    by (auto simp: mid_chunks mid_chunk_domain exr_dom_def)
next
  show "\<forall>ch\<in>chunks ex_run_mid. chunk_domain ex_run_mid ch \<noteq> {}"
    by (auto simp: mid_chunks mid_chunk_domain exr_dom_def)
next
  show "\<forall>k\<in>scope_of ex_run_mid.
          covers_ordinary_cdc ex_run_mid k (frontier_of ex_run_mid)"
  proof
    fix k :: nat assume "k \<in> scope_of ex_run_mid"
    hence k_cases: "k = 100 \<or> k = 200 \<or> k = 300"
      using mid_scope by auto
    show "covers_ordinary_cdc ex_run_mid k (frontier_of ex_run_mid)"
      unfolding covers_ordinary_cdc_def
    proof (intro exI[where x = "if k = 300 then 1 else (0::nat)"]
                 conjI allI impI)
      show "responsible_chunk ex_run_mid k = Some (if k = 300 then 1 else 0)"
        using k_cases by (auto simp: mid_responsible exr_resp_def)
    next
      \<comment> \<open>The observed CDC log is the full recorded history, so every
          history entry is trivially present in it.\<close>
      fix i
      assume "i < length (src_history_of ex_run_mid)"
      thus "src_history_of ex_run_mid ! i \<in> set (cdc_events_of ex_run_mid)"
        by (simp add: mid_hist mid_cdc)
    qed
  qed
next
  show "\<forall>p\<in>set (cdc_events_of ex_run_mid).
          key_of (hist_event p) \<in> scope_of ex_run_mid
          \<and> src_le (hist_coord p) (frontier_of ex_run_mid)
          \<longrightarrow> p \<in> set (src_history_of ex_run_mid)"
    by (simp add: mid_cdc mid_hist)
next
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of ex_run_mid
                                   \<and> src_le (hist_coord p) (frontier_of ex_run_mid));
                 cdc_in_slice  = filter in_slice (cdc_events_of ex_run_mid);
                 hist_in_slice = filter in_slice (src_history_of ex_run_mid)
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x = "\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of ex_run_mid
                                \<and> src_le (hist_coord p) (frontier_of ex_run_mid));
              cdc_in_slice  = filter in_slice (cdc_events_of ex_run_mid);
              hist_in_slice = filter in_slice (src_history_of ex_run_mid)
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      by (simp add: Let_def mid_cdc mid_hist)
  qed
next
  show "\<forall>k\<in>scope_of ex_run_mid. \<forall>ch c.
          responsible_chunk ex_run_mid k = Some ch
          \<and> src_lt (chunk_read_coordinate ex_run_mid ch) c
          \<and> src_le c (frontier_of ex_run_mid)
          \<longrightarrow>
            mset (source_key_coord_slice k c (cdc_events_of ex_run_mid))
            = mset (source_key_coord_slice k c (src_history_of ex_run_mid))"
    by (simp add: mid_cdc mid_hist)
next
  show "\<forall>ch\<in>chunks ex_run_mid.
          src_le (chunk_lower_watermark ex_run_mid ch)
                  (chunk_read_coordinate ex_run_mid ch)
        \<and> src_le (chunk_read_coordinate ex_run_mid ch)
                  (chunk_upper_watermark ex_run_mid ch)
        \<and> (\<forall>k\<in>chunk_domain ex_run_mid ch.
             \<exists>m. chunk_read_result ex_run_mid ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain ex_run_mid ch. \<forall>m.
             chunk_read_result ex_run_mid ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate ex_run_mid ch)
                    \<in> set (clean_prefix_of ex_run_mid))"
  proof
    fix ch :: nat
    assume "ch \<in> chunks ex_run_mid"
    hence ch_cases: "ch = 0 \<or> ch = 1" by (auto simp: mid_chunks)
    show "src_le (chunk_lower_watermark ex_run_mid ch)
                  (chunk_read_coordinate ex_run_mid ch)
        \<and> src_le (chunk_read_coordinate ex_run_mid ch)
                  (chunk_upper_watermark ex_run_mid ch)
        \<and> (\<forall>k\<in>chunk_domain ex_run_mid ch.
             \<exists>m. chunk_read_result ex_run_mid ch k = Some m)
        \<and> (\<forall>k\<in>chunk_domain ex_run_mid ch. \<forall>m.
             chunk_read_result ex_run_mid ch k = Some m
               \<longleftrightarrow> Refresh k m (chunk_read_coordinate ex_run_mid ch)
                    \<in> set (clean_prefix_of ex_run_mid))"
    proof (cases "ch = 0")
      case True
      show ?thesis
        using True mid_lwm mid_uwm mid_rcoord
              src_le_refl
              mid_chunk_domain mid_rresult
              mid_clean_prefix
        by (auto simp: exr_coord_def exr_dom_def exr_read_def
                       ec1_neq_ec3 ec1_neq_ec2 ec2_neq_ec3)
    next
      case False
      hence ch_1: "ch = 1" using ch_cases by simp
      show ?thesis
        using ch_1 mid_lwm mid_uwm mid_rcoord
              src_le_refl
              mid_chunk_domain mid_rresult
              mid_clean_prefix
        by (auto simp: exr_coord_def exr_dom_def exr_read_def
                       ec1_neq_ec3 ec1_neq_ec2 ec2_neq_ec3)
    qed
  qed
next
  show "\<forall>ch\<in>chunks ex_run_mid.
          src_le (chunk_read_coordinate ex_run_mid ch) (frontier_of ex_run_mid)"
    by (auto simp: mid_chunks mid_rcoord exr_coord_def mid_frontier
                   ec1_le_ec3 src_le_refl)
next
  show "\<forall>ch\<in>chunks ex_run_mid. \<forall>k\<in>chunk_domain ex_run_mid ch. \<forall>m.
          chunk_read_result ex_run_mid ch k = Some m
            \<longrightarrow> m = Src b0_ex H_ex (chunk_read_coordinate ex_run_mid ch) k"
    by (auto simp: mid_chunks mid_chunk_domain exr_dom_def
                   mid_rresult exr_read_def mid_rcoord exr_coord_def
                   Src_b0_ex_H_ex_ec1_100 Src_b0_ex_H_ex_ec1_200
                   Src_b0_ex_H_ex_ec3_300
             split: if_split_asm)
next
  show "\<forall>ch\<in>chunks ex_run_mid. \<forall>k\<in>chunk_domain ex_run_mid ch.
          chunk_read_result ex_run_mid ch k = Some None
            \<longrightarrow> row_absence_meaningful b0_ex H_ex ex_run_mid ch k"
    by (auto simp: mid_chunks mid_chunk_domain exr_dom_def
                   mid_rresult exr_read_def
             split: if_split_asm)
next
  show "\<forall>p \<in> set (cdc_events_of ex_run_mid).
          key_of (hist_event p) \<in> scope_of ex_run_mid
          \<and> src_le (hist_coord p) (frontier_of ex_run_mid)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (clean_prefix_of ex_run_mid)"
    using wf7_clean_prefix_cdc_coherence_redundant[of ex_run_mid] by blast
next
  show "\<forall>e c. Cdc c e \<in> set (clean_prefix_of ex_run_mid)
                 \<and> key_of e \<in> scope_of ex_run_mid
                 \<and> src_le c (frontier_of ex_run_mid)
                 \<longrightarrow> (c, e) \<in> set (cdc_events_of ex_run_mid)"
    using wf7_clean_prefix_cdc_coherence_redundant[of ex_run_mid] by blast
qed

lemma ex_run_mid_checker_wellformed: "checker_run_wellformed ex_run_mid"
  using ex_run_mid_wellformed wellformed_dblog_run_decompose by blast

lemma ex_run_mid_reflects_source: "run_reflects_source b0_ex ex_run_mid H_ex"
  using ex_run_mid_wellformed wellformed_dblog_run_decompose by blast

definition ex_cert_mid :: "(nat, nat) cert" where
  "ex_cert_mid = Cert {100, 200, 300} ec3 (clean_prefix_of ex_run_mid)"

definition ex_evidence_mid :: "(nat, nat) evidence" where
  "ex_evidence_mid = Evidence ex_run_mid"

lemma mid_cert_scope: "scope ex_cert_mid = {100, 200, 300}"
  by (simp add: scope_def ex_cert_mid_def)

lemma mid_cert_frontier: "frontier ex_cert_mid = ec3"
  by (simp add: frontier_def ex_cert_mid_def)

lemma mid_cert_clean_prefix:
  "clean_prefix ex_cert_mid = clean_prefix_of ex_run_mid"
  by (simp add: clean_prefix_def ex_cert_mid_def)

lemma mid_evidence_bound: "evidence_bound_to_cert ex_cert_mid ex_evidence_mid"
  by (simp add: evidence_bound_to_cert_def cert_accessors_agree_def
                ex_evidence_mid_def mid_cert_scope mid_cert_frontier
                mid_cert_clean_prefix mid_scope mid_frontier)

lemma mid_evidence_schema:
  "source_side_schema_supported ex_cert_mid ex_evidence_mid"
  by (simp add: source_side_schema_supported_def ex_evidence_mid_def
                ex_run_mid_checker_wellformed)

theorem mid_verify_accept: "verify ex_cert_mid ex_evidence_mid = Accept"
  by (simp add: verify_def mid_evidence_schema mid_evidence_bound)

theorem mid_faithful:
  "faithful_source_observation ex_evidence_mid b0_ex H_ex RawObservation"
  by (simp add: faithful_source_observation_def ex_evidence_mid_def
                ex_run_mid_reflects_source)

text \<open>The faithful continuation segment for \<open>(ec3, ec4]\<close> on the certified
  scope is non-empty: it carries the @{const ec4} update of key
  @{term "300::nat"}.\<close>

lemma mid_cdc_segment_ec3_ec4:
  "cdc_segment_between H_ex (scope ex_cert_mid) (frontier ex_cert_mid) ec4
     [Cdc ec4 (Update 300 3500)]"
  unfolding cdc_segment_between_def mid_cert_scope mid_cert_frontier
  by (simp add: H_ex_def ec_defs cdc_lift_def)

text \<open>Continuation corollary
  (@{text accepted_certificate_continuation_sound}), active-interval case:
  the accepted mid-frontier certificate's cut extends to the strictly
  later frontier @{const ec4} by the \<^emph>\<open>non-empty\<close> faithful continuation
  segment, whose replay applies the post-frontier source event.\<close>

theorem public_accepted_continuation_nonempty:
  "virtual_cut_state b0_ex
     (clean_prefix ex_cert_mid @ [Cdc ec4 (Update 300 3500)])
     (scope ex_cert_mid) ec4 H_ex"
  by (rule layer3_checker_substrate.accepted_certificate_continuation_sound
        [OF layer3_checker_substrate_holds mid_verify_accept mid_faithful
            wf_h_ex mid_cdc_segment_ec3_ec4])

text \<open>Continuation across frontiers (@{text virtual_cut_state_continuation})
  composed with
  state-level restriction (@{text virtual_cut_state_restrict_scope}), both
  at concrete
  instances: the mid-frontier cut restricted to the proper singleton
  sub-scope @{term "{300::nat}"} continues across @{text "(ec3, ec4]"} by
  the non-empty per-key segment.\<close>

theorem public_restricted_state_continuation:
  "virtual_cut_state b0_ex
     (clean_prefix ex_cert_mid @ [Cdc ec4 (Update 300 3500)]) {300} ec4 H_ex"
proof -
  have mid_cut: "virtual_cut_state b0_ex (clean_prefix ex_cert_mid)
                   (scope ex_cert_mid) (frontier ex_cert_mid) H_ex"
    using layer3_checker_substrate.accepted_virtual_cut_sound
            [OF layer3_checker_substrate_holds mid_verify_accept mid_faithful]
    unfolding virtual_cut_def .
  have restr: "virtual_cut_state b0_ex (clean_prefix ex_cert_mid) {300}
                 (frontier ex_cert_mid) H_ex"
    by (rule virtual_cut_state_restrict_scope[OF mid_cut])
       (simp add: mid_cert_scope)
  have seg: "cdc_segment_between H_ex {300} (frontier ex_cert_mid) ec4
               [Cdc ec4 (Update 300 3500)]"
    unfolding cdc_segment_between_def mid_cert_frontier
    by (simp add: H_ex_def ec_defs cdc_lift_def)
  show ?thesis
    by (rule virtual_cut_state_continuation[OF wf_h_ex restr seg])
qed

text \<open>Layer 4 whole-table side conditions hold at the mid frontier too
  (anchor @{const ec1}): the anchor domain is unchanged, the keys touched
  in @{text "(ec1, ec3]"} lie in the certified scope, and the six-event
  clean prefix claims no key outside it.\<close>

lemma mid_whole_table_claim_scope:
  "whole_table_claim_scope b0_ex ex_cert_mid H_ex ec1"
  unfolding whole_table_claim_scope_def
proof (intro conjI)
  show "ec1 \<le> frontier ex_cert_mid"
    using ec1_le_ec3 by (simp add: mid_cert_frontier less_eq_src_coord_def)
next
  show "anchor_complete_at_boundary b0_ex H_ex ec1 (scope ex_cert_mid)"
    unfolding anchor_complete_at_boundary_def
    using l4_anchor_domain[unfolded l4_anchor_def]
    by (simp add: mid_cert_scope)
next
  show "all_post_anchor_changes_covered H_ex ec1 (frontier ex_cert_mid)
          (scope ex_cert_mid)"
    unfolding all_post_anchor_changes_covered_def touched_between_def
    by (auto simp: mid_cert_scope H_ex_def)
next
  show "no_unclaimed_replay_keys (clean_prefix ex_cert_mid) (scope ex_cert_mid)"
    unfolding no_unclaimed_replay_keys_def replay_keys_def
    by (auto simp: mid_cert_clean_prefix mid_cert_scope mid_clean_prefix)
qed

text \<open>Layer 4 specialization
  (@{text accepted_whole_table_anchor_domain_specialization}) exercised a
  second time, at
  the accepted mid-frontier pair: unrestricted whole-table equality at
  @{const ec3}.\<close>

theorem public_mid_whole_table_equality:
  "Apply (clean_prefix ex_cert_mid) = Src b0_ex H_ex ec3"
  using layer3_checker_substrate.accepted_whole_table_anchor_domain_specialization
          [OF layer3_checker_substrate_holds mid_verify_accept mid_faithful
              mid_whole_table_claim_scope]
  by (simp add: mid_cert_frontier)

text \<open>Whole-table continuation (@{text whole_table_state_continuation})
  exercised with a
  \<^emph>\<open>non-empty\<close> @{term "UNIV :: nat set"} continuation segment: appending
  the full CDC segment for @{text "(ec3, ec4]"} extends the unrestricted
  mid-frontier equality to the unrestricted equality at @{const ec4}.\<close>

lemma mid_univ_segment:
  "cdc_segment_between H_ex UNIV ec3 ec4 [Cdc ec4 (Update 300 3500)]"
  unfolding cdc_segment_between_def
  by (simp add: H_ex_def ec_defs cdc_lift_def)

theorem public_whole_table_continuation_nonempty:
  "Apply (clean_prefix ex_cert_mid @ [Cdc ec4 (Update 300 3500)])
     = Src b0_ex H_ex ec4"
  by (rule whole_table_state_continuation
        [OF wf_h_ex public_mid_whole_table_equality mid_univ_segment])

text \<open>Coherence of continuation with direct certification: continuing the
  accepted mid-frontier certificate by the faithful @{text "(ec3, ec4]"}
  segment replays to exactly the state that the full-frontier certificate
  @{const ex_cert} certifies directly. The two certification routes ---
  verify at @{const ec4}, or verify at @{const ec3} and continue ---
  agree.\<close>

theorem public_continuation_meets_direct_certification:
  "Apply (clean_prefix ex_cert_mid @ [Cdc ec4 (Update 300 3500)])
     = Apply (clean_prefix ex_cert)"
proof -
  have direct: "Apply (clean_prefix ex_cert) = Src b0_ex H_ex ec4"
    using public_accepted_whole_table_equality
    by (simp add: ex_cert_frontier)
  show ?thesis
    by (simp add: public_whole_table_continuation_nonempty direct)
qed

subsection \<open>The non-vacuity gate theorem\<close>

lemma ex_cert_scope_nonempty: "scope ex_cert \<noteq> {}"
  by (simp add: ex_cert_scope)

lemma ex_cert_frontier_not_base: "frontier ex_cert \<noteq> c0"
  using c0_neq_ec4 by (auto simp: ex_cert_frontier)

text \<open>
  The public Layer 3 checker is non-vacuous: a concrete certificate /
  evidence pair satisfies the @{locale layer3_checker_substrate}
  predicate, is genuinely accepted by @{const verify}, and is genuinely
  faithful for a concrete deployment environment --- and at that pair
  the headline conclusions (virtual cut; unrestricted whole-table
  equality) actually fire, over a certificate with non-empty scope and
  a non-base frontier. Degenerating any public checker primitive makes
  this theorem unprovable and fails the build.
\<close>

theorem public_checker_nonvacuous:
  "\<exists>(C :: (nat, nat) cert) E b0 H Raw.
      layer3_checker_substrate C E
    \<and> verify C E = Accept
    \<and> faithful_source_observation E b0 H Raw
    \<and> scope C \<noteq> {}
    \<and> frontier C \<noteq> c0
    \<and> virtual_cut b0 C H
    \<and> Apply (clean_prefix C) = Src b0 H (frontier C)"
  using layer3_checker_substrate_holds[of ex_cert ex_evidence]
        ex_verify_accept ex_faithful
        ex_cert_scope_nonempty ex_cert_frontier_not_base
        public_accepted_virtual_cut
        public_accepted_whole_table_equality
  by blast

subsection \<open>Independence exhibits (formal non-circularity)\<close>

text \<open>
  Acceptance does not entail faithfulness: the same accepted pair is
  \<^emph>\<open>unfaithful\<close> against the empty deployment base state --- chunk
  @{term "0::nat"} recorded @{term "Some (10000::nat)"} for key
  @{term "200::nat"} at @{const ec1}, but under @{term "Map.empty"}
  the true source state there is @{term "None :: nat option"}. The
  verifier cannot see this (it never sees @{text b0} or @{text H});
  only the deployment-side faithfulness premise rules it out.
\<close>

theorem public_acceptance_not_sufficient_for_faithfulness:
  "verify ex_cert ex_evidence = Accept \<and>
   \<not> faithful_source_observation ex_evidence Map.empty H_ex RawObservation"
proof (intro conjI)
  show "verify ex_cert ex_evidence = Accept" by (rule ex_verify_accept)
next
  show "\<not> faithful_source_observation ex_evidence Map.empty H_ex RawObservation"
  proof
    assume "faithful_source_observation ex_evidence Map.empty H_ex RawObservation"
    hence refl: "run_reflects_source Map.empty ex_run H_ex"
      by (simp add: faithful_source_observation_def ex_evidence_def)
    have ch_in: "(0::nat) \<in> chunks ex_run" by (simp add: exr_chunks)
    have k_in: "(200::nat) \<in> chunk_domain ex_run 0"
      by (simp add: exr_chunk_domain exr_dom_def)
    have read: "chunk_read_result ex_run 0 200 = Some (Some 10000)"
      by (simp add: exr_rresult exr_read_def)
    from refl ch_in k_in read
    have "Some 10000 = Src Map.empty H_ex (chunk_read_coordinate ex_run 0) 200"
      unfolding run_reflects_source_def by blast
    moreover have
      "Src Map.empty H_ex (chunk_read_coordinate ex_run 0) 200 = None"
      unfolding Src_def
      using latest_src_event_H_ex_ec1_200
      by (simp add: exr_rcoord exr_coord_def)
    ultimately show False by simp
  qed
qed

text \<open>
  Faithfulness does not entail acceptance: an evidence bundle whose
  observation channel is perfectly faithful (same history, same reads)
  but whose chunk plan is broken --- @{text responsible_chunk} maps
  every key to @{term None} --- fails the mechanical check (WF1 (d)),
  so the verifier classifies it @{const Unsupported} for \<^emph>\<open>every\<close>
  certificate.
\<close>

definition ex_run_noresp :: "(nat, nat) run" where
  "ex_run_noresp =
     Run {100, 200, 300} ec4 [0, 1] H_ex H_ex
         exr_read exr_dom (\<lambda>_. None) exr_coord exr_coord exr_coord"

lemma noresp_scope: "scope_of ex_run_noresp = {100, 200, 300}"
  by (simp add: scope_of_def ex_run_noresp_def)

lemma noresp_chunks: "chunks ex_run_noresp = {0, 1}"
  by (simp add: chunks_def ex_run_noresp_def)

lemma noresp_hist: "src_history_of ex_run_noresp = H_ex"
  by (simp add: src_history_of_def ex_run_noresp_def)

lemma noresp_dom: "chunk_domain ex_run_noresp = exr_dom"
  by (simp add: chunk_domain_def ex_run_noresp_def)

lemma noresp_resp: "responsible_chunk ex_run_noresp = (\<lambda>_. None)"
  by (simp add: responsible_chunk_def ex_run_noresp_def)

lemma noresp_rcoord: "chunk_read_coordinate ex_run_noresp = exr_coord"
  by (simp add: chunk_read_coordinate_def ex_run_noresp_def)

lemma noresp_rresult: "chunk_read_result ex_run_noresp = exr_read"
  by (simp add: chunk_read_result_def ex_run_noresp_def)

lemma noresp_reflects_source:
  "run_reflects_source b0_ex ex_run_noresp H_ex"
  unfolding run_reflects_source_def
proof (intro conjI)
  show "src_history_of ex_run_noresp = H_ex" by (rule noresp_hist)
next
  show "\<forall>ch\<in>chunks ex_run_noresp. \<forall>k\<in>chunk_domain ex_run_noresp ch. \<forall>m.
          chunk_read_result ex_run_noresp ch k = Some m
            \<longrightarrow> m = Src b0_ex H_ex (chunk_read_coordinate ex_run_noresp ch) k"
    by (auto simp: noresp_chunks noresp_dom exr_dom_def
                   noresp_rresult exr_read_def noresp_rcoord exr_coord_def
                   Src_b0_ex_H_ex_ec1_100 Src_b0_ex_H_ex_ec1_200
                   Src_b0_ex_H_ex_ec3_300
             split: if_split_asm)
next
  show "\<forall>ch\<in>chunks ex_run_noresp. \<forall>k\<in>chunk_domain ex_run_noresp ch.
          chunk_read_result ex_run_noresp ch k = Some None
            \<longrightarrow> row_absence_meaningful b0_ex H_ex ex_run_noresp ch k"
    by (auto simp: noresp_chunks noresp_dom exr_dom_def
                   noresp_rresult exr_read_def
             split: if_split_asm)
qed

lemma noresp_not_checker_wellformed:
  "\<not> checker_run_wellformed ex_run_noresp"
proof
  assume wf: "checker_run_wellformed ex_run_noresp"
  \<comment> \<open>Extract the WF1 (d) conjunct structurally (the
      @{text \<open>wf_body + (elim conjE)\<close>} pattern of the Layer-2
      proofs); a @{text blast} over the whole unfolded body is
      pathologically slow here.\<close>
  note wf_body = wf[unfolded checker_run_wellformed_def]
  have wf1d:
    "\<forall>k\<in>scope_of ex_run_noresp. \<forall>ch.
       responsible_chunk ex_run_noresp k = Some ch
         \<longleftrightarrow> ch \<in> chunks ex_run_noresp \<and> k \<in> chunk_domain ex_run_noresp ch"
    using wf_body by (elim conjE)
  have k_in: "(100::nat) \<in> scope_of ex_run_noresp"
    by (simp add: noresp_scope)
  have owns0: "(0::nat) \<in> chunks ex_run_noresp
                \<and> (100::nat) \<in> chunk_domain ex_run_noresp 0"
    by (simp add: noresp_chunks noresp_dom exr_dom_def)
  from wf1d k_in owns0
  have "responsible_chunk ex_run_noresp 100 = Some 0" by blast
  thus False by (simp add: noresp_resp)
qed

theorem public_faithfulness_not_sufficient_for_acceptance:
  "faithful_source_observation (Evidence ex_run_noresp) b0_ex H_ex RawObservation
   \<and> (\<forall>C :: (nat, nat) cert. verify C (Evidence ex_run_noresp) = Unsupported)"
proof (intro conjI allI)
  show "faithful_source_observation (Evidence ex_run_noresp) b0_ex H_ex RawObservation"
    by (simp add: faithful_source_observation_def noresp_reflects_source)
next
  fix C :: "(nat, nat) cert"
  show "verify C (Evidence ex_run_noresp) = Unsupported"
    by (simp add: verify_def source_side_schema_supported_def
                  noresp_not_checker_wellformed)
qed

text \<open>The @{const Reject} branch is also reachable: in-schema evidence
  not bound to the presented certificate (here: an empty-scope
  certificate against the accepting evidence) is rejected.\<close>

theorem public_checker_rejects_unbound:
  "verify (Cert {} ec4 (clean_prefix_of ex_run)) ex_evidence = Reject"
  by (simp add: verify_def source_side_schema_supported_def
                evidence_bound_to_cert_def cert_accessors_agree_def
                ex_evidence_def ex_run_checker_wellformed
                scope_def frontier_def clean_prefix_def
                exr_scope exr_frontier)

end
