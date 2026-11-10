(*  Title:   Layer2_Fixtures_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer2_Fixtures_Inst
  imports
    Virtual_Cut
    Layer01_Witnesses_Inst
    Layer01_Virtual_Cut_Example_Inst
    Layer01_Witness_Topics_Inst
    Layer01_Fixtures_Inst
begin

section \<open>Constructed Layer 2 fixtures\<close>

text \<open>
  Constructed Layer 2 fixtures: the run-dependent Layer 2 fixture facts,
  established over the constructed run models of the Layer 0/1 witness and
  fixture theories. Every object mentioned is explicitly constructed; the
  theory introduces no axioms.

  The Layer 2 fixture facts come in three kinds:

    \<^item> \<^bold>\<open>positive Layer 2 witness lifts\<close>: the minimum-viable witness, the
        worked example, and the Topic 1/2 witnesses, established over the
        constructed run interpretations
        @{text wit_model} / @{text ex_model} / @{text t1_model} / @{text t2_model}
        and lifted through the \<^emph>\<open>locale\<close> Layer 2 theorem
        @{thm [source] dblog_run_substrate.wellformed_run_implies_virtual_cut},
        which each interpretation specializes to its constructed run. (Its
        non-locale counterpart at the concrete @{type run} carrier is
        @{thm [source] Virtual_Cut.wellformed_run_implies_virtual_cut}.)

    \<^item> \<^bold>\<open>WF-clause rejection rows\<close> (aliases of the Layer 1 negative fixtures,
        because Layer 2's theorem ranges over the same @{const wellformed_dblog_run}
        predicate). Re-exported here over the \<^emph>\<open>constructed\<close> Layer 1 fixtures of
        @{text Layer01_Fixtures_Inst}, i.e. over the
        @{text cmodel} interpretation and the @{text "crun_\<dots>"} runs.

    \<^item> \<^bold>\<open>canonical-clean-prefix structural + frontier-off-by-one rows\<close>
        (@{text "fix_layer2_misordered_clean_prefix_rejected"}
        and siblings). These are proved directly against the carrier-independent
        global @{const canonical_clean_prefix} / @{const cdc_event_replays} and
        mention no run carrier, so they need no constructed counterpart; they
        live in @{text Layer2_Fixtures_Core}.
\<close>


subsection \<open>Positive Layer 2 witness lifts over the constructed runs\<close>

text \<open>Each lift specializes the locale Layer 2 theorem ---
  @{text wellformed_run_implies_virtual_cut} under the
  @{text dblog_run_substrate} qualifier ---
  to a constructed run via its interpretation, discharged by that run's
  constructed wellformedness fact. The run-model @{text "_Inst"} theories import
  the Layer 2 locale extension @{text DBLog_Run_Substrate_Layer2},
  so each interpretation registers the qualified Layer 2 fact at declaration
  time (e.g. @{text wellformed_run_implies_virtual_cut} under the
  @{text wit_model} qualifier). The conclusions name the constructed
  (@{typ unit}) run @{term "()"} and the model accessors, so every object
  mentioned is explicitly constructed.\<close>

theorem layer2_witness_virtual_cut_state_constructed:
  "virtual_cut_state b0_w (wit_model.clean_prefix_of ())
                     (wit_cscope ()) (wit_cfrontier ()) H_w"
  unfolding virtual_cut_state_def
  using wit_model.wellformed_run_implies_virtual_cut
          [OF wit_model_wellformed, unfolded virtual_cut_state_def] .

theorem layer2_worked_example_virtual_cut_state_constructed:
  "virtual_cut_state b0_ex (ex_model.clean_prefix_of ())
                     (cscope_of ()) (cfrontier_of ()) H_ex"
  unfolding virtual_cut_state_def
  using ex_model.wellformed_run_implies_virtual_cut
          [OF ex_model_wellformed, unfolded virtual_cut_state_def] .

theorem layer2_topic1_virtual_cut_state_constructed:
  "virtual_cut_state b0_t1 (t1_model.clean_prefix_of ())
                     (t1_cscope ()) (t1_cfrontier ()) H_t1"
  unfolding virtual_cut_state_def
  using t1_model.wellformed_run_implies_virtual_cut
          [OF t1_model_wellformed, unfolded virtual_cut_state_def] .

theorem layer2_topic2_virtual_cut_state_constructed:
  "virtual_cut_state b0_t2 (t2_model.clean_prefix_of ())
                     (t2_cscope ()) (t2_cfrontier ()) H_t2"
  unfolding virtual_cut_state_def
  using t2_model.wellformed_run_implies_virtual_cut
          [OF t2_model_wellformed, unfolded virtual_cut_state_def] .


subsection \<open>WF-clause rejection rows over the constructed Layer 1 fixtures\<close>

text \<open>Layer 2 protects the hypotheses of the Layer 2 theorem; the rejection
  shapes are exactly the constructed @{const cmodel.wellformed_dblog_run}
  rejections of @{text Layer01_Fixtures_Inst}, re-exported
  here under their Layer 2 names.\<close>

theorem fix_layer2_missing_cdc_event_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_md crun_md H_md"
  by (rule fix_miss_dom_rejected_constructed)

theorem fix_layer2_overlapping_chunk_scope_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_ov crun_ov H_ov"
  by (rule fix_overlap_rejected_constructed)

theorem fix_layer2_same_coordinate_cdc_order_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_do crun_do H_do"
  by (rule fix_dup_order_rejected_constructed)

\<comment> \<open>Alias of @{text fix_layer2_same_coordinate_cdc_order_rejected_constructed},
     mirroring the dual-named Layer 2 fixture-table row.\<close>
theorem fix_layer2_cdc_events_out_of_source_order_same_coord_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_do crun_do H_do"
  by (rule fix_dup_order_rejected_constructed)

theorem fix_layer2_hallucinated_cdc_event_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_ec crun_ec []"
  by (rule fix_extra_cdc_rejected_constructed)

theorem fix_layer2_future_refresh_from_chunk_read_after_frontier_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_caf crun_caf H_caf"
  by (rule fix_after_f_rejected_constructed)

theorem fix_layer2_wrong_chunk_read_value_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_wr crun_wr H_wr"
  by (rule fix_wrong_r_rejected_constructed)


subsection \<open>Fixture bundle\<close>

theorem layer2_fixture_bundle_constructed:
  "virtual_cut_state b0_w (wit_model.clean_prefix_of ())
                     (wit_cscope ()) (wit_cfrontier ()) H_w
   \<and> \<not> cmodel.wellformed_dblog_run b0_md crun_md H_md
   \<and> \<not> cmodel.wellformed_dblog_run b0_do crun_do H_do"
  using layer2_witness_virtual_cut_state_constructed
        fix_layer2_missing_cdc_event_rejected_constructed
        fix_layer2_same_coordinate_cdc_order_rejected_constructed
  by blast

text \<open>
  The run-dependent Layer 2 fixture rows hold over the constructed runs and
  the constructed Layer 1 fixtures. Together with the carrier-independent
  canonical-clean-prefix and frontier-off-by-one rows of
  @{text Layer2_Fixtures_Core}, this covers the whole Layer 2 fixture bundle ---
  with no axioms anywhere.
\<close>

end
