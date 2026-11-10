(*  Title:   Layer01_Virtual_Cut_Example_Model.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Virtual_Cut_Example_Model
  imports Layer01_Virtual_Cut_Example_Core
begin

section \<open>Constructed model for the running-example run configuration\<close>

text \<open>
  \<^bold>\<open>Purpose.\<close> This theory exhibits the explicit model of the running
  example's run configuration: a one-point run carrier (@{typ unit}), a
  two-element chunk type, and concrete accessor functions giving the
  example's Layer 1 accessor values (scope, frontier, chunk domains,
  responsible chunk, watermarks, read coordinates, read results, source
  history, observed CDC events, chunk enumeration).

  @{text Layer01_Virtual_Cut_Example_Inst} interprets the run-substrate
  locale (@{text dblog_run_substrate}) at this model and proves, over it,
  that the example run is wellformed (@{text ex_model_wellformed}) and
  satisfies the virtual-cut equality (@{text ex_model_virtual_cut_holds})
  --- so the running example is established constructively, with no axioms.
  The constructed Layer 3 / Layer 4 witness interpretation
  (@{text Layer3_Witnesses_Inst}) reuses the same model as its run side.

  The carrier-independent example data this model realizes (@{const b0_ex},
  @{const H_ex}, the @{const Src} / @{const latest_src_event} computation
  lemmas, @{thm [source] wf_h_ex}) comes from the imported
  @{theory DBLog_Virtual_Cuts.Layer01_Virtual_Cut_Example_Core}.
\<close>

subsection \<open>Concrete carriers and accessor functions\<close>

text \<open>
  A two-element chunk type. Datatype distinctness gives @{text "ChA \<noteq> ChB"}
  for free, so the chunk enumeration @{text "[ChA, ChB]"} is duplicate-free
  --- the shape the run-substrate locale's chunk-enumeration assumptions
  require.
\<close>

datatype cchunk = ChA | ChB

text \<open>
  The run carrier is a single point (@{typ unit}); the example concerns one
  run only, so one inhabitant suffices. Each accessor is a total function
  returning the example's intended value.
\<close>

definition cscope_of :: "unit \<Rightarrow> nat set" where
  "cscope_of _ = {100, 200, 300}"

definition cfrontier_of :: "unit \<Rightarrow> frontier" where
  "cfrontier_of _ = ec4"

definition cchunks :: "unit \<Rightarrow> cchunk set" where
  "cchunks _ = {ChA, ChB}"

definition cchunks_list :: "unit \<Rightarrow> cchunk list" where
  "cchunks_list _ = [ChA, ChB]"

definition cchunk_domain :: "unit \<Rightarrow> cchunk \<Rightarrow> nat set" where
  "cchunk_domain _ ch = (case ch of ChA \<Rightarrow> {100, 200} | ChB \<Rightarrow> {300})"

definition cresponsible_chunk :: "unit \<Rightarrow> nat \<Rightarrow> cchunk option" where
  "cresponsible_chunk _ k =
     (if k = 100 \<or> k = 200 then Some ChA
      else if k = 300 then Some ChB else None)"

definition cchunk_read_coordinate :: "unit \<Rightarrow> cchunk \<Rightarrow> src_coord" where
  "cchunk_read_coordinate _ ch = (case ch of ChA \<Rightarrow> ec1 | ChB \<Rightarrow> ec3)"

definition cchunk_lower_watermark :: "unit \<Rightarrow> cchunk \<Rightarrow> src_coord" where
  "cchunk_lower_watermark _ ch = (case ch of ChA \<Rightarrow> ec1 | ChB \<Rightarrow> ec3)"

definition cchunk_upper_watermark :: "unit \<Rightarrow> cchunk \<Rightarrow> src_coord" where
  "cchunk_upper_watermark _ ch = (case ch of ChA \<Rightarrow> ec1 | ChB \<Rightarrow> ec3)"

definition csrc_history_of :: "unit \<Rightarrow> (nat, nat) src_history" where
  "csrc_history_of _ = H_ex"

definition ccdc_events_of :: "unit \<Rightarrow> (nat, nat) src_history" where
  "ccdc_events_of _ = H_ex"

definition cchunk_read_result :: "unit \<Rightarrow> cchunk \<Rightarrow> nat \<Rightarrow> nat option option" where
  "cchunk_read_result _ ch k =
     (if ch = ChA \<and> k = 100 then Some (Some 3000)
      else if ch = ChA \<and> k = 200 then Some (Some 10000)
      else if ch = ChB \<and> k = 300 then Some (Some 2500)
      else None)"

subsection \<open>The model realizes the example's accessor values\<close>

text \<open>
  Each conjunct below records one accessor value of the constructed model,
  ending with the two chunk-enumeration facts
  (@{text "set (cchunks_list ()) = cchunks ()"} and
  @{text "distinct (cchunks_list ())"}) that the run-substrate locale
  assumes. @{text Layer01_Virtual_Cut_Example_Inst} re-derives these
  equations as its per-accessor lemmas when interpreting the locale at this
  model.
\<close>

theorem running_example_model_accessor_values:
  "ChA \<noteq> ChB
   \<and> cscope_of () = {100, 200, 300}
   \<and> cfrontier_of () = ec4
   \<and> cchunks () = {ChA, ChB}
   \<and> cchunk_domain () ChA = {100, 200}
   \<and> cchunk_domain () ChB = {300}
   \<and> cresponsible_chunk () 100 = Some ChA
   \<and> cresponsible_chunk () 200 = Some ChA
   \<and> cresponsible_chunk () 300 = Some ChB
   \<and> (\<forall>k. k \<noteq> 100 \<longrightarrow> k \<noteq> 200 \<longrightarrow> k \<noteq> 300 \<longrightarrow> cresponsible_chunk () k = None)
   \<and> cchunk_read_coordinate () ChA = ec1
   \<and> cchunk_read_coordinate () ChB = ec3
   \<and> cchunk_lower_watermark () ChA = ec1
   \<and> cchunk_upper_watermark () ChA = ec1
   \<and> cchunk_lower_watermark () ChB = ec3
   \<and> cchunk_upper_watermark () ChB = ec3
   \<and> csrc_history_of () = H_ex
   \<and> cchunk_read_result () ChA 100 = Some (Some 3000)
   \<and> cchunk_read_result () ChA 200 = Some (Some 10000)
   \<and> cchunk_read_result () ChB 300 = Some (Some 2500)
   \<and> ccdc_events_of () = H_ex
   \<and> cchunks_list () = [ChA, ChB]
   \<and> set (cchunks_list ()) = cchunks ()
   \<and> distinct (cchunks_list ())"
  by (auto simp: cscope_of_def cfrontier_of_def cchunks_def cchunks_list_def
                 cchunk_domain_def cresponsible_chunk_def
                 cchunk_read_coordinate_def cchunk_lower_watermark_def
                 cchunk_upper_watermark_def csrc_history_of_def
                 ccdc_events_of_def cchunk_read_result_def)

text \<open>
  \<^bold>\<open>Conclusion.\<close> The running example's accessor values are jointly
  realized by an explicit construction: a concrete run with exactly these
  values exists. @{text Layer01_Virtual_Cut_Example_Inst} interprets the
  run-substrate locale at this model and proves the example's
  wellformedness (@{text ex_model_wellformed}) and virtual-cut equality
  (@{text ex_model_virtual_cut_holds}) for it.
\<close>

end
