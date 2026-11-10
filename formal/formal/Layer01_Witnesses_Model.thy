(*  Title:   Layer01_Witnesses_Model.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Witnesses_Model
  imports Layer01_Witnesses_Core
begin

section \<open>Constructed model for the minimum-viable wellformed-run witness\<close>

text \<open>
  This theory exhibits the explicit model of the minimum-viable wellformed-run
  witness data: a one-point run carrier (@{typ unit}), a two-element chunk
  type, and concrete accessor functions giving the witness run scope
  @{term "{0::nat, 1}"}, frontier @{const c2_w}, and two chunks with singleton
  domains. @{text Layer01_Witnesses_Inst} interprets the run-substrate locale
  (@{text dblog_run_substrate}) at this model, so the witness facts --- the
  run-wellformedness fact and the Layer 1 positive-witness existential --- are
  established constructively, with no axioms.

  The carrier-independent witness data this model realizes (@{const b0_w},
  @{const H_w}, the @{const Src} / @{const latest_src_event} computation
  lemmas, @{thm [source] wf_h_w}) comes from the imported
  @{theory DBLog_Virtual_Cuts.Layer01_Witnesses_Core}.
\<close>

datatype wit_cchunk = WCh1 | WCh2

definition wit_cscope :: "unit \<Rightarrow> nat set" where
  "wit_cscope _ = {0, 1}"

definition wit_cfrontier :: "unit \<Rightarrow> frontier" where
  "wit_cfrontier _ = c2_w"

definition wit_cchunks :: "unit \<Rightarrow> wit_cchunk set" where
  "wit_cchunks _ = {WCh1, WCh2}"

definition wit_cchunks_list :: "unit \<Rightarrow> wit_cchunk list" where
  "wit_cchunks_list _ = [WCh1, WCh2]"

definition wit_cchunk_domain :: "unit \<Rightarrow> wit_cchunk \<Rightarrow> nat set" where
  "wit_cchunk_domain _ ch = (case ch of WCh1 \<Rightarrow> {0} | WCh2 \<Rightarrow> {1})"

definition wit_cresponsible_chunk :: "unit \<Rightarrow> nat \<Rightarrow> wit_cchunk option" where
  "wit_cresponsible_chunk _ k =
     (if k = 0 then Some WCh1 else if k = 1 then Some WCh2 else None)"

definition wit_cchunk_read_coordinate :: "unit \<Rightarrow> wit_cchunk \<Rightarrow> src_coord" where
  "wit_cchunk_read_coordinate _ ch = (case ch of WCh1 \<Rightarrow> c0 | WCh2 \<Rightarrow> c2_w)"

definition wit_cchunk_lower_watermark :: "unit \<Rightarrow> wit_cchunk \<Rightarrow> src_coord" where
  "wit_cchunk_lower_watermark _ ch = (case ch of WCh1 \<Rightarrow> c0 | WCh2 \<Rightarrow> c2_w)"

definition wit_cchunk_upper_watermark :: "unit \<Rightarrow> wit_cchunk \<Rightarrow> src_coord" where
  "wit_cchunk_upper_watermark _ ch = (case ch of WCh1 \<Rightarrow> c0 | WCh2 \<Rightarrow> c2_w)"

definition wit_csrc_history_of :: "unit \<Rightarrow> (nat, nat) src_history" where
  "wit_csrc_history_of _ = H_w"

definition wit_ccdc_events_of :: "unit \<Rightarrow> (nat, nat) src_history" where
  "wit_ccdc_events_of _ = H_w"

definition wit_cchunk_read_result :: "unit \<Rightarrow> wit_cchunk \<Rightarrow> nat \<Rightarrow> nat option option" where
  "wit_cchunk_read_result _ ch k =
     (if ch = WCh1 \<and> k = 0 then Some None
      else if ch = WCh2 \<and> k = 1 then Some None
      else None)"

theorem wit_model_accessor_values:
  "WCh1 \<noteq> WCh2
   \<and> wit_cscope () = {0, 1}
   \<and> wit_cfrontier () = c2_w
   \<and> wit_cchunks () = {WCh1, WCh2}
   \<and> wit_cchunk_domain () WCh1 = {0}
   \<and> wit_cchunk_domain () WCh2 = {1}
   \<and> wit_cresponsible_chunk () 0 = Some WCh1
   \<and> wit_cresponsible_chunk () 1 = Some WCh2
   \<and> (\<forall>k. k \<noteq> 0 \<longrightarrow> k \<noteq> 1 \<longrightarrow> wit_cresponsible_chunk () k = None)
   \<and> wit_cchunk_read_coordinate () WCh1 = c0
   \<and> wit_cchunk_read_coordinate () WCh2 = c2_w
   \<and> wit_cchunk_lower_watermark () WCh1 = c0
   \<and> wit_cchunk_upper_watermark () WCh1 = c0
   \<and> wit_cchunk_lower_watermark () WCh2 = c2_w
   \<and> wit_cchunk_upper_watermark () WCh2 = c2_w
   \<and> wit_csrc_history_of () = H_w
   \<and> wit_cchunk_read_result () WCh1 0 = Some None
   \<and> wit_cchunk_read_result () WCh2 1 = Some None
   \<and> wit_ccdc_events_of () = H_w
   \<and> wit_cchunks_list () = [WCh1, WCh2]
   \<and> set (wit_cchunks_list ()) = wit_cchunks ()
   \<and> distinct (wit_cchunks_list ())"
  by (auto simp: wit_cscope_def wit_cfrontier_def wit_cchunks_def
                 wit_cchunks_list_def wit_cchunk_domain_def
                 wit_cresponsible_chunk_def wit_cchunk_read_coordinate_def
                 wit_cchunk_lower_watermark_def wit_cchunk_upper_watermark_def
                 wit_csrc_history_of_def wit_ccdc_events_of_def
                 wit_cchunk_read_result_def)

text \<open>
  The conjunction above gathers the model's accessor values in one place ---
  the witness configuration is realized by an explicit construction.
  @{text Layer01_Witnesses_Inst} re-derives these values as per-accessor
  lemmas and builds the wellformedness and positive-witness theorems
  (@{text wit_model_wellformed},
  @{text wellformed_run_positive_witness_constructed}) on top of them.
\<close>

end
