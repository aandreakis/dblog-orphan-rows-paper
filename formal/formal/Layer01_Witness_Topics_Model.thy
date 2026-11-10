(*  Title:   Layer01_Witness_Topics_Model.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Witness_Topics_Model
  imports Layer01_Witness_Topics_Core
begin

section \<open>Constructed models for the Topic 1 and Topic 2 witnesses\<close>

text \<open>
  Each section exhibits the explicit model of one topic's witness data: a
  one-point run carrier (@{typ unit}), a small chunk datatype, and concrete
  accessor functions returning the intended witness values.
  @{text Layer01_Witness_Topics_Inst} interprets the run-substrate locale
  (@{text dblog_run_substrate}) at these models, so the per-topic
  positive-witness theorems (@{text topic1_positive_witness_constructed},
  @{text topic2_positive_witness_constructed}) are established
  constructively, with no axioms. The carrier-independent witness data
  (@{const b0_t1} / @{const H_t1}, @{const b0_t2} / @{const H_t2}, and their
  computation lemmas) comes from the imported
  @{text Layer01_Witness_Topics_Core}.
\<close>

subsection \<open>Topic 1: single chunk, one CDC event\<close>

datatype t1_cchunk = T1Ch

definition t1_cscope :: "unit \<Rightarrow> nat set" where
  "t1_cscope _ = {1}"

definition t1_cfrontier :: "unit \<Rightarrow> frontier" where
  "t1_cfrontier _ = ct1"

definition t1_cchunks :: "unit \<Rightarrow> t1_cchunk set" where
  "t1_cchunks _ = {T1Ch}"

definition t1_cchunks_list :: "unit \<Rightarrow> t1_cchunk list" where
  "t1_cchunks_list _ = [T1Ch]"

definition t1_cchunk_domain :: "unit \<Rightarrow> t1_cchunk \<Rightarrow> nat set" where
  "t1_cchunk_domain _ _ = {1}"

definition t1_cresponsible_chunk :: "unit \<Rightarrow> nat \<Rightarrow> t1_cchunk option" where
  "t1_cresponsible_chunk _ k = (if k = 1 then Some T1Ch else None)"

definition t1_cchunk_read_coordinate :: "unit \<Rightarrow> t1_cchunk \<Rightarrow> src_coord" where
  "t1_cchunk_read_coordinate _ _ = c0"

definition t1_cchunk_lower_watermark :: "unit \<Rightarrow> t1_cchunk \<Rightarrow> src_coord" where
  "t1_cchunk_lower_watermark _ _ = c0"

definition t1_cchunk_upper_watermark :: "unit \<Rightarrow> t1_cchunk \<Rightarrow> src_coord" where
  "t1_cchunk_upper_watermark _ _ = c0"

definition t1_csrc_history_of :: "unit \<Rightarrow> (nat, nat) src_history" where
  "t1_csrc_history_of _ = H_t1"

definition t1_ccdc_events_of :: "unit \<Rightarrow> (nat, nat) src_history" where
  "t1_ccdc_events_of _ = H_t1"

definition t1_cchunk_read_result :: "unit \<Rightarrow> t1_cchunk \<Rightarrow> nat \<Rightarrow> nat option option" where
  "t1_cchunk_read_result _ ch k = (if ch = T1Ch \<and> k = 1 then Some (Some 5) else None)"

theorem t1_model_accessor_values:
  "t1_cscope () = {1}
   \<and> t1_cfrontier () = ct1
   \<and> t1_cchunks () = {T1Ch}
   \<and> t1_cchunk_domain () T1Ch = {1}
   \<and> t1_cresponsible_chunk () 1 = Some T1Ch
   \<and> (\<forall>k. k \<noteq> 1 \<longrightarrow> t1_cresponsible_chunk () k = None)
   \<and> t1_cchunk_read_coordinate () T1Ch = c0
   \<and> t1_cchunk_lower_watermark () T1Ch = c0
   \<and> t1_cchunk_upper_watermark () T1Ch = c0
   \<and> t1_csrc_history_of () = H_t1
   \<and> t1_cchunk_read_result () T1Ch 1 = Some (Some 5)
   \<and> t1_ccdc_events_of () = H_t1
   \<and> t1_cchunks_list () = [T1Ch]
   \<and> set (t1_cchunks_list ()) = t1_cchunks ()
   \<and> distinct (t1_cchunks_list ())"
  by (auto simp: t1_cscope_def t1_cfrontier_def t1_cchunks_def
                 t1_cchunks_list_def t1_cchunk_domain_def
                 t1_cresponsible_chunk_def t1_cchunk_read_coordinate_def
                 t1_cchunk_lower_watermark_def t1_cchunk_upper_watermark_def
                 t1_csrc_history_of_def t1_ccdc_events_of_def
                 t1_cchunk_read_result_def)

subsection \<open>Topic 2: two chunks partitioning the scope, empty history\<close>

datatype t2_cchunk = T2ChA | T2ChB

definition t2_cscope :: "unit \<Rightarrow> nat set" where
  "t2_cscope _ = {10, 20}"

definition t2_cfrontier :: "unit \<Rightarrow> frontier" where
  "t2_cfrontier _ = c0"

definition t2_cchunks :: "unit \<Rightarrow> t2_cchunk set" where
  "t2_cchunks _ = {T2ChA, T2ChB}"

definition t2_cchunks_list :: "unit \<Rightarrow> t2_cchunk list" where
  "t2_cchunks_list _ = [T2ChA, T2ChB]"

definition t2_cchunk_domain :: "unit \<Rightarrow> t2_cchunk \<Rightarrow> nat set" where
  "t2_cchunk_domain _ ch = (case ch of T2ChA \<Rightarrow> {10} | T2ChB \<Rightarrow> {20})"

definition t2_cresponsible_chunk :: "unit \<Rightarrow> nat \<Rightarrow> t2_cchunk option" where
  "t2_cresponsible_chunk _ k =
     (if k = 10 then Some T2ChA else if k = 20 then Some T2ChB else None)"

definition t2_cchunk_read_coordinate :: "unit \<Rightarrow> t2_cchunk \<Rightarrow> src_coord" where
  "t2_cchunk_read_coordinate _ _ = c0"

definition t2_cchunk_lower_watermark :: "unit \<Rightarrow> t2_cchunk \<Rightarrow> src_coord" where
  "t2_cchunk_lower_watermark _ _ = c0"

definition t2_cchunk_upper_watermark :: "unit \<Rightarrow> t2_cchunk \<Rightarrow> src_coord" where
  "t2_cchunk_upper_watermark _ _ = c0"

definition t2_csrc_history_of :: "unit \<Rightarrow> (nat, nat) src_history" where
  "t2_csrc_history_of _ = H_t2"

definition t2_ccdc_events_of :: "unit \<Rightarrow> (nat, nat) src_history" where
  "t2_ccdc_events_of _ = H_t2"

definition t2_cchunk_read_result :: "unit \<Rightarrow> t2_cchunk \<Rightarrow> nat \<Rightarrow> nat option option" where
  "t2_cchunk_read_result _ ch k =
     (if ch = T2ChA \<and> k = 10 then Some (Some 100)
      else if ch = T2ChB \<and> k = 20 then Some (Some 200)
      else None)"

theorem t2_model_accessor_values:
  "T2ChA \<noteq> T2ChB
   \<and> t2_cscope () = {10, 20}
   \<and> t2_cfrontier () = c0
   \<and> t2_cchunks () = {T2ChA, T2ChB}
   \<and> t2_cchunk_domain () T2ChA = {10}
   \<and> t2_cchunk_domain () T2ChB = {20}
   \<and> t2_cresponsible_chunk () 10 = Some T2ChA
   \<and> t2_cresponsible_chunk () 20 = Some T2ChB
   \<and> (\<forall>k. k \<noteq> 10 \<longrightarrow> k \<noteq> 20 \<longrightarrow> t2_cresponsible_chunk () k = None)
   \<and> t2_cchunk_read_coordinate () T2ChA = c0
   \<and> t2_cchunk_read_coordinate () T2ChB = c0
   \<and> t2_cchunk_lower_watermark () T2ChA = c0
   \<and> t2_cchunk_upper_watermark () T2ChA = c0
   \<and> t2_cchunk_lower_watermark () T2ChB = c0
   \<and> t2_cchunk_upper_watermark () T2ChB = c0
   \<and> t2_csrc_history_of () = H_t2
   \<and> t2_cchunk_read_result () T2ChA 10 = Some (Some 100)
   \<and> t2_cchunk_read_result () T2ChB 20 = Some (Some 200)
   \<and> t2_ccdc_events_of () = H_t2
   \<and> t2_cchunks_list () = [T2ChA, T2ChB]
   \<and> set (t2_cchunks_list ()) = t2_cchunks ()
   \<and> distinct (t2_cchunks_list ())"
  by (auto simp: t2_cscope_def t2_cfrontier_def t2_cchunks_def
                 t2_cchunks_list_def t2_cchunk_domain_def
                 t2_cresponsible_chunk_def t2_cchunk_read_coordinate_def
                 t2_cchunk_lower_watermark_def t2_cchunk_upper_watermark_def
                 t2_csrc_history_of_def t2_ccdc_events_of_def
                 t2_cchunk_read_result_def)

text \<open>
  Both topic configurations are realized by explicit constructions.
  @{text Layer01_Witness_Topics_Inst} interprets the run-substrate locale at
  each model and establishes the corresponding positive-witness theorem over
  it.
\<close>

end
