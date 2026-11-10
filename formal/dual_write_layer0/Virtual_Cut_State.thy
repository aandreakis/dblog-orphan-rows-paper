(*  Title:   Virtual_Cut_State.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Shared virtual-cut-state interface for DBLog_Virtual_Cuts and
    Dual_Write_Core.  WS4a factors this predicate into the shared Layer-0 entry
    so both developments use one HOL constant rather than copied definitions.
*)

theory Virtual_Cut_State
  imports Source_History Replay Scope
begin

section \<open>Shared virtual-cut-state interface\<close>

definition virtual_cut_state
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) replay_event list \<Rightarrow> 'k set
      \<Rightarrow> frontier \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "virtual_cut_state b0 \<sigma> K f H \<longleftrightarrow>
     restrict (Apply \<sigma>) K = restrict (Src b0 H f) K"

end
