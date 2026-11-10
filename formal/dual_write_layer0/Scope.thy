(*  Title:   Scope.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Scope
  imports Main
begin

section \<open>Layer 0: key-scope restriction\<close>

text \<open>
  Layer 0: key-scope restriction of a per-key state.

  Given a per-key state @{text x} and a key set @{text K}, the
  restriction @{text "x \<restriction> K"} keeps exactly the entries whose
  key lies in @{text K} and drops the rest. The paper writes this
  with the restriction operator @{text \<open>\<restriction>\<close>}; the formalism
  exposes it as the plain function @{text restrict}, whose semantics
  are standard map-restriction.
\<close>

definition restrict :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> ('k \<rightharpoonup> 'v)"
  where "restrict m K = (\<lambda>k. if k \<in> K then m k else None)"

text \<open>
  @{text restrict} coincides with the library's map restriction
  @{text "m |` K"}. The development keeps its own constant so that
  statements read with the paper's vocabulary; the bridge below makes
  the equivalence available wherever library lemmas about
  @{text restrict_map} are preferable.
\<close>

lemma restrict_eq_restrict_map: "restrict m K = m |` K"
  by (rule ext) (simp add: restrict_def restrict_map_def)

end
