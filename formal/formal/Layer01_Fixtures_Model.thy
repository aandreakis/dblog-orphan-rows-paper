(*  Title:   Layer01_Fixtures_Model.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Fixtures_Model
  imports Dual_Write_Layer0.Source_Coordinates
begin

section \<open>Concrete run models for the Layer 0/1 fixtures\<close>

text \<open>
  This theory exhibits the explicit run models of the Layer 0/1 fixture
  family. It gives one reusable concrete run carrier --- a record
  @{text crun} whose fields are the Layer 1 accessors, with chunks modeled
  as @{typ nat} --- and, for each fixture, a @{text crun} value realizing
  exactly the accessor values that fixture's targeted wellformedness clause
  references, plus the chunk-enumeration shape captured by
  @{text crun_wellshaped} (the chunk enumeration is a duplicate-free listing
  of the chunk set). Each @{text "*_model_values"} lemma is proved by
  @{method simp} and records those values in one place as a reader-facing
  accessor-value summary; no later proof consumes these lemmas --- the
  interpretation proofs in @{text Layer01_Fixtures_Inst} evaluate the model
  definitions directly.

  @{text Layer01_Fixtures_Inst} interprets the run-substrate locale
  (@{text dblog_run_substrate}) at the @{text crun} carrier and proves each
  negative fixture's rejection --- and the empty-scope boundary's acceptance
  --- over the corresponding value, so every fixture result is established
  constructively, with no axioms.

  Unconstrained accessors are left at their @{text default_crun} values: a
  fixture constrains only what its clause needs, so the model only needs to
  match those. Consequently an instance may violate clauses other than its
  documented target; each rejection proof in @{text Layer01_Fixtures_Inst}
  pivots on the documented clause alone. The source coordinates
  (@{const c0} and the fixtures' own
  @{text "*_c1"} coordinates) are @{const coord_of_nat} definitions from
  @{theory Dual_Write_Layer0.Source_Coordinates}, which also proves their
  order lemmas (@{text "src_lt c0 *"}). The Layer 0 source fixture needs no
  run model: its history @{text H_c0} is a concrete @{command definition} in
  @{text Layer01_Fixtures_Core}, with no run carrier involved.
\<close>

subsection \<open>A reusable concrete run model\<close>

record crun =
  cr_scope        :: "nat set"
  cr_frontier     :: "src_coord"
  cr_chunks       :: "nat set"
  cr_chunks_list  :: "nat list"
  cr_dom          :: "nat \<Rightarrow> nat set"
  cr_resp         :: "nat \<Rightarrow> nat option"
  cr_rcoord       :: "nat \<Rightarrow> src_coord"
  cr_lwm          :: "nat \<Rightarrow> src_coord"
  cr_uwm          :: "nat \<Rightarrow> src_coord"
  cr_src_history  :: "(nat, nat) src_history"
  cr_cdc          :: "(nat, nat) src_history"
  cr_rresult      :: "nat \<Rightarrow> nat \<Rightarrow> nat option option"

definition default_crun :: crun where
  "default_crun =
     \<lparr> cr_scope = {}, cr_frontier = c0, cr_chunks = {}, cr_chunks_list = [],
       cr_dom = (\<lambda>_. {}), cr_resp = (\<lambda>_. None), cr_rcoord = (\<lambda>_. c0),
       cr_lwm = (\<lambda>_. c0), cr_uwm = (\<lambda>_. c0),
       cr_src_history = [], cr_cdc = [], cr_rresult = (\<lambda>_ _. None) \<rparr>"

text \<open>The only global constraint on the run interface: the chunk enumeration
  is a duplicate-free listing of the chunk set.\<close>

definition crun_wellshaped :: "crun \<Rightarrow> bool" where
  "crun_wellshaped r \<longleftrightarrow> set (cr_chunks_list r) = cr_chunks r \<and> distinct (cr_chunks_list r)"

lemmas crun_simps = default_crun_def crun_wellshaped_def

subsection \<open>WF1 (b): overlapping chunk domains (@{text fix_overlap})\<close>

definition crun_ov :: crun where
  "crun_ov = default_crun
     \<lparr> cr_chunks := {0, 1}, cr_chunks_list := [0, 1],
       cr_dom := (\<lambda>n. if n = 0 then {1, 2} else if n = 1 then {2, 3} else {}) \<rparr>"

lemma ov_fixture_model_values:
  "(0::nat) \<noteq> 1
   \<and> cr_chunks crun_ov = {0, 1}
   \<and> cr_dom crun_ov 0 = {1, 2}
   \<and> cr_dom crun_ov 1 = {2, 3}
   \<and> crun_wellshaped crun_ov"
  by (simp add: crun_simps crun_ov_def)

subsection \<open>WF1 (c): chunk owns out-of-scope key (@{text fix_miss_cov})\<close>

definition crun_mc :: crun where
  "crun_mc = default_crun
     \<lparr> cr_scope := {1}, cr_chunks := {0}, cr_chunks_list := [0],
       cr_dom := (\<lambda>n. if n = 0 then {1, 2} else {}) \<rparr>"

lemma mc_fixture_model_values:
  "cr_scope crun_mc = {1}
   \<and> cr_chunks crun_mc = {0}
   \<and> cr_dom crun_mc 0 = {1, 2}
   \<and> crun_wellshaped crun_mc"
  by (simp add: crun_simps crun_mc_def)

subsection \<open>WF1 (f): infinite chunk domain (@{text fix_inf_dom})\<close>

definition crun_inf :: crun where
  "crun_inf = default_crun
     \<lparr> cr_chunks := {0}, cr_chunks_list := [0],
       cr_dom := (\<lambda>n. if n = 0 then UNIV else {}) \<rparr>"

lemma inf_fixture_model_values:
  "cr_chunks crun_inf = {0}
   \<and> cr_dom crun_inf 0 = (UNIV :: nat set)
   \<and> crun_wellshaped crun_inf"
  by (simp add: crun_simps crun_inf_def)

subsection \<open>WF5: chunk read after frontier (@{text fix_after_f})\<close>

definition crun_caf :: crun where
  "crun_caf = default_crun
     \<lparr> cr_chunks := {0}, cr_chunks_list := [0], cr_frontier := c0,
       cr_rcoord := (\<lambda>n. if n = 0 then caf_c1 else c0) \<rparr>"

lemma caf_fixture_model_values:
  "cr_chunks crun_caf = {0}
   \<and> cr_frontier crun_caf = c0
   \<and> cr_rcoord crun_caf 0 = caf_c1
   \<and> crun_wellshaped crun_caf"
  by (simp add: crun_simps crun_caf_def)

subsection \<open>WF6 main: wrong refresh value (@{text fix_wrong_r})\<close>

definition crun_wr :: crun where
  "crun_wr = default_crun
     \<lparr> cr_chunks := {0}, cr_chunks_list := [0],
       cr_dom := (\<lambda>n. if n = 0 then {1} else {}),
       cr_rcoord := (\<lambda>_. c0),
       cr_rresult := (\<lambda>ch k. if ch = 0 \<and> k = 1 then Some (Some 99) else None) \<rparr>"

lemma wr_fixture_model_values:
  "cr_chunks crun_wr = {0}
   \<and> cr_dom crun_wr 0 = {1}
   \<and> cr_rcoord crun_wr 0 = c0
   \<and> cr_rresult crun_wr 0 1 = Some (Some 99)
   \<and> crun_wellshaped crun_wr"
  by (simp add: crun_simps crun_wr_def)

subsection \<open>WF6 specialized: same-coord read/event ambiguity (@{text fix_same_c})\<close>

definition crun_sc :: crun where
  "crun_sc = default_crun
     \<lparr> cr_chunks := {0}, cr_chunks_list := [0],
       cr_dom := (\<lambda>n. if n = 0 then {1} else {}),
       cr_rcoord := (\<lambda>n. if n = 0 then sc_c1 else c0),
       cr_rresult := (\<lambda>ch k. if ch = 0 \<and> k = 1 then Some (Some 5) else None) \<rparr>"

lemma sc_fixture_model_values:
  "cr_chunks crun_sc = {0}
   \<and> cr_dom crun_sc 0 = {1}
   \<and> cr_rcoord crun_sc 0 = sc_c1
   \<and> cr_rresult crun_sc 0 1 = Some (Some 5)
   \<and> crun_wellshaped crun_sc"
  by (simp add: crun_simps crun_sc_def)

subsection \<open>WF2 faithfulness: extra observed CDC (@{text fix_extra_cdc})\<close>

definition crun_ec :: crun where
  "crun_ec = default_crun
     \<lparr> cr_scope := {1}, cr_chunks := {0}, cr_chunks_list := [0],
       cr_frontier := ec_c1, cr_src_history := [],
       cr_cdc := [(ec_c1, Insert 1 5)] \<rparr>"

lemma ec_fixture_model_values:
  "cr_scope crun_ec = {1}
   \<and> cr_frontier crun_ec = ec_c1
   \<and> cr_src_history crun_ec = []
   \<and> cr_cdc crun_ec = [(ec_c1, Insert 1 5)]
   \<and> crun_wellshaped crun_ec"
  by (simp add: crun_simps crun_ec_def)

subsection \<open>WF2 coverage: missing dominator (@{text fix_miss_dom})\<close>

definition crun_md :: crun where
  "crun_md = default_crun
     \<lparr> cr_scope := {1}, cr_chunks := {0}, cr_chunks_list := [0],
       cr_frontier := md_c1, cr_dom := (\<lambda>n. if n = 0 then {1} else {}),
       cr_resp := (\<lambda>k. if k = 1 then Some 0 else None),
       cr_rcoord := (\<lambda>_. c0),
       cr_src_history := [(md_c1, Update 1 7)], cr_cdc := [] \<rparr>"

lemma md_fixture_model_values:
  "cr_scope crun_md = {1}
   \<and> cr_frontier crun_md = md_c1
   \<and> cr_dom crun_md 0 = {1}
   \<and> cr_resp crun_md 1 = Some 0
   \<and> cr_rcoord crun_md 0 = c0
   \<and> cr_src_history crun_md = [(md_c1, Update 1 7)]
   \<and> cr_cdc crun_md = []
   \<and> crun_wellshaped crun_md"
  by (simp add: crun_simps crun_md_def)

subsection \<open>WF2 multiplicity: duplicate multiset gap (@{text fix_dup_mset})\<close>

definition crun_dm :: crun where
  "crun_dm = default_crun
     \<lparr> cr_scope := {1}, cr_chunks := {0}, cr_chunks_list := [0],
       cr_frontier := dm_c1, cr_resp := (\<lambda>k. if k = 1 then Some 0 else None),
       cr_rcoord := (\<lambda>_. c0),
       cr_src_history := [(dm_c1, Update 1 5), (dm_c1, Update 1 6), (dm_c1, Update 1 5)],
       cr_cdc := [(dm_c1, Update 1 5), (dm_c1, Update 1 6)] \<rparr>"

lemma dm_fixture_model_values:
  "cr_scope crun_dm = {1}
   \<and> cr_frontier crun_dm = dm_c1
   \<and> cr_resp crun_dm 1 = Some 0
   \<and> cr_rcoord crun_dm 0 = c0
   \<and> cr_src_history crun_dm = [(dm_c1, Update 1 5), (dm_c1, Update 1 6), (dm_c1, Update 1 5)]
   \<and> cr_cdc crun_dm = [(dm_c1, Update 1 5), (dm_c1, Update 1 6)]
   \<and> crun_wellshaped crun_dm"
  by (simp add: crun_simps crun_dm_def)

subsection \<open>WF2 order: duplicate order gap (@{text fix_dup_order})\<close>

definition crun_do :: crun where
  "crun_do = default_crun
     \<lparr> cr_scope := {1}, cr_frontier := do_c1,
       cr_src_history := [(do_c1, Update 1 5), (do_c1, Update 1 6), (do_c1, Update 1 5)],
       cr_cdc := [(do_c1, Update 1 5), (do_c1, Update 1 5), (do_c1, Update 1 6)] \<rparr>"

lemma do_fixture_model_values:
  "cr_scope crun_do = {1}
   \<and> cr_frontier crun_do = do_c1
   \<and> cr_src_history crun_do = [(do_c1, Update 1 5), (do_c1, Update 1 6), (do_c1, Update 1 5)]
   \<and> cr_cdc crun_do = [(do_c1, Update 1 5), (do_c1, Update 1 5), (do_c1, Update 1 6)]
   \<and> crun_wellshaped crun_do"
  by (simp add: crun_simps crun_do_def)

subsection \<open>WF1 (d): responsible-chunk vs chunk-domain mismatch (@{text fix_resp_dom})\<close>

definition crun_rd :: crun where
  "crun_rd = default_crun
     \<lparr> cr_scope := {1}, cr_chunks := {0}, cr_chunks_list := [0],
       cr_dom := (\<lambda>n. if n = 0 then {1} else {}), cr_resp := (\<lambda>_. None) \<rparr>"

lemma rd_fixture_model_values:
  "cr_scope crun_rd = {1}
   \<and> cr_chunks crun_rd = {0}
   \<and> cr_dom crun_rd 0 = {1}
   \<and> cr_resp crun_rd 1 = None
   \<and> crun_wellshaped crun_rd"
  by (simp add: crun_simps crun_rd_def)

subsection \<open>WF6 row-absence: absence-Refresh without empty source (@{text fix_row_abs})\<close>

definition crun_ra :: crun where
  "crun_ra = default_crun
     \<lparr> cr_chunks := {0}, cr_chunks_list := [0],
       cr_dom := (\<lambda>n. if n = 0 then {1} else {}), cr_rcoord := (\<lambda>_. c0),
       cr_rresult := (\<lambda>ch k. if ch = 0 \<and> k = 1 then Some None else None),
       cr_cdc := [] \<rparr>"

lemma ra_fixture_model_values:
  "cr_chunks crun_ra = {0}
   \<and> cr_dom crun_ra 0 = {1}
   \<and> cr_rcoord crun_ra 0 = c0
   \<and> cr_rresult crun_ra 0 1 = Some None
   \<and> cr_cdc crun_ra = []
   \<and> crun_wellshaped crun_ra"
  by (simp add: crun_simps crun_ra_def)

subsection \<open>Boundary: empty scope, vacuously wellformed (@{text boundary_empty_scope})\<close>

text \<open>The empty-scope boundary run has every component empty;
  @{const default_crun} already realizes it.\<close>

lemma es_fixture_model_values:
  "cr_scope default_crun = {}
   \<and> cr_chunks default_crun = {}
   \<and> cr_frontier default_crun = c0
   \<and> cr_src_history default_crun = []
   \<and> cr_cdc default_crun = []
   \<and> (\<forall>k. cr_resp default_crun k = None)
   \<and> crun_wellshaped default_crun"
  by (simp add: crun_simps)

text \<open>
  \<^bold>\<open>Outcome.\<close> Every Layer 0/1 fixture run is an explicit @{type crun} value
  realizing exactly the accessor values its wellformedness clause references
  (plus the chunk-enumeration shape @{text crun_wellshaped}).
  @{text Layer01_Fixtures_Inst} interprets the run-substrate locale at this
  carrier and proves each negative fixture rejected --- and the empty-scope
  boundary run wellformed --- over these values, so the fixture results are
  established constructively, not as artifacts of any assumption.
\<close>

text \<open>
  \<^emph>\<open>Deliberate coverage gaps.\<close> Not every wellformedness clause has a
  dedicated discriminating fixture. No fixture \<^emph>\<open>can\<close> isolate WF1 (a)
  (existence of a responsible chunk follows from WF1 (c) --- ownership
  union equals scope --- and uniqueness from WF1 (b) disjointness), the
  scope half of WF1 (f) (implied by WF1 (c), the chunk-domain half, and
  global chunk-set finiteness), the @{text Refresh}-iff half of WF4
  (automatic under the canonical clean-prefix construction together with
  WF1 (b) and the WF1 (f) finite chunk domains ---
  @{text wf4_refresh_agreement_redundant}), or WF7
  (@{text wf7_clean_prefix_cdc_coherence_redundant}
  proves it for every run). The clauses left untargeted by choice are
  WF0 (a) recorded-history binding and WF4 watermark bracketing /
  read-result totality (each violated only collaterally by fixtures aimed
  at other clauses), WF1 (e) out-of-scope responsible chunks (violated by
  no fixture), and WF1 (g) non-empty chunk domains (documented
  headline-inessential at its clause site in @{text DBLog_Run}).
\<close>

end
