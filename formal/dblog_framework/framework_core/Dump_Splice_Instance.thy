(*  Title:   Dump_Splice_Instance.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Dump_Splice_Instance
  imports Range_Merge
begin

section \<open>Native-dump splice and LSN-positioned selects\<close>

text \<open>
  Native-dump splices and LSN-positioned selects share one
  formal object: a point-bracket plan (\<open>lo = hi = c\<^sup>*\<close>) whose refresh
  is an engine-consistent read at a published coordinate. The plan
  signature is deliberately silent about refresh provenance, so the LSN-positioned select (MariaDB
  \<open>START TRANSACTION WITH CONSISTENT SNAPSHOT\<close> plus the
  binlog-snapshot status pair; PostgreSQL slot-exported snapshots)
  and the native dump (mysqldump
  \<open>--single-transaction --source-data\<close>, mariadb-dump, \<open>pg_dump\<close> on
  an exported snapshot) instantiate the SAME locale --- they differ in
  named-assumption pedigree and operational preconditions, not in
  formal content. For a coordinate-bound dump, the coordinate is
  captured at the snapshot instant (``In all
  cases, any action on logs happens at the exact moment of the
  dump''), no closing marker exists (the high edge is definitionally
  the low edge), and the consistency guarantee is engine-scoped
  (``only InnoDB tables are dumped in a consistent state'').

  \<^bold>\<open>The named assumption register\<close> (O4: externally asserted clauses
  enter as named assumptions, never as proved facts). Three carry
  formal content and are locale assumptions below; two are external
  preconditions whose in-model shadow is structural, carried by this
  register and the witness rather than by a vacuous axiom:

    \<^item> \<^bold>\<open>A-cert\<close> (@{text A_cert}): the snapshot's read view and the
      engine-published coordinate coincide (\<open>n_view = n_pub\<close>).
      O4 records this coincidence as a named external assumption.
    \<^item> \<^bold>\<open>A-scope\<close> (@{text A_scope}): the recorded splice coordinate
      is the published one (\<open>n_rec = n_pub\<close>) --- the MariaDB
      binlog-snapshot status pair is Global-scope, so the read must
      be sequenced against concurrent snapshots overwriting it.
      The assumption names exactly that hazard.
    \<^item> \<^bold>\<open>A-engine\<close> (@{text A_engine} with @{text A_engine_scope}):
      the dump is a consistent read at the view coordinate FOR
      ENGINE-BACKED KEYS ONLY (InnoDB-only; MyISAM/MEMORY excluded),
      and the dumped scope lies inside the engine-backed keys. The
      engine-scope caveat is a real premise of the derivation, not a
      footnote.
    \<^item> \<^bold>\<open>A-ddl\<close> (DDL prohibition during the dump): a documented,
      UNENFORCED external precondition (``no other connection should
      use ALTER TABLE, CREATE TABLE, DROP TABLE, RENAME TABLE, or
      TRUNCATE TABLE''). Its in-model shadow is
      structural: this event model has a fixed key space and no
      schema transitions, so the model REPRESENTS the deployment
      only when the prohibition holds. There is no in-model
      proposition to assume; the instance carries the precondition
      by this register.
    \<^item> \<^bold>\<open>Scope witness\<close> (server-wide vs dumped-scope coordinate, the
      \<open>gtid_purged\<close> caveat): the coordinate denotes a prefix of the
      WHOLE server log @{term L} --- covering transactions ``even
      those that changed suppressed parts of the database'' --- while
      the plan's scope is only @{text dumped}. The model expresses
      this directly: @{term L} ranges over all keys, the claim is
      restricted to @{text dumped}, and the witness log below
      contains a non-dumped key's event to keep the distinction
      visible.

  O5 (representation agreement) is this instance's load-bearing
  obligation and is discharged AT THE TYPED REFRESH: the locale fixes
  @{text R} at the contract's state type, which is exactly the point
  where a real deployment constructs typed rows from dump-file bytes.
  The dump-file-vs-log RENDERING half (charset, collation, numeric
  edge cases --- where real splices break) is the operational clause
  of O5, cite-only, discharged per deployment when @{text R} is
  constructed.

  \<^bold>\<open>Guarantee level\<close>: the point bracket puts the whole dedup machinery out of
  work (the window is empty --- @{text point_window_vacuous}; \S6
  point-splice: nothing to prove), and the recorded coordinate is a
  shared state witness for the one-unit plan, so Corollary 1 applies:
  an exhibited common read-state anchor AT the splice coordinate
  (@{text splice_trajectory}) --- tier T3 on the dumped scope, the
  fast-bootstrap headline. For this one point unit the splice
  coordinate is also the latest high, so T2 already implies the same
  trajectory interval. T3 additionally records why the refresh is one
  coherent source state. In a multi-unit plan a shared witness can
  also precede the latest high. Per-table
  splices at DISTINCT recorded points compose by Corollary 3 to
  global T2 (@{text splice_mix_any}). The composite has a conservative
  trajectory from its latest recorded splice, but the tablesync
  fixture shows that no common witness or earlier start follows
  automatically.

  \<^bold>\<open>The degradation theorem\<close>: an
  UNTRUSTED recovery point --- a restored physical backup whose
  asserted coordinate nobody certifies --- widens to a genuine
  bracket \<open>[backup-start, post-recovery]\<close> and stays INSIDE the
  contract: the widened plan is a contract instance
  (@{text degraded_cut}, placed at tier T2 under the available recorded
  bounds), has a safe canonical trajectory from the bracket high
  (@{text degraded_trajectory_from_end}), and the \S6
  formal window-discard construction across the uncertainty window
  has final replay equal to the canonical sink (@{text degraded_replay}).
  A physical emission inherits that result only when it realizes the
  formal construction and its observation and close premises. Formally
  the latent true view coordinate still sits in the bracket --- O2's
  existential witness --- and even remains a shared witness in the
  Corollary-1 equations. The locale does not encode what an operational
  capture knows or can exhibit. Under the available recorded evidence,
  the known high edge remains a safe, conservative canonical start. The citable
  claim of the untrusted instance is therefore T2, while the trusted
  point carries the additional T3 witness evidence. The trusted point instance is literally the
  degenerate member of the bracket family
  (@{text trusted_point_is_degenerate_bracket}).
\<close>

subsection \<open>The trusted point splice\<close>

locale dump_splice =
  fixes L :: "('k, 'v) event list"
    and \<sigma>0 :: "('k, 'v) state"
    and dumped :: "'k set"
    and R :: "('k, 'v) state"
    and n_view n_pub n_rec nf :: nat
    and engine_ok :: "'k \<Rightarrow> bool"
  assumes A_engine: "\<And>k. engine_ok k \<Longrightarrow>
            R k = state_after \<sigma>0 (take n_view L) k"
      and A_engine_scope: "\<And>k. k \<in> dumped \<Longrightarrow> engine_ok k"
      and A_cert: "n_view = n_pub"
      and A_scope: "n_rec = n_pub"
      and rec_f: "n_rec \<le> nf"
      and f_len: "nf \<le> length L"
begin

definition dunit :: "('k, 'v, nat) cunit" where
  "dunit = \<lparr>u_dom = dumped, u_lo = n_rec, u_hi = n_rec, u_refresh = R\<rparr>"

lemma view_eq_rec: "n_view = n_rec"
  using A_cert A_scope by simp

lemma rec_len: "n_rec \<le> length L"
  using rec_f f_len by simp

text \<open>
  The assumption composition: the engine's consistent read at the
  view (A-engine), the view--published coincidence (A-cert), and the
  published--recorded identity (A-scope) chain into point validity at
  the RECORDED coordinate --- O2 with a point witness.
\<close>

lemma refresh_honest_at_rec:
  assumes "k \<in> dumped"
  shows "R k = state_after \<sigma>0 (take n_rec L) k"
  using A_engine[OF A_engine_scope[OF assms]] view_eq_rec by simp

end  (* locale dump_splice *)

sublocale dump_splice \<subseteq> dcs: coordinate_space L "offden L"
  by unfold_locales (rule offden_le_len)

sublocale dump_splice \<subseteq> dc: capture_contract L "offden L" \<sigma>0 "[dunit]" dumped nf
proof (unfold_locales)
  show "(\<Union>u\<in>set [dunit]. u_dom u) = dumped"
    by (simp add: dunit_def)
next
  fix i j
  assume "i < length [dunit]" "j < length [dunit]" "i \<noteq> j"
  then show "u_dom ([dunit] ! i) \<inter> u_dom ([dunit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [dunit]"
  then show "dcs.cle (u_lo u) (u_hi u)"
    by (simp add: dunit_def dcs.cle_def)
next
  fix u assume "u \<in> set [dunit]"
  then show "dcs.cle (u_hi u) nf"
    using rec_f by (simp add: dunit_def dcs.cle_def offden_mono)
next
  fix u k assume "u \<in> set [dunit]" and k: "k \<in> u_dom u"
  then have u_eq: "u = dunit" and k_dom: "k \<in> dumped"
    by (auto simp: dunit_def)
  show "\<exists>c. dcs.cle (u_lo u) c \<and> dcs.cle c (u_hi u) \<and>
            u_refresh u k = state_after \<sigma>0 (dcs.pfx c) k"
  proof (intro exI[of _ n_rec] conjI)
    show "dcs.cle (u_lo u) n_rec"
      by (simp add: u_eq dunit_def dcs.cle_def)
    show "dcs.cle n_rec (u_hi u)"
      by (simp add: u_eq dunit_def dcs.cle_def)
    show "u_refresh u k = state_after \<sigma>0 (dcs.pfx n_rec) k"
      using refresh_honest_at_rec[OF k_dom]
      by (simp add: u_eq dunit_def dcs.pfx_def offden_id[OF rec_len])
  qed
qed

context dump_splice
begin

text \<open>
  \S6 point-splice, made literal: the window of the point bracket is
  empty --- there is nothing to dedup, and the merge machinery of the
  wider instances is vacuous here.
\<close>

lemma point_window_vacuous: "dcs.win n_rec n_rec = []"
  by (simp add: dcs.win_def)

theorem splice_cut:
  assumes "k \<in> dumped"
  shows "dc.sink_at nf k = state_after \<sigma>0 (take nf L) k"
proof -
  have "dc.sink_at nf k = state_after \<sigma>0 (dcs.pfx nf) k"
    by (rule dc.contract_cut[OF assms])
  then show ?thesis
    by (simp add: dcs.pfx_def offden_id[OF f_len])
qed

text \<open>
  A concrete point-splice emission uses the formal window-discard
  stream with consumption starting exactly at the splice coordinate.
  Because the unit closes at that same coordinate, the close block of
  present copied rows precedes the suffix event at that position and
  the rest of the observed suffix follows in log order.  The theorem
  is replay equivalence for this modeled order, not entry-for-entry
  identity with another stream representation.
\<close>

theorem splice_replay:
  assumes svl: "dc.svl_ok svl" and k: "k \<in> dumped"
  shows "stream_replay (dc.emission svl n_rec) k = dc.sink_at nf k"
proof (rule dc.window_discard_replay[OF svl _ k])
  fix u assume "u \<in> set [dunit]"
  then show "dcs.cle n_rec (u_lo u)"
    by (simp add: dunit_def dcs.cle_def)
qed

theorem splice_emitted_cut:
  assumes svl: "dc.svl_ok svl" and k: "k \<in> dumped"
  shows "stream_replay (dc.emission svl n_rec) k = state_after \<sigma>0 (take nf L) k"
  using splice_replay[OF svl k] splice_cut[OF k] by simp

text \<open>
  Corollary 1 at the instance --- tier T3: the recorded splice
  coordinate is an exhibited shared state witness, and from it up to
  the frontier the replay tracks the source trajectory. For this
  point unit the witness equals the latest high. The additional T3
  content is the exact view binding, not trajectory existence beyond
  what the latest-high theorem already supplies.
\<close>

theorem splice_trajectory:
  assumes rg: "n_rec \<le> g" and gf: "g \<le> nf" and k: "k \<in> dumped"
  shows "dc.sink_at g k = state_after \<sigma>0 (take g L) k"
proof -
  have g_len: "g \<le> length L"
    using gf f_len by simp
  have "dc.sink_at g k = state_after \<sigma>0 (dcs.pfx g) k"
  proof (rule dc.shared_witness_trajectory[where cstar = n_rec])
    show "\<And>u. u \<in> set [dunit] \<Longrightarrow> dcs.cle (u_lo u) n_rec \<and> dcs.cle n_rec (u_hi u)"
      by (simp add: dunit_def dcs.cle_def)
    show "\<And>u k. u \<in> set [dunit] \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
            u_refresh u k = state_after \<sigma>0 (dcs.pfx n_rec) k"
    proof -
      fix u kk assume "u \<in> set [dunit]" and "kk \<in> u_dom u"
      then have u_eq: "u = dunit" and kk_dom: "kk \<in> dumped"
        by (auto simp: dunit_def)
      show "u_refresh u kk = state_after \<sigma>0 (dcs.pfx n_rec) kk"
        using refresh_honest_at_rec[OF kk_dom]
        by (simp add: u_eq dunit_def dcs.pfx_def offden_id[OF rec_len])
    qed
    show "dcs.cle n_rec g"
      using rg by (simp add: dcs.cle_def offden_mono)
    show "dcs.cle g nf"
      using gf by (simp add: dcs.cle_def offden_mono)
    show "k \<in> dumped"
      by (rule k)
  qed
  then show ?thesis
    by (simp add: dcs.pfx_def offden_id[OF g_len])
qed

text \<open>
  Corollary 3 at the instance: the splice composes with ANY
  conforming plan over a disjoint scope at the shared frontier ---
  per-table dumps, chunk fleets, point selects. Two splices at
  DISTINCT recorded points compose conservatively to T2. Their union
  has a trajectory from its latest recorded splice, but composition
  alone supplies neither a common in-bracket witness nor an earlier
  start. The sharpness is witnessed by
  @{text fix_sync_no_early_onset} in theory
  @{text Contract_Witnesses}. One shared snapshot across the members
  supplies the common witness required for T3 via Corollary 1.
\<close>

theorem splice_mix_any:
  assumes "capture_contract L (offden L) \<sigma>0 us2 sc2 nf"
      and "dumped \<inter> sc2 = {}"
  shows "capture_contract L (offden L) \<sigma>0 ([dunit] @ us2) (dumped \<union> sc2) nf"
  by (rule dcs.mixing_union[OF dc.capture_contract_axioms assms])

end  (* context dump_splice *)

subsection \<open>The uncertainty-bracket degradation\<close>

text \<open>
  The untrusted variant: no A-cert, no A-scope --- nobody certifies
  WHERE the recovery point sits. What survives is a BOUND: the true
  read view lies between the backup start and the post-recovery
  coordinate (@{text A_uncertainty_lo}/@{text A_uncertainty_hi}),
  and the engine read is consistent at that unknown view
  (@{text A_engine}). The plan widens its bracket to the whole
  uncertainty interval; O2 holds with the unknown view as the
  existential witness. Trust is exchanged for dedup work, not for
  membership.
\<close>

locale dump_splice_untrusted =
  fixes L :: "('k, 'v) event list"
    and \<sigma>0 :: "('k, 'v) state"
    and dumped :: "'k set"
    and R :: "('k, 'v) state"
    and n_start n_view n_end nf :: nat
    and engine_ok :: "'k \<Rightarrow> bool"
  assumes A_engine: "\<And>k. engine_ok k \<Longrightarrow>
            R k = state_after \<sigma>0 (take n_view L) k"
      and A_engine_scope: "\<And>k. k \<in> dumped \<Longrightarrow> engine_ok k"
      and A_uncertainty_lo: "n_start \<le> n_view"
      and A_uncertainty_hi: "n_view \<le> n_end"
      and end_f: "n_end \<le> nf"
      and f_len: "nf \<le> length L"
begin

definition wunit :: "('k, 'v, nat) cunit" where
  "wunit = \<lparr>u_dom = dumped, u_lo = n_start, u_hi = n_end, u_refresh = R\<rparr>"

lemma view_len: "n_view \<le> length L"
  using A_uncertainty_hi end_f f_len by simp

end  (* locale dump_splice_untrusted *)

sublocale dump_splice_untrusted \<subseteq> ucs: coordinate_space L "offden L"
  by unfold_locales (rule offden_le_len)

sublocale dump_splice_untrusted \<subseteq>
  uc: capture_contract L "offden L" \<sigma>0 "[wunit]" dumped nf
proof (unfold_locales)
  show "(\<Union>u\<in>set [wunit]. u_dom u) = dumped"
    by (simp add: wunit_def)
next
  fix i j
  assume "i < length [wunit]" "j < length [wunit]" "i \<noteq> j"
  then show "u_dom ([wunit] ! i) \<inter> u_dom ([wunit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [wunit]"
  then show "ucs.cle (u_lo u) (u_hi u)"
    using A_uncertainty_lo A_uncertainty_hi
    by (simp add: wunit_def ucs.cle_def offden_mono)
next
  fix u assume "u \<in> set [wunit]"
  then show "ucs.cle (u_hi u) nf"
    using end_f by (simp add: wunit_def ucs.cle_def offden_mono)
next
  fix u k assume "u \<in> set [wunit]" and k: "k \<in> u_dom u"
  then have u_eq: "u = wunit" and k_dom: "k \<in> dumped"
    by (auto simp: wunit_def)
  show "\<exists>c. ucs.cle (u_lo u) c \<and> ucs.cle c (u_hi u) \<and>
            u_refresh u k = state_after \<sigma>0 (ucs.pfx c) k"
  proof (intro exI[of _ n_view] conjI)
    show "ucs.cle (u_lo u) n_view"
      using A_uncertainty_lo
      by (simp add: u_eq wunit_def ucs.cle_def offden_mono)
    show "ucs.cle n_view (u_hi u)"
      using A_uncertainty_hi
      by (simp add: u_eq wunit_def ucs.cle_def offden_mono)
    show "u_refresh u k = state_after \<sigma>0 (ucs.pfx n_view) k"
      using A_engine[OF A_engine_scope[OF k_dom]]
      by (simp add: u_eq wunit_def ucs.pfx_def offden_id[OF view_len])
  qed
qed

context dump_splice_untrusted
begin

text \<open>
  The widened-bracket plan is a T2 contract instance. The cut holds
  at the frontier, and the unit's known high edge is the conservative
  start supplied by the latest-high theorem.
\<close>

theorem degraded_cut:
  assumes "k \<in> dumped"
  shows "uc.sink_at nf k = state_after \<sigma>0 (take nf L) k"
proof -
  have "uc.sink_at nf k = state_after \<sigma>0 (ucs.pfx nf) k"
    by (rule uc.contract_cut[OF assms])
  then show ?thesis
    by (simp add: ucs.pfx_def offden_id[OF f_len])
qed

theorem degraded_trajectory_from_end:
  assumes eg: "n_end \<le> g" and gf: "g \<le> nf" and k: "k \<in> dumped"
  shows "uc.sink_at g k = state_after \<sigma>0 (take g L) k"
proof -
  have g_len: "g \<le> length L"
    using gf f_len by simp
  have "uc.sink_at g k = state_after \<sigma>0 (ucs.pfx g) k"
  proof (rule uc.contract_cut_at[OF _ k])
    fix u assume "u \<in> set [wunit]"
    then show "ucs.cle (u_hi u) g"
      using eg by (simp add: wunit_def ucs.cle_def offden_mono)
  qed
  then show ?thesis
    by (simp add: ucs.pfx_def offden_id[OF g_len])
qed

text \<open>
  And the \S6 window-discard discipline runs across the uncertainty
  window. With an exact survivor listing and consumption beginning at
  or before the backup start, @{text uc.emission} consumes the log
  through the frontier, closes the survivor block at the post-recovery
  edge after processing that window, and has final replay equal to the
  canonical sink. This theorem states final replay of that formal
  construction, not prefix equivalence of a physical shipped stream.
  The untrusted point costs
  dedup work over \<open>[backup-start, post-recovery]\<close>; it does not cost
  contract membership.
\<close>

theorem degraded_replay:
  assumes svl: "uc.svl_ok svl"
      and s0: "s0 \<le> n_start"
      and k: "k \<in> dumped"
  shows "stream_replay (uc.emission svl s0) k = uc.sink_at nf k"
proof (rule uc.window_discard_replay[OF svl _ k])
  fix u assume "u \<in> set [wunit]"
  then show "ucs.cle s0 (u_lo u)"
    using s0 by (simp add: wunit_def ucs.cle_def offden_mono)
qed

theorem degraded_emitted_cut:
  assumes svl: "uc.svl_ok svl"
      and s0: "s0 \<le> n_start"
      and k: "k \<in> dumped"
  shows "stream_replay (uc.emission svl s0) k = state_after \<sigma>0 (take nf L) k"
  using degraded_replay[OF svl s0 k] degraded_cut[OF k] by simp

end  (* context dump_splice_untrusted *)

text \<open>
  The trusted point instance is the degenerate member of the
  uncertainty-bracket family: certifying the coordinate collapses
  the bracket to a point. Both members remain inside one contract
  family. The point member additionally exhibits the true shared state
  witness, while the interval member retains its conservative start
  at the known high edge.
\<close>

context dump_splice
begin

theorem trusted_point_is_degenerate_bracket:
  "dump_splice_untrusted L \<sigma>0 dumped R n_rec n_view n_rec nf engine_ok"
proof (unfold_locales)
  show "\<And>k. engine_ok k \<Longrightarrow> R k = state_after \<sigma>0 (take n_view L) k"
    by (rule A_engine)
  show "\<And>k. k \<in> dumped \<Longrightarrow> engine_ok k"
    by (rule A_engine_scope)
  show "n_rec \<le> n_view"
    using view_eq_rec by simp
  show "n_view \<le> n_rec"
    using view_eq_rec by simp
  show "n_rec \<le> nf"
    by (rule rec_f)
  show "nf \<le> length L"
    by (rule f_len)
qed

end  (* context dump_splice *)

subsection \<open>Constructed witness: the trusted splice (non-vacuity)\<close>

text \<open>
  A three-event server log: the dumped key 1 is inserted, a
  NON-dumped key 9 is written (another database on the same server
  --- the server-wide coordinate covers it, the dumped-scope claim
  says nothing about it: the \<open>gtid_purged\<close> scope caveat made
  concrete), and key 1 is deleted AFTER the splice coordinate. The
  dump reads at coordinate 2, the splice replays the post-splice
  delete, and the trajectory holds from the splice coordinate: at
  the splice the key is present at its dumped value, at the
  frontier it is absent --- both equal to the source.
\<close>

definition L_d :: "(nat, nat) event list" where
  "L_d = [Event 1 (Some 8), Event 9 (Some 99), Event 1 None]"

definition R_d :: "(nat, nat) state" where
  "R_d = (\<lambda>k. if k = 1 then Some 8 else None)"

definition eng_d :: "nat \<Rightarrow> bool" where
  "eng_d k \<longleftrightarrow> k = 1"

interpretation ds: dump_splice L_d "\<lambda>_. None" "{1}" R_d 2 2 2 3 eng_d
proof (unfold_locales)
  fix k :: nat assume "eng_d k"
  then have "k = 1" by (simp add: eng_d_def)
  then show "R_d k = state_after (\<lambda>_. None) (take 2 L_d) k"
    by (simp add: R_d_def L_d_def state_after_def apply_ev_def)
next
  fix k :: nat assume "k \<in> {1}"
  then show "eng_d k" by (simp add: eng_d_def)
qed (simp_all add: L_d_def)

lemma wit_dump_the_unit [simp]: "ds.dc.the_unit 1 = ds.dunit"
  using ds.dc.the_unit_props[of 1] by simp

lemma wit_dump_cut:
  "ds.dc.sink_at 3 1 = state_after (\<lambda>_. None) (take 3 L_d) 1"
  by (rule ds.splice_cut) simp

lemma wit_dump_cut_value: "ds.dc.sink_at 3 1 = None"
proof -
  have win: "evs_for 1 (ds.dcs.win (u_lo ds.dunit) 3) = [Event 1 None]"
    unfolding ds.dcs.win_def ds.dunit_def
    by (simp add: offden_def L_d_def evs_for_def)
  show ?thesis
    unfolding ds.dc.sink_at_def wit_dump_the_unit win by simp
qed

lemma wit_dump_trajectory:
  "ds.dc.sink_at 2 1 = state_after (\<lambda>_. None) (take 2 L_d) 1"
  by (rule ds.splice_trajectory) simp_all

lemma wit_dump_trajectory_value: "ds.dc.sink_at 2 1 = Some 8"
proof -
  have win_e: "evs_for 1 (ds.dcs.win (u_lo ds.dunit) 2) = []"
    unfolding ds.dcs.win_def ds.dunit_def
    by (simp add: offden_def L_d_def evs_for_def)
  have "ds.dc.sink_at 2 1 = u_refresh ds.dunit 1"
    unfolding ds.dc.sink_at_def wit_dump_the_unit win_e by simp
  also have "\<dots> = R_d 1"
    unfolding ds.dunit_def by simp
  also have "\<dots> = Some 8"
    by (simp add: R_d_def)
  finally show ?thesis .
qed

subsection \<open>Constructed witness: the degraded bracket (non-vacuity)\<close>

text \<open>
  The uncertainty bracket doing real work: the restored read is
  valid at the unknown view coordinate 1 (after the first insert),
  the bracket spans the whole log, and an in-window event supersedes
  the restored value --- the \S6 discard discipline drops the
  buffered row and the log wins. The replay lands on the source
  state at the frontier, per the degradation theorems.
\<close>

definition L_u :: "(nat, nat) event list" where
  "L_u = [Event 1 (Some 4), Event 1 (Some 6)]"

definition R_u :: "(nat, nat) state" where
  "R_u = (\<lambda>k. if k = 1 then Some 4 else None)"

interpretation du: dump_splice_untrusted L_u "\<lambda>_. None" "{1}" R_u 0 1 2 2 eng_d
proof (unfold_locales)
  fix k :: nat assume "eng_d k"
  then have "k = 1" by (simp add: eng_d_def)
  then show "R_u k = state_after (\<lambda>_. None) (take 1 L_u) k"
    by (simp add: R_u_def L_u_def state_after_def apply_ev_def)
next
  fix k :: nat assume "k \<in> {1}"
  then show "eng_d k" by (simp add: eng_d_def)
next
  show "(0 :: nat) \<le> 1" by simp
next
  show "(1 :: nat) \<le> 2" by simp
next
  show "(2 :: nat) \<le> 2" by simp
next
  show "(2 :: nat) \<le> length L_u" by (simp add: L_u_def)
qed

lemma wit_degraded_the_unit [simp]: "du.uc.the_unit 1 = du.wunit"
  using du.uc.the_unit_props[of 1] by simp

lemma wit_degraded_cut:
  "du.uc.sink_at 2 1 = state_after (\<lambda>_. None) (take 2 L_u) 1"
  by (rule du.degraded_cut) simp

lemma wit_degraded_win:
  "evs_for 1 (du.ucs.win (u_lo du.wunit) (u_hi du.wunit)) =
     [Event 1 (Some 4), Event 1 (Some 6)]"
  unfolding du.ucs.win_def du.wunit_def
  by (simp add: offden_def L_u_def evs_for_def)

lemma wit_degraded_cut_value: "du.uc.sink_at 2 1 = Some 6"
proof -
  have win: "evs_for 1 (du.ucs.win (u_lo du.wunit) 2) =
      [Event 1 (Some 4), Event 1 (Some 6)]"
    unfolding du.ucs.win_def du.wunit_def
    by (simp add: offden_def L_u_def evs_for_def)
  show ?thesis
    unfolding du.uc.sink_at_def wit_degraded_the_unit win by simp
qed

lemma wit_degraded_surv_empty: "du.uc.survivors du.wunit = {}"
proof (rule ccontr)
  have dom_eq: "u_dom du.wunit = {1}"
    unfolding du.wunit_def by simp
  assume "du.uc.survivors du.wunit \<noteq> {}"
  then obtain x where x: "x \<in> du.uc.survivors du.wunit"
    by blast
  have x_dom: "x \<in> u_dom du.wunit"
    using x du.uc.survivors_sub_dom by blast
  have x_quiet: "evs_for x (du.ucs.win (u_lo du.wunit)
                              (u_hi du.wunit)) = []"
    using x unfolding du.uc.survivors_def by blast
  have x1: "x = 1"
    using x_dom unfolding dom_eq by blast
  have "evs_for 1 (du.ucs.win (u_lo du.wunit) (u_hi du.wunit)) = []"
    using x_quiet unfolding x1 .
  then show False
    using wit_degraded_win by simp
qed

lemma wit_degraded_svl_ok: "du.uc.svl_ok (\<lambda>_. [])"
  unfolding du.uc.svl_ok_def
proof
  fix u assume "u \<in> set [du.wunit]"
  then have "u = du.wunit" by simp
  then show "distinct ((\<lambda>_. []) u) \<and>
             set ((\<lambda>_. []) u) = du.uc.survivors u"
    using wit_degraded_surv_empty by simp
qed

lemma wit_degraded_replay:
  "stream_replay (du.uc.emission (\<lambda>_. []) 0) 1 = du.uc.sink_at 2 1"
  by (rule du.degraded_replay[OF wit_degraded_svl_ok]) simp_all

lemma wit_degraded_replay_value:
  "stream_replay (du.uc.emission (\<lambda>_. []) 0) 1 = Some 6"
  using wit_degraded_replay wit_degraded_cut_value by simp

end
