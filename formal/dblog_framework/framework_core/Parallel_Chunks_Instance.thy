(*  Title:   Parallel_Chunks_Instance.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Parallel_Chunks_Instance
  imports Range_Merge
begin

section \<open>A parallel-chunks instance: Flink-style incremental
         snapshots\<close>

text \<open>
  This theory models the parallel chunk algorithm described for
  Flink CDC 3.6.0's MySQL connector. The algorithm records
  the current binlog position as LOW before the chunk select and as
  HIGH after it (write-free: both are READS of a server-side offset,
  no watermark write exists anywhere in the algorithm), backfills
  ``the binlog records that belong to the snapshot chunk from LOW
  offset to HIGH offset'', upserts them onto the buffered chunk
  records, and emits the merged buffer once, all as INSERT records;
  chunks run in parallel across readers. The documented lineage line
  sits directly under the algorithm: ``The algorithm is inspired by
  [DBLog Paper]''.

  The formalization:

    \<^item> Scalar offset coordinates via @{const offden}
      (@{text Range_Merge}); the declared endpoint-to-prefix
      normalization for this instance: the protocol description records the
      consumed span as offset-inclusive ``[LOW, HIGH]'' shorthand,
      raw-offset edge inclusivity undocumented, so the instance
      DECLARES the normalization
      \<open>[LOW, HIGH] \<mapsto> \<lbrakk>HIGH\<rbrakk> \<setminus> \<lbrakk>LOW\<rbrakk>\<close> --- realized below by the
      brackets denoting offset prefixes and the window machinery;
      @{text offset_window} exhibits the declared window as exactly
      the \<open>[LOW, HIGH)\<close> position segment of the log, and
      @{text offset_fidelity} discharges the operational-fidelity
      clause for offset comparisons.
    \<^item> @{text A_read} is O2 verbatim at instance level --- per-key
      in-bracket validity enters as a NAMED assumption rather
      than being derived from an isolation level, mirroring the
      read-only instance's assumption of the same name.
    \<^item> Two further instantiation requirements
      enter as NAMED locale assumptions, never silently. They live at
      different proof boundaries:
      (i) @{text A_handoff} --- the streaming-phase start offset
      relative to the chunks' HIGH watermarks plus the cross-phase
      dedup rule. The development DERIVES the sufficient condition
      the equivalence needs: consumption starts at-or-before every
      chunk's HIGH edge, with the \S6 clause-(a) withholding as the
      cross-phase dedup rule --- exactly the weaker-than-window-discard
      observability premise of @{text range_merge_replay}. This premise
      belongs only to the actual-emission locale below, not to the
      plan-level contract or its cut theorem.
      (ii) @{text A_identity} --- final logical ownership (the paper's
      A-identity). The docs
      state exactly-once holds only if the chunk key column is never
      updated; a moving chunk key relocates a key
      between units mid-plan, so the FINAL plan would not
      partition the scope unless operational normalization restores
      stable logical ownership. Formally the assumption below states
      only that final unit domains are disjoint. It does not itself
      assert physical immutability of a particular split column.
    \<^item> The parallel structure needs NO new coordination argument ---
      every locale
      assumption below is per-chunk except disjointness itself, the
      contract instantiation is proved unit-by-unit, and composition
      with ANY other conforming plan over a disjoint scope is
      Corollary 3's mixing (@{text parallel_mix_any}). Nothing
      couples two chunks anywhere in the development.

  \<^bold>\<open>backfill.skip\<close>: with backfill skipped, changes
  during the snapshot phase ``will be consumed later in change log
  reading phase instead of being merged into the snapshot'', and the
  docs price it: ``Skipping backfill might lead to data inconsistency
  because some change log events happened within the snapshot phase
  might be replayed (only at-least-once semantic is promised).''
  Contract-level placement: T1 at most (\S5 --- the emission as
  shipped discharges no merge-discipline equivalence), and only under
  a separately named external convergence mechanism; its exact
  placement is not established here and is deliberately NOT
  forced here.

  Guarantee level: plan-level T2 --- reached below
  (@{text parallel_cut}) without a handoff premise. The actual modeled
  emitted stream reaches the same final source state under the
  additional handoff premise (@{text parallel_emitted_cut}) and is
  per-key monotone (@{text parallel_monotone}).
\<close>

subsection \<open>The parallel-chunks plan\<close>

locale parallel_chunks_plan =
  fixes L :: "('k, 'v) event list"
    and \<sigma>0 :: "('k, 'v) state"
    and n :: nat
    and cdom :: "nat \<Rightarrow> 'k set"
    and clow chigh :: "nat \<Rightarrow> nat"
    and cread :: "nat \<Rightarrow> ('k, 'v) state"
    and scope :: "'k set"
    and nf :: nat
  assumes bracket_ord: "\<And>i. i < n \<Longrightarrow> clow i \<le> chigh i"
      and bracket_f: "\<And>i. i < n \<Longrightarrow> chigh i \<le> nf"
      and f_len: "nf \<le> length L"
      and PO1_cover: "(\<Union>i\<in>{0..<n}. cdom i) = scope"
      and A_identity: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow>
            cdom i \<inter> cdom j = {}"
      and A_read: "\<And>i k. i < n \<Longrightarrow> k \<in> cdom i \<Longrightarrow>
            \<exists>c. clow i \<le> c \<and> c \<le> chigh i \<and>
                cread i k = state_after \<sigma>0 (take c L) k"
begin

definition punit :: "nat \<Rightarrow> ('k, 'v, nat) cunit" where
  "punit i = \<lparr>u_dom = cdom i, u_lo = clow i, u_hi = chigh i,
              u_refresh = cread i\<rparr>"

definition punits :: "('k, 'v, nat) cunit list" where
  "punits = map punit [0..<n]"

lemma length_punits [simp]: "length punits = n"
  by (simp add: punits_def)

lemma punits_nth [simp]: "i < n \<Longrightarrow> punits ! i = punit i"
  by (simp add: punits_def)

lemma punits_mem:
  assumes "u \<in> set punits"
  obtains i where "i < n" and "u = punit i"
  using assms by (auto simp: punits_def)

end  (* locale parallel_chunks_plan *)

sublocale parallel_chunks_plan \<subseteq> ocs: coordinate_space L "offden L"
  by unfold_locales (rule offden_le_len)

sublocale parallel_chunks_plan \<subseteq> pc: capture_contract L "offden L" \<sigma>0 punits scope nf
proof (unfold_locales)
  have "(\<Union>u\<in>set punits. u_dom u) = (\<Union>i\<in>{0..<n}. cdom i)"
    by (auto simp: punits_def punit_def)
  then show "(\<Union>u\<in>set punits. u_dom u) = scope"
    by (simp add: PO1_cover)
next
  fix i j
  assume "i < length punits" "j < length punits" "i \<noteq> j"
  then show "u_dom (punits ! i) \<inter> u_dom (punits ! j) = {}"
    using A_identity by (simp add: punit_def)
next
  fix u assume "u \<in> set punits"
  then obtain i where i: "i < n" "u = punit i"
    by (rule punits_mem)
  show "ocs.cle (u_lo u) (u_hi u)"
    using bracket_ord[OF i(1)]
    by (simp add: i(2) punit_def ocs.cle_def offden_mono)
next
  fix u assume "u \<in> set punits"
  then obtain i where i: "i < n" "u = punit i"
    by (rule punits_mem)
  show "ocs.cle (u_hi u) nf"
    using bracket_f[OF i(1)]
    by (simp add: i(2) punit_def ocs.cle_def offden_mono)
next
  fix u k assume "u \<in> set punits" and k: "k \<in> u_dom u"
  then obtain i where i: "i < n" "u = punit i"
    by (auto elim: punits_mem)
  have k_dom: "k \<in> cdom i"
    using k by (simp add: i(2) punit_def)
  from A_read[OF i(1) k_dom] obtain c where
    c: "clow i \<le> c" "c \<le> chigh i" "cread i k = state_after \<sigma>0 (take c L) k"
    by blast
  have c_len: "c \<le> length L"
    using c(2) bracket_f[OF i(1)] f_len by simp
  show "\<exists>c. ocs.cle (u_lo u) c \<and> ocs.cle c (u_hi u) \<and>
            u_refresh u k = state_after \<sigma>0 (ocs.pfx c) k"
  proof (intro exI[of _ c] conjI)
    show "ocs.cle (u_lo u) c"
      using c(1) by (simp add: i(2) punit_def ocs.cle_def offden_mono)
    show "ocs.cle c (u_hi u)"
      using c(2) by (simp add: i(2) punit_def ocs.cle_def offden_mono)
    show "u_refresh u k = state_after \<sigma>0 (ocs.pfx c) k"
      using c(3)
      by (simp add: i(2) punit_def ocs.pfx_def offden_id[OF c_len])
  qed
qed

text \<open>
  The emission locale adds only the streaming handoff needed to
  identify the modeled gated range-merge stream with the plan's
  canonical replay. All plan construction, contract membership, the
  cut, and heterogeneous mixing remain in @{text parallel_chunks_plan}
  and therefore do not depend syntactically on this premise.
\<close>

locale parallel_chunks =
  parallel_chunks_plan L \<sigma>0 n cdom clow chigh cread scope nf
  for L :: "('k, 'v) event list"
    and \<sigma>0 :: "('k, 'v) state"
    and n :: nat
    and cdom :: "nat \<Rightarrow> 'k set"
    and clow chigh :: "nat \<Rightarrow> nat"
    and cread :: "nat \<Rightarrow> ('k, 'v) state"
    and scope :: "'k set"
    and nf :: nat +
  fixes s0off :: nat
  assumes A_handoff: "\<And>i. i < n \<Longrightarrow> s0off \<le> chigh i"

subsection \<open>Fidelity, cut, equivalence, and mixing at the instance\<close>

context parallel_chunks_plan
begin

text \<open>
  The operational-fidelity discharge for offset coordinates: on the
  offsets the plan uses (all bounded by the committed history) the
  instance's own comparisons agree with the denotational \<open>\<sqsubseteq>\<close>, and
  the declared window of a bracket is exactly the \<open>[LOW, HIGH)\<close>
  position segment of the log --- the membership decision ``the
  event's position lies in the consumed span'' is the denotational
  window membership.
\<close>

lemma offset_fidelity:
  assumes "a \<le> length L" and "b \<le> length L"
  shows "ocs.cle a b \<longleftrightarrow> a \<le> b"
  using assms by (simp add: ocs.cle_def offden_le_iff)

lemma offset_window:
  assumes "lo \<le> hi" and "hi \<le> length L"
  shows "ocs.win lo hi = drop lo (take hi L)"
proof -
  have lo_len: "lo \<le> length L"
    using assms by linarith
  show ?thesis
    by (simp add: ocs.win_def offden_id[OF lo_len] offden_id[OF assms(2)])
qed

text \<open>
  The plan guarantee: the parallel-chunks plan is a
  contract instance, so THE theorem applies at the frontier --- tier
  T2. Note what the proof did NOT need: any premise coupling two
  chunks (beyond disjointness), any bound on how many chunks run
  concurrently, any relation between distinct chunks' brackets.
  Wall-clock overlap of brackets is invisible to the plan.
\<close>

theorem parallel_cut:
  assumes "k \<in> scope"
  shows "pc.sink_at nf k = state_after \<sigma>0 (take nf L) k"
proof -
  have "pc.sink_at nf k = state_after \<sigma>0 (ocs.pfx nf) k"
    by (rule pc.contract_cut[OF assms])
  then show ?thesis
    by (simp add: ocs.pfx_def offden_id[OF f_len])
qed

text \<open>
  The mixing form is plan-level as well. The final logical ownership
  partition composes with any conforming plan over a disjoint scope at
  the shared frontier, without a streaming-handoff premise.
\<close>

theorem parallel_mix_any:
  assumes "capture_contract L (offden L) \<sigma>0 us2 sc2 nf"
      and "scope \<inter> sc2 = {}"
  shows "capture_contract L (offden L) \<sigma>0 (punits @ us2) (scope \<union> sc2) nf"
  by (rule ocs.mixing_union[OF pc.capture_contract_axioms assms])

end  (* context parallel_chunks_plan *)

context parallel_chunks
begin

text \<open>
  The discipline half: the emitted stream the connector actually
  ships --- merged chunks once at their HIGH edges, all as INSERT
  records, stream events above the HIGH edges only --- replays to the
  canonical sink. The consumption-start premise is discharged by
  @{text A_handoff}: this is precisely where the named handoff
  assumption is load-bearing.
\<close>

theorem parallel_replay:
  assumes rml: "pc.rml_ok rml" and k: "k \<in> scope"
  shows "stream_replay (pc.rm_emission rml s0off) k = pc.sink_at nf k"
proof (rule pc.range_merge_replay[OF rml _ k])
  fix u assume "u \<in> set punits"
  then obtain i where i: "i < n" "u = punit i"
    by (rule punits_mem)
  show "ocs.cle s0off (u_hi u)"
    using A_handoff[OF i(1)]
    by (simp add: i(2) punit_def ocs.cle_def offden_mono)
qed

text \<open>
  This is the direct final-output result. The exact range-merge
  enumeration, the modeled withholding gate, and the handoff premise
  first establish replay equivalence. The plan-level cut then yields
  equality with the source row-event replay at the configured
  frontier. The conclusion is final replay from the empty state, not
  physical prefix equivalence or an exactly-once delivery theorem.
\<close>

theorem parallel_emitted_cut:
  assumes rml: "pc.rml_ok rml" and k: "k \<in> scope"
  shows "stream_replay (pc.rm_emission rml s0off) k = state_after \<sigma>0 (take nf L) k"
  using parallel_replay[OF rml k] parallel_cut[OF k] by simp

theorem parallel_monotone:
  assumes rml: "pc.rml_ok rml" and k: "k \<in> scope"
  shows "sorted (map fst (pc.titems_for k (pc.rm_emission_t rml s0off)))"
proof (rule pc.range_merge_monotone[OF rml _ k])
  fix u assume "u \<in> set punits"
  then obtain i where i: "i < n" "u = punit i"
    by (rule punits_mem)
  show "ocs.cle s0off (u_hi u)"
    using A_handoff[OF i(1)]
    by (simp add: i(2) punit_def ocs.cle_def offden_mono)
qed

end  (* context parallel_chunks *)

subsection \<open>Constructed witness (non-vacuity)\<close>

text \<open>
  Two chunks over a four-event log, brackets genuinely overlapping in
  coordinates (chunk 1's whole bracket lies inside chunk 0's ---
  parallel wall-clock execution made visible), both windows
  non-trivial: chunk 0's window contains a delete-then-reinsert of
  key 1 (clause (b)'s present-again case: the LAST in-window event
  decides, so the merged unit re-emits the key at its reinserted
  value), chunk 1's refresh reads key 2 as absent BEFORE its
  in-window insert (the upsert overrides the absent read result). The
  emitted stream is two INSERT records --- key 1's three log events
  produce zero stream emissions below its chunk's HIGH edge --- and
  replays to the source state at the frontier on both keys.
\<close>

definition L_p :: "(nat, nat) event list" where
  "L_p = [Event 1 (Some 10), Event 2 (Some 20),
          Event 1 None, Event 1 (Some 11)]"

definition cdom_p :: "nat \<Rightarrow> nat set" where
  "cdom_p i = (if i = 0 then {1} else {2})"

definition clow_p :: "nat \<Rightarrow> nat" where
  "clow_p i = (if i = 0 then 0 else 1)"

definition chigh_p :: "nat \<Rightarrow> nat" where
  "chigh_p i = (if i = 0 then 4 else 2)"

definition cread_p :: "nat \<Rightarrow> (nat, nat) state" where
  "cread_p i = (\<lambda>k. if i = 0 \<and> k = 1 then Some 10 else None)"

interpretation pw: parallel_chunks L_p "\<lambda>_. None" 2 cdom_p clow_p chigh_p
                     cread_p "{1, 2}" 4 0
proof (unfold_locales)
  fix i :: nat assume "i < 2"
  then show "clow_p i \<le> chigh_p i"
    by (auto simp: clow_p_def chigh_p_def)
next
  fix i :: nat assume "i < 2"
  then show "chigh_p i \<le> 4"
    by (auto simp: chigh_p_def)
next
  show "(4 :: nat) \<le> length L_p"
    by (simp add: L_p_def)
next
  show "(\<Union>i\<in>{0..<2}. cdom_p i) = {1, 2}"
  proof (intro subset_antisym subsetI)
    fix x assume "x \<in> (\<Union>i\<in>{0..<2}. cdom_p i)"
    then obtain i where "i \<in> {0..<(2::nat)}" and "x \<in> cdom_p i"
      by blast
    then show "x \<in> {1, 2}"
      by (auto simp: cdom_p_def split: if_splits)
  next
    fix x assume "x \<in> {1, (2::nat)}"
    then consider (K1) "x = 1" | (K2) "x = 2"
      by auto
    then show "x \<in> (\<Union>i\<in>{0..<2}. cdom_p i)"
    proof cases
      case K1
      have "(0::nat) \<in> {0..<2}" by simp
      moreover have "x \<in> cdom_p 0"
        using K1 by (simp add: cdom_p_def)
      ultimately show ?thesis by blast
    next
      case K2
      have "(1::nat) \<in> {0..<2}" by simp
      moreover have "x \<in> cdom_p 1"
        using K2 by (simp add: cdom_p_def)
      ultimately show ?thesis by blast
    qed
  qed
next
  fix i j :: nat
  assume "i < 2" "j < 2" "i \<noteq> j"
  then show "cdom_p i \<inter> cdom_p j = {}"
    by (auto simp: cdom_p_def)
next
  fix i :: nat and k :: nat
  assume i: "i < 2" and k: "k \<in> cdom_p i"
  show "\<exists>c. clow_p i \<le> c \<and> c \<le> chigh_p i \<and>
            cread_p i k = state_after (\<lambda>_. None) (take c L_p) k"
  proof (cases "i = 0")
    case True
    then have "k = 1" using k by (simp add: cdom_p_def)
    then show ?thesis
      by (intro exI[of _ 1])
         (simp add: True clow_p_def chigh_p_def cread_p_def L_p_def
                    state_after_def apply_ev_def)
  next
    case False
    then have "k = 2" using k by (simp add: cdom_p_def)
    then show ?thesis
      using False
      by (intro exI[of _ 1])
         (simp add: clow_p_def chigh_p_def cread_p_def L_p_def
                    state_after_def apply_ev_def)
  qed
next
  fix i :: nat assume "i < 2"
  then show "(0 :: nat) \<le> chigh_p i"
    by simp
qed

lemma wit_parallel_cut:
  "pw.pc.sink_at 4 1 = state_after (\<lambda>_. None) (take 4 L_p) 1"
  "pw.pc.sink_at 4 2 = state_after (\<lambda>_. None) (take 4 L_p) 2"
  by (rule pw.parallel_cut, simp)+

lemma wit_parallel_punit_ne: "pw.punit 0 \<noteq> pw.punit 1"
proof
  assume "pw.punit 0 = pw.punit 1"
  then have "u_lo (pw.punit 0) = u_lo (pw.punit 1)"
    by simp
  then show False
    by (simp add: pw.punit_def clow_p_def)
qed

lemma wit_parallel_the_unit_1 [simp]: "pw.pc.the_unit 1 = pw.punit 0"
proof -
  have props: "pw.pc.the_unit 1 \<in> set pw.punits"
              "(1 :: nat) \<in> u_dom (pw.pc.the_unit 1)"
    by (rule pw.pc.the_unit_props, simp)+
  from props(1) obtain i where i: "i < 2" "pw.pc.the_unit 1 = pw.punit i"
    by (rule pw.punits_mem)
  have "i \<noteq> 1"
  proof
    assume "i = 1"
    then have "(1 :: nat) \<in> u_dom (pw.punit 1)"
      using props(2) i(2) by simp
    then show False
      by (simp add: pw.punit_def cdom_p_def)
  qed
  with i(1) have "i = 0" by linarith
  with i(2) show ?thesis by simp
qed

lemma wit_parallel_the_unit_2 [simp]: "pw.pc.the_unit 2 = pw.punit 1"
proof -
  have props: "pw.pc.the_unit 2 \<in> set pw.punits"
              "(2 :: nat) \<in> u_dom (pw.pc.the_unit 2)"
    by (rule pw.pc.the_unit_props, simp)+
  from props(1) obtain i where i: "i < 2" "pw.pc.the_unit 2 = pw.punit i"
    by (rule pw.punits_mem)
  have "i \<noteq> 0"
  proof
    assume "i = 0"
    then have "(2 :: nat) \<in> u_dom (pw.punit 0)"
      using props(2) i(2) by simp
    then show False
      by (simp add: pw.punit_def cdom_p_def)
  qed
  with i(1) have "i = 1" by linarith
  with i(2) show ?thesis by simp
qed

lemma wit_parallel_merged_1: "pw.pc.merged (pw.punit 0) 1 = Some 11"
proof -
  have "pw.ocs.win (u_lo (pw.punit 0)) (u_hi (pw.punit 0)) = L_p"
    unfolding pw.ocs.win_def
    by (simp add: pw.punit_def clow_p_def chigh_p_def offden_def L_p_def)
  moreover have "evs_for 1 L_p =
      [Event 1 (Some 10), Event 1 None, Event 1 (Some 11)]"
    by (simp add: evs_for_def L_p_def)
  ultimately show ?thesis
    by (simp add: pw.pc.merged_def)
qed

lemma wit_parallel_merged_2: "pw.pc.merged (pw.punit 1) 2 = Some 20"
proof -
  have "pw.ocs.win (u_lo (pw.punit 1)) (u_hi (pw.punit 1)) =
          [Event 2 (Some 20)]"
    unfolding pw.ocs.win_def
    by (simp add: pw.punit_def clow_p_def chigh_p_def offden_def L_p_def)
  then show ?thesis
    by (simp add: pw.pc.merged_def evs_for_def)
qed

definition rml_p :: "(nat, nat, nat) cunit \<Rightarrow> nat list" where
  "rml_p u = (if u = pw.punit 0 then [1] else [2])"

lemma wit_parallel_rml_ok: "pw.pc.rml_ok rml_p"
proof -
  have p0: "pw.pc.rm_present (pw.punit 0) = {1}"
    using wit_parallel_merged_1
    by (auto simp: pw.pc.rm_present_def pw.punit_def cdom_p_def)
  have p1: "pw.pc.rm_present (pw.punit 1) = {2}"
    using wit_parallel_merged_2
    by (auto simp: pw.pc.rm_present_def pw.punit_def cdom_p_def)
  have "distinct (rml_p u) \<and> set (rml_p u) = pw.pc.rm_present u"
    if u: "u \<in> set pw.punits" for u
  proof -
    from u obtain i where i: "i < 2" "u = pw.punit i"
      by (rule pw.punits_mem)
    consider (Z) "i = 0" | (O) "i = 1"
      using i(1) by linarith
    then show ?thesis
    proof cases
      case Z
      then have "rml_p u = [1]"
        using i(2) by (simp add: rml_p_def)
      then show ?thesis
        using i(2) Z p0 by simp
    next
      case O
      then have "u \<noteq> pw.punit 0"
        using i(2) wit_parallel_punit_ne by simp
      then have "rml_p u = [2]"
        by (simp add: rml_p_def)
      then show ?thesis
        using i(2) O p1 by simp
    qed
  qed
  then show ?thesis
    by (simp add: pw.pc.rml_ok_def)
qed

text \<open>
  The equivalence theorem at the witness, plus the concrete replay
  values: the merged-chunk stream replays key 1 to its reinserted
  value and key 2 to its inserted value --- the source state at the
  frontier, per @{text wit_parallel_cut}.
\<close>

lemma wit_parallel_replay:
  "stream_replay (pw.pc.rm_emission rml_p 0) 1 = pw.pc.sink_at 4 1"
  "stream_replay (pw.pc.rm_emission rml_p 0) 2 = pw.pc.sink_at 4 2"
  by (rule pw.parallel_replay[OF wit_parallel_rml_ok], simp)+

lemma wit_parallel_values:
  "pw.pc.sink_at 4 1 = Some 11"
  "pw.pc.sink_at 4 2 = Some 20"
proof -
  have e1: "evs_for 1 (pw.ocs.win (u_lo (pw.punit 0)) 4) =
      [Event 1 (Some 10), Event 1 None, Event 1 (Some 11)]"
    unfolding pw.ocs.win_def
    by (simp add: pw.punit_def clow_p_def offden_def L_p_def evs_for_def)
  show "pw.pc.sink_at 4 1 = Some 11"
    unfolding pw.pc.sink_at_def wit_parallel_the_unit_1 e1 by simp
  have e2: "evs_for 2 (pw.ocs.win (u_lo (pw.punit 1)) 4) =
      [Event 2 (Some 20)]"
    unfolding pw.ocs.win_def
    by (simp add: pw.punit_def clow_p_def offden_def L_p_def evs_for_def)
  show "pw.pc.sink_at 4 2 = Some 20"
    unfolding pw.pc.sink_at_def wit_parallel_the_unit_2 e2 by simp
qed

end
