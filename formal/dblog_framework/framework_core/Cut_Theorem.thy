(*  Title:   Cut_Theorem.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Cut_Theorem
  imports Contract_Base
begin

section \<open>Capture plans, the contract, and the contract-level cut theorem\<close>

text \<open>
  Capture plans as finite families of units
  (domain, bracket, refresh), the plan obligations O1--O5, the
  canonical per-key replay, the contract-level virtual-cut
  theorem, and Corollaries 1--3.

  Obligation placement in the mechanization:

    \<^item> O1 (coverage/disjointness) and O2 (bracket-local per-key
      existential validity) are locale assumptions below.
      Operational DBLog instances additionally construct refreshes
      from committed reads: they do not expose in-progress writes. If
      transaction labels are retained, the operational O2 witness is
      therefore a transaction boundary, as encoded explicitly by
      theory @{text ReadOnly_Instance}. The transaction-free core
      records only the extensional per-key equality consumed by the
      proof; an interior replay prefix is not thereby licensed as a
      dirty-read state.
    \<^item> O3 (domain completeness) is carried by representation plus O2:
      a refresh is a total function @{typ "('k, 'v) state"}, so every
      key of the unit yields exactly one value-or-absence read result
      (``exactly one'' is structural), and O2 quantifies over ALL keys
      of the unit's domain, so a scan that silently missed a key
      cannot discharge O2 unless that key was genuinely absent at an
      in-bracket coordinate --- absence-by-omission is only valid
      when it is true absence.
    \<^item> O4 (declared external assertions) has no core-level content: it
      disciplines HOW an instance may discharge bracket/validity
      premises (by named assumption rather than by proof) and
      surfaces in the instance theories, never here.
    \<^item> O5 (representation agreement) is carried by typing in the
      core: refresh values and log images land in the same @{typ 'k}
      and @{typ 'v} by construction. Its operational half (dump-file
      rendering vs log rendering) is an instance-side obligation
      discharged when an instance constructs the typed refresh.
    \<^item> S-OBS: the model's log @{term L} is the committed history the
      capture consumes; the fold below is defined from @{term L}
      directly, so the core theorem needs no separate observability
      premise. Observability becomes real at the discipline level
      (theory @{text Merge_Disciplines}): an emission is constructed from a consumed
      segment, and the consumption-start premise @{text "s\<^sub>0 \<sqsubseteq> lo\<^sub>i"}
      appears there. Because @{text sink_at} never mentions the
      frontier parameter, the fold-level results below are
      frontier-parametric; the observation-frontier
      bound is stated at each corollary.
\<close>

subsection \<open>Units and plans\<close>

record ('k, 'v, 'c) cunit =
  u_dom :: "'k set"
  u_lo :: 'c
  u_hi :: 'c
  u_refresh :: "('k, 'v) state"

text \<open>
  A capture plan: a coordinate space plus a finite family of units, a
  scope, and a frontier. The family is a list --- an indexed family in
  the paper's sense (the final partition the run produced);
  positions are the family's index set. This locale fixes only the
  signature; the obligations live in @{text capture_contract} below.
  The plan is deliberately silent about how refreshes were obtained,
  how units were scheduled, and how brackets were realized: none of
  those occur in the signature at all.
\<close>

locale capture_plan = coordinate_space L den
  for L :: "('k, 'v) event list" and den :: "'c \<Rightarrow> nat" +
  fixes \<sigma>0 :: "('k, 'v) state"
    and units :: "('k, 'v, 'c) cunit list"
    and scope :: "'k set"
    and f :: 'c
begin

definition the_unit :: "'k \<Rightarrow> ('k, 'v, 'c) cunit" where
  "the_unit k = (THE u. u \<in> set units \<and> k \<in> u_dom u)"

text \<open>
  The canonical replay, per key: the last event for the key in
  the half-open interval from the covering unit's low bracket edge to
  the queried coordinate wins; absent any such event, the unit's
  read result stands. This fold is stated at
  any coordinate @{text g} (the emission truncated at @{text g}):
  refreshes are placed at @{text "lo\<^sub>i"} and later events win.
\<close>

definition sink_at :: "'c \<Rightarrow> ('k, 'v) state" where
  "sink_at g k =
     (if evs_for k (win (u_lo (the_unit k)) g) = []
      then u_refresh (the_unit k) k
      else ev_img (last (evs_for k (win (u_lo (the_unit k)) g))))"

end

subsection \<open>The contract\<close>

locale capture_contract = capture_plan L den \<sigma>0 units scope f
  for L :: "('k, 'v) event list" and den :: "'c \<Rightarrow> nat"
  and \<sigma>0 :: "('k, 'v) state"
  and units :: "('k, 'v, 'c) cunit list"
  and scope :: "'k set"
  and f :: 'c +
  assumes O1_cover: "(\<Union>u\<in>set units. u_dom u) = scope"
      and O1_disjoint: "\<lbrakk> i < length units; j < length units; i \<noteq> j \<rbrakk> \<Longrightarrow>
                          u_dom (units ! i) \<inter> u_dom (units ! j) = {}"
      and bracket_lo_hi: "u \<in> set units \<Longrightarrow> u_lo u \<sqsubseteq> u_hi u"
      and bracket_hi_f: "u \<in> set units \<Longrightarrow> u_hi u \<sqsubseteq> f"
      and O2_honest: "\<lbrakk> u \<in> set units; k \<in> u_dom u \<rbrakk> \<Longrightarrow>
                        \<exists>c. u_lo u \<sqsubseteq> c \<and> c \<sqsubseteq> u_hi u \<and>
                            u_refresh u k = state_after \<sigma>0 (pfx c) k"
begin

lemma dom_sub_scope: "u \<in> set units \<Longrightarrow> u_dom u \<subseteq> scope"
  using O1_cover by auto

lemma covering_unit_unique:
  assumes u: "u \<in> set units" "k \<in> u_dom u"
      and u': "u' \<in> set units" "k \<in> u_dom u'"
  shows "u = u'"
proof (rule ccontr)
  assume ne: "u \<noteq> u'"
  obtain i where i: "i < length units" "units ! i = u"
    using u(1) by (meson in_set_conv_nth)
  obtain j where j: "j < length units" "units ! j = u'"
    using u'(1) by (meson in_set_conv_nth)
  have "i \<noteq> j" using ne i(2) j(2) by auto
  then have "u_dom (units ! i) \<inter> u_dom (units ! j) = {}"
    using O1_disjoint i(1) j(1) by blast
  with i(2) j(2) u(2) u'(2) show False by auto
qed

lemma the_unit_props:
  assumes "k \<in> scope"
  shows "the_unit k \<in> set units" and "k \<in> u_dom (the_unit k)"
proof -
  from assms O1_cover obtain u where u: "u \<in> set units" "k \<in> u_dom u"
    by auto
  have "the_unit k = u"
    unfolding the_unit_def
  proof (rule the_equality)
    show "u \<in> set units \<and> k \<in> u_dom u" using u by simp
  next
    fix x assume "x \<in> set units \<and> k \<in> u_dom x"
    then show "x = u" using u covering_unit_unique by blast
  qed
  then show "the_unit k \<in> set units" "k \<in> u_dom (the_unit k)"
    using u by auto
qed

lemma the_unit_position_unique:
  assumes k: "k \<in> scope"
      and i: "i < length units" "units ! i = the_unit k"
      and j: "j < length units" "units ! j = the_unit k"
  shows "i = j"
proof (rule ccontr)
  assume "i \<noteq> j"
  then have "u_dom (units ! i) \<inter> u_dom (units ! j) = {}"
    using O1_disjoint i(1) j(1) by blast
  then have "u_dom (the_unit k) = {}"
    using i(2) j(2) by auto
  then show False
    using the_unit_props(2)[OF k] by auto
qed

subsection \<open>The contract-level cut theorem\<close>

text \<open>
  The frontier-parametric workhorse: at ANY coordinate @{text g} that
  bounds every unit's high bracket edge, the canonical replay equals
  the source state. The proof is per-key local: Case A (some event for
  the key after its unit's low edge) --- the last such event wins the
  fold and is also the last event for the key in the whole prefix;
  Case B (no such event) --- O2 supplies an in-bracket coordinate
  where the read result is valid, and window invariance propagates
  its value to @{text g}.
  Nothing couples distinct units beyond O1 disjointness and the
  shared bound.
\<close>

theorem contract_cut_at:
  assumes bound: "\<And>u. u \<in> set units \<Longrightarrow> u_hi u \<sqsubseteq> g"
      and k: "k \<in> scope"
  shows "sink_at g k = state_after \<sigma>0 (pfx g) k"
proof -
  define u where "u = the_unit k"
  have u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
    using the_unit_props[OF k] u_def by auto
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u"
    by (rule bracket_lo_hi[OF u_in])
  have hi_g: "u_hi u \<sqsubseteq> g"
    by (rule bound[OF u_in])
  have lo_g: "u_lo u \<sqsubseteq> g"
    using lo_hi hi_g by (rule cle_trans)
  show ?thesis
  proof (cases "evs_for k (win (u_lo u) g) = []")
    case False
    have split: "evs_for k (pfx g) =
                   evs_for k (pfx (u_lo u)) @ evs_for k (win (u_lo u) g)"
      by (rule evs_for_pfx_split[OF lo_g])
    have "sink_at g k = ev_img (last (evs_for k (win (u_lo u) g)))"
      using False by (simp add: sink_at_def u_def)
    moreover have "evs_for k (pfx g) \<noteq> []"
      using split False by auto
    moreover have "last (evs_for k (pfx g)) = last (evs_for k (win (u_lo u) g))"
      using split False by (simp add: last_append)
    ultimately show ?thesis
      by (simp add: state_after_last_event)
  next
    case True
    from O2_honest[OF u_in k_dom] obtain c where
      c_lo: "u_lo u \<sqsubseteq> c" and c_hi: "c \<sqsubseteq> u_hi u" and
      honest: "u_refresh u k = state_after \<sigma>0 (pfx c) k"
      by blast
    have c_g: "c \<sqsubseteq> g"
      using c_hi hi_g by (rule cle_trans)
    have "sink_at g k = u_refresh u k"
      using True by (simp add: sink_at_def u_def)
    also have "\<dots> = state_after \<sigma>0 (pfx c) k"
      by (rule honest)
    also have "\<dots> = state_after \<sigma>0 (pfx (u_lo u)) k"
      by (rule win_invariant_state[OF c_lo c_g True])
    also have "\<dots> = state_after \<sigma>0 (pfx g) k"
      by (rule win_invariant_state[OF lo_g cle_refl True, symmetric])
    finally show ?thesis .
  qed
qed

text \<open>
  The per-unit form (paper Lemma 4.3, the closed-unit cut): the bound
  above is consumed only for the key's own unit, so at any coordinate
  @{text g} the canonical replay is exact on every key whose unit has
  closed by @{text g}, whatever the other units are doing.
\<close>

theorem contract_cut_unit:
  assumes k: "k \<in> scope"
      and hi: "u_hi (the_unit k) \<sqsubseteq> g"
  shows "sink_at g k = state_after \<sigma>0 (pfx g) k"
proof -
  define u where "u = the_unit k"
  have u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
    using the_unit_props[OF k] u_def by auto
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u"
    by (rule bracket_lo_hi[OF u_in])
  have hi_g: "u_hi u \<sqsubseteq> g"
    using hi u_def by simp
  have lo_g: "u_lo u \<sqsubseteq> g"
    using lo_hi hi_g by (rule cle_trans)
  show ?thesis
  proof (cases "evs_for k (win (u_lo u) g) = []")
    case False
    have split: "evs_for k (pfx g) =
                   evs_for k (pfx (u_lo u)) @ evs_for k (win (u_lo u) g)"
      by (rule evs_for_pfx_split[OF lo_g])
    have "sink_at g k = ev_img (last (evs_for k (win (u_lo u) g)))"
      using False by (simp add: sink_at_def u_def)
    moreover have "evs_for k (pfx g) \<noteq> []"
      using split False by auto
    moreover have "last (evs_for k (pfx g)) = last (evs_for k (win (u_lo u) g))"
      using split False by (simp add: last_append)
    ultimately show ?thesis
      by (simp add: state_after_last_event)
  next
    case True
    from O2_honest[OF u_in k_dom] obtain c where
      c_lo: "u_lo u \<sqsubseteq> c" and c_hi: "c \<sqsubseteq> u_hi u" and
      honest: "u_refresh u k = state_after \<sigma>0 (pfx c) k"
      by blast
    have c_g: "c \<sqsubseteq> g"
      using c_hi hi_g by (rule cle_trans)
    have "sink_at g k = u_refresh u k"
      using True by (simp add: sink_at_def u_def)
    also have "\<dots> = state_after \<sigma>0 (pfx c) k"
      by (rule honest)
    also have "\<dots> = state_after \<sigma>0 (pfx (u_lo u)) k"
      by (rule win_invariant_state[OF c_lo c_g True])
    also have "\<dots> = state_after \<sigma>0 (pfx g) k"
      by (rule win_invariant_state[OF lo_g cle_refl True, symmetric])
    finally show ?thesis .
  qed
qed

text \<open>
  The cut theorem: the replay of the emission is exactly
  the source state at the frontier, on the whole scope.
\<close>

theorem contract_cut:
  assumes "k \<in> scope"
  shows "sink_at f k = state_after \<sigma>0 (pfx f) k"
  by (rule contract_cut_at[OF bracket_hi_f assms])

corollary contract_cut_scope:
  "\<forall>k\<in>scope. sink_at f k = state_after \<sigma>0 (pfx f) k"
  using contract_cut by blast

subsection \<open>The conservative trajectory after the latest high\<close>

text \<open>
  The workhorse theorem already gives more than one correct state at
  @{text f}. A nonempty plan is a finite list, and coordinate
  denotations are totally ordered by prefix length. The recorded high
  edges therefore contain a maximal one @{text h}. Every coordinate
  at or after @{text h} bounds every unit high, so @{text
  contract_cut_at} gives the source trajectory from @{text h} onward.
  This is the conservative trajectory available to every nonempty
  contract plan. A shared state witness can move the start back to a
  particular common read coordinate, but it is not needed for the
  existence of some trajectory start.

  If the unit list is empty, O1 forces an empty scope. The scoped
  equality is then vacuous, but there is no recorded high edge to
  select.
\<close>

lemma latest_high_exists:
  assumes units_ne: "units \<noteq> []"
  obtains h where "h \<in> u_hi ` set units"
      and "\<And>u. u \<in> set units \<Longrightarrow> u_hi u \<sqsubseteq> h"
proof -
  let ?N = "den ` u_hi ` set units"
  have fin: "finite ?N" by simp
  have ne: "?N \<noteq> {}" using units_ne by simp
  have max_in: "Max ?N \<in> ?N"
    by (rule Max_in[OF fin ne])
  then obtain u0 where u0_mem: "u0 \<in> set units"
      and max_eq: "Max ?N = den (u_hi u0)"
    by auto
  let ?h = "u_hi u0"
  have h_mem: "?h \<in> u_hi ` set units"
    using u0_mem by blast
  have h_den: "den ?h = Max ?N"
    using max_eq by simp
  have bound: "\<And>u. u \<in> set units \<Longrightarrow> u_hi u \<sqsubseteq> ?h"
  proof -
    fix u assume u_mem: "u \<in> set units"
    have "den (u_hi u) \<le> Max ?N"
      by (rule Max_ge[OF fin]) (use u_mem in auto)
    then show "u_hi u \<sqsubseteq> ?h"
      by (simp add: cle_def h_den)
  qed
  show thesis by (rule that[OF h_mem bound])
qed

theorem latest_high_trajectory:
  assumes units_ne: "units \<noteq> []"
  obtains h where
      "h \<in> u_hi ` set units"
      "\<And>u. u \<in> set units \<Longrightarrow> u_hi u \<sqsubseteq> h"
      "h \<sqsubseteq> f"
      "\<And>g k. h \<sqsubseteq> g \<Longrightarrow> g \<sqsubseteq> f \<Longrightarrow> k \<in> scope \<Longrightarrow>
         sink_at g k = state_after \<sigma>0 (pfx g) k"
proof -
  from latest_high_exists[OF units_ne] obtain h where h_mem: "h \<in> u_hi ` set units"
      and h_max: "\<And>u. u \<in> set units \<Longrightarrow> u_hi u \<sqsubseteq> h"
    by blast
  have h_f: "h \<sqsubseteq> f"
  proof -
    from h_mem obtain u where "u \<in> set units" "h = u_hi u" by auto
    then show ?thesis using bracket_hi_f by simp
  qed
  have traj: "\<And>g k. h \<sqsubseteq> g \<Longrightarrow> g \<sqsubseteq> f \<Longrightarrow> k \<in> scope \<Longrightarrow>
      sink_at g k = state_after \<sigma>0 (pfx g) k"
  proof -
    fix g k
    assume h_g: "h \<sqsubseteq> g" and "g \<sqsubseteq> f" and k: "k \<in> scope"
    show "sink_at g k = state_after \<sigma>0 (pfx g) k"
    proof (rule contract_cut_at[OF _ k])
      fix u assume "u \<in> set units"
      then have "u_hi u \<sqsubseteq> h" by (rule h_max)
      then show "u_hi u \<sqsubseteq> g" using h_g by (rule cle_trans)
    qed
  qed
  show thesis by (rule that[OF h_mem h_max h_f traj])
qed

subsection \<open>Corollary 1: exhibited shared-witness strengthening (T3)\<close>

text \<open>
  The engine lemma, frontier-parametric: with one coordinate
  @{text cstar} that is a shared state witness for the whole plan ---
  in every bracket, and every read result valid AT it --- the replay at
  every @{text "g \<sqsupseteq> cstar"} equals the source state at @{text g}:
  the sink trajectory coincides with the source trajectory from that
  particular witness onward. This strengthens
  @{text latest_high_trajectory} by supplying a common read-state
  anchor and, when the witness precedes the latest high, an earlier
  trajectory interval. It does not create trajectory existence from
  nothing. Case A keys never consult the refresh; Case B keys are
  quiet from the witness to @{text g}, so the witness value is the
  @{text g} value.
\<close>

lemma shared_witness_trajectory_at:
  assumes wit_bracket: "\<And>u. u \<in> set units \<Longrightarrow> u_lo u \<sqsubseteq> cstar \<and> cstar \<sqsubseteq> u_hi u"
      and wit_honest: "\<And>u k. u \<in> set units \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
                          u_refresh u k = state_after \<sigma>0 (pfx cstar) k"
      and cg: "cstar \<sqsubseteq> g"
      and k: "k \<in> scope"
  shows "sink_at g k = state_after \<sigma>0 (pfx g) k"
proof -
  define u where "u = the_unit k"
  have u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
    using the_unit_props[OF k] u_def by auto
  have lo_cs: "u_lo u \<sqsubseteq> cstar"
    using wit_bracket[OF u_in] by auto
  have lo_g: "u_lo u \<sqsubseteq> g"
    using lo_cs cg by (rule cle_trans)
  show ?thesis
  proof (cases "evs_for k (win (u_lo u) g) = []")
    case False
    have split: "evs_for k (pfx g) =
                   evs_for k (pfx (u_lo u)) @ evs_for k (win (u_lo u) g)"
      by (rule evs_for_pfx_split[OF lo_g])
    have "sink_at g k = ev_img (last (evs_for k (win (u_lo u) g)))"
      using False by (simp add: sink_at_def u_def)
    moreover have "evs_for k (pfx g) \<noteq> []"
      using split False by auto
    moreover have "last (evs_for k (pfx g)) = last (evs_for k (win (u_lo u) g))"
      using split False by (simp add: last_append)
    ultimately show ?thesis
      by (simp add: state_after_last_event)
  next
    case True
    have quiet_cs_g: "evs_for k (win cstar g) = []"
      using evs_for_win_split[OF lo_cs cg] True by auto
    have "sink_at g k = u_refresh u k"
      using True by (simp add: sink_at_def u_def)
    also have "\<dots> = state_after \<sigma>0 (pfx cstar) k"
      by (rule wit_honest[OF u_in k_dom])
    also have "\<dots> = state_after \<sigma>0 (pfx g) k"
      by (rule win_invariant_state[OF cg cle_refl quiet_cs_g, symmetric])
    finally show ?thesis .
  qed
qed

text \<open>
  Corollary 1: the trajectory claim runs from the exhibited shared-state anchor
  @{text cstar} up to the observation frontier @{text f}; beyond
  @{text f} it extends exactly as far as S-OBS is extended (Corollary
  2's premise), never for free. The @{text "g \<sqsubseteq> f"} premise scopes
  the claim to what the capture has observed; the fold-level engine
  above is what discharges it.
\<close>

corollary shared_witness_trajectory:
  assumes "\<And>u. u \<in> set units \<Longrightarrow> u_lo u \<sqsubseteq> cstar \<and> cstar \<sqsubseteq> u_hi u"
      and "\<And>u k. u \<in> set units \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
             u_refresh u k = state_after \<sigma>0 (pfx cstar) k"
      and "cstar \<sqsubseteq> g" and "g \<sqsubseteq> f" and "k \<in> scope"
  shows "sink_at g k = state_after \<sigma>0 (pfx g) k"
  using assms shared_witness_trajectory_at by blast

subsection \<open>Corollary 2: continuation under extended observation\<close>

text \<open>
  Corollary 2: if S-OBS holds with @{text f} replaced
  by @{text "f'"} --- the capture keeps consuming --- then replay to
  @{text "f'"} equals the source state there: pure log replay
  preserves the cut. The extension premise @{text "f \<sqsubseteq> f'"} is
  genuine (it is what makes every bracket bound @{text "f'"}); a
  capture that stops observing at @{text f} claims nothing beyond
  @{text f}.
\<close>

theorem continuation:
  assumes ff': "f \<sqsubseteq> f'"
      and k: "k \<in> scope"
  shows "sink_at f' k = state_after \<sigma>0 (pfx f') k"
proof (rule contract_cut_at[OF _ k])
  fix u assume "u \<in> set units"
  then have "u_hi u \<sqsubseteq> f" by (rule bracket_hi_f)
  then show "u_hi u \<sqsubseteq> f'" using ff' by (rule cle_trans)
qed

end  (* locale capture_contract *)

subsection \<open>Corollary 3: mixing (heterogeneous composition)\<close>

text \<open>
  Corollary 3: the theorem quantifies over an
  arbitrary finite plan with per-unit brackets and arbitrary per-unit
  refresh provenance --- heterogeneous bootstrap is the theorem's
  normal case, not a special case. The composition content is
  mechanized as: two contract instances over the same source with
  disjoint scopes union to a contract instance (whose cut is then
  @{text contract_cut}), and a witness shared by ALL members lifts
  the composite to Corollary 1 (the premises decompose over the
  union). Members with distinct exhibited witnesses compose
  conservatively to T2. The union still has the trajectory supplied
  by @{text latest_high_trajectory}, beginning at its latest high,
  but composition alone supplies neither one common in-bracket state
  witness nor an earlier start. The tablesync fixture in theory
  @{text Contract_Witnesses} shows this automatic guarantee is sharp.
\<close>

context coordinate_space
begin

theorem mixing_union:
  assumes A: "capture_contract L den \<sigma>0 us1 sc1 f"
      and B: "capture_contract L den \<sigma>0 us2 sc2 f"
      and disj: "sc1 \<inter> sc2 = {}"
  shows "capture_contract L den \<sigma>0 (us1 @ us2) (sc1 \<union> sc2) f"
proof -
  interpret a: capture_contract L den \<sigma>0 us1 sc1 f by (rule A)
  interpret b: capture_contract L den \<sigma>0 us2 sc2 f by (rule B)
  show ?thesis
  proof (unfold_locales)
    show "(\<Union>u\<in>set (us1 @ us2). u_dom u) = sc1 \<union> sc2"
      using a.O1_cover b.O1_cover by auto
  next
    fix i j
    assume i: "i < length (us1 @ us2)" and j: "j < length (us1 @ us2)"
       and ne: "i \<noteq> j"
    consider
        (AA) "i < length us1" "j < length us1"
      | (AB) "i < length us1" "\<not> j < length us1"
      | (BA) "\<not> i < length us1" "j < length us1"
      | (BB) "\<not> i < length us1" "\<not> j < length us1"
      by blast
    then show "u_dom ((us1 @ us2) ! i) \<inter> u_dom ((us1 @ us2) ! j) = {}"
    proof cases
      case AA
      then show ?thesis
        using a.O1_disjoint[OF AA(1) AA(2) ne] by (simp add: nth_append)
    next
      case AB
      have m1: "(us1 @ us2) ! i \<in> set us1"
        using AB(1) by (simp add: nth_append)
      have m2: "(us1 @ us2) ! j \<in> set us2"
        using AB(2) j by (auto simp: nth_append)
      show ?thesis
        using a.dom_sub_scope[OF m1] b.dom_sub_scope[OF m2] disj by blast
    next
      case BA
      have m1: "(us1 @ us2) ! i \<in> set us2"
        using BA(1) i by (auto simp: nth_append)
      have m2: "(us1 @ us2) ! j \<in> set us1"
        using BA(2) by (simp add: nth_append)
      show ?thesis
        using a.dom_sub_scope[OF m2] b.dom_sub_scope[OF m1] disj by blast
    next
      case BB
      have b1: "i - length us1 < length us2"
        using i BB(1) by auto
      have b2: "j - length us1 < length us2"
        using j BB(2) by auto
      have b3: "i - length us1 \<noteq> j - length us1"
        using ne BB by auto
      have "u_dom (us2 ! (i - length us1)) \<inter> u_dom (us2 ! (j - length us1)) = {}"
        by (rule b.O1_disjoint[OF b1 b2 b3])
      then show ?thesis
        using BB by (simp add: nth_append)
    qed
  next
    fix u assume "u \<in> set (us1 @ us2)"
    then show "u_lo u \<sqsubseteq> u_hi u"
      using a.bracket_lo_hi b.bracket_lo_hi by auto
  next
    fix u assume "u \<in> set (us1 @ us2)"
    then show "u_hi u \<sqsubseteq> f"
      using a.bracket_hi_f b.bracket_hi_f by auto
  next
    fix u k assume "u \<in> set (us1 @ us2)" and "k \<in> u_dom u"
    then show "\<exists>c. u_lo u \<sqsubseteq> c \<and> c \<sqsubseteq> u_hi u \<and>
                   u_refresh u k = state_after \<sigma>0 (pfx c) k"
      using a.O2_honest b.O2_honest by auto
  qed
qed

text \<open>
  The shared-witness lift: Corollary 1's premises over the union
  decompose over the append, so one witness shared by all members of
  both plans makes the composite plan satisfy Corollary 1's premises
  outright. With distinct witnesses this particular decomposition is
  unavailable. The union retains its T2 cut and conservative
  latest-high trajectory, while a common witness or any earlier start
  needs separate evidence.
\<close>

lemma mixing_shared_witness_lift:
  assumes "\<And>u. u \<in> set us1 \<Longrightarrow> u_lo u \<sqsubseteq> cstar \<and> cstar \<sqsubseteq> u_hi u"
      and "\<And>u. u \<in> set us2 \<Longrightarrow> u_lo u \<sqsubseteq> cstar \<and> cstar \<sqsubseteq> u_hi u"
  shows "\<And>u. u \<in> set (us1 @ us2) \<Longrightarrow> u_lo u \<sqsubseteq> cstar \<and> cstar \<sqsubseteq> u_hi u"
  using assms by auto

lemma mixing_shared_honesty_lift:
  assumes "\<And>u k. u \<in> set us1 \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
             u_refresh u k = state_after \<sigma>0 (pfx cstar) k"
      and "\<And>u k. u \<in> set us2 \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
             u_refresh u k = state_after \<sigma>0 (pfx cstar) k"
  shows "\<And>u k. u \<in> set (us1 @ us2) \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
             u_refresh u k = state_after \<sigma>0 (pfx cstar) k"
  using assms by (metis Un_iff set_append)

end  (* context coordinate_space *)

end
