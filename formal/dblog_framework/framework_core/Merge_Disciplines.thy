(*  Title:   Merge_Disciplines.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Merge_Disciplines
  imports Cut_Theorem
begin

section \<open>Emitted streams and the window-discard equivalence\<close>

text \<open>
  Real merge disciplines must meet an equivalence obligation:
  a discipline's emitted stream must replay to the same @{text sink}
  as the canonical rule. This theory builds the stream substrate and
  discharges the obligation for the classic \<^emph>\<open>window-discard\<close>
  discipline --- the engine of the classic bridge, and the discipline
  the write-free instance reuses.

  Stream model: an emitted stream is a list of events --- each item
  writes a key's value-or-absence --- replayed by the same per-key
  fold as the source dynamics but starting from the EMPTY map. The
  empty start is the stream-replay convention: a key never emitted
  denotes absence, so absence-by-omission IS the absence result.
  Refresh entries for absent keys are therefore never emitted, while
  delete EVENTS are (they arrive from the log).

  The emission is built occurrence-tagged: each item carries the
  source version it denotes --- an event at log position @{text p} is
  tagged @{text "Suc p"} (the state version after it commits); a
  unit's surviving refresh entries are emitted when the unit's window
  closes, tagged with the close position. Tags make the
  window-discard per-key monotonicity claim a sortedness statement
  (@{text window_discard_monotone}); dropping tags gives the plain
  stream. S-OBS enters exactly here: the emission is constructed from
  the consumed segment starting at @{text s0}, and the discipline
  premise @{text "s0 \<sqsubseteq> u_lo u"} for every unit is S-OBS's
  consumption-start clause; the construction is single-pass, which is
  the discipline's retention requirement.
\<close>

subsection \<open>List auxiliaries\<close>

lemma upt_split:
  "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> [a..<c] = [a..<b] @ [b..<c]"
  by (metis le_Suc_ex upt_add_eq_append)

lemma sorted_filter':
  "sorted xs \<Longrightarrow> sorted (filter P xs)"
  by (induction xs) auto

lemma concat_map_upt_single:
  assumes zero: "\<And>i. i < n \<Longrightarrow> i \<noteq> i0 \<Longrightarrow> g i = []"
      and i0: "i0 < n"
  shows "concat (map g [0..<n]) = g i0"
proof -
  have split: "[0..<n] = [0..<i0] @ [i0..<n]"
    using i0 by (intro upt_split) linarith+
  have head: "[i0..<n] = i0 # [Suc i0..<n]"
    using i0 by (simp add: upt_rec)
  have all_nil: "\<And>xs. (\<And>i. i \<in> set xs \<Longrightarrow> g i = []) \<Longrightarrow> concat (map g xs) = []"
  proof -
    fix xs :: "nat list"
    assume "\<And>i. i \<in> set xs \<Longrightarrow> g i = []"
    then show "concat (map g xs) = []"
      by (induction xs) auto
  qed
  have left: "concat (map g [0..<i0]) = []"
    by (rule all_nil) (use zero i0 in auto)
  have right: "concat (map g [Suc i0..<n]) = []"
    by (rule all_nil) (use zero in auto)
  have "concat (map g [0..<n]) = concat (map g [0..<i0]) @ concat (map g [i0..<n])"
    unfolding split by (simp only: map_append concat_append)
  also have "\<dots> = concat (map g [0..<i0]) @ g i0 @ concat (map g [Suc i0..<n])"
    unfolding head by (simp only: list.map(2) concat.simps(2))
  also have "\<dots> = g i0"
    unfolding left right by simp
  finally show ?thesis .
qed

lemma concat_if_map_filter:
  "concat (map (\<lambda>p. if Q p then [h p] else []) ps) = map h (filter Q ps)"
  by (induction ps) auto

lemma filter_concat_map:
  "filter P (concat (map g xs)) = concat (map (filter P \<circ> g) xs)"
  by (induction xs) auto

lemma distinct_filter_eq:
  "distinct ks \<Longrightarrow> filter (\<lambda>x. x = k) ks = (if k \<in> set ks then [k] else [])"
  by (induction ks) auto

lemma sorted_map_Suc: "sorted xs \<Longrightarrow> sorted (map Suc xs)"
  by (induction xs) auto

subsection \<open>Stream replay and position normal forms\<close>

definition stream_replay :: "('k, 'v) event list \<Rightarrow> ('k, 'v) state" where
  "stream_replay S = state_after (\<lambda>_. None) S"

text \<open>
  The generic final-output lift separates two proof boundaries.  The
  contract theorem establishes the canonical replay at the frontier.
  A merge discipline separately establishes that its finite emitted
  list has the same final replay, from the empty replay state, on every
  scoped key.  Composing those equalities gives the source state at the
  frontier.  This statement concerns final replay only.  It does not
  identify physical prefixes of the emitted list with canonical replay
  prefixes, and it carries no transport, populated-sink, or
  exactly-once claim.
\<close>

context capture_contract
begin

theorem emitted_replay_cut:
  assumes equiv: "\<And>k. k \<in> scope \<Longrightarrow> stream_replay E k = sink_at f k"
      and k: "k \<in> scope"
  shows "stream_replay E k = state_after \<sigma>0 (pfx f) k"
  using equiv[OF k] contract_cut[OF k] by simp

corollary emitted_replay_cut_scope:
  assumes equiv: "\<And>k. k \<in> scope \<Longrightarrow> stream_replay E k = sink_at f k"
  shows "\<forall>k\<in>scope. stream_replay E k = state_after \<sigma>0 (pfx f) k"
  using emitted_replay_cut[OF equiv] by blast

end  (* context capture_contract *)

context coordinate_space
begin

text \<open>
  Positions of a key's events in a half-open position interval: the
  normal form every interleaving argument reduces to. @{text kposs}
  is sorted (a filtered enumeration), and windows and prefixes both
  project onto it.
\<close>

definition kposs :: "'k \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "kposs k a b = filter (\<lambda>p. ev_key (L ! p) = k) [a..<b]"

lemma kposs_sorted: "sorted (kposs k a b)"
  unfolding kposs_def by (intro sorted_filter') simp

lemma kposs_bounds: "p \<in> set (kposs k a b) \<Longrightarrow> a \<le> p \<and> p < b"
  by (auto simp: kposs_def)

lemma kposs_split:
  "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> kposs k a c = kposs k a b @ kposs k b c"
  by (metis filter_append kposs_def upt_split)

lemma win_map_nth:
  assumes le: "lo \<sqsubseteq> hi"
  shows "win lo hi = map ((!) L) [den lo..<den hi]"
proof (rule nth_equalityI)
  show "length (win lo hi) = length (map ((!) L) [den lo..<den hi])"
    using win_length[OF le] by simp
  fix p assume "p < length (win lo hi)"
  then show "win lo hi ! p = map ((!) L) [den lo..<den hi] ! p"
    using win_nth[OF le] win_length[OF le] by simp
qed

lemma evs_for_win_kposs:
  "lo \<sqsubseteq> hi \<Longrightarrow> evs_for k (win lo hi) = map ((!) L) (kposs k (den lo) (den hi))"
  by (simp add: win_map_nth evs_for_def kposs_def filter_map comp_def)

lemma pfx_map_nth: "pfx c = map ((!) L) [0..<den c]"
proof (rule nth_equalityI)
  show "length (pfx c) = length (map ((!) L) [0..<den c])"
    by simp
  fix p assume "p < length (pfx c)"
  then show "pfx c ! p = map ((!) L) [0..<den c] ! p"
    by (simp add: pfx_def den_le_len)
qed

lemma evs_for_pfx_kposs:
  "evs_for k (pfx c) = map ((!) L) (kposs k 0 (den c))"
  by (simp add: pfx_map_nth evs_for_def kposs_def filter_map comp_def)

end  (* context coordinate_space *)

subsection \<open>The window-discard emission\<close>

context capture_plan
begin

text \<open>
  Survivors of a unit: keys of its domain that are present in the
  refresh AND untouched by the unit's own window --- exactly the
  buffered rows the classic discipline still holds when the high
  watermark arrives. The emission takes a survivor ENUMERATION
  @{text svl} as a parameter (any duplicate-free listing of each
  unit's survivor set); real captures emit rows physically, so an
  enumeration always exists (@{text svl_exists} below), and no
  finiteness assumption on states is smuggled into the contract.
\<close>

definition survivors :: "('k, 'v, 'c) cunit \<Rightarrow> 'k set" where
  "survivors u =
     {k \<in> u_dom u. u_refresh u k \<noteq> None \<and>
                    evs_for k (win (u_lo u) (u_hi u)) = []}"

definition svl_ok :: "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> bool" where
  "svl_ok svl \<longleftrightarrow>
     (\<forall>u \<in> set units. distinct (svl u) \<and> set (svl u) = survivors u)"

definition close_block ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> ('k, 'v, 'c) cunit
       \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "close_block svl u =
     map (\<lambda>k. (den (u_hi u), Event k (u_refresh u k))) (svl u)"

definition closes_at ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> nat \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "closes_at svl p =
     concat (map (\<lambda>i. if den (u_hi (units ! i)) = p
                      then close_block svl (units ! i) else [])
                 [0..<length units])"

text \<open>
  The tagged window-discard emission from consumption start
  @{text s0} to the frontier: a single pass over the consumed log
  segment; every event is passed through at its own position; when a
  position reaches a unit's high edge, that unit's survivors are
  emitted before the event at that position (their refresh entries
  are older than anything from the high edge onward). Units whose
  high edge sits at the frontier close after the last consumed
  event.
\<close>

definition emission_t ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "emission_t svl s0 =
     concat (map (\<lambda>p. closes_at svl p @ [(Suc p, L ! p)]) [den s0..<den f])
     @ closes_at svl (den f)"

definition emission ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c \<Rightarrow> ('k, 'v) event list" where
  "emission svl s0 = map snd (emission_t svl s0)"

definition titems_for ::
    "'k \<Rightarrow> (nat \<times> ('k, 'v) event) list \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "titems_for k S = filter (\<lambda>x. ev_key (snd x) = k) S"

lemma evs_for_map_snd:
  "evs_for k (map snd S) = map snd (titems_for k S)"
  by (simp add: evs_for_def titems_for_def filter_map comp_def)

end  (* context capture_plan *)

subsection \<open>Per-key characterization of the emission\<close>

context capture_contract
begin

lemma survivors_sub_dom: "survivors u \<subseteq> u_dom u"
  by (auto simp: survivors_def)

lemma svl_exists:
  assumes fin: "\<And>u. u \<in> set units \<Longrightarrow> finite (survivors u)"
  shows "\<exists>svl. svl_ok svl"
proof -
  define svl where
    "svl = (\<lambda>u. SOME xs. distinct xs \<and> set xs = survivors u)"
  have "distinct (svl u) \<and> set (svl u) = survivors u"
    if u: "u \<in> set units" for u
  proof -
    have "\<exists>xs. distinct xs \<and> set xs = survivors u"
      using finite_distinct_list[OF fin[OF u]] by metis
    then show ?thesis
      unfolding svl_def by (rule someI_ex)
  qed
  then have "svl_ok svl"
    by (simp add: svl_ok_def)
  then show ?thesis by blast
qed

lemma titems_close_block:
  assumes svl: "svl_ok svl" and u_in: "u \<in> set units"
  shows "titems_for k (close_block svl u) =
           (if k \<in> set (svl u)
            then [(den (u_hi u), Event k (u_refresh u k))] else [])"
proof -
  have dis: "distinct (svl u)"
    using svl u_in by (simp add: svl_ok_def)
  have "titems_for k (close_block svl u) =
          map (\<lambda>k'. (den (u_hi u), Event k' (u_refresh u k')))
              (filter (\<lambda>k'. k' = k) (svl u))"
    by (simp add: titems_for_def close_block_def filter_map comp_def)
  then show ?thesis
    using distinct_filter_eq[OF dis] by simp
qed

lemma titems_closes_at:
  assumes svl: "svl_ok svl" and k: "k \<in> scope"
  shows "titems_for k (closes_at svl p) =
           (if den (u_hi (the_unit k)) = p \<and> k \<in> set (svl (the_unit k))
            then [(p, Event k (u_refresh (the_unit k) k))] else [])"
proof -
  obtain i0 where i0: "i0 < length units" "units ! i0 = the_unit k"
    using the_unit_props(1)[OF k] by (meson in_set_conv_nth)
  have others: "titems_for k (if den (u_hi (units ! i)) = p
                              then close_block svl (units ! i) else []) = []"
    if i: "i < length units" and ne: "i \<noteq> i0" for i
  proof -
    have ui_in: "units ! i \<in> set units" using i by simp
    have "k \<notin> set (svl (units ! i))"
    proof
      assume "k \<in> set (svl (units ! i))"
      then have "k \<in> survivors (units ! i)"
        using svl ui_in by (simp add: svl_ok_def)
      then have "k \<in> u_dom (units ! i)"
        using survivors_sub_dom by auto
      then have eq: "units ! i = the_unit k"
        using covering_unit_unique[OF ui_in _ the_unit_props(1)[OF k]
                                       the_unit_props(2)[OF k]] by blast
      have "i = i0"
        by (rule the_unit_position_unique[OF k i eq i0(1) i0(2)])
      with ne show False ..
    qed
    then show ?thesis
      using titems_close_block[OF svl ui_in]
      by (simp add: titems_for_def)
  qed
  have "titems_for k (closes_at svl p) =
          concat (map (\<lambda>i. titems_for k (if den (u_hi (units ! i)) = p
                                          then close_block svl (units ! i) else []))
                      [0..<length units])"
    unfolding closes_at_def titems_for_def
    by (simp add: filter_concat_map comp_def if_distrib
             cong: if_cong)
  also have "\<dots> = titems_for k (if den (u_hi (units ! i0)) = p
                                 then close_block svl (units ! i0) else [])"
    by (rule concat_map_upt_single[OF others i0(1)])
  finally show ?thesis
    using titems_close_block[OF svl the_unit_props(1)[OF k]] i0(2)
    by (simp add: titems_for_def)
qed

text \<open>
  The master characterization: a key's occurrences in the emission
  are its consumed pre-close events, then (iff it survived) its
  unit's refresh entry at the close position, then its post-close
  events. Everything below --- the equivalence and the monotonicity
  claim --- reads off this shape.
\<close>

lemma titems_emission_master:
  assumes svl: "svl_ok svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
  shows "titems_for k (emission_t svl s0) =
           map (\<lambda>p. (Suc p, L ! p)) (kposs k (den s0) (den (u_hi (the_unit k))))
           @ (if k \<in> set (svl (the_unit k))
              then [(den (u_hi (the_unit k)),
                     Event k (u_refresh (the_unit k) k))] else [])
           @ map (\<lambda>p. (Suc p, L ! p)) (kposs k (den (u_hi (the_unit k))) (den f))"
proof -
  define u where "u = the_unit k"
  define hp where "hp = den (u_hi u)"
  have u_in: "u \<in> set units"
    using the_unit_props(1)[OF k] u_def by simp
  have s0_le_lo: "den s0 \<le> den (u_lo u)"
    using s0lo[OF u_in] by (simp add: cle_def)
  have lo_le_hp: "den (u_lo u) \<le> hp"
    using bracket_lo_hi[OF u_in] by (simp add: cle_def hp_def)
  have hp_le_f: "hp \<le> den f"
    using bracket_hi_f[OF u_in] by (simp add: cle_def hp_def)
  have s0_le_hp: "den s0 \<le> hp"
    using s0_le_lo lo_le_hp by simp

  have closes: "\<And>p. titems_for k (closes_at svl p) =
           (if hp = p \<and> k \<in> set (svl u)
            then [(p, Event k (u_refresh u k))] else [])"
    using titems_closes_at[OF svl k] by (simp add: u_def hp_def)

  have dist: "titems_for k (emission_t svl s0) =
        concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<den f])
        @ titems_for k (closes_at svl (den f))"
    unfolding emission_t_def titems_for_def
    by (simp add: filter_concat_map comp_def cong: map_cong if_cong)

  show ?thesis
  proof (cases "hp < den f")
    case False
    then have hp_f: "hp = den f"
      using hp_le_f by simp
    have no_close: "\<And>p. p \<in> set [den s0..<den f] \<Longrightarrow>
                      titems_for k (closes_at svl p) = []"
      using closes hp_f by auto
    have "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<den f])
          = concat (map (\<lambda>p. if ev_key (L ! p) = k then [(Suc p, L ! p)] else [])
                    [den s0..<den f])"
      using no_close by (intro arg_cong[where f = concat] map_cong) auto
    also have "\<dots> = map (\<lambda>p. (Suc p, L ! p)) (kposs k (den s0) (den f))"
      by (simp add: concat_if_map_filter kposs_def)
    finally show ?thesis
      using dist closes hp_f
      by (simp add: u_def hp_def kposs_def)
  next
    case True
    have split: "[den s0..<den f] = [den s0..<hp] @ [hp..<den f]"
      using s0_le_hp hp_le_f by (rule upt_split)
    have head: "[hp..<den f] = hp # [Suc hp..<den f]"
      using True by (simp add: upt_rec)
    have pre: "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<hp])
          = map (\<lambda>p. (Suc p, L ! p)) (kposs k (den s0) hp)"
    proof -
      have "\<And>p. p \<in> set [den s0..<hp] \<Longrightarrow> titems_for k (closes_at svl p) = []"
        using closes by auto
      then have "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<hp])
            = concat (map (\<lambda>p. if ev_key (L ! p) = k then [(Suc p, L ! p)] else [])
                      [den s0..<hp])"
        by (intro arg_cong[where f = concat] map_cong) auto
      then show ?thesis
        by (simp add: concat_if_map_filter kposs_def)
    qed
    have post: "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [Suc hp..<den f])
          = map (\<lambda>p. (Suc p, L ! p)) (kposs k (Suc hp) (den f))"
    proof -
      have "\<And>p. p \<in> set [Suc hp..<den f] \<Longrightarrow> titems_for k (closes_at svl p) = []"
        using closes by auto
      then have "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [Suc hp..<den f])
            = concat (map (\<lambda>p. if ev_key (L ! p) = k then [(Suc p, L ! p)] else [])
                      [Suc hp..<den f])"
        by (intro arg_cong[where f = concat] map_cong) auto
      then show ?thesis
        by (simp add: concat_if_map_filter kposs_def)
    qed
    have closes_hp: "titems_for k (closes_at svl hp)
          = (if k \<in> set (svl u) then [(hp, Event k (u_refresh u k))] else [])"
      using closes[of hp] by simp
    have trail: "titems_for k (closes_at svl (den f)) = []"
      using closes True by auto
    have kposs_peel: "kposs k hp (den f)
          = (if ev_key (L ! hp) = k then hp # kposs k (Suc hp) (den f)
             else kposs k (Suc hp) (den f))"
      unfolding kposs_def using head by simp
    have peel: "titems_for k (emission_t svl s0)
            = concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<hp])
              @ titems_for k (closes_at svl hp)
              @ (if ev_key (L ! hp) = k then [(Suc hp, L ! hp)] else [])
              @ concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [Suc hp..<den f])
              @ titems_for k (closes_at svl (den f))"
      unfolding dist by (simp add: split head)
    show ?thesis
      unfolding peel pre post trail closes_hp
      by (simp add: kposs_peel flip: u_def hp_def)
  qed
qed

subsection \<open>The window-discard equivalence theorem\<close>

text \<open>
  Window-discard equivalence: the emitted stream replays to the
  canonical @{text sink} on the scope. Together with
  @{text contract_cut} this is ``the log wins'' as a theorem: buffer
  the unit's refresh, discard on any in-window event for a buffered
  key, emit survivors at the high edge --- and the replay is exactly
  the source state at the frontier.
\<close>

theorem window_discard_replay:
  assumes svl: "svl_ok svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
  shows "stream_replay (emission svl s0) k = sink_at f k"
proof -
  define u where "u = the_unit k"
  define hp where "hp = den (u_hi u)"
  have u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
    using the_unit_props[OF k] u_def by auto
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" using bracket_lo_hi[OF u_in] .
  have hi_f: "u_hi u \<sqsubseteq> f" using bracket_hi_f[OF u_in] .
  have lo_f: "u_lo u \<sqsubseteq> f" using lo_hi hi_f by (rule cle_trans)
  have s0_le_lo: "den s0 \<le> den (u_lo u)"
    using s0lo[OF u_in] by (simp add: cle_def)
  have lo_le_hp: "den (u_lo u) \<le> hp"
    using lo_hi by (simp add: cle_def hp_def)
  have hp_le_f: "hp \<le> den f"
    using hi_f by (simp add: cle_def hp_def)
  have s0_le_hp: "den s0 \<le> hp" using s0_le_lo lo_le_hp by simp

  have surv_iff: "k \<in> set (svl u) \<longleftrightarrow> k \<in> survivors u"
    using svl u_in by (simp add: svl_ok_def)

  have master: "evs_for k (emission svl s0) =
          map ((!) L) (kposs k (den s0) hp)
          @ (if k \<in> set (svl u) then [Event k (u_refresh u k)] else [])
          @ map ((!) L) (kposs k hp (den f))"
    unfolding emission_def evs_for_map_snd
    using titems_emission_master[OF svl s0lo k]
    by (simp add: u_def hp_def comp_def if_distrib map_append
             cong: if_cong)

  have win_lo_hi: "evs_for k (win (u_lo u) (u_hi u))
                     = map ((!) L) (kposs k (den (u_lo u)) hp)"
    using evs_for_win_kposs[OF lo_hi] by (simp add: hp_def)
  have win_lo_f: "evs_for k (win (u_lo u) f)
                     = map ((!) L) (kposs k (den (u_lo u)) (den f))"
    using evs_for_win_kposs[OF lo_f] by simp
  have kposs_lo_f_split:
      "kposs k (den (u_lo u)) (den f)
         = kposs k (den (u_lo u)) hp @ kposs k hp (den f)"
    using lo_le_hp hp_le_f by (rule kposs_split)
  have kposs_s0_hp_split:
      "kposs k (den s0) hp
         = kposs k (den s0) (den (u_lo u)) @ kposs k (den (u_lo u)) hp"
    using s0_le_lo lo_le_hp by (rule kposs_split)

  show ?thesis
  proof (cases "kposs k (den (u_lo u)) (den f) = []")
    case False
    then have sink: "sink_at f k
                       = ev_img (last (map ((!) L) (kposs k (den (u_lo u)) (den f))))"
      by (simp add: sink_at_def win_lo_f flip: u_def)
    show ?thesis
    proof (cases "kposs k hp (den f) = []")
      case post_ne: False
      have last_sink: "last (kposs k (den (u_lo u)) (den f)) = last (kposs k hp (den f))"
        using kposs_lo_f_split post_ne by (simp add: last_append)
      have stream_ne: "evs_for k (emission svl s0) \<noteq> []"
        using master post_ne by auto
      have last_stream: "last (evs_for k (emission svl s0))
                           = (!) L (last (kposs k hp (den f)))"
        using master post_ne by (simp add: last_append last_map)
      have "stream_replay (emission svl s0) k
              = ev_img (L ! last (kposs k hp (den f)))"
        unfolding stream_replay_def
        using state_after_last_event[OF stream_ne] last_stream by simp
      moreover have "sink_at f k = ev_img (L ! last (kposs k hp (den f)))"
        using sink last_sink False by (simp add: last_map)
      ultimately show ?thesis by simp
    next
      case post_e: True
      have win_ne: "kposs k (den (u_lo u)) hp \<noteq> []"
        using False kposs_lo_f_split post_e by auto
      have not_surv: "k \<notin> set (svl u)"
        using surv_iff win_lo_hi win_ne by (auto simp: survivors_def)
      have master': "evs_for k (emission svl s0)
                       = map ((!) L) (kposs k (den s0) hp)"
        using master not_surv post_e by simp
      have s0_ne: "kposs k (den s0) hp \<noteq> []"
        using kposs_s0_hp_split win_ne by auto
      have last_pre: "last (kposs k (den s0) hp) = last (kposs k (den (u_lo u)) hp)"
        using kposs_s0_hp_split win_ne by (simp add: last_append)
      have last_sink: "last (kposs k (den (u_lo u)) (den f))
                         = last (kposs k (den (u_lo u)) hp)"
        using kposs_lo_f_split post_e by simp
      have "stream_replay (emission svl s0) k
              = ev_img (L ! last (kposs k (den (u_lo u)) hp))"
        unfolding stream_replay_def
        by (subst state_after_key)
           (simp add: master' s0_ne last_pre last_map)
      moreover have "sink_at f k = ev_img (L ! last (kposs k (den (u_lo u)) hp))"
        using sink last_sink False by (simp add: last_map)
      ultimately show ?thesis by simp
    qed
  next
    case True
    have win_e: "kposs k (den (u_lo u)) hp = []"
     and post_e: "kposs k hp (den f) = []"
      using True kposs_lo_f_split by auto
    have no_win_evs: "evs_for k (win (u_lo u) (u_hi u)) = []"
      using win_lo_hi win_e by simp
    have sink: "sink_at f k = u_refresh u k"
      using True by (simp add: sink_at_def win_lo_f flip: u_def)
    have pre_only: "kposs k (den s0) hp = kposs k (den s0) (den (u_lo u))"
      using kposs_s0_hp_split win_e by simp
    show ?thesis
    proof (cases "u_refresh u k")
      case (Some v)
      then have "k \<in> survivors u"
        using k_dom no_win_evs by (simp add: survivors_def)
      then have surv: "k \<in> set (svl u)"
        using surv_iff by simp
      have "evs_for k (emission svl s0)
              = map ((!) L) (kposs k (den s0) hp) @ [Event k (u_refresh u k)]"
        using master surv post_e by simp
      then have "stream_replay (emission svl s0) k = u_refresh u k"
        unfolding stream_replay_def
        by (simp add: state_after_key last_append)
      then show ?thesis using sink by simp
    next
      case None
      then have not_surv: "k \<notin> set (svl u)"
        using surv_iff by (auto simp: survivors_def)
      have master': "evs_for k (emission svl s0)
                       = map ((!) L) (kposs k (den s0) (den (u_lo u)))"
        using master not_surv post_e pre_only by simp
      from O2_honest[OF u_in k_dom] obtain c where
        c_lo: "u_lo u \<sqsubseteq> c" and c_hi: "c \<sqsubseteq> u_hi u" and
        honest: "u_refresh u k = state_after \<sigma>0 (pfx c) k"
        by blast
      show ?thesis
      proof (cases "kposs k (den s0) (den (u_lo u)) = []")
        case True
        then have "evs_for k (emission svl s0) = []"
          using master' by simp
        then have "stream_replay (emission svl s0) k = None"
          unfolding stream_replay_def by (simp add: state_after_no_events)
        then show ?thesis using sink None by simp
      next
        case pre_ne: False
        define q where "q = last (kposs k (den s0) (den (u_lo u)))"
        have lo_le_c: "den (u_lo u) \<le> den c" using c_lo by (simp add: cle_def)
        have c_le_hp: "den c \<le> hp" using c_hi by (simp add: cle_def hp_def)
        have win_lo_c_e: "kposs k (den (u_lo u)) (den c) = []"
          using win_e kposs_split[OF lo_le_c c_le_hp] by auto
        have c_split: "kposs k 0 (den c)
                         = kposs k 0 (den s0) @ kposs k (den s0) (den (u_lo u))"
          using kposs_split[OF le0 s0_le_lo, of k]
                kposs_split[OF _ lo_le_c, of 0 k] win_lo_c_e
          by (metis append_Nil2 le0 s0_le_lo order_trans)
        have pfx_ne: "evs_for k (pfx c) \<noteq> []"
          using evs_for_pfx_kposs c_split pre_ne by simp
        have last_pfx: "last (kposs k 0 (den c)) = q"
          using c_split pre_ne q_def by (simp add: last_append)
        have "state_after \<sigma>0 (pfx c) k = ev_img (L ! q)"
          using state_after_last_event[OF pfx_ne] evs_for_pfx_kposs last_pfx pre_ne
          by (simp add: last_map last_append c_split)
        with honest None have img_q: "ev_img (L ! q) = None" by simp
        have "stream_replay (emission svl s0) k = ev_img (L ! q)"
          unfolding stream_replay_def
          by (subst state_after_key)
             (simp add: master' pre_ne q_def last_map)
        then show ?thesis using sink None img_q by simp
      qed
    qed
  qed
qed

subsection \<open>Window-discard per-key monotonicity\<close>

text \<open>
  Under window-discard the emission is per-key monotone outright: the
  occurrence tags of a key's items never decrease along the stream
  --- a key emits its events in commit order, plus its refresh at the
  unit's high edge if it survived the window, and a survivor's later
  post-window events follow the refresh. Never an older state over a
  newer one.
\<close>

theorem window_discard_monotone:
  assumes svl: "svl_ok svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
  shows "sorted (map fst (titems_for k (emission_t svl s0)))"
proof -
  define hp where "hp = den (u_hi (the_unit k))"
  have m: "map fst (titems_for k (emission_t svl s0)) =
        map Suc (kposs k (den s0) hp)
        @ (if k \<in> set (svl (the_unit k)) then [hp] else [])
        @ map Suc (kposs k hp (den f))"
    using titems_emission_master[OF svl s0lo k]
    by (cases "k \<in> set (svl (the_unit k))") (simp_all add: hp_def comp_def)
  have s_pre: "sorted (map Suc (kposs k (den s0) hp))"
    by (simp add: sorted_map_Suc kposs_sorted)
  have s_post: "sorted (map Suc (kposs k hp (den f)))"
    by (simp add: sorted_map_Suc kposs_sorted)
  have pre_le: "\<And>a. a \<in> set (map Suc (kposs k (den s0) hp)) \<Longrightarrow> a \<le> hp"
    using kposs_bounds by (auto intro: Suc_leI)
  have post_ge: "\<And>b. b \<in> set (map Suc (kposs k hp (den f))) \<Longrightarrow> hp \<le> b"
    using kposs_bounds by (auto intro: le_SucI)
  have cross: "\<And>x y. x \<in> set (kposs k (den s0) hp) \<Longrightarrow>
                  y \<in> set (kposs k hp (den f)) \<Longrightarrow> x \<le> y"
    using kposs_bounds by (metis less_le_trans less_imp_le)
  show ?thesis
  proof (cases "k \<in> set (svl (the_unit k))")
    case True
    have "sorted (map Suc (kposs k (den s0) hp)
                    @ hp # map Suc (kposs k hp (den f)))"
      using s_pre s_post pre_le post_ge cross
      by (auto simp: sorted_append intro: order.trans)
    then show ?thesis using m True by simp
  next
    case False
    have "sorted (map Suc (kposs k (den s0) hp)
                    @ map Suc (kposs k hp (den f)))"
      using s_pre s_post pre_le post_ge cross
      by (auto simp: sorted_append intro: order.trans)
    then show ?thesis using m False by simp
  qed
qed

end  (* context capture_contract *)

end
