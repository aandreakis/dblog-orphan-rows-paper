(*  Title:   Classic_Instance.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Classic_Instance
  imports Cut_Theorem
          "DBLog_Virtual_Cuts.DBLog_Run"
          "DBLog_Virtual_Cuts.Continuation"
begin

section \<open>Classic DBLog satisfies the contract\<close>

text \<open>
  The classic watermarked DBLog formalization is imported as the
  separate session \<^emph>\<open>DBLog\_Virtual\_Cuts\<close>. Its shared-session
  refactoring preserves the published v2.1 mathematical content, as
  documented in \texttt{ARTIFACT\_PROVENANCE.md} at the archive root.
  This theory proves that every wellformed classic DBLog run yields a
  capture plan satisfying the contract, so the contract-level cut
  theorem covers the classic instance. The classic model's chunk
  evidence is
  SINGLE-COORDINATE (each chunk carries one read coordinate, and its
  wellformedness clause WF6 makes every in-domain read result equal the
  source state AT that one coordinate), which INSTANTIATES the
  contract's per-key existential O2 --- the classic instance
  imports upward into the strictly weaker obligation. The bridge
  direction (contract \<open>\<Rightarrow>\<close> classic wellformedness) is not
  claimed.

  The mapping, clause by clause (classic model name \<open>\<rightarrow>\<close> contract name):

    \<^item> source history @{text H} (coordinate-tagged source events,
      WF-H1 non-decreasing) \<open>\<rightarrow>\<close> the log @{text "log_of H"}: Insert
      and Update collapse to a @{const Some} image, Delete to
      @{const None} (@{text img_of}) --- 2020 \S3.1's all-columns
      post-image assumption is S-IMG at the import;
    \<^item> a coordinate @{text c} \<open>\<rightarrow>\<close> the prefix of all events with
      coordinate at-or-before @{text c} (@{text den_of}): under
      WF-H1 sortedness the at-or-before filter IS a list prefix.
      The declared endpoint normalization for this instance: a
      coordinate denotes the prefix INCLUDING every event at that
      coordinate --- the same at-or-before convention the classic model's own
      @{const latest_src_event} uses, and same-coordinate runs land
      wholly inside a denotation, matching the classic model's index
      tie-breaking (its @{const source_pos_order} resolves equal
      coordinates by position, and its latest-lookup takes the LAST
      qualifying position);
    \<^item> chunk \<open>\<rightarrow>\<close> unit: domain \<open>\<rightarrow>\<close> @{text u_dom}; lower watermark
      \<open>\<rightarrow>\<close> @{text u_lo}; upper watermark TRUNCATED AT THE FRONTIER
      \<open>\<rightarrow>\<close> @{text u_hi}; the chunk's read map \<open>\<rightarrow>\<close>
      @{text u_refresh}. The truncation is needed because the classic model's
      wellformedness bounds the READ coordinate by the frontier
      (WF5) but deliberately never bounds the upper watermark ---
      its own headline theorems never consume the watermark
      bracketing --- while the contract's plans live at-or-before
      the frontier by definition. WF4 (bracketing) plus WF5 keep the
      read coordinate inside the truncated bracket, so nothing is
      lost;
    \<^item> WF1(b)/(c) partition clauses \<open>\<rightarrow>\<close> O1; WF4 totality + WF6
      read validity at the read coordinate \<open>\<rightarrow>\<close> O2 (the per-key
      existential witnessed uniformly by the chunk's one
      coordinate); O3 is the totality half of WF4 made
      representational; O5 is discharged by construction (one event
      vocabulary on both paths --- the import maps the same history
      that generated the CDC stream).

  The classic model's observed-CDC clauses (WF2, WF7) and its replay/certificate
  layers are NOT consumed here: the contract's log is the source
  history itself, and observation lives at the contract's discipline
  layer (S-OBS). The consistency corollary at the end ties the two
  developments' conclusions together: the contract's canonical sink
  at the frontier equals the classic model's @{const Src} there --- the
  contract-level theorem generalizes the classic model's result and never
  contradicts it.
\<close>

subsection \<open>History-to-log mapping\<close>

definition img_of :: "('k, 'v) source_event \<Rightarrow> 'v option" where
  "img_of e = (case e of Insert _ v \<Rightarrow> Some v
                       | Update _ v \<Rightarrow> Some v
                       | Delete _ \<Rightarrow> None)"

definition ev_of :: "src_coord \<times> ('k, 'v) source_event \<Rightarrow> ('k, 'v) event" where
  "ev_of p = Event (key_of (hist_event p)) (img_of (hist_event p))"

definition log_of :: "('k, 'v) src_history \<Rightarrow> ('k, 'v) event list" where
  "log_of H = map ev_of H"

definition den_of :: "('k, 'v) src_history \<Rightarrow> src_coord \<Rightarrow> nat" where
  "den_of H c = length (filter (\<lambda>p. hist_coord p \<le> c) H)"

lemma length_log_of [simp]: "length (log_of H) = length H"
  by (simp add: log_of_def)

lemma den_of_le_len: "den_of H c \<le> length (log_of H)"
  by (simp add: den_of_def)

lemma den_of_mono:
  assumes "c \<le> c'"
  shows "den_of H c \<le> den_of H c'"
  unfolding den_of_def
proof (induction H)
  case Nil
  then show ?case by simp
next
  case (Cons p H)
  then show ?case
    using assms by (auto intro: order.trans)
qed

subsection \<open>Sorted histories: the at-or-before filter is a prefix\<close>

lemma sorted_filter_le_takeWhile:
  assumes "sorted (map f xs)"
  shows "filter (\<lambda>x. f x \<le> c) xs = takeWhile (\<lambda>x. f x \<le> c) xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "f x \<le> c")
    case True
    then show ?thesis using Cons by simp
  next
    case False
    have "\<And>y. y \<in> set xs \<Longrightarrow> \<not> f y \<le> c"
    proof -
      fix y assume "y \<in> set xs"
      then have "f x \<le> f y" using Cons.prems by simp
      then show "\<not> f y \<le> c" using False by (auto intro: order.trans)
    qed
    then have "filter (\<lambda>x. f x \<le> c) xs = []"
      by (simp add: filter_empty_conv)
    then show ?thesis using False by simp
  qed
qed

lemma den_of_take:
  assumes "sorted (map hist_coord H)"
  shows "take (den_of H c) H = filter (\<lambda>p. hist_coord p \<le> c) H"
proof -
  have "filter (\<lambda>p. hist_coord p \<le> c) H = takeWhile (\<lambda>p. hist_coord p \<le> c) H"
    by (rule sorted_filter_le_takeWhile[OF assms])
  then show ?thesis
    unfolding den_of_def
    by (metis takeWhile_eq_take)
qed

subsection \<open>Generic filter-by-position normal form\<close>

lemma filter_map_nth_upt:
  "filter Q xs = map ((!) xs) (filter (\<lambda>i. Q (xs ! i)) [0..<length xs])"
proof -
  have "filter Q xs = filter Q (map ((!) xs) [0..<length xs])"
    by (simp add: map_nth)
  also have "\<dots> = map ((!) xs) (filter (Q \<circ> (!) xs) [0..<length xs])"
    by (rule filter_map)
  finally show ?thesis
    by (simp add: comp_def)
qed

subsection \<open>State correspondence: the contract fold meets @{const Src}\<close>

lemma evs_for_log_of:
  "evs_for k (log_of (filter (\<lambda>p. hist_coord p \<le> c) H))
     = map ev_of (filter (\<lambda>p. hist_coord p \<le> c \<and> key_of (hist_event p) = k) H)"
proof -
  have "evs_for k (log_of (filter (\<lambda>p. hist_coord p \<le> c) H))
          = map ev_of (filter (\<lambda>p. key_of (hist_event p) = k)
                              (filter (\<lambda>p. hist_coord p \<le> c) H))"
    by (simp add: log_of_def evs_for_def filter_map comp_def ev_of_def)
  then show ?thesis
    by (simp add: conj_commute)
qed

lemma state_correspondence:
  fixes b0 :: "('k, 'v) state" and H :: "('k, 'v) src_history"
  assumes srt: "sorted (map hist_coord H)"
  shows "state_after b0 (take (den_of H c) (log_of H)) k = Src b0 H c k"
proof -
  have take_log: "take (den_of H c) (log_of H)
                    = log_of (filter (\<lambda>p. hist_coord p \<le> c) H)"
    by (simp add: log_of_def take_map den_of_take[OF srt])
  define P where
    "P = (\<lambda>p :: src_coord \<times> ('k, 'v) source_event.
            hist_coord p \<le> c \<and> key_of (hist_event p) = k)"
  define cand where "cand = filter (\<lambda>i. P (H ! i)) [0..<length H]"
  have elems: "filter P H = map ((!) H) cand"
    unfolding cand_def by (rule filter_map_nth_upt)
  have evs: "evs_for k (take (den_of H c) (log_of H)) = map ev_of (map ((!) H) cand)"
    by (simp add: take_log evs_for_log_of elems flip: P_def)
  have latest: "latest_src_event H c k
                  = (if cand = [] then None else Some (last cand))"
    unfolding latest_src_event_def cand_def P_def
    by (simp add: src_le_eq_less_eq Let_def conj_commute)
  show ?thesis
  proof (cases "cand = []")
    case True
    then have "evs_for k (take (den_of H c) (log_of H)) = []"
      by (simp add: evs)
    then have lhs: "state_after b0 (take (den_of H c) (log_of H)) k = b0 k"
      by (simp add: state_after_no_events)
    have "Src b0 H c k = b0 k"
      using latest True by (simp add: Src_def)
    then show ?thesis using lhs by simp
  next
    case False
    then have ne: "evs_for k (take (den_of H c) (log_of H)) \<noteq> []"
      by (simp add: evs)
    have lhs: "state_after b0 (take (den_of H c) (log_of H)) k
                 = ev_img (ev_of (H ! last cand))"
      using state_after_last_event[OF ne] evs False
      by (simp add: last_map)
    have "Src b0 H c k = img_of (hist_event (H ! last cand))"
      using latest False
      by (simp add: Src_def img_of_def split: source_event.split)
    then show ?thesis
      using lhs by (simp add: ev_of_def)
  qed
qed

subsection \<open>Derived units and the import theorem\<close>

definition unit_of_chunk ::
    "('k :: linorder, 'v) run \<Rightarrow> nat \<Rightarrow> ('k, 'v, src_coord) cunit" where
  "unit_of_chunk R ch =
     \<lparr>u_dom = chunk_domain R ch,
      u_lo = chunk_lower_watermark R ch,
      u_hi = min (chunk_upper_watermark R ch) (frontier_of R),
      u_refresh = (\<lambda>k. case chunk_read_result R ch k of
                         Some m \<Rightarrow> m | None \<Rightarrow> None)\<rparr>"

definition units_of ::
    "('k :: linorder, 'v) run \<Rightarrow> ('k, 'v, src_coord) cunit list" where
  "units_of R = map (unit_of_chunk R) (chunks_list R)"

text \<open>
  Projections of the wellformedness clauses this import consumes. The
  wellformedness body is one large conjunction; searchful methods are
  unreliable at that hypothesis size, so each projection first splits
  the body into its verbatim conjuncts by deterministic conjunction
  elimination plus assumption matching, then instantiates the one
  small fact it needs.
\<close>

lemma wf_src_binding:
  assumes "wellformed_dblog_run b0 R H"
  shows "src_history_of R = H"
  using assms unfolding wellformed_dblog_run_def by (rule conjunct1)

lemma wf_src_wellformed:
  assumes wf: "wellformed_dblog_run b0 R H"
  shows "wellformed_src_history H"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body show ?thesis by (elim conjE)
qed

lemma wf_domains_disjoint:
  assumes wf: "wellformed_dblog_run b0 R H"
      and ch: "ch1 \<in> chunks R" "ch2 \<in> chunks R" "ch1 \<noteq> ch2"
  shows "chunk_domain R ch1 \<inter> chunk_domain R ch2 = {}"
proof -
  have all: "\<forall>ch1\<in>chunks R. \<forall>ch2\<in>chunks R.
               ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R ch1 \<inter> chunk_domain R ch2 = {}"
    using wf[unfolded wellformed_dblog_run_def] by (elim conjE)
  from bspec[OF bspec[OF all ch(1)] ch(2)] ch(3) show ?thesis by blast
qed

lemma wf_domains_cover:
  assumes wf: "wellformed_dblog_run b0 R H"
  shows "canonical_chunk_ownership_domain R = scope_of R"
proof -
  note wf_body = wf[unfolded wellformed_dblog_run_def]
  from wf_body show ?thesis by (elim conjE)
qed

lemma wf_read_evidence:
  assumes "wellformed_dblog_run b0 R H"
  shows "\<forall>ch\<in>chunks R.
           src_le (chunk_lower_watermark R ch) (chunk_read_coordinate R ch)
         \<and> src_le (chunk_read_coordinate R ch) (chunk_upper_watermark R ch)
         \<and> (\<forall>k\<in>chunk_domain R ch.
              \<exists>m. chunk_read_result R ch k = Some m)
         \<and> (\<forall>k\<in>chunk_domain R ch. \<forall>m.
              chunk_read_result R ch k = Some m
                \<longleftrightarrow> Refresh k m (chunk_read_coordinate R ch)
                     \<in> set (clean_prefix_of R))"
  using assms[unfolded wellformed_dblog_run_def] by (elim conjE)

lemma wf_watermark_bracket:
  assumes wf: "wellformed_dblog_run b0 R H" and ch: "ch \<in> chunks R"
  shows "chunk_lower_watermark R ch \<le> chunk_read_coordinate R ch"
    and "chunk_read_coordinate R ch \<le> chunk_upper_watermark R ch"
  using bspec[OF wf_read_evidence[OF wf] ch]
  by (simp_all add: src_le_eq_less_eq)

lemma wf_read_total:
  assumes wf: "wellformed_dblog_run b0 R H"
      and ch: "ch \<in> chunks R" and k: "k \<in> chunk_domain R ch"
  shows "\<exists>m. chunk_read_result R ch k = Some m"
  using bspec[OF wf_read_evidence[OF wf] ch] k by blast

lemma wf_read_before_frontier:
  assumes wf: "wellformed_dblog_run b0 R H" and ch: "ch \<in> chunks R"
  shows "chunk_read_coordinate R ch \<le> frontier_of R"
proof -
  have all: "\<forall>ch\<in>chunks R. src_le (chunk_read_coordinate R ch) (frontier_of R)"
    using wf[unfolded wellformed_dblog_run_def] by (elim conjE)
  from bspec[OF all ch] show ?thesis by (simp add: src_le_eq_less_eq)
qed

lemma wf_read_honest:
  assumes wf: "wellformed_dblog_run b0 R H"
      and ch: "ch \<in> chunks R" and k: "k \<in> chunk_domain R ch"
      and m: "chunk_read_result R ch k = Some m"
  shows "m = Src b0 H (chunk_read_coordinate R ch) k"
proof -
  have all: "\<forall>ch\<in>chunks R. \<forall>k\<in>chunk_domain R ch. \<forall>m.
               chunk_read_result R ch k = Some m
                 \<longrightarrow> m = Src b0 H (chunk_read_coordinate R ch) k"
    using wf[unfolded wellformed_dblog_run_def] by (elim conjE)
  from bspec[OF bspec[OF all ch] k] m show ?thesis by blast
qed

theorem classic_imports_upward:
  assumes wf: "wellformed_dblog_run b0 R H"
  shows "capture_contract (log_of H) (den_of H) b0 (units_of R)
                          (scope_of R) (frontier_of R)"
proof -
  have wf_h: "wellformed_src_history H"
    by (rule wf_src_wellformed[OF wf])
  have srt: "sorted (map hist_coord H)"
    using wf_h by (rule wellformed_src_history_sorted)
  interpret pc: coordinate_space "log_of H" "den_of H"
    by unfold_locales (rule den_of_le_len)
  show ?thesis
  proof (unfold_locales)
    show "(\<Union>u\<in>set (units_of R). u_dom u) = scope_of R"
      using wf_domains_cover[OF wf]
      by (simp add: units_of_def unit_of_chunk_def
                    canonical_chunk_ownership_domain_def chunks_list_set)
  next
    fix i j
    assume i: "i < length (units_of R)" and j: "j < length (units_of R)"
       and ne: "i \<noteq> j"
    have li: "i < length (chunks_list R)" and lj: "j < length (chunks_list R)"
      using i j by (simp_all add: units_of_def)
    have mem_i: "chunks_list R ! i \<in> chunks R"
     and mem_j: "chunks_list R ! j \<in> chunks R"
      using li lj chunks_list_set by (metis nth_mem)+
    have "chunks_list R ! i \<noteq> chunks_list R ! j"
      using chunks_list_distinct li lj ne nth_eq_iff_index_eq by blast
    then have "chunk_domain R (chunks_list R ! i)
                 \<inter> chunk_domain R (chunks_list R ! j) = {}"
      by (rule wf_domains_disjoint[OF wf mem_i mem_j])
    then show "u_dom (units_of R ! i) \<inter> u_dom (units_of R ! j) = {}"
      using li lj by (simp add: units_of_def unit_of_chunk_def)
  next
    fix u assume "u \<in> set (units_of R)"
    then obtain ch where ch: "ch \<in> chunks R" and u: "u = unit_of_chunk R ch"
      by (auto simp: units_of_def chunks_list_set)
    have rc_min: "chunk_read_coordinate R ch
                    \<le> min (chunk_upper_watermark R ch) (frontier_of R)"
      using wf_watermark_bracket(2)[OF wf ch] wf_read_before_frontier[OF wf ch]
      by (simp add: min.bounded_iff)
    have "chunk_lower_watermark R ch
            \<le> min (chunk_upper_watermark R ch) (frontier_of R)"
      using wf_watermark_bracket(1)[OF wf ch] rc_min
      by (rule order.trans)
    then show "pc.cle (u_lo u) (u_hi u)"
      by (simp add: u unit_of_chunk_def pc.cle_def den_of_mono)
  next
    fix u assume "u \<in> set (units_of R)"
    then obtain ch where ch: "ch \<in> chunks R" and u: "u = unit_of_chunk R ch"
      by (auto simp: units_of_def chunks_list_set)
    show "pc.cle (u_hi u) (frontier_of R)"
      by (simp add: u unit_of_chunk_def pc.cle_def den_of_mono)
  next
    fix u k assume "u \<in> set (units_of R)" and k: "k \<in> u_dom u"
    then obtain ch where ch: "ch \<in> chunks R" and u: "u = unit_of_chunk R ch"
      by (auto simp: units_of_def chunks_list_set)
    have k_dom: "k \<in> chunk_domain R ch"
      using k by (simp add: u unit_of_chunk_def)
    obtain m where m: "chunk_read_result R ch k = Some m"
      using wf_read_total[OF wf ch k_dom] by blast
    have refresh: "u_refresh u k = m"
      by (simp add: u unit_of_chunk_def m)
    have honest: "m = Src b0 H (chunk_read_coordinate R ch) k"
      by (rule wf_read_honest[OF wf ch k_dom m])
    show "\<exists>c. pc.cle (u_lo u) c \<and> pc.cle c (u_hi u) \<and>
              u_refresh u k = state_after b0 (pc.pfx c) k"
    proof (intro exI[of _ "chunk_read_coordinate R ch"] conjI)
      show "pc.cle (u_lo u) (chunk_read_coordinate R ch)"
        using wf_watermark_bracket(1)[OF wf ch]
        by (simp add: u unit_of_chunk_def pc.cle_def den_of_mono)
      have "chunk_read_coordinate R ch
              \<le> min (chunk_upper_watermark R ch) (frontier_of R)"
        using wf_watermark_bracket(2)[OF wf ch] wf_read_before_frontier[OF wf ch]
        by (simp add: min.bounded_iff)
      then show "pc.cle (chunk_read_coordinate R ch) (u_hi u)"
        by (simp add: u unit_of_chunk_def pc.cle_def den_of_mono)
      show "u_refresh u k = state_after b0 (pc.pfx (chunk_read_coordinate R ch)) k"
        using refresh honest state_correspondence[OF srt]
        by (simp add: pc.pfx_def)
    qed
  qed
qed

subsection \<open>Consistency with the classic model's conclusion\<close>

corollary classic_sink_is_Src:
  assumes wf: "wellformed_dblog_run b0 R H"
      and k: "k \<in> scope_of R"
  shows "capture_plan.sink_at (log_of H) (den_of H) (units_of R)
                              (frontier_of R) k
           = Src b0 H (frontier_of R) k"
proof -
  interpret cc: capture_contract "log_of H" "den_of H" b0 "units_of R"
                  "scope_of R" "frontier_of R"
    by (rule classic_imports_upward[OF wf])
  have srt: "sorted (map hist_coord H)"
    using wf_src_wellformed[OF wf] by (rule wellformed_src_history_sorted)
  have "cc.sink_at (frontier_of R) k
          = state_after b0 (cc.pfx (frontier_of R)) k"
    by (rule cc.contract_cut[OF k])
  also have "\<dots> = Src b0 H (frontier_of R) k"
    using state_correspondence[OF srt] by (simp add: cc.pfx_def)
  finally show ?thesis .
qed

end
