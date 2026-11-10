(*  Title:   ReadOnly_Instance.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory ReadOnly_Instance
  imports Merge_Disciplines
begin

section \<open>A write-free instance: read-only incremental snapshots over
         executed-GTID sets\<close>

text \<open>
  This theory models read-only incremental snapshots in the style of
  Debezium. The read-only incremental snapshot takes the
  executed global-transaction-ID set as low and high watermarks by
  READING it before and after each chunk select ("uses the executed
  global transaction IDs (GTID) set as high and low watermarks"); an
  event is in the window iff its GTID lies in the high set minus the
  low set; dedup is an in-memory window-discard.

  The formalization:

    \<^item> @{text gtid_history}: one commit-ordered log whose positions
      carry GTIDs, with the single assumption that equal GTIDs occupy
      CONTIGUOUS position blocks (a transaction commits as one
      contiguous run of row events). @{text L} contains completed
      transaction blocks only: no event from an active or aborted
      transaction inhabits the history. This is the model-level content
      of the single-linear-history requirements --- named
      here the \<^bold>\<open>A-linear\<close> assumption class: @{text gtid_mode}
      enforced, and, when the connector reads a replica, the
      commit-order-preserving apply that makes the replica's history
      THE history. A configuration
      violating these is outside the instance's premises, exactly as
      the contract's T0 boundary prescribes.
    \<^item> Executed-set snapshots at transaction boundaries are the
      set-valued coordinates (no
      total order on @{typ "'g set"} is available or needed ---
      subset inclusion is partial; the DENOTATIONS are nested).
      @{text gden} recovers the denoted prefix length;
      @{text gset_inj_on_boundaries} makes it well-defined.
    \<^item> @{text oracle_agreement}: the instance's own operational
      membership decision --- ``GTID in high-set minus low-set'' ---
      agrees exactly with the denotational window. This discharges
      the operational-fidelity requirement for this
      instance; it is the lemma this instance rests on.
    \<^item> @{text readonly_incremental}: the plan locale; its
      @{text A_read} assumption is O2 verbatim at instance level ---
      per-key in-bracket validity enters as a NAMED assumption rather
      than being derived from an isolation level, and each read
      witness sits at a transaction boundary (reads see committed
      states). The sublocale then instantiates the full contract:
      the cut theorem and the window-discard equivalence follow.

  No watermark writes: the
  locale constrains only READS --- the bracket coordinates are
  observed executed-set snapshots, and no assumption places any
  marker/watermark event in @{term L}. Contrast the classic instance,
  whose brackets ARE log positions of watermark UPDATE events.
  Heartbeat-driven window-closure detection is a liveness device for
  DECIDING when the high snapshot may be taken; it has no safety
  content and is deliberately not a locale assumption.
\<close>

subsection \<open>GTID-labeled histories and executed-set coordinates\<close>

locale gtid_history =
  fixes L :: "('k, 'v) event list"
    and gtid :: "nat \<Rightarrow> 'g"
  assumes contiguous:
    "\<And>p q r. p \<le> q \<Longrightarrow> q \<le> r \<Longrightarrow> r < length L \<Longrightarrow>
       gtid p = gtid r \<Longrightarrow> gtid q = gtid p"
begin

definition gset :: "nat \<Rightarrow> 'g set" where
  "gset n = gtid ` {p. p < n}"

text \<open>
  A position @{text n} is a (transaction) boundary when no
  transaction straddles it: no earlier position shares a GTID with
  any position at or after @{text n}. Executed-set snapshots are
  taken between transactions, so observed coordinates live exactly
  on boundaries.
\<close>

definition boundary :: "nat \<Rightarrow> bool" where
  "boundary n \<longleftrightarrow>
     n \<le> length L \<and>
     (\<forall>p q. p < n \<longrightarrow> n \<le> q \<longrightarrow> q < length L \<longrightarrow> gtid p \<noteq> gtid q)"

lemma boundary_zero: "boundary 0"
  by (simp add: boundary_def)

lemma boundary_len: "boundary (length L)"
  by (simp add: boundary_def)

lemma boundary_le_len: "boundary n \<Longrightarrow> n \<le> length L"
  by (simp add: boundary_def)

lemma gset_mono: "m \<le> n \<Longrightarrow> gset m \<subseteq> gset n"
  by (auto simp: gset_def)

lemma gset_strict_new:
  assumes bm: "boundary m" and m_len: "m < length L"
  shows "gtid m \<notin> gset m"
proof
  assume "gtid m \<in> gset m"
  then obtain p where "p < m" and "gtid p = gtid m"
    by (auto simp: gset_def)
  then show False
    using bm m_len by (auto simp: boundary_def)
qed

lemma gset_inj_on_boundaries:
  assumes bm: "boundary m" and bn: "boundary n" and eq: "gset m = gset n"
  shows "m = n"
proof (rule ccontr)
  assume ne: "m \<noteq> n"
  then consider (mn) "m < n" | (nm) "n < m"
    by linarith
  then show False
  proof cases
    case mn
    have m_len: "m < length L"
      using mn boundary_le_len[OF bn] by simp
    have "gtid m \<in> gset n"
      using mn by (auto simp: gset_def)
    then show False
      using gset_strict_new[OF bm m_len] eq by simp
  next
    case nm
    have n_len: "n < length L"
      using nm boundary_le_len[OF bm] by simp
    have "gtid n \<in> gset m"
      using nm by (auto simp: gset_def)
    then show False
      using gset_strict_new[OF bn n_len] eq by simp
  qed
qed

definition gden :: "'g set \<Rightarrow> nat" where
  "gden S = (if \<exists>n. boundary n \<and> gset n = S
             then THE n. boundary n \<and> gset n = S else 0)"

lemma gden_gset [simp]:
  assumes b: "boundary n"
  shows "gden (gset n) = n"
proof -
  have "(THE m. boundary m \<and> gset m = gset n) = n"
  proof (rule the_equality)
    show "boundary n \<and> gset n = gset n"
      using b by simp
  next
    fix m assume "boundary m \<and> gset m = gset n"
    then show "m = n"
      using b gset_inj_on_boundaries by blast
  qed
  then show ?thesis
    using b by (auto simp: gden_def)
qed

lemma gden_le_len: "gden S \<le> length L"
proof (cases "\<exists>n. boundary n \<and> gset n = S")
  case True
  then obtain n where n: "boundary n" "gset n = S"
    by blast
  then have "gden S = n"
    using gden_gset by blast
  then show ?thesis
    using boundary_le_len[OF n(1)] by simp
next
  case False
  then have "gden S = 0"
    unfolding gden_def by (rule if_not_P)
  then show ?thesis by simp
qed

end  (* locale gtid_history *)

sublocale gtid_history \<subseteq> gcs: coordinate_space L gden
  by unfold_locales (rule gden_le_len)

context gtid_history
begin

text \<open>
  The membership-oracle agreement: for coordinates observed at
  boundaries, the instance's operational decision ``the event's GTID
  is in the high set and not in the low set'' holds exactly when the
  event's position lies in the denotational half-open window. This
  is the operational-fidelity requirement, discharged for the
  executed-GTID-set coordinate space.
\<close>

theorem oracle_agreement:
  assumes blo: "boundary nlo" and bhi: "boundary nhi"
      and p: "p < length L"
  shows "gtid p \<in> gset nhi - gset nlo \<longleftrightarrow> nlo \<le> p \<and> p < nhi"
proof
  assume mem: "gtid p \<in> gset nhi - gset nlo"
  have not_lt: "\<not> p < nlo"
  proof
    assume "p < nlo"
    then have "gtid p \<in> gset nlo"
      by (auto simp: gset_def)
    then show False using mem by simp
  qed
  have "p < nhi"
  proof (rule ccontr)
    assume "\<not> p < nhi"
    then have hi_le_p: "nhi \<le> p" by simp
    from mem obtain q where q: "q < nhi" "gtid q = gtid p"
      by (auto simp: gset_def)
    then show False
      using bhi hi_le_p p by (auto simp: boundary_def)
  qed
  with not_lt show "nlo \<le> p \<and> p < nhi" by simp
next
  assume "nlo \<le> p \<and> p < nhi"
  then have lo_le: "nlo \<le> p" and lt_hi: "p < nhi" by auto
  have "gtid p \<in> gset nhi"
    using lt_hi by (auto simp: gset_def)
  moreover have "gtid p \<notin> gset nlo"
  proof
    assume "gtid p \<in> gset nlo"
    then obtain q where "q < nlo" and "gtid q = gtid p"
      by (auto simp: gset_def)
    then show False
      using blo lo_le p by (auto simp: boundary_def)
  qed
  ultimately show "gtid p \<in> gset nhi - gset nlo" by simp
qed

corollary oracle_agreement_den:
  assumes blo: "boundary nlo" and bhi: "boundary nhi"
      and p: "p < length L"
  shows "gtid p \<in> gset nhi - gset nlo \<longleftrightarrow>
           gden (gset nlo) \<le> p \<and> p < gden (gset nhi)"
  using oracle_agreement[OF blo bhi p] by (simp add: blo bhi)

end  (* context gtid_history *)

subsection \<open>The read-only incremental plan\<close>

locale readonly_incremental = gtid_history L gtid
  for L :: "('k, 'v) event list" and gtid :: "nat \<Rightarrow> 'g" +
  fixes \<sigma>0 :: "('k, 'v) state"
    and units :: "('k, 'v, 'g set) cunit list"
    and scope :: "'k set"
    and nf :: nat
    and ulo uhi :: "('k, 'v, 'g set) cunit \<Rightarrow> nat"
  assumes f_boundary: "boundary nf"
      and lo_boundary: "\<And>u. u \<in> set units \<Longrightarrow>
            boundary (ulo u) \<and> u_lo u = gset (ulo u)"
      and hi_boundary: "\<And>u. u \<in> set units \<Longrightarrow>
            boundary (uhi u) \<and> u_hi u = gset (uhi u)"
      and bracket_ord: "\<And>u. u \<in> set units \<Longrightarrow> ulo u \<le> uhi u"
      and bracket_f: "\<And>u. u \<in> set units \<Longrightarrow> uhi u \<le> nf"
      and RO1_cover: "(\<Union>u\<in>set units. u_dom u) = scope"
      and RO1_disjoint: "\<And>i j. i < length units \<Longrightarrow> j < length units \<Longrightarrow>
            i \<noteq> j \<Longrightarrow> u_dom (units ! i) \<inter> u_dom (units ! j) = {}"
      and A_read: "\<And>u k. u \<in> set units \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
            \<exists>n. boundary n \<and> ulo u \<le> n \<and> n \<le> uhi u \<and>
                u_refresh u k = state_after \<sigma>0 (take n L) k"

text \<open>
  The named assumptions: the locale's
  history shape is A-linear (single linear history, contiguous
  transactions); @{text A_read} is the chunk-select read assumption
  (O2 at instance level, witnesses at transaction boundaries);
  bracket coordinates are OBSERVED executed-set snapshots
  (@{text lo_boundary}/@{text hi_boundary}, with no watermark writes).
  Everything else is the plan
  shape (partition, bracket order, frontier bound).
\<close>

sublocale readonly_incremental \<subseteq> rc: capture_contract L gden \<sigma>0 units scope "gset nf"
proof (unfold_locales)
  show "(\<Union>u\<in>set units. u_dom u) = scope"
    by (rule RO1_cover)
next
  fix i j
  assume "i < length units" "j < length units" "i \<noteq> j"
  then show "u_dom (units ! i) \<inter> u_dom (units ! j) = {}"
    by (rule RO1_disjoint)
next
  fix u assume u: "u \<in> set units"
  show "gcs.cle (u_lo u) (u_hi u)"
    using lo_boundary[OF u] hi_boundary[OF u] bracket_ord[OF u]
    by (simp add: gcs.cle_def)
next
  fix u assume u: "u \<in> set units"
  show "gcs.cle (u_hi u) (gset nf)"
    using hi_boundary[OF u] bracket_f[OF u] f_boundary
    by (simp add: gcs.cle_def)
next
  fix u k assume u: "u \<in> set units" and k: "k \<in> u_dom u"
  from A_read[OF u k] obtain n where
    n: "boundary n" "ulo u \<le> n" "n \<le> uhi u"
       "u_refresh u k = state_after \<sigma>0 (take n L) k"
    by blast
  show "\<exists>c. gcs.cle (u_lo u) c \<and> gcs.cle c (u_hi u) \<and>
            u_refresh u k = state_after \<sigma>0 (gcs.pfx c) k"
  proof (intro exI[of _ "gset n"] conjI)
    show "gcs.cle (u_lo u) (gset n)"
      using lo_boundary[OF u] n(1,2) by (simp add: gcs.cle_def)
    show "gcs.cle (gset n) (u_hi u)"
      using hi_boundary[OF u] n(1,3) by (simp add: gcs.cle_def)
    show "u_refresh u k = state_after \<sigma>0 (gcs.pfx (gset n)) k"
      using n(1,4) by (simp add: gcs.pfx_def)
  qed
qed

context readonly_incremental
begin

text \<open>
  The write-free plan is a contract instance,
  so THE theorem applies --- the canonical replay at the frontier
  snapshot is exactly the source state there (tier T2), and the
  in-memory window-discard discipline the connector actually runs is
  covered by the \S6 equivalence theorem, reused verbatim.
\<close>

corollary readonly_cut:
  assumes "k \<in> scope"
  shows "rc.sink_at (gset nf) k = state_after \<sigma>0 (take nf L) k"
proof -
  have "rc.sink_at (gset nf) k = state_after \<sigma>0 (gcs.pfx (gset nf)) k"
    by (rule rc.contract_cut[OF assms])
  then show ?thesis
    by (simp add: gcs.pfx_def f_boundary)
qed

corollary readonly_window_discard:
  assumes "rc.svl_ok svl"
      and "\<And>u. u \<in> set units \<Longrightarrow> gcs.cle s0g (u_lo u)"
      and "k \<in> scope"
  shows "stream_replay (rc.emission svl s0g) k = rc.sink_at (gset nf) k"
  by (rule rc.window_discard_replay[OF assms])

text \<open>
  The two proof boundaries composed explicitly: an exact survivor
  enumeration and consumption beginning at or before every low edge make
  the formal window-discard emission replay to the canonical sink,
  and the contract cut then identifies that final replay with the
  source state at the observed executed-set frontier.  The equality is
  from the empty stream-replay state and is not a physical-prefix or
  delivery guarantee.
\<close>

corollary readonly_emitted_cut:
  assumes svl: "rc.svl_ok svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> gcs.cle s0g (u_lo u)"
      and k: "k \<in> scope"
  shows "stream_replay (rc.emission svl s0g) k = state_after \<sigma>0 (take nf L) k"
  using readonly_window_discard[OF svl s0lo k] readonly_cut[OF k]
  by simp

end  (* context readonly_incremental *)

subsection \<open>Constructed witness (non-vacuity)\<close>

definition L_r :: "(nat, nat) event list" where
  "L_r = [Event 1 (Some 5), Event 2 (Some 6)]"

definition gtid_r :: "nat \<Rightarrow> nat" where
  "gtid_r p = p"

interpretation gh: gtid_history L_r gtid_r
  by unfold_locales (auto simp: gtid_r_def)

lemma gh_boundary_all: "n \<le> 2 \<Longrightarrow> gh.boundary n"
  unfolding gh.boundary_def
  by (auto simp: gtid_r_def L_r_def)

definition unit_r :: "(nat, nat, nat set) cunit" where
  "unit_r = \<lparr>u_dom = {1, 2}, u_lo = gh.gset 0, u_hi = gh.gset 2,
             u_refresh = (\<lambda>k. if k = 1 then Some 5
                              else if k = 2 then Some 6 else None)\<rparr>"

interpretation rw: readonly_incremental L_r gtid_r "\<lambda>_. None" "[unit_r]"
                     "{1, 2}" 2 "\<lambda>_. 0" "\<lambda>_. 2"
proof (unfold_locales)
  show "gh.boundary 2"
    by (simp add: gh_boundary_all)
next
  fix u assume "u \<in> set [unit_r]"
  then show "gh.boundary 0 \<and> u_lo u = gh.gset 0"
    by (simp add: unit_r_def gh_boundary_all)
next
  fix u assume "u \<in> set [unit_r]"
  then show "gh.boundary 2 \<and> u_hi u = gh.gset 2"
    by (simp add: unit_r_def gh_boundary_all)
next
  fix u assume "u \<in> set [unit_r]"
  then show "(0 :: nat) \<le> 2" by simp
next
  fix u assume "u \<in> set [unit_r]"
  then show "(2 :: nat) \<le> 2" by simp
next
  show "(\<Union>u\<in>set [unit_r]. u_dom u) = {1, 2}"
    by (simp add: unit_r_def)
next
  fix i j
  assume "i < length [unit_r]" "j < length [unit_r]" "i \<noteq> j"
  then show "u_dom ([unit_r] ! i) \<inter> u_dom ([unit_r] ! j) = {}"
    by simp
next
  fix u k assume "u \<in> set [unit_r]" and "k \<in> u_dom u"
  then show "\<exists>n. gh.boundary n \<and> 0 \<le> n \<and> n \<le> 2 \<and>
                 u_refresh u k = state_after (\<lambda>_. None) (take n L_r) k"
    by (intro exI[of _ 2] conjI gh_boundary_all)
       (auto simp: unit_r_def L_r_def state_after_def apply_ev_def)
qed

lemma wit_readonly_cut:
  "k \<in> {1, 2} \<Longrightarrow>
     rw.rc.sink_at (gh.gset 2) k = state_after (\<lambda>_. None) (take 2 L_r) k"
  by (rule rw.readonly_cut)

lemma wit_readonly_oracle:
  "gtid_r 1 \<in> gh.gset 2 - gh.gset 0 \<and> gtid_r 0 \<notin> gh.gset 0"
  by (auto simp: gh.gset_def gtid_r_def L_r_def)

end
