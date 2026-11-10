(*  Title:   Contract_Witnesses.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Contract_Witnesses
  imports Merge_Disciplines
begin

section \<open>Constructed witnesses and boundary fixtures\<close>

text \<open>
  House discipline: every main result is exercised at concrete
  witnesses, so none is vacuously true. @{text wit_}-prefixed facts
  are positive witnesses; @{text fix_}-prefixed facts are negative or
  boundary fixtures. Four fixtures over small concrete logs:

    \<^item> the \<^emph>\<open>torn read\<close>: a unit whose
      refresh is valid per key at DIFFERENT in-bracket coordinates,
      with provably NO single in-bracket coordinate serving all keys
      --- an instance the single-coordinate obligation would reject,
      yet the cut theorem still delivers the frontier state;
    \<^item> the \<^emph>\<open>tablesync\<close> shape (Corollary 3's sharpness
      boundary): two point-bracket units, each T3 on its own scope at
      its own witness, whose composite has no common in-bracket
      witness and provably breaks the source-trajectory property at an
      intermediate coordinate. The automatic composition result is
      T2 with its conservative trajectory beginning at the latest
      high;
    \<^item> the \<^emph>\<open>amortized shared bracket\<close>: one bracket
      shared by two units with one shared state witness --- Corollary
      1 lifts the composite to T3, so amortization preserved the
      tier;
    \<^item> a \<^emph>\<open>surviving refresh\<close> under window-discard: a unit whose
      refresh entry survives its window and must override a pre-low
      consumed event in the emitted stream --- the equivalence
      theorem's subtlest path, evaluated concretely.
\<close>

subsection \<open>The witness log and coordinate space\<close>

definition L_w :: "(nat, nat) event list" where
  "L_w = [Event 1 (Some 1), Event 2 (Some 2)]"

definition den_w :: "nat \<Rightarrow> nat" where
  "den_w c = min c 2"

definition s0_w :: "(nat, nat) state" where
  "s0_w = (\<lambda>_. None)"

interpretation wc: coordinate_space L_w den_w
  by unfold_locales (simp add: den_w_def L_w_def)

lemma den_w_cases: "den_w c = 0 \<or> den_w c = 1 \<or> den_w c = 2"
  by (simp add: den_w_def) linarith

subsection \<open>Fixture 1: the torn read\<close>

definition torn_unit :: "(nat, nat, nat) cunit" where
  "torn_unit = \<lparr>u_dom = {1, 2}, u_lo = 0, u_hi = 2,
                u_refresh = (\<lambda>k. if k = 2 then Some 2 else None)\<rparr>"

interpretation torn: capture_contract L_w den_w s0_w "[torn_unit]" "{1, 2}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [torn_unit]. u_dom u) = {1, 2}"
    by (simp add: torn_unit_def)
next
  fix i j
  assume "i < length [torn_unit]" "j < length [torn_unit]" "i \<noteq> j"
  then show "u_dom ([torn_unit] ! i) \<inter> u_dom ([torn_unit] ! j) = {}"
    by simp
next
  fix u assume "u \<in> set [torn_unit]"
  then show "wc.cle (u_lo u) (u_hi u)"
    by (simp add: torn_unit_def wc.cle_def den_w_def)
next
  fix u assume "u \<in> set [torn_unit]"
  then show "wc.cle (u_hi u) 2"
    by (simp add: torn_unit_def wc.cle_def den_w_def)
next
  fix u k assume u: "u \<in> set [torn_unit]" and k: "k \<in> u_dom u"
  then have u_eq: "u = torn_unit" and k_cases: "k = 1 \<or> k = 2"
    by (auto simp: torn_unit_def)
  show "\<exists>c. wc.cle (u_lo u) c \<and> wc.cle c (u_hi u) \<and>
            u_refresh u k = state_after s0_w (wc.pfx c) k"
  proof (cases "k = 1")
    case True
    then show ?thesis
      unfolding wc.cle_def wc.pfx_def
      by (intro exI[of _ 0])
         (simp add: u_eq torn_unit_def den_w_def L_w_def
                    s0_w_def state_after_def apply_ev_def)
  next
    case False
    with k_cases have "k = 2" by simp
    then show ?thesis
      unfolding wc.cle_def wc.pfx_def
      by (intro exI[of _ 2])
         (simp add: u_eq torn_unit_def den_w_def L_w_def
                    s0_w_def state_after_def apply_ev_def)
  qed
qed

lemma wit_torn_contract:
  "capture_contract L_w den_w s0_w [torn_unit] {1, 2} 2"
  by (rule torn.capture_contract_axioms)

text \<open>
  NO single in-bracket coordinate is valid
  for both keys of the unit --- key 1's absence result is valid
  only before the first event, key 2's presence result only after
  the second. Single-coordinate validity would reject this instance;
  the contract admits it, and the cut still holds
  (@{text wit_torn_cut} below). Together with theorem
  @{text "capture_contract.contract_cut"}, this shows that per-key
  validity suffices even when no shared read coordinate exists.
\<close>

lemma fix_torn_no_single_witness:
  "\<not> (\<exists>c. wc.cle (u_lo torn_unit) c \<and> wc.cle c (u_hi torn_unit) \<and>
          (\<forall>k \<in> u_dom torn_unit.
             u_refresh torn_unit k = state_after s0_w (wc.pfx c) k))"
proof
  assume "\<exists>c. wc.cle (u_lo torn_unit) c \<and> wc.cle c (u_hi torn_unit) \<and>
              (\<forall>k \<in> u_dom torn_unit.
                 u_refresh torn_unit k = state_after s0_w (wc.pfx c) k)"
  then obtain c where
    honest: "\<forall>k \<in> u_dom torn_unit.
               u_refresh torn_unit k = state_after s0_w (wc.pfx c) k"
    by blast
  have h1: "None = state_after s0_w (take (den_w c) L_w) 1"
   and h2: "Some 2 = state_after s0_w (take (den_w c) L_w) 2"
    using honest unfolding wc.pfx_def by (auto simp: torn_unit_def)
  from den_w_cases[of c] show False
  proof (elim disjE)
    assume d: "den_w c = 0"
    then show False
      using h2 by (simp add: d L_w_def s0_w_def state_after_def apply_ev_def)
  next
    assume d: "den_w c = 1"
    then show False
      using h2 by (simp add: d L_w_def s0_w_def state_after_def apply_ev_def)
  next
    assume d: "den_w c = 2"
    then show False
      using h1 by (simp add: d L_w_def s0_w_def state_after_def apply_ev_def)
  qed
qed

lemma wit_torn_the_unit [simp]:
  assumes "k \<in> {1 :: nat, 2}"
  shows "torn.the_unit k = torn_unit"
  using torn.the_unit_props[OF assms] by simp

lemma wit_torn_cut:
  "torn.sink_at 2 1 = Some 1" "torn.sink_at 2 2 = Some 2"
proof -
  have c1: "torn.sink_at 2 1 = state_after s0_w (wc.pfx 2) 1"
    by (rule torn.contract_cut) simp
  show "torn.sink_at 2 1 = Some 1"
    unfolding c1 wc.pfx_def
    by (simp add: den_w_def L_w_def s0_w_def state_after_def apply_ev_def)
  have c2: "torn.sink_at 2 2 = state_after s0_w (wc.pfx 2) 2"
    by (rule torn.contract_cut) simp
  show "torn.sink_at 2 2 = Some 2"
    unfolding c2 wc.pfx_def
    by (simp add: den_w_def L_w_def s0_w_def state_after_def apply_ev_def)
qed

subsection \<open>Fixture 2: the tablesync shape (composition is sharp at T2)\<close>

definition syncA :: "(nat, nat, nat) cunit" where
  "syncA = \<lparr>u_dom = {1}, u_lo = 0, u_hi = 0, u_refresh = (\<lambda>_. None)\<rparr>"

definition syncB :: "(nat, nat, nat) cunit" where
  "syncB = \<lparr>u_dom = {2}, u_lo = 2, u_hi = 2,
            u_refresh = (\<lambda>k. if k = 2 then Some 2 else None)\<rparr>"

interpretation sync: capture_contract L_w den_w s0_w "[syncA, syncB]" "{1, 2}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [syncA, syncB]. u_dom u) = {1, 2}"
    by (auto simp: syncA_def syncB_def)
next
  fix i j
  assume i: "i < length [syncA, syncB]" and j: "j < length [syncA, syncB]"
     and ne: "i \<noteq> j"
  then have "(i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0)"
    by auto
  then show "u_dom ([syncA, syncB] ! i) \<inter> u_dom ([syncA, syncB] ! j) = {}"
    by (auto simp: syncA_def syncB_def)
next
  fix u assume "u \<in> set [syncA, syncB]"
  then show "wc.cle (u_lo u) (u_hi u)"
    by (auto simp: syncA_def syncB_def wc.cle_def den_w_def)
next
  fix u assume "u \<in> set [syncA, syncB]"
  then show "wc.cle (u_hi u) 2"
    by (auto simp: syncA_def syncB_def wc.cle_def den_w_def)
next
  fix u k assume u: "u \<in> set [syncA, syncB]" and k: "k \<in> u_dom u"
  show "\<exists>c. wc.cle (u_lo u) c \<and> wc.cle c (u_hi u) \<and>
            u_refresh u k = state_after s0_w (wc.pfx c) k"
  proof (cases "u = syncA")
    case True
    then have "k = 1" using k by (simp add: syncA_def)
    then show ?thesis
      unfolding wc.cle_def wc.pfx_def
      by (intro exI[of _ 0])
         (simp add: True syncA_def den_w_def L_w_def
                    s0_w_def state_after_def apply_ev_def)
  next
    case False
    then have uB: "u = syncB" using u by simp
    then have "k = 2" using k by (simp add: syncB_def)
    then show ?thesis
      unfolding wc.cle_def wc.pfx_def
      by (intro exI[of _ 2])
         (simp add: uB syncB_def den_w_def L_w_def
                    s0_w_def state_after_def apply_ev_def)
  qed
qed

lemma wit_sync_contract:
  "capture_contract L_w den_w s0_w [syncA, syncB] {1, 2} 2"
  by (rule sync.capture_contract_axioms)

lemma wit_sync_the_unit_2 [simp]: "sync.the_unit 2 = syncB"
  using sync.the_unit_props[of 2] by (auto simp: syncA_def)

text \<open>
  The composite breaks the source-trajectory property at the
  intermediate coordinate 1: unit B's refresh (valid at ITS witness,
  the log end) already shows key 2 present, while the source at
  coordinate 1 does not. Hence no trajectory onset strictly before
  the frontier exists for this composite plan. Its latest high is the
  frontier 2, so @{text latest_high_trajectory} still supplies the
  degenerate conservative interval from 2 to 2. The two point
  brackets also have no common in-bracket coordinate. Each member
  alone nevertheless has its own exhibited shared witness, as shown
  by @{text wit_sync_memberA_T3} and @{text wit_sync_memberB_T3}.
\<close>

lemma fix_sync_trajectory_breaks:
  "sync.sink_at 1 2 \<noteq> state_after s0_w (wc.pfx 1) 2"
proof -
  have win_e: "wc.win (u_lo syncB) 1 = []"
    unfolding wc.win_def by (simp add: syncB_def den_w_def L_w_def)
  have "sync.sink_at 1 2 = Some 2"
    unfolding sync.sink_at_def wit_sync_the_unit_2 win_e
    by (simp add: syncB_def)
  moreover have "state_after s0_w (wc.pfx 1) 2 = None"
    unfolding wc.pfx_def
    by (simp add: den_w_def L_w_def s0_w_def state_after_def apply_ev_def)
  ultimately show ?thesis by simp
qed

lemma fix_sync_no_early_onset:
  "\<not> (\<exists>cstar. wc.cle cstar 1 \<and>
        (\<forall>g. wc.cle cstar g \<longrightarrow> wc.cle g 2 \<longrightarrow>
           (\<forall>k \<in> {1, 2}. sync.sink_at g k = state_after s0_w (wc.pfx g) k)))"
proof
  assume "\<exists>cstar. wc.cle cstar 1 \<and>
        (\<forall>g. wc.cle cstar g \<longrightarrow> wc.cle g 2 \<longrightarrow>
           (\<forall>k \<in> {1, 2}. sync.sink_at g k = state_after s0_w (wc.pfx g) k))"
  then obtain cstar where cs: "wc.cle cstar 1"
    and traj: "\<And>g. wc.cle cstar g \<Longrightarrow> wc.cle g 2 \<Longrightarrow>
                 \<forall>k \<in> {1, 2}. sync.sink_at g k = state_after s0_w (wc.pfx g) k"
    by blast
  have "wc.cle 1 2"
    by (simp add: wc.cle_def den_w_def)
  then have "sync.sink_at 1 2 = state_after s0_w (wc.pfx 1) 2"
    using traj[OF cs] by simp
  then show False
    using fix_sync_trajectory_breaks by simp
qed

text \<open>
  The paper states Proposition 2 with an onset strictly below the
  frontier. The preceding lemma is an equivalent fixture-specific form:
  in this fixture, strictly below frontier 2 is exactly at or below
  coordinate 1. The following
  statement gives the paper's quantifier exactly. Strictness is expressed
  by @{term "wc.cle cstar 2 \<and> \<not> wc.cle 2 cstar"}.
\<close>

lemma fix_sync_no_strictly_below_frontier_onset:
  "\<not> (\<exists>cstar. wc.cle cstar 2 \<and> \<not> wc.cle 2 cstar \<and>
        (\<forall>g. wc.cle cstar g \<longrightarrow> wc.cle g 2 \<longrightarrow>
           (\<forall>k \<in> {1, 2}.
              sync.sink_at g k = state_after s0_w (wc.pfx g) k)))"
proof
  assume "\<exists>cstar. wc.cle cstar 2 \<and> \<not> wc.cle 2 cstar \<and>
        (\<forall>g. wc.cle cstar g \<longrightarrow> wc.cle g 2 \<longrightarrow>
           (\<forall>k \<in> {1, 2}.
              sync.sink_at g k = state_after s0_w (wc.pfx g) k))"
  then obtain cstar where below: "wc.cle cstar 2" "\<not> wc.cle 2 cstar"
    and traj: "\<And>g. wc.cle cstar g \<Longrightarrow> wc.cle g 2 \<Longrightarrow>
                 \<forall>k \<in> {1, 2}.
                   sync.sink_at g k = state_after s0_w (wc.pfx g) k"
    by blast
  have den_le_one: "den_w cstar \<le> 1"
    using below unfolding wc.cle_def
    by (simp add: den_w_def)
  have cs1: "wc.cle cstar 1"
    using den_le_one by (simp add: wc.cle_def den_w_def)
  have one_two: "wc.cle 1 2"
    by (simp add: wc.cle_def den_w_def)
  have "sync.sink_at 1 2 = state_after s0_w (wc.pfx 1) 2"
    using traj[OF cs1 one_two] by simp
  then show False
    using fix_sync_trajectory_breaks by simp
qed

lemma fix_sync_no_common_bracket_witness:
  "\<not> (\<exists>cstar. \<forall>u \<in> set [syncA, syncB].
          wc.cle (u_lo u) cstar \<and> wc.cle cstar (u_hi u))"
proof
  assume "\<exists>cstar. \<forall>u \<in> set [syncA, syncB].
          wc.cle (u_lo u) cstar \<and> wc.cle cstar (u_hi u)"
  then obtain cstar where all:
      "\<forall>u \<in> set [syncA, syncB].
        wc.cle (u_lo u) cstar \<and> wc.cle cstar (u_hi u)" by blast
  have upper0: "wc.cle cstar 0"
    using all by (simp add: syncA_def)
  have lower2: "wc.cle 2 cstar"
    using all by (simp add: syncB_def)
  have "den_w cstar \<le> 0" and "2 \<le> den_w cstar"
    using upper0 lower2 by (simp_all add: wc.cle_def den_w_def)
  then show False by linarith
qed

interpretation syncAo: capture_contract L_w den_w s0_w "[syncA]" "{1}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [syncA]. u_dom u) = {1}"
    by (simp add: syncA_def)
next
  fix i j
  assume "i < length [syncA]" "j < length [syncA]" "i \<noteq> j"
  then show "u_dom ([syncA] ! i) \<inter> u_dom ([syncA] ! j) = {}" by simp
next
  fix u assume "u \<in> set [syncA]"
  then show "wc.cle (u_lo u) (u_hi u)"
    by (simp add: syncA_def wc.cle_def den_w_def)
next
  fix u assume "u \<in> set [syncA]"
  then show "wc.cle (u_hi u) 2"
    by (simp add: syncA_def wc.cle_def den_w_def)
next
  fix u k assume "u \<in> set [syncA]" and "k \<in> u_dom u"
  then show "\<exists>c. wc.cle (u_lo u) c \<and> wc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after s0_w (wc.pfx c) k"
    unfolding wc.cle_def wc.pfx_def
    by (intro exI[of _ 0])
       (simp add: syncA_def den_w_def L_w_def
                  s0_w_def state_after_def apply_ev_def)
qed

lemma wit_sync_memberA_shared_bracket:
  "\<And>u. u \<in> set [syncA] \<Longrightarrow>
      wc.cle (u_lo u) 0 \<and> wc.cle 0 (u_hi u)"
  by (simp add: syncA_def wc.cle_def den_w_def)

lemma wit_sync_memberA_shared_honesty:
  "\<And>u k. u \<in> set [syncA] \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
      u_refresh u k = state_after s0_w (wc.pfx 0) k"
  unfolding wc.pfx_def
  by (simp add: syncA_def den_w_def L_w_def
                s0_w_def state_after_def apply_ev_def)

lemma wit_sync_memberA_T3:
  assumes "wc.cle 0 g" and "wc.cle g 2" and "k \<in> {1 :: nat}"
  shows "syncAo.sink_at g k = state_after s0_w (wc.pfx g) k"
  by (rule syncAo.shared_witness_trajectory[OF
        wit_sync_memberA_shared_bracket wit_sync_memberA_shared_honesty assms])

interpretation syncBo: capture_contract L_w den_w s0_w "[syncB]" "{2}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [syncB]. u_dom u) = {2}"
    by (simp add: syncB_def)
next
  fix i j
  assume "i < length [syncB]" "j < length [syncB]" "i \<noteq> j"
  then show "u_dom ([syncB] ! i) \<inter> u_dom ([syncB] ! j) = {}" by simp
next
  fix u assume "u \<in> set [syncB]"
  then show "wc.cle (u_lo u) (u_hi u)"
    by (simp add: syncB_def wc.cle_def den_w_def)
next
  fix u assume "u \<in> set [syncB]"
  then show "wc.cle (u_hi u) 2"
    by (simp add: syncB_def wc.cle_def den_w_def)
next
  fix u k assume "u \<in> set [syncB]" and "k \<in> u_dom u"
  then show "\<exists>c. wc.cle (u_lo u) c \<and> wc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after s0_w (wc.pfx c) k"
    unfolding wc.cle_def wc.pfx_def
    by (intro exI[of _ 2])
       (simp add: syncB_def den_w_def L_w_def
                  s0_w_def state_after_def apply_ev_def)
qed

lemma wit_sync_memberB_shared_bracket:
  "\<And>u. u \<in> set [syncB] \<Longrightarrow>
      wc.cle (u_lo u) 2 \<and> wc.cle 2 (u_hi u)"
  by (simp add: syncB_def wc.cle_def den_w_def)

lemma wit_sync_memberB_shared_honesty:
  "\<And>u k. u \<in> set [syncB] \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
      u_refresh u k = state_after s0_w (wc.pfx 2) k"
  unfolding wc.pfx_def
  by (auto simp: syncB_def den_w_def L_w_def s0_w_def
                 state_after_def apply_ev_def)

lemma wit_sync_memberB_T3:
  assumes "wc.cle 2 g" and "wc.cle g 2" and "k \<in> {2 :: nat}"
  shows "syncBo.sink_at g k = state_after s0_w (wc.pfx g) k"
proof (rule syncBo.shared_witness_trajectory[of 2 g k])
  show "\<And>u. u \<in> set [syncB] \<Longrightarrow> wc.cle (u_lo u) 2 \<and> wc.cle 2 (u_hi u)"
    by (rule wit_sync_memberB_shared_bracket)
  show "\<And>u k. u \<in> set [syncB] \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
          u_refresh u k = state_after s0_w (wc.pfx 2) k"
    by (rule wit_sync_memberB_shared_honesty)
qed (use assms in auto)

theorem wit_sync_composition_sharpness:
  shows "capture_contract L_w den_w s0_w [syncA] {1} 2"
    and "capture_contract L_w den_w s0_w [syncB] {2} 2"
    and "\<forall>u \<in> set [syncA].
           wc.cle (u_lo u) 0 \<and> wc.cle 0 (u_hi u)"
    and "\<forall>u \<in> set [syncA]. \<forall>k \<in> u_dom u.
           u_refresh u k = state_after s0_w (wc.pfx 0) k"
    and "\<forall>u \<in> set [syncB].
           wc.cle (u_lo u) 2 \<and> wc.cle 2 (u_hi u)"
    and "\<forall>u \<in> set [syncB]. \<forall>k \<in> u_dom u.
           u_refresh u k = state_after s0_w (wc.pfx 2) k"
    and "capture_contract L_w den_w s0_w [syncA, syncB] {1, 2} 2"
    and "\<not> (\<exists>cstar. \<forall>u \<in> set [syncA, syncB].
           wc.cle (u_lo u) cstar \<and> wc.cle cstar (u_hi u))"
    and "\<not> (\<exists>cstar. wc.cle cstar 1 \<and>
          (\<forall>g. wc.cle cstar g \<longrightarrow> wc.cle g 2 \<longrightarrow>
             (\<forall>k \<in> {1, 2}.
                sync.sink_at g k = state_after s0_w (wc.pfx g) k)))"
    and "\<not> (\<exists>cstar. wc.cle cstar 2 \<and> \<not> wc.cle 2 cstar \<and>
          (\<forall>g. wc.cle cstar g \<longrightarrow> wc.cle g 2 \<longrightarrow>
             (\<forall>k \<in> {1, 2}.
                sync.sink_at g k = state_after s0_w (wc.pfx g) k)))"
  by (rule syncAo.capture_contract_axioms,
      rule syncBo.capture_contract_axioms,
      use wit_sync_memberA_shared_bracket in blast,
      use wit_sync_memberA_shared_honesty in blast,
      use wit_sync_memberB_shared_bracket in blast,
      use wit_sync_memberB_shared_honesty in blast,
      rule sync.capture_contract_axioms,
      rule fix_sync_no_common_bracket_witness,
      rule fix_sync_no_early_onset,
      rule fix_sync_no_strictly_below_frontier_onset)

subsection \<open>Fixture 3: amortized shared bracket with a shared witness (T3)\<close>

definition shrC :: "(nat, nat, nat) cunit" where
  "shrC = \<lparr>u_dom = {1}, u_lo = 0, u_hi = 2,
           u_refresh = (\<lambda>k. if k = 1 then Some 1 else None)\<rparr>"

definition shrD :: "(nat, nat, nat) cunit" where
  "shrD = \<lparr>u_dom = {2}, u_lo = 0, u_hi = 2, u_refresh = (\<lambda>_. None)\<rparr>"

interpretation shr: capture_contract L_w den_w s0_w "[shrC, shrD]" "{1, 2}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [shrC, shrD]. u_dom u) = {1, 2}"
    by (auto simp: shrC_def shrD_def)
next
  fix i j
  assume i: "i < length [shrC, shrD]" and j: "j < length [shrC, shrD]"
     and ne: "i \<noteq> j"
  then have "(i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0)"
    by auto
  then show "u_dom ([shrC, shrD] ! i) \<inter> u_dom ([shrC, shrD] ! j) = {}"
    by (auto simp: shrC_def shrD_def)
next
  fix u assume "u \<in> set [shrC, shrD]"
  then show "wc.cle (u_lo u) (u_hi u)"
    by (auto simp: shrC_def shrD_def wc.cle_def den_w_def)
next
  fix u assume "u \<in> set [shrC, shrD]"
  then show "wc.cle (u_hi u) 2"
    by (auto simp: shrC_def shrD_def wc.cle_def den_w_def)
next
  fix u k assume u: "u \<in> set [shrC, shrD]" and k: "k \<in> u_dom u"
  show "\<exists>c. wc.cle (u_lo u) c \<and> wc.cle c (u_hi u) \<and>
            u_refresh u k = state_after s0_w (wc.pfx c) k"
  proof (cases "u = shrC")
    case True
    then have "k = 1" using k by (simp add: shrC_def)
    then show ?thesis
      unfolding wc.cle_def wc.pfx_def
      by (intro exI[of _ 1])
         (simp add: True shrC_def den_w_def L_w_def
                    s0_w_def state_after_def apply_ev_def)
  next
    case False
    then have uD: "u = shrD" using u by simp
    then have "k = 2" using k by (simp add: shrD_def)
    then show ?thesis
      unfolding wc.cle_def wc.pfx_def
      by (intro exI[of _ 1])
         (simp add: uD shrD_def den_w_def L_w_def
                    s0_w_def state_after_def apply_ev_def)
  qed
qed

text \<open>
  One bracket, amortized over both units, with ONE shared state
  witness (coordinate 1): Corollary 1 lifts the composite to T3 ---
  the sink trajectory tracks the source from the witness onward.
  Amortization preserved the tier.
\<close>

lemma wit_shared_bracket_T3:
  assumes "wc.cle 1 g" and "wc.cle g 2" and "k \<in> {1 :: nat, 2}"
  shows "shr.sink_at g k = state_after s0_w (wc.pfx g) k"
proof (rule shr.shared_witness_trajectory[of 1 g k])
  show "\<And>u. u \<in> set [shrC, shrD] \<Longrightarrow> wc.cle (u_lo u) 1 \<and> wc.cle 1 (u_hi u)"
    by (auto simp: shrC_def shrD_def wc.cle_def den_w_def)
  show "\<And>u k. u \<in> set [shrC, shrD] \<Longrightarrow> k \<in> u_dom u \<Longrightarrow>
          u_refresh u k = state_after s0_w (wc.pfx 1) k"
    unfolding wc.pfx_def
    by (auto simp: shrC_def shrD_def den_w_def L_w_def s0_w_def
                   state_after_def apply_ev_def)
qed (use assms in auto)

subsection \<open>Fixture 4: a surviving refresh under window-discard\<close>

definition L_s :: "(nat, nat) event list" where
  "L_s = [Event 3 (Some 7), Event 1 (Some 1)]"

interpretation sc: coordinate_space L_s den_w
  by unfold_locales (simp add: den_w_def L_s_def)

definition surv_unit :: "(nat, nat, nat) cunit" where
  "surv_unit = \<lparr>u_dom = {3}, u_lo = 1, u_hi = 2,
                u_refresh = (\<lambda>k. if k = 3 then Some 7 else None)\<rparr>"

interpretation surv: capture_contract L_s den_w s0_w "[surv_unit]" "{3}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [surv_unit]. u_dom u) = {3}"
    by (simp add: surv_unit_def)
next
  fix i j
  assume "i < length [surv_unit]" "j < length [surv_unit]" "i \<noteq> j"
  then show "u_dom ([surv_unit] ! i) \<inter> u_dom ([surv_unit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [surv_unit]"
  then show "sc.cle (u_lo u) (u_hi u)"
    by (simp add: surv_unit_def sc.cle_def den_w_def)
next
  fix u assume "u \<in> set [surv_unit]"
  then show "sc.cle (u_hi u) 2"
    by (simp add: surv_unit_def sc.cle_def den_w_def)
next
  fix u k assume "u \<in> set [surv_unit]" and "k \<in> u_dom u"
  then show "\<exists>c. sc.cle (u_lo u) c \<and> sc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after s0_w (sc.pfx c) k"
    unfolding sc.cle_def sc.pfx_def
    by (intro exI[of _ 1])
       (simp add: surv_unit_def den_w_def
                  L_s_def s0_w_def state_after_def apply_ev_def)
qed

lemma wit_surv_svl_ok: "surv.svl_ok (\<lambda>_. [3])"
proof -
  have "evs_for 3 (sc.win (u_lo surv_unit) (u_hi surv_unit)) = []"
    unfolding sc.win_def
    by (simp add: surv_unit_def den_w_def L_s_def evs_for_def)
  then have "surv.survivors surv_unit = {3}"
    by (auto simp: surv.survivors_def surv_unit_def)
  then show ?thesis
    by (simp add: surv.svl_ok_def)
qed

text \<open>
  Key 3's pre-window event (position 0, value 7) is consumed and
  emitted; the unit's window contains no event for key 3, so its
  refresh entry survives and is emitted at the window close ---
  AFTER the pre-window event. The equivalence theorem says the
  stream replays to the canonical sink; the concrete evaluation
  confirms both sides at the value @{term "Some 7 :: nat option"}.
\<close>

lemma wit_surv_replay_theorem:
  "stream_replay (surv.emission (\<lambda>_. [3]) 0) 3 = surv.sink_at 2 3"
proof (rule surv.window_discard_replay[OF wit_surv_svl_ok])
  show "\<And>u. u \<in> set [surv_unit] \<Longrightarrow> sc.cle 0 (u_lo u)"
    by (simp add: surv_unit_def sc.cle_def den_w_def)
qed simp

lemma wit_surv_the_unit [simp]: "surv.the_unit 3 = surv_unit"
  using surv.the_unit_props[of 3] by simp

lemma wit_surv_replay_value:
  "stream_replay (surv.emission (\<lambda>_. [3]) 0) 3 = Some 7"
proof -
  have win_e: "evs_for 3 (sc.win (u_lo surv_unit) 2) = []"
    unfolding sc.win_def
    by (simp add: surv_unit_def den_w_def L_s_def evs_for_def)
  have "surv.sink_at 2 3 = Some 7"
    unfolding surv.sink_at_def wit_surv_the_unit win_e
    by (simp add: surv_unit_def)
  then show ?thesis
    using wit_surv_replay_theorem by simp
qed

end
