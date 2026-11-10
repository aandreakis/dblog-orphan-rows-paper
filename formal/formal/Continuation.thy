(*  Title:   Continuation.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Continuation
  imports Virtual_Cut
begin

section \<open>Source-side continuation and restriction of virtual cuts\<close>

text \<open>
  Source-side continuation and sub-scope restriction of virtual cuts
  (the post-core continuation extension).

  A certified virtual cut is a point-in-time object --- it certifies
  replay equality at one source frontier on one key scope. This
  theory proves two primary source-side algebra facts that place a single cut
  inside DBLog's continuous operation:

    \<^item> \<^emph>\<open>continuation across frontiers\<close>: a virtual cut at frontier
      @{text f} extends to a virtual cut at a later frontier
      @{text f'} by appending the faithful in-scope CDC segment for
      the half-open interval @{text "(f, f']"};
    \<^item> \<^emph>\<open>restriction to a sub-scope\<close>: a virtual cut on key scope
      @{text K} restricts to a virtual cut on any
      @{text "K' \<subseteq> K"}.

  Both facts are stated at the @{const virtual_cut_state} level ---
  the factored source-side extensional-equality core to which the
  Layer 2 run-side theorem and the Layer 3 cert-side
  @{const virtual_cut} predicate both reduce --- so continuation
  composes with the existing ladder without re-opening the abstract
  run model. An accessor-level corollary lifts continuation onto an
  accepted certificate's clean prefix; a whole-table instance
  specializes continuation to @{text "K = UNIV"}.

  Every theorem conclusion is an @{const Apply}-against-@{const Src}
  equality: continuation is a source-side replay-equality statement,
  not a destination-state, delivery, or sink claim. Nothing here
  asserts that an extended certificate is accepted by the verifier,
  and nothing here asserts downstream repair.

  In the companion fixture theories (@{text Continuation_Fixtures_Core}
  and @{text Continuation_Fixtures_Inst}) the @{text l7_} /
  @{text l7f_} / @{text fix_l7_} prefixes tag the continuation fixture
  family (historically the seventh fixture layer); the prefix does not
  denote a model layer.

  Paper "Source-Side Continuation and Restriction of Virtual Cuts".
\<close>

subsection \<open>The continuation segment\<close>

text \<open>
  @{text "cdc_segment_between H K f f' \<delta>"} holds exactly when
  @{text \<delta>} is the continuation segment for the half-open interval
  @{text "(f, f']"} on key scope @{text K}: the source history
  @{text H} filtered to the events whose source coordinate @{text c}
  satisfies @{text "f < c \<and> c \<le> f'"} and whose key lies in
  @{text K}, with each surviving pair @{text "(c, e)"} lifted to its
  replay-side CDC event @{text "cdc_lift c e"}.

  Defining the segment as \<^emph>\<open>filter the source history, then map to a
  CDC event\<close> --- rather than as a loose "the CDC events between
  @{text f} and @{text f'}" --- makes source order, same-coordinate
  source-position order, and event multiplicity structural
  consequences of the definition. A caller cannot satisfy the
  predicate with a reordered, thinned, or padded segment.

  The interval is half-open @{text "(f, f']"} because frontiers are
  inclusive: @{const Src} at @{text f} already reflects every event
  at coordinate @{text f}, so continuation begins strictly after
  @{text f}; the target frontier @{text f'} includes its own
  coordinate.

  Paper "Source-Side Continuation and Restriction of Virtual Cuts" /
  "Definition (continuation segment)".
\<close>

definition cdc_segment_between
  :: "('k, 'v) src_history \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> frontier
      \<Rightarrow> ('k, 'v) replay_event list \<Rightarrow> bool"
where
  "cdc_segment_between H K f f' \<delta> \<longleftrightarrow>
     f \<le> f'
   \<and> \<delta> = map (\<lambda>(c, e). cdc_lift c e)
              (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H)"

text \<open>
  A wellformed source history is sorted by source coordinate. WF-H1
  fixes non-decreasing coordinates between adjacent indices; by
  transitivity this is coordinate-monotonicity across every index
  pair --- exactly @{const sorted} on the @{const hist_coord}
  projection. Naming this consequence lets the segment-concatenation
  lemma reason by list position.
\<close>

lemma wellformed_src_history_sorted:
  assumes wfH: "wellformed_src_history H"
  shows "sorted (map hist_coord H)"
  unfolding sorted_iff_nth_mono
proof (intro allI impI)
  fix i j
  assume ij: "i \<le> j" and j_lt: "j < length (map hist_coord H)"
  have j_lt_H: "j < length H" using j_lt by simp
  have i_lt: "i < length H" using ij j_lt_H by (rule le_less_trans)
  have "src_le (hist_coord (H ! i)) (hist_coord (H ! j))"
    by (rule wellformed_src_history_coord_mono[OF wfH ij j_lt_H])
  thus "map hist_coord H ! i \<le> map hist_coord H ! j"
    by (simp add: src_le_eq_less_eq nth_map i_lt j_lt_H)
qed

text \<open>
  Interval-filter concatenation. On a coordinate-sorted source
  history, the events filtered to the half-open interval
  @{text "(f, f']"}, followed by those filtered to
  @{text "(f', f'']"}, are --- in list order --- exactly the events
  filtered to the combined interval @{text "(f, f'']"}: sortedness
  places every lower-interval event before every upper-interval
  event, so the two sub-histories concatenate rather than
  interleave. The key scope @{text K} is carried unchanged. This is
  the source-order fact underlying @{const cdc_segment_between}'s
  chaining lemma.
\<close>

lemma filter_src_interval_concat:
  fixes H :: "('k, 'v) src_history"
  assumes ff':   "f \<le> f'"
      and f'f'': "f' \<le> f''"
      and srt:   "sorted (map hist_coord H)"
  shows "filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H
           @ filter (\<lambda>(c, e). f' < c \<and> c \<le> f'' \<and> key_of e \<in> K) H
         = filter (\<lambda>(c, e). f < c \<and> c \<le> f'' \<and> key_of e \<in> K) H"
  using srt
proof (induction H)
  case Nil
  show ?case by simp
next
  case (Cons p H')
  obtain pc pe where p: "p = (pc, pe)" by (cases p)
  have srt': "sorted (map hist_coord H')"
    using Cons.prems by simp
  have IH: "filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H'
              @ filter (\<lambda>(c, e). f' < c \<and> c \<le> f'' \<and> key_of e \<in> K) H'
            = filter (\<lambda>(c, e). f < c \<and> c \<le> f'' \<and> key_of e \<in> K) H'"
    by (rule Cons.IH[OF srt'])
  show ?case
  proof (cases "pc \<le> f'")
    case lo: True
    \<comment> \<open>Head in the lower interval: it joins the lower and combined
        segments identically; the tail closes by induction.\<close>
    have pcf'': "pc \<le> f''" using lo f'f'' by (rule order_trans)
    have not_f': "\<not> f' < pc" using lo by simp
    show ?thesis using p lo pcf'' not_f' IH by simp
  next
    case hi: False
    \<comment> \<open>Head strictly above \<open>f'\<close>: sortedness puts the whole tail
        above \<open>f'\<close>, so the lower segment of the tail is empty.\<close>
    hence f'_lt: "f' < pc" by simp
    have f_lt: "f < pc" using ff' f'_lt by (rule le_less_trans)
    have tail_above: "f' < hist_coord q" if q_in: "q \<in> set H'" for q
    proof -
      have "sorted (pc # map hist_coord H')"
        using Cons.prems p by simp
      moreover have "hist_coord q \<in> set (map hist_coord H')"
        using q_in by auto
      ultimately have pc_le_q: "pc \<le> hist_coord q" by auto
      show "f' < hist_coord q" using f'_lt pc_le_q by (rule less_le_trans)
    qed
    have lo_empty:
      "filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H' = []"
    proof -
      have "\<not> (case q of (c, e) \<Rightarrow> f < c \<and> c \<le> f' \<and> key_of e \<in> K)"
        if q_in: "q \<in> set H'" for q
        using tail_above[OF q_in] by (auto simp: case_prod_beta)
      thus ?thesis by (simp add: filter_empty_conv)
    qed
    show ?thesis
      using p hi f'_lt f_lt IH lo_empty by simp
  qed
qed

text \<open>
  Continuation segments chain: the segment for @{text "(f, f']"}
  followed by the segment for @{text "(f', f'']"} is the segment for
  @{text "(f, f'']"}. This supports the reader-facing statement that
  a finite prefix of ongoing CDC is a fold of continuation segments.

  Wellformedness of @{text H} is required. On a non-decreasing
  history (WF-H1) the @{text "(f, f']"} events precede the
  @{text "(f', f'']"} events in list order, so the two filtered
  sub-histories concatenate, in source order, into the
  @{text "(f, f'']"} sub-history. Without WF-H1 a history could
  interleave the two coordinate ranges, and the concatenation would
  not be in source order --- so the wellformedness premise is not a
  convenience but a soundness requirement.
\<close>

lemma cdc_segment_between_concat:
  assumes wfH:  "wellformed_src_history H"
      and seg1: "cdc_segment_between H K f f' \<delta>1"
      and seg2: "cdc_segment_between H K f' f'' \<delta>2"
  shows "cdc_segment_between H K f f'' (\<delta>1 @ \<delta>2)"
proof -
  from seg1 have ff': "f \<le> f'"
    and \<delta>1_eq: "\<delta>1 = map (\<lambda>(c, e). cdc_lift c e)
                       (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H)"
    unfolding cdc_segment_between_def by simp_all
  from seg2 have f'f'': "f' \<le> f''"
    and \<delta>2_eq: "\<delta>2 = map (\<lambda>(c, e). cdc_lift c e)
                       (filter (\<lambda>(c, e). f' < c \<and> c \<le> f'' \<and> key_of e \<in> K) H)"
    unfolding cdc_segment_between_def by simp_all
  have ff'': "f \<le> f''" using ff' f'f'' by (rule order_trans)
  have "\<delta>1 @ \<delta>2
          = map (\<lambda>(c, e). cdc_lift c e)
                (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H
                 @ filter (\<lambda>(c, e). f' < c \<and> c \<le> f'' \<and> key_of e \<in> K) H)"
    unfolding \<delta>1_eq \<delta>2_eq by simp
  also have "\<dots> = map (\<lambda>(c, e). cdc_lift c e)
                      (filter (\<lambda>(c, e). f < c \<and> c \<le> f'' \<and> key_of e \<in> K) H)"
    by (simp only:
          filter_src_interval_concat
            [OF ff' f'f'' wellformed_src_history_sorted[OF wfH]])
  finally show ?thesis
    unfolding cdc_segment_between_def using ff'' by simp
qed

text \<open>
  Continuation-segment / per-key bridge. On scope @{text K} and a key
  @{text "k \<in> K"}, the @{text k}-events of the continuation segment
  @{text \<delta>} --- the events @{const event_key} selects for @{text k}
  --- are exactly the @{text k}-events of the source history
  @{text H} in the half-open interval @{text "(f, f']"}, each lifted
  to its replay-side CDC event by @{const cdc_lift}.

  The lemma connects the @{const cdc_segment_between} predicate to the
  per-key @{const Apply}-against-@{const Src} reasoning the
  continuation theorem performs: it lets that proof identify the
  @{text k}-events of @{text \<delta>} with the interval segment
  @{text Src_interval_decomposition} characterizes.
\<close>

lemma cdc_segment_between_event_key_filter:
  assumes seg: "cdc_segment_between H K f f' \<delta>"
      and kK:  "k \<in> K"
  shows "filter (\<lambda>e. event_key e = k) \<delta>
           = map (\<lambda>(c, e). cdc_lift c e)
                 (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H)"
proof -
  from seg have \<delta>_eq:
    "\<delta> = map (\<lambda>(c, e). cdc_lift c e)
             (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H)"
    unfolding cdc_segment_between_def by simp
  have key_filter:
    "filter ((\<lambda>e. event_key e = k) \<circ> (\<lambda>(c, e). cdc_lift c e))
            (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H)
       = filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H"
    unfolding filter_filter
    by (rule filter_cong[OF refl])
       (use kK in \<open>auto simp: cdc_lift_def case_prod_beta\<close>)
  show ?thesis
    by (simp only: \<delta>_eq filter_map key_filter)
qed

subsection \<open>Layer 0 --- replay-append and source-state interval lemmas\<close>

text \<open>
  Replaying a concatenation @{text "\<sigma> @ \<delta>"} is replaying @{text \<delta>}
  from the state @{term "Apply \<sigma>"}. Immediate from @{const Apply}'s
  left-fold definition. Recorded as the obvious replay-append API
  fact; the continuation proof itself works per key (through the
  per-key filter lemmas) and does not consume it.
\<close>

lemma Apply_append:
  "Apply (\<sigma> @ \<delta>) = foldl apply_step (Apply \<sigma>) \<delta>"
  unfolding Apply_def by (simp add: foldl_append)

text \<open>
  The load-bearing Layer 0 lemma for continuation. It characterizes
  the source state at the later frontier @{text f'} from the source
  state at the earlier frontier @{text f} and the key's own source
  events inside the interval @{text "(f, f']"}.

  For a fixed key @{text k}, let @{text segk} be the @{text k}-events
  of @{text H} in @{text "(f, f']"}, in source order. If @{text segk}
  is empty --- no source event for @{text k} in the interval --- then
  @{const Src} at @{text f'} agrees with @{const Src} at @{text f} on
  @{text k}. Otherwise the latest interval event wins: @{const Src}
  at @{text f'} on @{text k} is the per-event effect of the last
  entry of @{text segk}.

  The proof case-splits on whether such an interval event exists,
  using @{text src_eq_when_no_later_src_event_for_k}, direct
  unfolding of @{const Src}, and the
  @{type src_coord} linear order. The empty case needs only
  @{text "f \<le> f'"} and linear-order totality. The non-empty case
  uses WF-H1 to place the interval events after the
  @{text "c \<le> f"} events in list order, so the latest
  @{text "c \<le> f'"} event for @{text k} is exactly the latest
  interval event.
\<close>

lemma Src_interval_decomposition:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
  assumes wfH:  "wellformed_src_history H"
      and f_le: "f \<le> f'"
  shows
    "Src b0 H f' k
       = (let segk = filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H
          in if segk = []
             then Src b0 H f k
             else (case snd (last segk) of
                     Insert _ v \<Rightarrow> Some v
                   | Update _ v \<Rightarrow> Some v
                   | Delete _   \<Rightarrow> None))"
proof -
  define Q where
    "Q = (\<lambda>p :: src_coord \<times> ('k, 'v) source_event.
            f < hist_coord p \<and> hist_coord p \<le> f'
            \<and> key_of (hist_event p) = k)"
  have segk_eq:
    "filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H = filter Q H"
    by (rule filter_cong[OF refl]) (simp add: Q_def case_prod_beta)
  show ?thesis
  proof (cases "filter Q H = []")
    case True
    \<comment> \<open>No source event for \<open>k\<close> in \<open>(f, f']\<close>: Src is unchanged.\<close>
    have no_later:
      "\<forall>i < length H. src_lt f (hist_coord (H ! i))
                       \<and> src_le (hist_coord (H ! i)) f'
                       \<longrightarrow> key_of (hist_event (H ! i)) \<noteq> k"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < length H"
        and between: "src_lt f (hist_coord (H ! i))
                       \<and> src_le (hist_coord (H ! i)) f'"
      have "\<not> Q (H ! i)"
        using True i_lt by (metis filter_empty_conv nth_mem)
      thus "key_of (hist_event (H ! i)) \<noteq> k"
        using between
        by (auto simp: Q_def src_lt_eq_less src_le_eq_less_eq)
    qed
    have src_eq: "Src b0 H f' k = Src b0 H f k"
    proof (rule src_eq_when_no_later_src_event_for_k[OF _ no_later])
      show "src_le f f'"
        using f_le by (simp add: src_le_eq_less_eq)
    qed
    show ?thesis
      using src_eq True segk_eq by (simp add: Let_def)
  next
    case False
    \<comment> \<open>The latest \<open>k\<close>-event in \<open>(f, f']\<close> determines Src at \<open>f'\<close>.\<close>
    obtain i where
      i_lt: "i < length H" and
      Q_i: "Q (H ! i)" and
      H_i_last: "H ! i = last (filter Q H)" and
      no_after_Q: "\<forall>j. i < j \<and> j < length H \<longrightarrow> \<not> Q (H ! j)"
      using last_filter_index[OF False] by blast
    let ?P = "\<lambda>j. src_le (hist_coord (H ! j)) f'
                  \<and> key_of (hist_event (H ! j)) = k"
    have P_i: "?P i"
      using Q_i by (simp add: Q_def src_le_eq_less_eq)
    have f_lt_i: "f < hist_coord (H ! i)"
      using Q_i by (simp add: Q_def)
    have no_after_P: "\<forall>j. i < j \<and> j < length H \<longrightarrow> \<not> ?P j"
    proof (intro allI impI)
      fix j
      assume j_assm: "i < j \<and> j < length H"
      hence i_le_j: "i \<le> j" and j_lt: "j < length H" by auto
      show "\<not> ?P j"
      proof
        assume P_j: "?P j"
        hence j_le_f': "src_le (hist_coord (H ! j)) f'"
          and j_key: "key_of (hist_event (H ! j)) = k"
          by auto
        have coord_mono:
          "src_le (hist_coord (H ! i)) (hist_coord (H ! j))"
          by (rule wellformed_src_history_coord_mono[OF wfH i_le_j j_lt])
        have "f < hist_coord (H ! j)"
        proof -
          have "hist_coord (H ! i) \<le> hist_coord (H ! j)"
            using coord_mono by (simp add: src_le_eq_less_eq)
          with f_lt_i show ?thesis by (rule less_le_trans)
        qed
        hence "Q (H ! j)"
          using j_le_f' j_key
          by (simp add: Q_def src_le_eq_less_eq)
        with no_after_Q j_assm show False by blast
      qed
    qed
    have cand_ne: "filter ?P [0..<length H] \<noteq> []"
      and cand_last: "last (filter ?P [0..<length H]) = i"
      using last_filter_upt_eq[OF i_lt P_i no_after_P] by auto
    have latest_eq: "latest_src_event H f' k = Some i"
      using cand_ne cand_last
      unfolding latest_src_event_def by (simp add: Let_def)
    have "Src b0 H f' k = (case hist_event (H ! i) of
                             Insert _ v \<Rightarrow> Some v
                           | Update _ v \<Rightarrow> Some v
                           | Delete _   \<Rightarrow> None)"
      unfolding Src_def using latest_eq by simp
    thus ?thesis
      using segk_eq False H_i_last by (simp add: Let_def)
  qed
qed

subsection \<open>Continuation across frontiers\<close>

text \<open>
  The primary theorem. A virtual cut at frontier @{text f} on scope
  @{text K} --- a sequence @{text \<sigma>} whose replay agrees with
  @{const Src} at @{text f} on @{text K} --- extends to a virtual cut
  at any later frontier @{text f'} by appending the continuation
  segment @{text \<delta>} for @{text "(f, f']"} on @{text K}.

  The proof is pointwise on @{text "k \<in> K"}. By
  @{text apply_latest_event_wins} the replay value of
  @{text "\<sigma> @ \<delta>"} at @{text k} is governed by the last
  @{text k}-event of @{text "\<sigma> @ \<delta>"}. If @{text \<delta>} carries a
  @{text k}-event, that last event lies in @{text \<delta>} --- a CDC event
  lifted from the latest interval source event for @{text k} --- and
  @{text Src_interval_decomposition} equates its effect with
  @{const Src} at @{text f'} on @{text k}. If @{text \<delta>} carries no
  @{text k}-event, replay of @{text "\<sigma> @ \<delta>"} at @{text k} equals
  replay of @{text \<sigma>}, which the premise equates with @{const Src}
  at @{text f} on @{text k}, and @{text Src_interval_decomposition}
  equates that with @{const Src} at @{text f'} on @{text k}.

  The result is \<^emph>\<open>Conditional\<close> at the paper level: on a wellformed
  source history and on @{text \<delta>} being exactly the faithful
  continuation segment for the interval.

  Paper "Source-Side Continuation and Restriction of Virtual Cuts" /
  "Theorem (continuation across frontiers)".
\<close>

theorem virtual_cut_state_continuation:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
  assumes wfH: "wellformed_src_history H"
      and cut: "virtual_cut_state b0 \<sigma> K f H"
      and seg: "cdc_segment_between H K f f' \<delta>"
  shows "virtual_cut_state b0 (\<sigma> @ \<delta>) K f' H"
proof -
  from seg have f_le: "f \<le> f'"
    unfolding cdc_segment_between_def by simp
  have cut_k: "Apply \<sigma> k = Src b0 H f k" if "k \<in> K" for k
  proof -
    have "restrict (Apply \<sigma>) K k = restrict (Src b0 H f) K k"
      using cut unfolding virtual_cut_state_def by simp
    thus ?thesis using that by (simp add: restrict_def)
  qed
  have key_eq: "Apply (\<sigma> @ \<delta>) k = Src b0 H f' k" if kK: "k \<in> K" for k
  proof -
    define segk where
      "segk = filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H"
    have \<delta>_k: "filter (\<lambda>e. event_key e = k) \<delta>
                 = map (\<lambda>(c, e). cdc_lift c e) segk"
      unfolding segk_def
      by (rule cdc_segment_between_event_key_filter[OF seg kK])
    have src_f':
      "Src b0 H f' k
         = (if segk = []
            then Src b0 H f k
            else (case snd (last segk) of
                    Insert _ v \<Rightarrow> Some v
                  | Update _ v \<Rightarrow> Some v
                  | Delete _   \<Rightarrow> None))"
      unfolding segk_def
      using Src_interval_decomposition[OF wfH f_le] by (simp add: Let_def)
    have filt_app: "filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>)
                      = filter (\<lambda>e. event_key e = k) \<sigma>
                        @ map (\<lambda>(c, e). cdc_lift c e) segk"
      using \<delta>_k by simp
    show ?thesis
    proof (cases "segk = []")
      case True
      \<comment> \<open>No source event for \<open>k\<close> in \<open>(f, f']\<close>: replay of \<open>\<sigma> @ \<delta>\<close> at
          \<open>k\<close> reduces to replay of \<open>\<sigma>\<close>, and Src is unchanged.\<close>
      have "Apply (\<sigma> @ \<delta>) k
              = Apply (filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>)) k"
        by (rule apply_eq_apply_filter_key)
      also have "\<dots> = Apply (filter (\<lambda>e. event_key e = k) \<sigma>) k"
        using filt_app True by simp
      also have "\<dots> = Apply \<sigma> k"
        by (rule apply_eq_apply_filter_key[symmetric])
      also have "\<dots> = Src b0 H f k"
        by (rule cut_k[OF kK])
      also have "\<dots> = Src b0 H f' k"
        using src_f' True by simp
      finally show ?thesis .
    next
      case False
      \<comment> \<open>The latest \<open>k\<close>-event lies in \<open>\<delta>\<close>; it is the \<^const>\<open>cdc_lift\<close>
          of the latest interval source event for \<open>k\<close>.\<close>
      have map_ne: "map (\<lambda>(c, e). cdc_lift c e) segk \<noteq> []"
        using False by simp
      have filt_ne: "filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>) \<noteq> []"
        using filt_app map_ne by simp
      have last_eq: "last (filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>))
                       = Cdc (fst (last segk)) (snd (last segk))"
      proof -
        have "last (filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>))
                = last (map (\<lambda>(c, e). cdc_lift c e) segk)"
          using filt_app map_ne by (simp add: last_appendR)
        also have "\<dots> = (\<lambda>(c, e). cdc_lift c e) (last segk)"
          using False by (simp add: last_map)
        also have "\<dots> = Cdc (fst (last segk)) (snd (last segk))"
          by (simp add: cdc_lift_def case_prod_beta)
        finally show ?thesis .
      qed
      have step: "Apply (\<sigma> @ \<delta>) k
              = (case filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>) of
                   [] \<Rightarrow> None
                 | _ # _ \<Rightarrow>
                     (case last (filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>)) of
                        Cdc _ (Insert _ v) \<Rightarrow> Some v
                      | Cdc _ (Update _ v) \<Rightarrow> Some v
                      | Cdc _ (Delete _)   \<Rightarrow> None
                      | Refresh _ m_obs _  \<Rightarrow> m_obs))"
        by (rule apply_latest_event_wins)
      obtain z zs where
        zzs: "filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>) = z # zs"
        by (metis filt_ne neq_Nil_conv)
      have "Apply (\<sigma> @ \<delta>) k = (case snd (last segk) of
                                  Insert _ v \<Rightarrow> Some v
                                | Update _ v \<Rightarrow> Some v
                                | Delete _   \<Rightarrow> None)"
        unfolding step last_eq using zzs by simp
      also have "\<dots> = Src b0 H f' k"
        using src_f' False by simp
      finally show ?thesis .
    qed
  qed
  show ?thesis
    unfolding virtual_cut_state_def
  proof (rule ext)
    fix k
    show "restrict (Apply (\<sigma> @ \<delta>)) K k = restrict (Src b0 H f') K k"
      using key_eq unfolding restrict_def by (cases "k \<in> K") auto
  qed
qed

subsection \<open>Restriction to a sub-scope\<close>

text \<open>
  A virtual cut on key scope @{text K} restricts to a virtual cut on
  any @{text "K' \<subseteq> K"}. The proof is pointwise: two per-key states
  that agree on every key of @{text K} agree on every key of any
  subset.

  Restriction does not extend the other way. Widening the scope
  would assert agreement on keys never certified --- for a key
  outside @{text K} the cut says nothing about its state at
  @{text f} --- so no scope-widening lemma is stated.

  Paper "Source-Side Continuation and Restriction of Virtual Cuts" /
  "Lemma (sub-scope restriction)".
\<close>

theorem virtual_cut_state_restrict_scope:
  fixes b0 :: "'k \<rightharpoonup> 'v"
  assumes cut: "virtual_cut_state b0 \<sigma> K f H"
      and sub: "K' \<subseteq> K"
  shows "virtual_cut_state b0 \<sigma> K' f H"
proof -
  have eqK: "restrict (Apply \<sigma>) K = restrict (Src b0 H f) K"
    using cut by (simp add: virtual_cut_state_def)
  show ?thesis
    unfolding virtual_cut_state_def
  proof (rule ext)
    fix k
    from eqK have "restrict (Apply \<sigma>) K k = restrict (Src b0 H f) K k"
      by simp
    with sub show "restrict (Apply \<sigma>) K' k = restrict (Src b0 H f) K' k"
      by (auto simp: restrict_def)
  qed
qed

subsection \<open>Whole-table continuation\<close>

text \<open>
  The @{text "K = UNIV"} instance of continuation. When replay of
  @{text \<sigma>} reaches the source state at @{text f} on \<^emph>\<open>every\<close> key
  --- an unrestricted equality, as the Layer 4 whole-table
  specialization yields --- appending the full CDC segment for
  @{text "(f, f']"} on every key reaches the source state at
  @{text f'}.

  The continuation segment here ranges over @{text UNIV}, so it must
  include every source event in @{text "(f, f']"}, not only the
  events of a finite certificate scope. A scoped continuation does
  not become whole-table for free: a key inserted outside the scope
  in @{text "(f, f']"} would change the table without changing the
  scoped equality.

  Paper "Source-Side Continuation and Restriction of Virtual Cuts" /
  "Corollary (whole-table continuation)".
\<close>

theorem whole_table_state_continuation:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
  assumes wfH: "wellformed_src_history H"
      and tab: "Apply \<sigma> = Src b0 H f"
      and seg: "cdc_segment_between H UNIV f f' \<delta>"
  shows "Apply (\<sigma> @ \<delta>) = Src b0 H f'"
proof -
  have univ: "restrict m UNIV = m" for m :: "'k \<rightharpoonup> 'v"
    by (simp add: restrict_def)
  have "virtual_cut_state b0 \<sigma> UNIV f H"
    unfolding virtual_cut_state_def using tab by (simp add: univ)
  from virtual_cut_state_continuation[OF wfH this seg]
  have "virtual_cut_state b0 (\<sigma> @ \<delta>) UNIV f' H" .
  thus ?thesis
    unfolding virtual_cut_state_def by (simp add: univ)
qed

subsection \<open>Sub-scope restriction over a certificate\<close>

text \<open>
  The certificate-accessor corollary of sub-scope restriction: an
  accepted certificate's virtual cut, read through its accessors,
  restricts to any sub-scope of its certified scope. The conclusion
  is the @{const virtual_cut_state} predicate on the certificate's
  clean prefix and frontier at the narrowed scope @{text K'}.

  It is \<^emph>\<open>not\<close> a claim that a restricted certificate is accepted by
  the verifier --- the verifier acceptance of any concrete
  restricted certificate is an evidence obligation, not a
  consequence of the source-side algebra.

  Paper "Source-Side Continuation and Restriction of Virtual Cuts" /
  "Corollary (sub-scope restriction over a certificate)".
\<close>

theorem virtual_cut_restrict_to_subscope:
  fixes b0 :: "'k \<rightharpoonup> 'v"
  assumes vc:  "virtual_cut b0 C H"
      and sub: "K' \<subseteq> scope C"
  shows "virtual_cut_state b0 (clean_prefix C) K' (frontier C) H"
proof -
  have "virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"
    using vc by (simp add: virtual_cut_def)
  thus ?thesis
    using sub by (rule virtual_cut_state_restrict_scope)
qed

subsection \<open>Continuation over an accepted certificate\<close>

text \<open>
  The accessor-level accepted-certificate corollary. Inside the
  @{text layer3_checker_substrate} locale, an accepted certificate
  under faithful source observation yields a virtual cut
  (@{text accepted_virtual_cut_sound}); continuation then extends the
  certified clean prefix by a faithful continuation segment to a
  virtual cut at the later frontier @{text f'}.

  The conclusion is the @{const virtual_cut_state} equality on the
  \<^emph>\<open>sequence\<close> @{text "clean_prefix C @ \<delta>"}. It is not a claim that
  the verifier accepts an extended certificate: certificate
  acceptance is an evidence and verifier obligation, not a
  consequence of the source-side algebra. The continuation segment
  @{text \<delta>} is itself an external observation; its faithfulness to
  @{text H} is a premise, discharged at deployment, exactly as the
  faithfulness of the certificate's own evidence is.

  Paper "Source-Side Continuation and Restriction of Virtual Cuts" /
  "Corollary (continuation over an accepted certificate)".

  The @{text wellformed_src_history} premise is stated explicitly so
  the theorem reads self-contained; under the locale it is also
  derivable from acceptance plus faithfulness (acceptance forces
  @{text checker_run_wellformed} on the evidence run, whose first
  conjunct is wellformedness of the recorded history, and
  faithfulness identifies that history with @{text H}).
\<close>

context layer3_checker_substrate
begin

theorem accepted_certificate_continuation_sound:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
  assumes accept:   "verify C E = Accept"
      and faithful: "faithful_source_observation E b0 H Raw"
      and wfH:      "wellformed_src_history H"
      and seg:      "cdc_segment_between H (scope C) (frontier C) f' \<delta>"
  shows "virtual_cut_state b0 (clean_prefix C @ \<delta>) (scope C) f' H"
proof -
  have "virtual_cut b0 C H"
    by (rule accepted_virtual_cut_sound[OF accept faithful])
  hence "virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"
    unfolding virtual_cut_def .
  from virtual_cut_state_continuation[OF wfH this seg]
  show ?thesis .
qed

end

end
