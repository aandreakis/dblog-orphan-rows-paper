(*  Title:   Contract_Base.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Contract_Base
  imports Main "HOL-Library.Sublist"
begin

section \<open>Contract base: events, source states, coordinates, and windows\<close>

text \<open>
  Base substrate for the source-side capture contract: keyed events
  in a commit-ordered log, the source state as a
  per-key fold of the log, coordinate spaces as prefix denotations
  with the membership oracle, and half-open windows.

  Representational notes --- which contract clauses are carried by the
  representation itself rather than by named assumptions:

    \<^item> S-LOG (commit-ordered keyed log): the log is a fixed finite
      list of events in commit order; ``every committed change to a
      scoped key appears as exactly one event'' is the modeling
      identification of committed changes with list occurrences.
      The event type denotes a post-commit occurrence: @{text L} has
      no pending, uncommitted, or aborted-transaction component. In a
      transaction-aware instance, a committed transaction contributes
      its complete contiguous row-event block only after commit. A list
      prefix inside such a block is an intermediate replay prefix of
      already-committed events, not a source state during the commit.
      Transaction labels and the predicate that a prefix is a block
      boundary are deliberately instance-side; the unlabelled core
      needs neither for its per-key theorem.
      Positions, not event values, are the occurrence identity: a log
      may contain equal events at distinct positions, and the
      development reasons at position level throughout.
    \<^item> S-IMG (image sufficiency): an event carries the full
      post-image of its key (@{text "ev_img e"}, @{const None} for a
      delete), and the source dynamics @{text apply_ev} makes that
      image the post-state by definition. Delta logs are outside this
      core (S-IMG); their re-read repair is a log
      normalization producing effective full-image events, not an
      in-core case.
    \<^item> Coordinates denote nested prefixes: a coordinate space
      is a type @{typ 'c} together with a denotation into prefixes of
      the log, represented here by prefix length. Linear nestedness of
      denoted prefixes is a theorem of this representation
      (@{text den_nested}), and the derived relation @{text "\<sqsubseteq>"}
      agrees with prefix inclusion of denotations
      (@{text cle_iff_prefix}). No total order on the coordinate type
      is assumed; @{text "\<sqsubseteq>"} is a preorder, and distinct coordinates
      may denote the same prefix. The operational-fidelity
      admissibility clause is an instance-level obligation: an
      instance must prove that its own operational window-membership
      decisions agree with its declared denotation (discharged per
      instance; the write-free instance's executed-GTID-set
      oracle-agreement lemma is the paradigm case).
    \<^item> Half-open windows: the window of @{text "lo \<sqsubseteq> hi"} is
      the log segment strictly after the events of @{text "pfx lo"}
      up to and including position @{text "den hi - 1"}: the list
      difference of the two denoted prefixes. Low edge excluded, high
      edge included, uniformly for every instance; an instance whose
      raw endpoint records use another convention declares its
      endpoint-to-prefix normalization before using windows.
\<close>

subsection \<open>Events, logs, and source states\<close>

datatype ('k, 'v) event = Event (ev_key: 'k) (ev_img: "'v option")

type_synonym ('k, 'v) state = "'k \<Rightarrow> 'v option"

definition apply_ev :: "('k, 'v) state \<Rightarrow> ('k, 'v) event \<Rightarrow> ('k, 'v) state" where
  "apply_ev \<sigma> e = \<sigma>(ev_key e := ev_img e)"

definition state_after :: "('k, 'v) state \<Rightarrow> ('k, 'v) event list \<Rightarrow> ('k, 'v) state" where
  "state_after \<sigma>0 P = foldl apply_ev \<sigma>0 P"

text \<open>
  @{text "state_after \<sigma>0 P"} is the contract's \<open>\<sigma>\<^sub>P\<close>: the row-event
  replay state after the committed-log prefix @{text P}, over the initial
  state @{text \<sigma>0}. In a transaction-aware instance it is also a
  committed database state when @{text P} ends at a transaction boundary.
\<close>

definition evs_for :: "'k \<Rightarrow> ('k, 'v) event list \<Rightarrow> ('k, 'v) event list" where
  "evs_for k P = filter (\<lambda>e. ev_key e = k) P"

lemma evs_for_Nil [simp]: "evs_for k [] = []"
  by (simp add: evs_for_def)

lemma evs_for_append [simp]:
  "evs_for k (P @ Q) = evs_for k P @ evs_for k Q"
  by (simp add: evs_for_def)

lemma state_after_Nil [simp]: "state_after \<sigma>0 [] = \<sigma>0"
  by (simp add: state_after_def)

lemma state_after_append:
  "state_after \<sigma>0 (P @ Q) = state_after (state_after \<sigma>0 P) Q"
  by (simp add: state_after_def)

lemma state_after_snoc:
  "state_after \<sigma>0 (P @ [e]) = apply_ev (state_after \<sigma>0 P) e"
  by (simp add: state_after_def)

text \<open>
  The per-key characterization of the source state: the last event for
  the key decides, and absent any event the initial state persists.
  This is the shape every argument below reduces to.
\<close>

lemma state_after_key:
  "state_after \<sigma>0 P k =
     (if evs_for k P = [] then \<sigma>0 k else ev_img (last (evs_for k P)))"
proof (induction P rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc e P)
  show ?case
  proof (cases "ev_key e = k")
    case True
    then show ?thesis
      by (simp add: state_after_snoc apply_ev_def evs_for_def)
  next
    case False
    then show ?thesis
      using snoc.IH by (simp add: state_after_snoc apply_ev_def evs_for_def)
  qed
qed

lemma state_after_no_events:
  "evs_for k P = [] \<Longrightarrow> state_after \<sigma>0 P k = \<sigma>0 k"
  by (simp add: state_after_key)

lemma state_after_last_event:
  "evs_for k P \<noteq> [] \<Longrightarrow> state_after \<sigma>0 P k = ev_img (last (evs_for k P))"
  by (simp add: state_after_key)

lemma state_after_append_no_k:
  "evs_for k Q = [] \<Longrightarrow> state_after \<sigma>0 (P @ Q) k = state_after \<sigma>0 P k"
  by (simp add: state_after_append state_after_no_events)

subsection \<open>Coordinate spaces: prefix denotations\<close>

text \<open>
  A coordinate space over a log @{text L}: an arbitrary coordinate
  type @{typ 'c} with a denotation @{text den} giving, for each
  coordinate, the length of the log prefix it denotes. Prefixes of one
  list biject with prefix lengths, so this representation is exactly
  ``denotations are prefixes of the log''; the bound
  @{text den_le_len} says a coordinate never denotes beyond the
  committed history under discussion.
\<close>

locale coordinate_space =
  fixes L :: "('k, 'v) event list"
    and den :: "'c \<Rightarrow> nat"
  assumes den_le_len: "\<And>c. den c \<le> length L"
begin

definition pfx :: "'c \<Rightarrow> ('k, 'v) event list" where
  "pfx c = take (den c) L"

definition cle :: "'c \<Rightarrow> 'c \<Rightarrow> bool"  (infix \<open>\<sqsubseteq>\<close> 50) where
  "c \<sqsubseteq> c' \<longleftrightarrow> den c \<le> den c'"

lemma cle_refl [simp]: "c \<sqsubseteq> c"
  by (simp add: cle_def)

lemma cle_trans [trans]: "c \<sqsubseteq> c' \<Longrightarrow> c' \<sqsubseteq> c'' \<Longrightarrow> c \<sqsubseteq> c''"
  by (simp add: cle_def)

lemma cle_total: "c \<sqsubseteq> c' \<or> c' \<sqsubseteq> c"
  by (simp add: cle_def nat_le_linear)

lemma pfx_length [simp]: "length (pfx c) = den c"
  by (simp add: pfx_def den_le_len)

lemma take_prefix_take: "m \<le> n \<Longrightarrow> prefix (take m xs) (take n xs)"
  by (metis min.absorb1 take_is_prefix take_take)

text \<open>
  The nestedness clause is a theorem of the representation, and
  @{text "\<sqsubseteq>"} agrees with prefix inclusion of the denotations --- the
  representation is faithful to the contract's
  @{text "c \<sqsubseteq> c' \<equiv> \<lbrakk>c\<rbrakk> \<subseteq> \<lbrakk>c'\<rbrakk>"}.
\<close>

lemma cle_iff_prefix: "c \<sqsubseteq> c' \<longleftrightarrow> prefix (pfx c) (pfx c')"
proof
  assume "c \<sqsubseteq> c'"
  then show "prefix (pfx c) (pfx c')"
    by (simp add: cle_def pfx_def take_prefix_take)
next
  assume "prefix (pfx c) (pfx c')"
  then have "length (pfx c) \<le> length (pfx c')"
    by (rule prefix_length_le)
  then show "c \<sqsubseteq> c'" by (simp add: cle_def)
qed

lemma den_nested: "prefix (pfx c) (pfx c') \<or> prefix (pfx c') (pfx c)"
  by (metis cle_def cle_iff_prefix nat_le_linear)

subsection \<open>Half-open windows and the membership oracle\<close>

text \<open>
  The window @{text "(lo, hi]"} as a log segment: the list difference
  of the denoted prefixes, kept in commit order with occurrence
  (position) identity preserved.
\<close>

definition win :: "'c \<Rightarrow> 'c \<Rightarrow> ('k, 'v) event list" where
  "win lo hi = drop (den lo) (take (den hi) L)"

lemma pfx_split: "lo \<sqsubseteq> hi \<Longrightarrow> pfx hi = pfx lo @ win lo hi"
  by (metis append_take_drop_id cle_def min.absorb1 pfx_def take_take win_def)

lemma win_length: "lo \<sqsubseteq> hi \<Longrightarrow> length (win lo hi) = den hi - den lo"
  by (metis add_diff_cancel_left' length_append pfx_length pfx_split)

lemma win_empty_iff: "lo \<sqsubseteq> hi \<Longrightarrow> (win lo hi = [] \<longleftrightarrow> den lo = den hi)"
  by (metis cle_def diff_is_0_eq le_antisym length_0_conv win_length)

lemma win_split: "lo \<sqsubseteq> mid \<Longrightarrow> mid \<sqsubseteq> hi \<Longrightarrow> win lo hi = win lo mid @ win mid hi"
  by (metis append.assoc cle_trans pfx_split same_append_eq)

lemma win_nth:
  "lo \<sqsubseteq> hi \<Longrightarrow> p < den hi - den lo \<Longrightarrow> win lo hi ! p = L ! (den lo + p)"
  by (simp add: win_def cle_def den_le_len add.commute)

text \<open>
  The membership oracle's set reading: under distinct occurrences the
  window is exactly the set difference of the denoted prefixes ---
  the paper's ``@{text "e \<in> \<lbrakk>c'\<rbrakk> \\ \<lbrakk>c\<rbrakk>"}''. The development
  itself reasons at position level (where no distinctness is needed);
  this lemma ties the representation to the paper-level set phrasing.
\<close>

lemma oracle_set_reading:
  assumes "distinct L" and "lo \<sqsubseteq> hi"
  shows "set (win lo hi) = set (pfx hi) - set (pfx lo)"
proof -
  have split: "pfx hi = pfx lo @ win lo hi"
    by (rule pfx_split[OF assms(2)])
  have "distinct (pfx hi)"
    using assms(1) by (simp add: pfx_def)
  with split have disj: "set (pfx lo) \<inter> set (win lo hi) = {}"
    by (metis distinct_append)
  from split have "set (pfx hi) = set (pfx lo) \<union> set (win lo hi)"
    by (metis set_append)
  with disj show ?thesis by auto
qed

subsection \<open>Per-key event selection over prefixes and windows\<close>

lemma evs_for_pfx_split:
  "lo \<sqsubseteq> hi \<Longrightarrow> evs_for k (pfx hi) = evs_for k (pfx lo) @ evs_for k (win lo hi)"
  by (metis evs_for_append pfx_split)

lemma evs_for_win_split:
  "lo \<sqsubseteq> mid \<Longrightarrow> mid \<sqsubseteq> hi \<Longrightarrow>
     evs_for k (win lo hi) = evs_for k (win lo mid) @ evs_for k (win mid hi)"
  by (metis evs_for_append win_split)

text \<open>
  Window invariance: if no event for a key falls in a window, the
  source state on that key is the same at every coordinate of the
  window --- the fact that lets a bracket-locally valid read result
  propagate to any other coordinate of its bracket (O2 together with O3).
\<close>

lemma win_invariant_state:
  assumes lo_c: "lo \<sqsubseteq> c" and c_hi: "c \<sqsubseteq> hi"
      and quiet: "evs_for k (win lo hi) = []"
  shows "state_after \<sigma>0 (pfx c) k = state_after \<sigma>0 (pfx lo) k"
proof -
  have "evs_for k (win lo hi) = evs_for k (win lo c) @ evs_for k (win c hi)"
    by (rule evs_for_win_split[OF lo_c c_hi])
  with quiet have "evs_for k (win lo c) = []"
    by simp
  moreover have "pfx c = pfx lo @ win lo c"
    by (rule pfx_split[OF lo_c])
  ultimately show ?thesis
    by (metis state_after_append_no_k)
qed

lemma win_invariant_state2:
  assumes "lo \<sqsubseteq> c" and "c \<sqsubseteq> hi" and "lo \<sqsubseteq> c'" and "c' \<sqsubseteq> hi"
      and "evs_for k (win lo hi) = []"
  shows "state_after \<sigma>0 (pfx c) k = state_after \<sigma>0 (pfx c') k"
  using assms win_invariant_state by metis

end  (* locale coordinate_space *)

end
