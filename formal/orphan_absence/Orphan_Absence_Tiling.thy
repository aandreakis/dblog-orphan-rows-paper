(* SPDX-License-Identifier: BSD-3-Clause *)
(*
  Orphan_Absence_Tiling: the chunk ranges of one completed snapshot pass tile
  the key space without gaps or overlaps, and on finite source states every
  range is exact for its own read, so the absence claim of a chunk info record
  is sound.

  Additive to the session Orphan_Absence; nothing in the archived development
  is modified. The model and its theorems use only Main. The last section, a
  bridge to the contract core, imports the core's Cut_Theorem.
*)
theory Orphan_Absence_Tiling
  imports DBLog_Framework_Core.Cut_Theorem
begin

text \<open>
  Section 5.2 of the paper (``Covering the entire key space'') argues in
  prose that the chunk ranges of one snapshot pass cover the key space
  without gaps, and that a range may be left open above only after a short
  page. The other theories of this session take each unit's key range as
  given. This theory proves the tiling and the soundness of the ranges for a
  small model of one pass. Everything up to the last section uses only
  @{text Main}. The last section connects the result to the contract core.

  The model. Keys are of any linearly ordered type. The source state at a
  read's cut is the set of keys present there. Each read has its own cut, so
  a pass consumes a list of such sets, one per read, and the source may change
  between reads. This is how inserts above the recorded maximum appear. A page
  is the @{text n} smallest present keys strictly above the previous chunk's
  last returned key. A bounded page also stays at or below the maximum key
  @{text M} recorded at the start of the pass. A chunk's range runs from the
  previous chunk's last returned key (exclusive, and open below for the first
  chunk) to its own last returned key (inclusive). A short page, one with
  fewer than @{text n} rows, ends the range open above, except in the bounded
  main loop, where it ends the range at @{text M} (inclusive) and hands over to
  the tail reads above @{text M}. The tail reads follow the plain rule. After
  @{text T} tail reads with full pages the pass stops, and the keys above the
  last returned key stay uncovered. With no tail reads configured, the keys
  above the recorded maximum stay uncovered.

  Results, for every chunk limit @{text "n > 0"}, every recorded maximum, every
  tail-read limit and every sequence of source states, unless an item states
  a further assumption:

  \<^item> The emitted ranges are pairwise disjoint, the first is open below, and
    each next range starts exactly where the previous one ends.
  \<^item> A completed pass covers every key. With at least one tail read
    configured, a pass stopped by the tail-read limit covers exactly the keys
    at or below the last key its last read returned, and leaves every key
    above it uncovered. With no tail reads configured, the frontier of a
    stopped pass is the recorded maximum, and no key is covered when no
    maximum was recorded (@{text limit_frontier_no_tail_reads}).
  \<^item> On a finite source state, as a table is, every range is exact for its
    own read: the keys the query returned are exactly the keys of the range
    present at that read's cut. So a key in the range that the query did not
    return was absent at the cut.
  \<^item> The terminal rule is necessary whenever the key type has a key above
    the page's last key, as every unbounded key type does: a full page reads
    the same on a source with that key added, so closing a full page open
    above would certify a present key absent.

  The classic loop, with no recorded maximum and no tail-read limit, is a
  special case of the bounded pass and gets its own statements. None of the
  results depends on the recorded maximum being the true maximum. A wrong
  bound moves keys between the main loop and the tail reads, so with a finite
  tail-read limit it can leave keys uncovered.

  Bridge: the ranges of a completed pass serve as the domains of the units
  of a capture contract whose scope is every key. The tiling gives the
  coverage and disjointness obligation O1, and the exactness of each range
  gives the validity obligation O2 at the read's own cut.
\<close>

subsection \<open>Bounds, ranges and chunks\<close>

text \<open>
  A lower bound is exclusive or open, an upper bound inclusive or open. Both
  are options: a lower bound @{term None} is open below, an upper bound
  @{term None} is open above.
\<close>

definition above_lo :: "'k::linorder option \<Rightarrow> 'k \<Rightarrow> bool" where
  "above_lo lo k \<longleftrightarrow> (case lo of None \<Rightarrow> True | Some a \<Rightarrow> a < k)"

definition upto_hi :: "'k::linorder option \<Rightarrow> 'k \<Rightarrow> bool" where
  "upto_hi hi k \<longleftrightarrow> (case hi of None \<Rightarrow> True | Some b \<Rightarrow> k \<le> b)"

lemma above_lo_None [simp]: "above_lo None k"
  by (simp add: above_lo_def)

lemma above_lo_Some [simp]: "above_lo (Some a) k \<longleftrightarrow> a < k"
  by (simp add: above_lo_def)

lemma upto_hi_None [simp]: "upto_hi None k"
  by (simp add: upto_hi_def)

lemma upto_hi_Some [simp]: "upto_hi (Some b) k \<longleftrightarrow> k \<le> b"
  by (simp add: upto_hi_def)

text \<open>
  A chunk as the connector records it: the two range bounds and the raw keys
  the chunk query returned, in key order, before any row of a changed key is
  dropped. The keys of a chunk are the keys inside its range. The keys a list
  of chunks covers are the union of their ranges.
\<close>

record 'k chunk =
  c_lo :: "'k option"
  c_hi :: "'k option"
  c_rows :: "'k list"

definition chunk_keys :: "'k::linorder chunk \<Rightarrow> 'k set" where
  "chunk_keys c = {k. above_lo (c_lo c) k \<and> upto_hi (c_hi c) k}"

definition covered :: "'k::linorder chunk list \<Rightarrow> 'k set" where
  "covered cs = (\<Union>c \<in> set cs. chunk_keys c)"

text \<open>
  A chunk is exact for a source state @{text S} when the keys it returned are
  exactly the keys of its range that are present in @{text S}. This is the
  claim a chunk info record makes: every key of the range that is not
  selected was absent at the read's cut.
\<close>

definition chunk_exact :: "'k::linorder set \<Rightarrow> 'k chunk \<Rightarrow> bool" where
  "chunk_exact S c \<longleftrightarrow> set (c_rows c) = chunk_keys c \<inter> S"

lemma exact_sound:
  assumes "chunk_exact S c" and "k \<in> chunk_keys c" and "k \<in> S"
  shows "k \<in> set (c_rows c)"
  using assms by (simp add: chunk_exact_def)

lemma exact_absent:
  assumes "chunk_exact S c" and "k \<in> chunk_keys c" and "k \<notin> set (c_rows c)"
  shows "k \<notin> S"
  using assms by (auto simp: chunk_exact_def)

subsection \<open>Pages: the \<open>n\<close> smallest keys of a set\<close>

definition smallest :: "nat \<Rightarrow> 'k::linorder set \<Rightarrow> 'k list" where
  "smallest n A = take n (sorted_list_of_set A)"

text \<open>
  The page of a plain chunk query, \<open>SELECT ... WHERE k > lo ORDER BY k
  LIMIT n\<close>, and of a bounded one, which adds \<open>k \<le> M\<close>.
\<close>

definition page :: "'k::linorder set \<Rightarrow> 'k option \<Rightarrow> nat \<Rightarrow> 'k list" where
  "page S lo n = smallest n {k \<in> S. above_lo lo k}"

definition bpage :: "'k::linorder set \<Rightarrow> 'k option \<Rightarrow> 'k \<Rightarrow> nat \<Rightarrow> 'k list" where
  "bpage S lo M n = smallest n {k \<in> S. above_lo lo k \<and> k \<le> M}"

lemma sorted_le_last:
  fixes xs :: "'k::linorder list"
  assumes "sorted_wrt (<) xs" and "x \<in> set xs"
  shows "x \<le> last xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "ys = []")
    case True
    then show ?thesis using Cons.prems(2) by simp
  next
    case False
    have sy: "sorted_wrt (<) ys" using Cons.prems(1) by simp
    have y_last: "y < last ys" using Cons.prems(1) False by simp
    consider (hd) "x = y" | (tl) "x \<in> set ys" using Cons.prems(2) by auto
    then show ?thesis
    proof cases
      case hd
      then show ?thesis using y_last False by simp
    next
      case tl
      then show ?thesis using Cons.IH[OF sy tl] False by simp
    qed
  qed
qed

lemma sorted_take_no_skip:
  fixes xs :: "'k::linorder list"
  assumes "sorted_wrt (<) xs" and "x \<in> set xs"
      and "take m xs \<noteq> []" and "x \<le> last (take m xs)"
  shows "x \<in> set (take m xs)"
  using assms
proof (induction xs arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  obtain m' where m: "m = Suc m'"
    using Cons.prems(3) by (cases m) auto
  consider (hd) "x = y" | (tl) "x \<in> set ys" "x \<noteq> y"
    using Cons.prems(2) by auto
  then show ?case
  proof cases
    case hd
    then show ?thesis using m by simp
  next
    case tl
    have sy: "sorted_wrt (<) ys" using Cons.prems(1) by simp
    have yx: "y < x" using Cons.prems(1) tl(1) by simp
    have ne: "take m' ys \<noteq> []"
    proof
      assume "take m' ys = []"
      then have "x \<le> y" using Cons.prems(4) m by simp
      then show False using yx by (simp add: not_less[symmetric])
    qed
    have le: "x \<le> last (take m' ys)"
      using Cons.prems(4) m ne by simp
    have "x \<in> set (take m' ys)"
      by (rule Cons.IH[OF sy tl(1) ne le])
    then show ?thesis using m by simp
  qed
qed

lemma smallest_subset: "set (smallest n A) \<subseteq> A"
proof (cases "finite A")
  case True
  have "set (take n (sorted_list_of_set A)) \<subseteq> set (sorted_list_of_set A)"
    by (rule set_take_subset)
  then show ?thesis using True by (simp add: smallest_def)
next
  case False
  then show ?thesis by (simp add: smallest_def)
qed

lemma smallest_sorted: "sorted_wrt (<) (smallest n A)"
  unfolding smallest_def by (rule sorted_wrt_take) simp

lemma smallest_length: "length (smallest n A) = min n (card A)"
  by (simp add: smallest_def min.commute)

lemma smallest_upto_last:
  assumes fin: "finite A" and ne: "smallest n A \<noteq> []"
  shows "set (smallest n A) = {k \<in> A. k \<le> last (smallest n A)}"
proof
  show "set (smallest n A) \<subseteq> {k \<in> A. k \<le> last (smallest n A)}"
  proof
    fix k assume k: "k \<in> set (smallest n A)"
    have "k \<in> A" using smallest_subset k by blast
    moreover have "k \<le> last (smallest n A)"
      by (rule sorted_le_last[OF smallest_sorted k])
    ultimately show "k \<in> {k \<in> A. k \<le> last (smallest n A)}" by simp
  qed
next
  show "{k \<in> A. k \<le> last (smallest n A)} \<subseteq> set (smallest n A)"
  proof
    fix k assume k: "k \<in> {k \<in> A. k \<le> last (smallest n A)}"
    have sorted: "sorted_wrt (<) (sorted_list_of_set A)" by simp
    have in_list: "k \<in> set (sorted_list_of_set A)" using k fin by simp
    have ne': "take n (sorted_list_of_set A) \<noteq> []"
      using ne by (simp add: smallest_def)
    have le: "k \<le> last (take n (sorted_list_of_set A))"
      using k by (simp add: smallest_def)
    show "k \<in> set (smallest n A)"
      using sorted_take_no_skip[OF sorted in_list ne' le] by (simp add: smallest_def)
  qed
qed

lemma smallest_short:
  assumes fin: "finite A" and short: "length (smallest n A) < n"
  shows "set (smallest n A) = A"
proof -
  have "card A < n" using short by (simp add: smallest_length)
  then have "length (sorted_list_of_set A) \<le> n" by simp
  then have "smallest n A = sorted_list_of_set A" by (simp add: smallest_def)
  then show ?thesis using fin by simp
qed

text \<open>
  Three facts characterize @{const smallest} as the \<open>n\<close> smallest keys.
  It returns keys of the set (@{text smallest_subset}), as many as the limit
  and the set allow (@{text smallest_length}), and it never skips a key below
  one it returned (@{text smallest_no_skip}, next).
\<close>

lemma smallest_no_skip:
  assumes fin: "finite A" and x: "x \<in> A" and nx: "x \<notin> set (smallest n A)"
      and y: "y \<in> set (smallest n A)"
  shows "y < x"
proof (rule ccontr)
  assume "\<not> y < x"
  then have xy: "x \<le> y" by simp
  have ne: "smallest n A \<noteq> []" using y by auto
  have "y \<le> last (smallest n A)" by (rule sorted_le_last[OF smallest_sorted y])
  then have "x \<le> last (smallest n A)" using xy by simp
  then have "x \<in> set (smallest n A)"
    using smallest_upto_last[OF fin ne] x by simp
  with nx show False by simp
qed

text \<open>
  On a finite set given as a strictly sorted list, the \<open>n\<close> smallest keys
  are the first \<open>n\<close> entries of the list. This computes the witness pages
  below.
\<close>

lemma smallest_eqI:
  fixes xs :: "'k::linorder list"
  assumes sorted: "sorted_wrt (<) xs" and set_xs: "set xs = A" and take_n: "take n xs = ys"
  shows "smallest n A = ys"
proof -
  have sd: "sorted xs \<and> distinct xs" using sorted by (simp add: strict_sorted_iff)
  have "sorted_list_of_set A = xs"
    using sd set_xs[symmetric]
    by (simp add: sorted_list_of_set_sort_remdups distinct_remdups_id sorted_sort_id)
  then show ?thesis using take_n by (simp add: smallest_def)
qed

lemma page_sub: "set (page S lo n) \<subseteq> {k \<in> S. above_lo lo k}"
  unfolding page_def by (rule smallest_subset)

lemma bpage_sub: "set (bpage S lo M n) \<subseteq> {k \<in> S. above_lo lo k \<and> k \<le> M}"
  unfolding bpage_def by (rule smallest_subset)

subsection \<open>Each of the four chunk kinds is exact for its read\<close>

text \<open>
  There are four kinds of chunk.

  \<^item> A full plain page closes its range at its last key.
  \<^item> A short plain page leaves its range open above.
  \<^item> A full bounded page closes its range at its last key.
  \<^item> A short bounded page closes its range at the recorded maximum @{text M}.

  In each case the page returns exactly the keys of the range that are present
  at the read's cut, provided the source state there is finite.
\<close>

lemma exact_closed:
  assumes fin: "finite S" and ne: "page S lo n \<noteq> []"
  shows "chunk_exact S \<lparr>c_lo = lo, c_hi = Some (last (page S lo n)),
                         c_rows = page S lo n\<rparr>"
proof -
  let ?A = "{k \<in> S. above_lo lo k}"
  have finA: "finite ?A" using fin by simp
  have neA: "smallest n ?A \<noteq> []" using ne by (simp add: page_def)
  have eq: "set (page S lo n) = {k \<in> ?A. k \<le> last (page S lo n)}"
    using smallest_upto_last[OF finA neA] by (simp add: page_def)
  show ?thesis
    unfolding chunk_exact_def chunk_keys_def using eq by auto
qed

lemma exact_open_above:
  assumes fin: "finite S" and short: "length (page S lo n) < n"
  shows "chunk_exact S \<lparr>c_lo = lo, c_hi = None, c_rows = page S lo n\<rparr>"
proof -
  let ?A = "{k \<in> S. above_lo lo k}"
  have finA: "finite ?A" using fin by simp
  have shortA: "length (smallest n ?A) < n" using short by (simp add: page_def)
  have eq: "set (page S lo n) = ?A"
    using smallest_short[OF finA shortA] by (simp add: page_def)
  show ?thesis
    unfolding chunk_exact_def chunk_keys_def using eq by auto
qed

lemma exact_bounded_closed:
  assumes fin: "finite S" and ne: "bpage S lo M n \<noteq> []"
  shows "chunk_exact S \<lparr>c_lo = lo, c_hi = Some (last (bpage S lo M n)),
                         c_rows = bpage S lo M n\<rparr>"
proof -
  let ?A = "{k \<in> S. above_lo lo k \<and> k \<le> M}"
  let ?p = "bpage S lo M n"
  have finA: "finite ?A" using fin by simp
  have neA: "smallest n ?A \<noteq> []" using ne by (simp add: bpage_def)
  have eq: "set ?p = {k \<in> ?A. k \<le> last ?p}"
    using smallest_upto_last[OF finA neA] by (simp add: bpage_def)
  have last_M: "last ?p \<le> M"
    using subsetD[OF bpage_sub last_in_set[OF ne]] by simp
  have "set ?p = {k. above_lo lo k \<and> k \<le> last ?p} \<inter> S"
  proof (rule set_eqI)
    fix k
    have kM: "k \<le> M" if "k \<le> last ?p"
      using that last_M by (rule order_trans)
    show "k \<in> set ?p \<longleftrightarrow> k \<in> {k. above_lo lo k \<and> k \<le> last ?p} \<inter> S"
      using eq kM by auto
  qed
  then show ?thesis
    by (simp add: chunk_exact_def chunk_keys_def)
qed

lemma exact_closed_at_max:
  assumes fin: "finite S" and short: "length (bpage S lo M n) < n"
  shows "chunk_exact S \<lparr>c_lo = lo, c_hi = Some M, c_rows = bpage S lo M n\<rparr>"
proof -
  let ?A = "{k \<in> S. above_lo lo k \<and> k \<le> M}"
  have finA: "finite ?A" using fin by simp
  have shortA: "length (smallest n ?A) < n" using short by (simp add: bpage_def)
  have eq: "set (bpage S lo M n) = ?A"
    using smallest_short[OF finA shortA] by (simp add: bpage_def)
  show ?thesis
    unfolding chunk_exact_def chunk_keys_def using eq by auto
qed

subsection \<open>Chains of ranges tile their span\<close>

text \<open>
  The tiling is pure geometry, separate from the loop control. A list of
  chunks is a chain from a lower bound @{text lo} when the first range starts
  at @{text lo}, each next range starts at the previous range's upper bound,
  only the last range may be open above, and no upper bound lies below the
  range's own lower bound. The part of the key space above @{text lo} that a
  chain leaves to later reads is everything above its last upper bound, or
  nothing when the last range is open above.
\<close>

definition lower_le :: "'k::linorder option \<Rightarrow> 'k \<Rightarrow> bool" where
  "lower_le lo b \<longleftrightarrow> (case lo of None \<Rightarrow> True | Some a \<Rightarrow> a \<le> b)"

lemma lower_le_None [simp]: "lower_le None b"
  by (simp add: lower_le_def)

lemma lower_le_Some [simp]: "lower_le (Some a) b \<longleftrightarrow> a \<le> b"
  by (simp add: lower_le_def)

lemma above_lower_le: "above_lo lo b \<Longrightarrow> lower_le lo b"
  by (cases lo) auto

lemma lower_le_above:
  assumes "lower_le lo b" and "b < k"
  shows "above_lo lo k"
proof (cases lo)
  case None
  then show ?thesis by simp
next
  case (Some a)
  then have "a \<le> b" using assms(1) by simp
  then have "a < k" using assms(2) by (rule le_less_trans)
  then show ?thesis using Some by simp
qed

fun ranges_chain :: "'k::linorder option \<Rightarrow> 'k chunk list \<Rightarrow> bool" where
  "ranges_chain lo [] \<longleftrightarrow> True"
| "ranges_chain lo (c # cs) \<longleftrightarrow>
     c_lo c = lo \<and>
     (case c_hi c of
        None \<Rightarrow> cs = []
      | Some b \<Rightarrow> lower_le lo b \<and> ranges_chain (Some b) cs)"

fun chain_rest :: "'k::linorder option \<Rightarrow> 'k chunk list \<Rightarrow> 'k set" where
  "chain_rest lo [] = {k. above_lo lo k}"
| "chain_rest lo (c # cs) =
     (case c_hi c of None \<Rightarrow> {} | Some b \<Rightarrow> chain_rest (Some b) cs)"

lemma chain_above:
  assumes "ranges_chain lo cs" and "c \<in> set cs" and "k \<in> chunk_keys c"
  shows "above_lo lo k"
  using assms
proof (induction cs arbitrary: lo)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have d_lo: "c_lo d = lo" using Cons.prems(1) by simp
  consider (head) "c = d" | (rest) "c \<in> set ds" using Cons.prems(2) by auto
  then show ?case
  proof cases
    case head
    then show ?thesis using Cons.prems(3) d_lo by (simp add: chunk_keys_def)
  next
    case rest
    obtain b where b: "c_hi d = Some b"
      using Cons.prems(1) rest by (cases "c_hi d") auto
    have le: "lower_le lo b" and ch: "ranges_chain (Some b) ds"
      using Cons.prems(1) b by simp_all
    have "b < k" using Cons.IH[OF ch rest Cons.prems(3)] by simp
    then show ?thesis by (rule lower_le_above[OF le])
  qed
qed

lemma chain_rest_above:
  assumes "ranges_chain lo cs" and "k \<in> chain_rest lo cs"
  shows "above_lo lo k"
  using assms
proof (induction cs arbitrary: lo)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  show ?case
  proof (cases "c_hi c")
    case None
    then show ?thesis using Cons.prems(2) by simp
  next
    case (Some b)
    have le: "lower_le lo b" and ch: "ranges_chain (Some b) cs"
      using Cons.prems(1) Some by simp_all
    have "b < k" using Cons.IH[OF ch] Cons.prems(2) Some by simp
    then show ?thesis by (rule lower_le_above[OF le])
  qed
qed

lemma chain_covered:
  assumes "ranges_chain lo cs"
  shows "covered cs = {k. above_lo lo k} - chain_rest lo cs"
  using assms
proof (induction cs arbitrary: lo)
  case Nil
  then show ?case by (simp add: covered_def)
next
  case (Cons c cs)
  have c_lo: "c_lo c = lo" using Cons.prems by simp
  show ?case
  proof (cases "c_hi c")
    case None
    then have "cs = []" using Cons.prems by simp
    then show ?thesis using None c_lo by (simp add: covered_def chunk_keys_def)
  next
    case (Some b)
    have le: "lower_le lo b" and ch: "ranges_chain (Some b) cs"
      using Cons.prems Some by simp_all
    have ih: "covered cs = {k. b < k} - chain_rest (Some b) cs"
      using Cons.IH[OF ch] by simp
    have rest_b: "\<And>k. k \<in> chain_rest (Some b) cs \<Longrightarrow> b < k"
      using chain_rest_above[OF ch] by simp
    have "covered (c # cs) = {k. above_lo lo k \<and> k \<le> b} \<union> covered cs"
      using c_lo Some by (simp add: covered_def chunk_keys_def)
    also have "\<dots> = {k. above_lo lo k} - chain_rest (Some b) cs"
    proof (rule set_eqI)
      fix k
      consider (low) "k \<le> b" | (high) "b < k" by fastforce
      then show "k \<in> {k. above_lo lo k \<and> k \<le> b} \<union> covered cs \<longleftrightarrow>
                 k \<in> {k. above_lo lo k} - chain_rest (Some b) cs"
      proof cases
        case low
        then have "k \<notin> chain_rest (Some b) cs" using rest_b by (auto simp: not_less[symmetric])
        moreover have "k \<notin> covered cs" using ih low by (auto simp: not_less[symmetric])
        ultimately show ?thesis using low by simp
      next
        case high
        then have "above_lo lo k" by (rule lower_le_above[OF le])
        then show ?thesis using ih high by (auto simp: not_less[symmetric])
      qed
    qed
    also have "\<dots> = {k. above_lo lo k} - chain_rest lo (c # cs)"
      using Some by simp
    finally show ?thesis .
  qed
qed

lemma chain_disjoint:
  assumes "ranges_chain lo cs"
  shows "sorted_wrt (\<lambda>c d. chunk_keys c \<inter> chunk_keys d = {}) cs"
  using assms
proof (induction cs arbitrary: lo)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  show ?case
  proof (cases "c_hi c")
    case None
    then have "cs = []" using Cons.prems by simp
    then show ?thesis by simp
  next
    case (Some b)
    have ch: "ranges_chain (Some b) cs" using Cons.prems Some by simp
    have sep: "chunk_keys c \<inter> chunk_keys d = {}" if d: "d \<in> set cs" for d
    proof -
      have hi: "\<And>k. k \<in> chunk_keys d \<Longrightarrow> b < k"
        using chain_above[OF ch d] by simp
      have lo: "\<And>k. k \<in> chunk_keys c \<Longrightarrow> k \<le> b"
        using Some by (simp add: chunk_keys_def)
      show ?thesis
      proof (rule equals0I)
        fix k assume "k \<in> chunk_keys c \<inter> chunk_keys d"
        then have "k \<le> b" and "b < k" using hi lo by auto
        then show False by simp
      qed
    qed
    show ?thesis using sep Cons.IH[OF ch] by simp
  qed
qed

lemma chain_consecutive:
  assumes "ranges_chain lo cs" and "Suc i < length cs"
  shows "\<exists>b. c_hi (cs ! i) = Some b \<and> c_lo (cs ! Suc i) = Some b"
  using assms
proof (induction cs arbitrary: lo i)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  have ne: "cs \<noteq> []" using Cons.prems(2) by auto
  obtain b where b: "c_hi c = Some b"
    using Cons.prems(1) ne by (cases "c_hi c") auto
  have ch: "ranges_chain (Some b) cs" using Cons.prems(1) b by simp
  show ?case
  proof (cases i)
    case 0
    obtain d ds where cs: "cs = d # ds" using ne by (cases cs) auto
    have "c_lo d = Some b" using ch cs by simp
    then show ?thesis using b cs 0 by simp
  next
    case (Suc j)
    have "Suc j < length cs" using Cons.prems(2) Suc by simp
    then show ?thesis using Cons.IH[OF ch] Suc by simp
  qed
qed

lemma chain_first:
  assumes "ranges_chain lo cs" and "cs \<noteq> []"
  shows "c_lo (cs ! 0) = lo"
  using assms by (cases cs) auto

subsection \<open>The pass: the bounded main loop, the tail reads, the classic loop\<close>

text \<open>
  The outcome of a pass.

  \<^item> @{text Completed}: a short page was observed in an unbounded read (a
    tail read, or a read of the classic loop), so the last range is open
    above.
  \<^item> @{text "Tail_Limit f"}: the tail-read limit stopped the pass. Here
    @{text f} is the exclusive lower bound the next read would have used, and
    every key above it is uncovered.
  \<^item> @{text "Running f"}: the list of reads ran out before the pass ended.
    The keys above @{text f} are not yet covered.

  The frontier @{text f} is an option, and @{term None} means that no key is
  covered.
\<close>

datatype 'k pass_status =
    Completed
  | Tail_Limit "'k option"
  | Running "'k option"

fun uncovered :: "'k::linorder pass_status \<Rightarrow> 'k set" where
  "uncovered Completed = {}"
| "uncovered (Tail_Limit f) = {k. above_lo f k}"
| "uncovered (Running f) = {k. above_lo f k}"

text \<open>
  The tail reads: plain pages above the current lower bound, at most
  @{text t} of them. A short page ends the pass with a range open above. A
  full page closes its range at its last key, and the next read starts there.
  When @{text t} full pages have been read the pass stops.
\<close>

fun tail_scan ::
  "nat \<Rightarrow> nat \<Rightarrow> 'k::linorder option \<Rightarrow> 'k set list
     \<Rightarrow> 'k chunk list \<times> 'k pass_status" where
  "tail_scan n 0 lo Ss = ([], Tail_Limit lo)"
| "tail_scan n (Suc t) lo [] = ([], Running lo)"
| "tail_scan n (Suc t) lo (S # Ss) =
     (if length (page S lo n) < n
      then ([\<lparr>c_lo = lo, c_hi = None, c_rows = page S lo n\<rparr>], Completed)
      else apfst (Cons \<lparr>c_lo = lo, c_hi = Some (last (page S lo n)),
                        c_rows = page S lo n\<rparr>)
                 (tail_scan n t (Some (last (page S lo n))) Ss))"

text \<open>
  The bounded main loop: bounded pages at or below the recorded maximum
  @{text M}. A short page closes its range at @{text M}. A short bounded page
  shows only that the keys in @{text "(lo, M]"} are exhausted, whether the
  bound or the end of the table stopped the query, so closing at @{text M} is
  sound either way. The tail reads above @{text M} follow, at most @{text T}
  of them.
\<close>

fun bounded_scan ::
  "nat \<Rightarrow> nat \<Rightarrow> 'k::linorder \<Rightarrow> 'k option \<Rightarrow> 'k set list
     \<Rightarrow> 'k chunk list \<times> 'k pass_status" where
  "bounded_scan n T M lo [] = ([], Running lo)"
| "bounded_scan n T M lo (S # Ss) =
     (if length (bpage S lo M n) < n
      then apfst (Cons \<lparr>c_lo = lo, c_hi = Some M, c_rows = bpage S lo M n\<rparr>)
                 (tail_scan n T (Some M) Ss)
      else apfst (Cons \<lparr>c_lo = lo, c_hi = Some (last (bpage S lo M n)),
                        c_rows = bpage S lo M n\<rparr>)
                 (bounded_scan n T M (Some (last (bpage S lo M n))) Ss))"

text \<open>
  A bounded pass starts open below. The recorded maximum is an option:
  @{term None} stands for a table that was empty when the pass started, which
  has no maximum, so the pass goes straight to the tail reads. When at least
  one tail read is allowed and the table is still empty, the first tail read
  is short and emits the single range open at both ends, with no rows
  (@{text empty_table_single_range} below).
\<close>

definition bounded_pass ::
  "nat \<Rightarrow> nat \<Rightarrow> 'k::linorder option \<Rightarrow> 'k set list
     \<Rightarrow> 'k chunk list \<times> 'k pass_status" where
  "bounded_pass n T Mo Ss =
     (case Mo of None \<Rightarrow> tail_scan n T None Ss
               | Some M \<Rightarrow> bounded_scan n T M None Ss)"

text \<open>
  The classic DBLog loop: plain pages until a short page, with no recorded
  maximum and no limit on the number of reads.
\<close>

fun classic_scan ::
  "nat \<Rightarrow> 'k::linorder option \<Rightarrow> 'k set list \<Rightarrow> 'k chunk list \<times> 'k pass_status" where
  "classic_scan n lo [] = ([], Running lo)"
| "classic_scan n lo (S # Ss) =
     (if length (page S lo n) < n
      then ([\<lparr>c_lo = lo, c_hi = None, c_rows = page S lo n\<rparr>], Completed)
      else apfst (Cons \<lparr>c_lo = lo, c_hi = Some (last (page S lo n)),
                        c_rows = page S lo n\<rparr>)
                 (classic_scan n (Some (last (page S lo n))) Ss))"

definition classic_pass ::
  "nat \<Rightarrow> 'k::linorder set list \<Rightarrow> 'k chunk list \<times> 'k pass_status" where
  "classic_pass n Ss = classic_scan n None Ss"

subsection \<open>The tail reads emit an exact chain\<close>

text \<open>
  The tail-read equations for a positive limit, which also apply when the
  limit is written as a numeral.
\<close>

lemma tail_scan_pos_Nil: "0 < t \<Longrightarrow> tail_scan n t lo [] = ([], Running lo)"
  by (cases t) simp_all

lemma tail_scan_pos_Cons:
  "0 < t \<Longrightarrow> tail_scan n t lo (S # Ss) =
     (if length (page S lo n) < n
      then ([\<lparr>c_lo = lo, c_hi = None, c_rows = page S lo n\<rparr>], Completed)
      else apfst (Cons \<lparr>c_lo = lo, c_hi = Some (last (page S lo n)),
                        c_rows = page S lo n\<rparr>)
                 (tail_scan n (t - 1) (Some (last (page S lo n))) Ss))"
  by (cases t) simp_all

lemma page_full_ne:
  assumes "0 < n" and "\<not> length (page S lo n) < n"
  shows "page S lo n \<noteq> []"
  using assms by auto

lemma bpage_full_ne:
  assumes "0 < n" and "\<not> length (bpage S lo M n) < n"
  shows "bpage S lo M n \<noteq> []"
  using assms by auto

lemma page_last_above:
  assumes "page S lo n \<noteq> []"
  shows "above_lo lo (last (page S lo n))"
  using page_sub[of S lo n] last_in_set[OF assms] by auto

lemma bpage_last_above:
  assumes "bpage S lo M n \<noteq> []"
  shows "above_lo lo (last (bpage S lo M n))"
  using bpage_sub[of S lo M n] last_in_set[OF assms] by auto

lemma bpage_last_le:
  assumes "bpage S lo M n \<noteq> []"
  shows "last (bpage S lo M n) \<le> M"
  using bpage_sub[of S lo M n] last_in_set[OF assms] by auto

lemma page_length_le: "length (page S lo n) \<le> n"
  by (simp add: page_def smallest_length)

lemma bpage_length_le: "length (bpage S lo M n) \<le> n"
  by (simp add: bpage_def smallest_length)

lemma tail_scan_chain:
  assumes "0 < n"
  shows "ranges_chain lo (fst (tail_scan n t lo Ss))"
  using assms
proof (induction n t lo Ss rule: tail_scan.induct)
  case (1 n lo Ss)
  then show ?case by simp
next
  case (2 n t lo)
  then show ?case by simp
next
  case (3 n t lo S Ss)
  show ?case
  proof (cases "length (page S lo n) < n")
    case True
    then show ?thesis by simp
  next
    case full: False
    have ne: "page S lo n \<noteq> []" by (rule page_full_ne[OF "3.prems" full])
    have le: "lower_le lo (last (page S lo n))"
      by (rule above_lower_le[OF page_last_above[OF ne]])
    have ch: "ranges_chain (Some (last (page S lo n)))
                (fst (tail_scan n t (Some (last (page S lo n))) Ss))"
      by (rule "3.IH"[OF full "3.prems"])
    show ?thesis using full le ch by simp
  qed
qed

lemma tail_scan_rest:
  "chain_rest lo (fst (tail_scan n t lo Ss)) = uncovered (snd (tail_scan n t lo Ss))"
proof (induction n t lo Ss rule: tail_scan.induct)
  case (1 n lo Ss)
  then show ?case by simp
next
  case (2 n t lo)
  then show ?case by simp
next
  case (3 n t lo S Ss)
  then show ?case by simp
qed

lemma tail_scan_length: "length (fst (tail_scan n t lo Ss)) \<le> length Ss"
proof (induction n t lo Ss rule: tail_scan.induct)
  case (1 n lo Ss)
  then show ?case by simp
next
  case (2 n t lo)
  then show ?case by simp
next
  case (3 n t lo S Ss)
  then show ?case by simp
qed

lemma tail_scan_exact:
  assumes "0 < n" and "i < length (fst (tail_scan n t lo Ss))" and "finite (Ss ! i)"
  shows "chunk_exact (Ss ! i) (fst (tail_scan n t lo Ss) ! i)"
  using assms
proof (induction n t lo Ss arbitrary: i rule: tail_scan.induct)
  case (1 n lo Ss)
  then show ?case by simp
next
  case (2 n t lo)
  then show ?case by simp
next
  case (3 n t lo S Ss)
  show ?case
  proof (cases "length (page S lo n) < n")
    case short: True
    have i0: "i = 0" using "3.prems"(2) short by simp
    have fin: "finite S" using "3.prems"(3) i0 by simp
    show ?thesis using exact_open_above[OF fin short] short i0 by simp
  next
    case full: False
    have ne: "page S lo n \<noteq> []" by (rule page_full_ne[OF "3.prems"(1) full])
    consider (head) "i = 0" | (rest) j where "i = Suc j" by (cases i) auto
    then show ?thesis
    proof cases
      case head
      have fin: "finite S" using "3.prems"(3) head by simp
      show ?thesis using exact_closed[OF fin ne] full head by simp
    next
      case rest
      have j: "j < length (fst (tail_scan n t (Some (last (page S lo n))) Ss))"
        using "3.prems"(2) full rest by simp
      have fin: "finite (Ss ! j)" using "3.prems"(3) rest by simp
      have "chunk_exact (Ss ! j) (fst (tail_scan n t (Some (last (page S lo n))) Ss) ! j)"
        by (rule "3.IH"[OF full "3.prems"(1) j fin])
      then show ?thesis using full rest by simp
    qed
  qed
qed

lemma tail_scan_limit_last:
  assumes "0 < n" and "0 < t" and "snd (tail_scan n t lo Ss) = Tail_Limit f"
  shows "fst (tail_scan n t lo Ss) \<noteq> [] \<and>
         c_rows (last (fst (tail_scan n t lo Ss))) \<noteq> [] \<and>
         f = Some (last (c_rows (last (fst (tail_scan n t lo Ss)))))"
  using assms
proof (induction n t lo Ss rule: tail_scan.induct)
  case (1 n lo Ss)
  then show ?case by simp
next
  case (2 n t lo)
  then show ?case by simp
next
  case (3 n t lo S Ss)
  show ?case
  proof (cases "length (page S lo n) < n")
    case True
    then show ?thesis using "3.prems"(3) by simp
  next
    case full: False
    have ne: "page S lo n \<noteq> []" by (rule page_full_ne[OF "3.prems"(1) full])
    let ?r = "tail_scan n t (Some (last (page S lo n))) Ss"
    have stop: "snd ?r = Tail_Limit f" using "3.prems"(3) full by simp
    consider (last_read) "t = 0" | (more) "0 < t" by blast
    then show ?thesis
    proof cases
      case last_read
      then show ?thesis using full ne stop by simp
    next
      case more
      have "fst ?r \<noteq> [] \<and> c_rows (last (fst ?r)) \<noteq> [] \<and>
            f = Some (last (c_rows (last (fst ?r))))"
        by (rule "3.IH"[OF full "3.prems"(1) more stop])
      then show ?thesis using full by simp
    qed
  qed
qed

lemma tail_scan_reads:
  assumes "i < length (fst (tail_scan n t lo Ss))"
  shows "c_rows (fst (tail_scan n t lo Ss) ! i)
           = page (Ss ! i) (c_lo (fst (tail_scan n t lo Ss) ! i)) n"
  using assms
proof (induction n t lo Ss arbitrary: i rule: tail_scan.induct)
  case (1 n lo Ss)
  then show ?case by simp
next
  case (2 n t lo)
  then show ?case by simp
next
  case (3 n t lo S Ss)
  show ?case
  proof (cases "length (page S lo n) < n")
    case short: True
    have "i = 0" using "3.prems" short by simp
    then show ?thesis using short by simp
  next
    case full: False
    consider (head) "i = 0" | (rest) j where "i = Suc j" by (cases i) auto
    then show ?thesis
    proof cases
      case head
      then show ?thesis using full by simp
    next
      case rest
      have j: "j < length (fst (tail_scan n t (Some (last (page S lo n))) Ss))"
        using "3.prems" full rest by simp
      have "c_rows (fst (tail_scan n t (Some (last (page S lo n))) Ss) ! j)
              = page (Ss ! j) (c_lo (fst (tail_scan n t (Some (last (page S lo n))) Ss) ! j)) n"
        by (rule "3.IH"[OF full j])
      then show ?thesis using full rest by simp
    qed
  qed
qed

lemma tail_scan_rule:
  assumes "c \<in> set (fst (tail_scan n t lo Ss))"
  shows "(length (c_rows c) = n \<and> c_hi c = Some (last (c_rows c)))
         \<or> (length (c_rows c) < n \<and> c_hi c = None)"
  using assms
proof (induction n t lo Ss rule: tail_scan.induct)
  case (1 n lo Ss)
  then show ?case by simp
next
  case (2 n t lo)
  then show ?case by simp
next
  case (3 n t lo S Ss)
  show ?case
  proof (cases "length (page S lo n) < n")
    case short: True
    then show ?thesis using "3.prems" by auto
  next
    case full: False
    have len: "length (page S lo n) = n"
      using full page_length_le[of S lo n] by simp
    consider (head) "c = \<lparr>c_lo = lo, c_hi = Some (last (page S lo n)), c_rows = page S lo n\<rparr>"
      | (rest) "c \<in> set (fst (tail_scan n t (Some (last (page S lo n))) Ss))"
      using "3.prems" full by auto
    then show ?thesis
    proof cases
      case head
      then show ?thesis using len by simp
    next
      case rest
      then show ?thesis by (rule "3.IH"[OF full])
    qed
  qed
qed

lemma tail_scan_completed:
  assumes "snd (tail_scan n t lo Ss) = Completed"
  shows "fst (tail_scan n t lo Ss) \<noteq> [] \<and>
         c_hi (last (fst (tail_scan n t lo Ss))) = None \<and>
         length (c_rows (last (fst (tail_scan n t lo Ss)))) < n"
  using assms
proof (induction n t lo Ss rule: tail_scan.induct)
  case (1 n lo Ss)
  then show ?case by simp
next
  case (2 n t lo)
  then show ?case by simp
next
  case (3 n t lo S Ss)
  show ?case
  proof (cases "length (page S lo n) < n")
    case short: True
    then show ?thesis by simp
  next
    case full: False
    let ?r = "tail_scan n t (Some (last (page S lo n))) Ss"
    have "snd ?r = Completed" using "3.prems" full by simp
    then have "fst ?r \<noteq> [] \<and> c_hi (last (fst ?r)) = None \<and> length (c_rows (last (fst ?r))) < n"
      by (rule "3.IH"[OF full])
    then show ?thesis using full by simp
  qed
qed

subsection \<open>The bounded main loop emits an exact chain\<close>

lemma bounded_scan_chain:
  assumes "0 < n" and "lower_le lo M"
  shows "ranges_chain lo (fst (bounded_scan n T M lo Ss))"
  using assms
proof (induction n T M lo Ss rule: bounded_scan.induct)
  case (1 n T M lo)
  then show ?case by simp
next
  case (2 n T M lo S Ss)
  show ?case
  proof (cases "length (bpage S lo M n) < n")
    case short: True
    have ch: "ranges_chain (Some M) (fst (tail_scan n T (Some M) Ss))"
      by (rule tail_scan_chain[OF "2.prems"(1)])
    show ?thesis using short "2.prems"(2) ch by simp
  next
    case full: False
    have ne: "bpage S lo M n \<noteq> []" by (rule bpage_full_ne[OF "2.prems"(1) full])
    have le: "lower_le lo (last (bpage S lo M n))"
      by (rule above_lower_le[OF bpage_last_above[OF ne]])
    have leM: "lower_le (Some (last (bpage S lo M n))) M"
      using bpage_last_le[OF ne] by simp
    have ch: "ranges_chain (Some (last (bpage S lo M n)))
                (fst (bounded_scan n T M (Some (last (bpage S lo M n))) Ss))"
      by (rule "2.IH"[OF full "2.prems"(1) leM])
    show ?thesis using full le ch by simp
  qed
qed

lemma bounded_scan_rest:
  "chain_rest lo (fst (bounded_scan n T M lo Ss)) = uncovered (snd (bounded_scan n T M lo Ss))"
proof (induction n T M lo Ss rule: bounded_scan.induct)
  case (1 n T M lo)
  then show ?case by simp
next
  case (2 n T M lo S Ss)
  then show ?case by (simp add: tail_scan_rest)
qed

lemma bounded_scan_length: "length (fst (bounded_scan n T M lo Ss)) \<le> length Ss"
proof (induction n T M lo Ss rule: bounded_scan.induct)
  case (1 n T M lo)
  then show ?case by simp
next
  case (2 n T M lo S Ss)
  then show ?case using tail_scan_length[of n T "Some M" Ss] by simp
qed

lemma bounded_scan_exact:
  assumes "0 < n" and "i < length (fst (bounded_scan n T M lo Ss))" and "finite (Ss ! i)"
  shows "chunk_exact (Ss ! i) (fst (bounded_scan n T M lo Ss) ! i)"
  using assms
proof (induction n T M lo Ss arbitrary: i rule: bounded_scan.induct)
  case (1 n T M lo)
  then show ?case by simp
next
  case (2 n T M lo S Ss)
  consider (head) "i = 0" | (rest) j where "i = Suc j" by (cases i) auto
  then show ?case
  proof cases
    case head
    have fin: "finite S" using "2.prems"(3) head by simp
    show ?thesis
    proof (cases "length (bpage S lo M n) < n")
      case short: True
      show ?thesis using exact_closed_at_max[OF fin short] short head by simp
    next
      case full: False
      have ne: "bpage S lo M n \<noteq> []" by (rule bpage_full_ne[OF "2.prems"(1) full])
      show ?thesis using exact_bounded_closed[OF fin ne] full head by simp
    qed
  next
    case rest
    have fin: "finite (Ss ! j)" using "2.prems"(3) rest by simp
    show ?thesis
    proof (cases "length (bpage S lo M n) < n")
      case short: True
      have j: "j < length (fst (tail_scan n T (Some M) Ss))"
        using "2.prems"(2) short rest by simp
      have "chunk_exact (Ss ! j) (fst (tail_scan n T (Some M) Ss) ! j)"
        by (rule tail_scan_exact[OF "2.prems"(1) j fin])
      then show ?thesis using short rest by simp
    next
      case full: False
      have j: "j < length (fst (bounded_scan n T M (Some (last (bpage S lo M n))) Ss))"
        using "2.prems"(2) full rest by simp
      have "chunk_exact (Ss ! j)
              (fst (bounded_scan n T M (Some (last (bpage S lo M n))) Ss) ! j)"
        by (rule "2.IH"[OF full "2.prems"(1) j fin])
      then show ?thesis using full rest by simp
    qed
  qed
qed

lemma bounded_scan_limit_last:
  assumes "0 < n" and "0 < T" and "snd (bounded_scan n T M lo Ss) = Tail_Limit f"
  shows "fst (bounded_scan n T M lo Ss) \<noteq> [] \<and>
         c_rows (last (fst (bounded_scan n T M lo Ss))) \<noteq> [] \<and>
         f = Some (last (c_rows (last (fst (bounded_scan n T M lo Ss)))))"
  using assms
proof (induction n T M lo Ss rule: bounded_scan.induct)
  case (1 n T M lo)
  then show ?case by simp
next
  case (2 n T M lo S Ss)
  show ?case
  proof (cases "length (bpage S lo M n) < n")
    case short: True
    let ?r = "tail_scan n T (Some M) Ss"
    have stop: "snd ?r = Tail_Limit f" using "2.prems"(3) short by simp
    have "fst ?r \<noteq> [] \<and> c_rows (last (fst ?r)) \<noteq> [] \<and>
          f = Some (last (c_rows (last (fst ?r))))"
      by (rule tail_scan_limit_last[OF "2.prems"(1) "2.prems"(2) stop])
    then show ?thesis using short by simp
  next
    case full: False
    let ?r = "bounded_scan n T M (Some (last (bpage S lo M n))) Ss"
    have stop: "snd ?r = Tail_Limit f" using "2.prems"(3) full by simp
    have "fst ?r \<noteq> [] \<and> c_rows (last (fst ?r)) \<noteq> [] \<and>
          f = Some (last (c_rows (last (fst ?r))))"
      by (rule "2.IH"[OF full "2.prems"(1) "2.prems"(2) stop])
    then show ?thesis using full by simp
  qed
qed

lemma bounded_scan_no_tail_reads:
  assumes "snd (bounded_scan n 0 M lo Ss) = Tail_Limit f"
  shows "f = Some M"
  using assms
proof (induction n "0::nat" M lo Ss rule: bounded_scan.induct)
  case (1 n M lo)
  then show ?case by simp
next
  case (2 n M lo S Ss)
  then show ?case by (cases "length (bpage S lo M n) < n") simp_all
qed

lemma bounded_scan_reads:
  assumes "i < length (fst (bounded_scan n T M lo Ss))"
  shows "c_rows (fst (bounded_scan n T M lo Ss) ! i)
           = page (Ss ! i) (c_lo (fst (bounded_scan n T M lo Ss) ! i)) n
         \<or> c_rows (fst (bounded_scan n T M lo Ss) ! i)
           = bpage (Ss ! i) (c_lo (fst (bounded_scan n T M lo Ss) ! i)) M n"
  using assms
proof (induction n T M lo Ss arbitrary: i rule: bounded_scan.induct)
  case (1 n T M lo)
  then show ?case by simp
next
  case (2 n T M lo S Ss)
  consider (head) "i = 0" | (rest) j where "i = Suc j" by (cases i) auto
  then show ?case
  proof cases
    case head
    then show ?thesis by simp
  next
    case rest
    show ?thesis
    proof (cases "length (bpage S lo M n) < n")
      case short: True
      have j: "j < length (fst (tail_scan n T (Some M) Ss))"
        using "2.prems" short rest by simp
      have "c_rows (fst (tail_scan n T (Some M) Ss) ! j)
              = page (Ss ! j) (c_lo (fst (tail_scan n T (Some M) Ss) ! j)) n"
        by (rule tail_scan_reads[OF j])
      then show ?thesis using short rest by simp
    next
      case full: False
      let ?r = "bounded_scan n T M (Some (last (bpage S lo M n))) Ss"
      have j: "j < length (fst ?r)" using "2.prems" full rest by simp
      have "c_rows (fst ?r ! j) = page (Ss ! j) (c_lo (fst ?r ! j)) n
            \<or> c_rows (fst ?r ! j) = bpage (Ss ! j) (c_lo (fst ?r ! j)) M n"
        by (rule "2.IH"[OF full j])
      then show ?thesis using full rest by simp
    qed
  qed
qed

lemma bounded_scan_rule:
  assumes "c \<in> set (fst (bounded_scan n T M lo Ss))"
  shows "(length (c_rows c) = n \<and> c_hi c = Some (last (c_rows c)))
         \<or> (length (c_rows c) < n \<and> c_hi c = None)
         \<or> (length (c_rows c) < n \<and> c_hi c = Some M)"
  using assms
proof (induction n T M lo Ss rule: bounded_scan.induct)
  case (1 n T M lo)
  then show ?case by simp
next
  case (2 n T M lo S Ss)
  show ?case
  proof (cases "length (bpage S lo M n) < n")
    case short: True
    consider (head) "c = \<lparr>c_lo = lo, c_hi = Some M, c_rows = bpage S lo M n\<rparr>"
      | (rest) "c \<in> set (fst (tail_scan n T (Some M) Ss))"
      using "2.prems" short by auto
    then show ?thesis
    proof cases
      case head
      then show ?thesis using short by simp
    next
      case rest
      then show ?thesis using tail_scan_rule[OF rest] by blast
    qed
  next
    case full: False
    have len: "length (bpage S lo M n) = n"
      using full bpage_length_le[of S lo M n] by simp
    consider (head) "c = \<lparr>c_lo = lo, c_hi = Some (last (bpage S lo M n)), c_rows = bpage S lo M n\<rparr>"
      | (rest) "c \<in> set (fst (bounded_scan n T M (Some (last (bpage S lo M n))) Ss))"
      using "2.prems" full by auto
    then show ?thesis
    proof cases
      case head
      then show ?thesis using len by simp
    next
      case rest
      then show ?thesis by (rule "2.IH"[OF full])
    qed
  qed
qed

lemma bounded_scan_completed:
  assumes "snd (bounded_scan n T M lo Ss) = Completed"
  shows "fst (bounded_scan n T M lo Ss) \<noteq> [] \<and>
         c_hi (last (fst (bounded_scan n T M lo Ss))) = None \<and>
         length (c_rows (last (fst (bounded_scan n T M lo Ss)))) < n"
  using assms
proof (induction n T M lo Ss rule: bounded_scan.induct)
  case (1 n T M lo)
  then show ?case by simp
next
  case (2 n T M lo S Ss)
  show ?case
  proof (cases "length (bpage S lo M n) < n")
    case short: True
    let ?r = "tail_scan n T (Some M) Ss"
    have "snd ?r = Completed" using "2.prems" short by simp
    then have "fst ?r \<noteq> [] \<and> c_hi (last (fst ?r)) = None \<and> length (c_rows (last (fst ?r))) < n"
      by (rule tail_scan_completed)
    then show ?thesis using short by simp
  next
    case full: False
    let ?r = "bounded_scan n T M (Some (last (bpage S lo M n))) Ss"
    have "snd ?r = Completed" using "2.prems" full by simp
    then have "fst ?r \<noteq> [] \<and> c_hi (last (fst ?r)) = None \<and> length (c_rows (last (fst ?r))) < n"
      by (rule "2.IH"[OF full])
    then show ?thesis using full by simp
  qed
qed

subsection \<open>Pass-level facts\<close>

lemma pass_chain:
  assumes "0 < n"
  shows "ranges_chain None (fst (bounded_pass n T Mo Ss))"
proof (cases Mo)
  case None
  then show ?thesis using tail_scan_chain[OF assms] by (simp add: bounded_pass_def)
next
  case (Some M)
  have "ranges_chain None (fst (bounded_scan n T M None Ss))"
    by (rule bounded_scan_chain[OF assms]) simp
  then show ?thesis using Some by (simp add: bounded_pass_def)
qed

lemma pass_rest:
  "chain_rest None (fst (bounded_pass n T Mo Ss)) = uncovered (snd (bounded_pass n T Mo Ss))"
  by (cases Mo) (simp_all add: bounded_pass_def tail_scan_rest bounded_scan_rest)

lemma pass_covered:
  assumes "0 < n"
  shows "covered (fst (bounded_pass n T Mo Ss)) = - uncovered (snd (bounded_pass n T Mo Ss))"
proof -
  have "covered (fst (bounded_pass n T Mo Ss))
          = {k. above_lo None k} - chain_rest None (fst (bounded_pass n T Mo Ss))"
    by (rule chain_covered[OF pass_chain[OF assms]])
  then show ?thesis by (simp add: pass_rest Compl_eq_Diff_UNIV)
qed

lemma pass_exact:
  assumes "0 < n" and "i < length (fst (bounded_pass n T Mo Ss))" and "finite (Ss ! i)"
  shows "chunk_exact (Ss ! i) (fst (bounded_pass n T Mo Ss) ! i)"
proof (cases Mo)
  case None
  then show ?thesis
    using tail_scan_exact[OF assms(1) _ assms(3), of T None] assms(2)
    by (simp add: bounded_pass_def)
next
  case (Some M)
  then show ?thesis
    using bounded_scan_exact[OF assms(1) _ assms(3), of T M None] assms(2)
    by (simp add: bounded_pass_def)
qed

subsection \<open>Main results for the bounded pass\<close>

text \<open>
  Throughout, @{text n} is the chunk limit, @{text T} the tail-read limit,
  @{text Mo} the maximum key recorded at the start (or @{term None} for a
  table that was empty then), and @{text Ss} the source states at the cuts of
  the successive reads. The @{text i}-th chunk is the result of the
  @{text i}-th read.
\<close>

theorem chunks_le_reads: "length (fst (bounded_pass n T Mo Ss)) \<le> length Ss"
  by (cases Mo) (simp_all add: bounded_pass_def tail_scan_length bounded_scan_length)

text \<open>
  Each chunk is the result of its own read: its rows are the page of the
  source state at the @{text i}-th cut, queried from the chunk's own lower
  bound, either plain or bounded at the recorded maximum.
\<close>

theorem chunk_is_read:
  assumes cs: "cs = fst (bounded_pass n T Mo Ss)" and i: "i < length cs"
  shows "c_rows (cs ! i) = page (Ss ! i) (c_lo (cs ! i)) n
         \<or> (\<exists>M. Mo = Some M \<and> c_rows (cs ! i) = bpage (Ss ! i) (c_lo (cs ! i)) M n)"
proof (cases Mo)
  case None
  then show ?thesis
    using tail_scan_reads[of i n T None Ss] cs i by (simp add: bounded_pass_def)
next
  case (Some M)
  then show ?thesis
    using bounded_scan_reads[of i n T M None Ss] cs i by (simp add: bounded_pass_def)
qed

text \<open>
  The range rule, as a property of the output. A chunk with a full page
  closes at its last returned key. A chunk with a short page is open above,
  or closes at the recorded maximum.
\<close>

theorem range_rule:
  assumes cs: "cs = fst (bounded_pass n T Mo Ss)" and c: "c \<in> set cs"
  shows "(length (c_rows c) = n \<and> c_hi c = Some (last (c_rows c)))
         \<or> (length (c_rows c) < n \<and> c_hi c = None)
         \<or> (length (c_rows c) < n \<and> c_hi c = Mo)"
proof (cases Mo)
  case None
  then show ?thesis
    using tail_scan_rule[of c n T None Ss] cs c by (simp add: bounded_pass_def)
next
  case (Some M)
  then show ?thesis
    using bounded_scan_rule[of c n T M None Ss] cs c by (simp add: bounded_pass_def)
qed

text \<open>
  A pass completes only on a short page of an unbounded read: its last
  range is open above and its last page is short.
\<close>

theorem completed_last_open_above:
  assumes complete: "snd (bounded_pass n T Mo Ss) = Completed"
      and cs: "cs = fst (bounded_pass n T Mo Ss)"
  shows "cs \<noteq> [] \<and> c_hi (last cs) = None \<and> length (c_rows (last cs)) < n"
proof (cases Mo)
  case None
  then show ?thesis
    using tail_scan_completed[of n T None Ss] complete cs by (simp add: bounded_pass_def)
next
  case (Some M)
  then show ?thesis
    using bounded_scan_completed[of n T M None Ss] complete cs by (simp add: bounded_pass_def)
qed

text \<open>
  With at least one tail read configured, an empty source table produces a
  single chunk with both bounds open and no rows, as Section 5.2 states.
\<close>

theorem empty_table_single_range:
  fixes Ss :: "'k::linorder set list"
  assumes n: "0 < n" and T: "0 < T"
  shows "bounded_pass n T None ({} # Ss) =
           ([\<lparr>c_lo = None, c_hi = None, c_rows = []\<rparr>], Completed)"
proof -
  have "page ({} :: 'k set) None n = []" by (simp add: page_def smallest_def)
  then show ?thesis using n T by (simp add: bounded_pass_def tail_scan_pos_Cons)
qed

theorem ranges_disjoint:
  assumes n: "0 < n" and cs: "cs = fst (bounded_pass n T Mo Ss)"
      and i: "i < length cs" and j: "j < length cs" and ij: "i \<noteq> j"
  shows "chunk_keys (cs ! i) \<inter> chunk_keys (cs ! j) = {}"
proof -
  have sw: "sorted_wrt (\<lambda>c d. chunk_keys c \<inter> chunk_keys d = {}) cs"
    using chain_disjoint[OF pass_chain[OF n]] cs by simp
  consider (lt) "i < j" | (gt) "j < i" using ij by linarith
  then show ?thesis
  proof cases
    case lt
    show ?thesis using sorted_wrt_nth_less[OF sw lt j] by simp
  next
    case gt
    have "chunk_keys (cs ! j) \<inter> chunk_keys (cs ! i) = {}"
      using sorted_wrt_nth_less[OF sw gt i] by simp
    then show ?thesis by blast
  qed
qed

theorem ranges_first_open_below:
  assumes n: "0 < n" and cs: "cs = fst (bounded_pass n T Mo Ss)" and ne: "cs \<noteq> []"
  shows "c_lo (cs ! 0) = None"
  using chain_first[OF pass_chain[OF n] ne[unfolded cs]] cs by simp

theorem ranges_consecutive:
  assumes n: "0 < n" and cs: "cs = fst (bounded_pass n T Mo Ss)" and i: "Suc i < length cs"
  shows "\<exists>b. c_hi (cs ! i) = Some b \<and> c_lo (cs ! Suc i) = Some b"
  using chain_consecutive[OF pass_chain[OF n] i[unfolded cs]] cs by simp

text \<open>
  Consecutive ranges @{text "(a, b]"} and @{text "(b, c]"} leave no gap: every
  key between the first range's lower bound and the second range's upper
  bound lies in one of the two.
\<close>

corollary ranges_no_gap:
  assumes n: "0 < n" and cs: "cs = fst (bounded_pass n T Mo Ss)" and i: "Suc i < length cs"
      and lo: "above_lo (c_lo (cs ! i)) k" and hi: "upto_hi (c_hi (cs ! Suc i)) k"
  shows "k \<in> chunk_keys (cs ! i) \<union> chunk_keys (cs ! Suc i)"
proof -
  obtain b where b: "c_hi (cs ! i) = Some b" "c_lo (cs ! Suc i) = Some b"
    using ranges_consecutive[OF n cs i] by blast
  consider (low) "k \<le> b" | (high) "b < k" by fastforce
  then show ?thesis
  proof cases
    case low
    then have "k \<in> chunk_keys (cs ! i)" using lo b by (simp add: chunk_keys_def)
    then show ?thesis by simp
  next
    case high
    then have "k \<in> chunk_keys (cs ! Suc i)" using hi b by (simp add: chunk_keys_def)
    then show ?thesis by simp
  qed
qed

theorem union_on_completion:
  assumes n: "0 < n" and complete: "snd (bounded_pass n T Mo Ss) = Completed"
  shows "covered (fst (bounded_pass n T Mo Ss)) = UNIV"
  using pass_covered[OF n, of T Mo Ss] complete by simp

theorem union_on_limit:
  assumes n: "0 < n" and stop: "snd (bounded_pass n T Mo Ss) = Tail_Limit f"
  shows "covered (fst (bounded_pass n T Mo Ss)) = {k. \<not> above_lo f k}"
  using pass_covered[OF n, of T Mo Ss] stop by auto

theorem uncovered_on_limit:
  assumes n: "0 < n" and stop: "snd (bounded_pass n T Mo Ss) = Tail_Limit f"
  shows "- covered (fst (bounded_pass n T Mo Ss)) = {k. above_lo f k}"
  using pass_covered[OF n, of T Mo Ss] stop by auto

text \<open>
  The frontier of a pass stopped by the tail-read limit. With at least one
  tail read allowed, it is the last key that the last read returned. With no
  tail reads allowed, it is the recorded maximum, which is @{term None} for a
  table that was empty at the start.
\<close>

theorem limit_frontier_last_returned:
  assumes n: "0 < n" and T: "0 < T" and stop: "snd (bounded_pass n T Mo Ss) = Tail_Limit f"
      and cs: "cs = fst (bounded_pass n T Mo Ss)"
  shows "cs \<noteq> [] \<and> c_rows (last cs) \<noteq> [] \<and> f = Some (last (c_rows (last cs)))"
proof (cases Mo)
  case None
  then show ?thesis
    using tail_scan_limit_last[OF n T, of None Ss f] stop cs by (simp add: bounded_pass_def)
next
  case (Some M)
  then show ?thesis
    using bounded_scan_limit_last[OF n T, of M None Ss f] stop cs by (simp add: bounded_pass_def)
qed

theorem limit_frontier_no_tail_reads:
  assumes stop: "snd (bounded_pass n 0 Mo Ss) = Tail_Limit f"
  shows "f = Mo"
proof (cases Mo)
  case None
  then show ?thesis using stop by (simp add: bounded_pass_def)
next
  case (Some M)
  then show ?thesis using bounded_scan_no_tail_reads[of n M None Ss f] stop
    by (simp add: bounded_pass_def)
qed

corollary union_on_limit_last_returned:
  assumes n: "0 < n" and T: "0 < T" and stop: "snd (bounded_pass n T Mo Ss) = Tail_Limit f"
      and cs: "cs = fst (bounded_pass n T Mo Ss)" and b: "b = last (c_rows (last cs))"
  shows "covered cs = {k. k \<le> b}"
proof -
  have "f = Some b" using limit_frontier_last_returned[OF n T stop cs] b by simp
  then show ?thesis using union_on_limit[OF n stop] cs by (auto simp: not_less)
qed

corollary uncovered_on_limit_last_returned:
  assumes n: "0 < n" and T: "0 < T" and stop: "snd (bounded_pass n T Mo Ss) = Tail_Limit f"
      and cs: "cs = fst (bounded_pass n T Mo Ss)" and b: "b = last (c_rows (last cs))"
  shows "- covered cs = {k. b < k}"
proof -
  have "f = Some b" using limit_frontier_last_returned[OF n T stop cs] b by simp
  then show ?thesis using uncovered_on_limit[OF n stop] cs by simp
qed

text \<open>
  While the pass is still running, the ranges emitted so far tile exactly the
  keys at or below the frontier: the invariant of the loop.
\<close>

theorem union_in_progress:
  assumes n: "0 < n" and run: "snd (bounded_pass n T Mo Ss) = Running f"
  shows "covered (fst (bounded_pass n T Mo Ss)) = {k. \<not> above_lo f k}"
  using pass_covered[OF n, of T Mo Ss] run by auto

text \<open>
  Soundness of every range for its own read. The source state at the read's
  cut is assumed finite, as a table is.
\<close>

theorem range_exact:
  assumes n: "0 < n" and cs: "cs = fst (bounded_pass n T Mo Ss)"
      and i: "i < length cs" and fin: "finite (Ss ! i)"
  shows "set (c_rows (cs ! i)) = chunk_keys (cs ! i) \<inter> Ss ! i"
  using pass_exact[OF n i[unfolded cs] fin] cs by (simp add: chunk_exact_def)

theorem range_sound:
  assumes n: "0 < n" and cs: "cs = fst (bounded_pass n T Mo Ss)"
      and i: "i < length cs" and fin: "finite (Ss ! i)"
      and k: "k \<in> chunk_keys (cs ! i)" and present: "k \<in> Ss ! i"
  shows "k \<in> set (c_rows (cs ! i))"
  using range_exact[OF n cs i fin] k present by simp

corollary range_absent:
  assumes n: "0 < n" and cs: "cs = fst (bounded_pass n T Mo Ss)"
      and i: "i < length cs" and fin: "finite (Ss ! i)"
      and k: "k \<in> chunk_keys (cs ! i)" and not_selected: "k \<notin> set (c_rows (cs ! i))"
  shows "k \<notin> Ss ! i"
  using range_sound[OF n cs i fin k] not_selected by blast

subsection \<open>The classic loop as a special case\<close>

lemma tail_scan_unlimited:
  assumes "length Ss < t"
  shows "tail_scan n t lo Ss = classic_scan n lo Ss"
  using assms
proof (induction Ss arbitrary: t lo)
  case Nil
  then obtain t' where "t = Suc t'" by (cases t) auto
  then show ?case by simp
next
  case (Cons S Ss)
  then obtain t' where t: "t = Suc t'" and lt: "length Ss < t'" by (cases t) auto
  have "tail_scan n t' (Some (last (page S lo n))) Ss
          = classic_scan n (Some (last (page S lo n))) Ss"
    by (rule Cons.IH[OF lt])
  then show ?case using t by simp
qed

theorem classic_is_special_case:
  assumes "length Ss < T"
  shows "bounded_pass n T None Ss = classic_pass n Ss"
  using tail_scan_unlimited[OF assms] by (simp add: bounded_pass_def classic_pass_def)

lemma classic_special: "classic_pass n Ss = bounded_pass n (Suc (length Ss)) None Ss"
  using classic_is_special_case[of Ss "Suc (length Ss)" n] by simp

lemma classic_scan_not_limited: "snd (classic_scan n lo Ss) \<noteq> Tail_Limit f"
proof (induction n lo Ss rule: classic_scan.induct)
  case (1 n lo)
  then show ?case by simp
next
  case (2 n lo S Ss)
  then show ?case by simp
qed

theorem classic_not_limited: "snd (classic_pass n Ss) \<noteq> Tail_Limit f"
  by (simp add: classic_pass_def classic_scan_not_limited)

lemma classic_chunks:
  assumes "cs = fst (classic_pass n Ss)"
  shows "cs = fst (bounded_pass n (Suc (length Ss)) None Ss)"
  using assms by (simp add: classic_special)

theorem classic_ranges_disjoint:
  assumes n: "0 < n" and cs: "cs = fst (classic_pass n Ss)"
      and i: "i < length cs" and j: "j < length cs" and ij: "i \<noteq> j"
  shows "chunk_keys (cs ! i) \<inter> chunk_keys (cs ! j) = {}"
  by (rule ranges_disjoint[OF n classic_chunks[OF cs] i j ij])

theorem classic_ranges_first_open_below:
  assumes n: "0 < n" and cs: "cs = fst (classic_pass n Ss)" and ne: "cs \<noteq> []"
  shows "c_lo (cs ! 0) = None"
  by (rule ranges_first_open_below[OF n classic_chunks[OF cs] ne])

theorem classic_ranges_consecutive:
  assumes n: "0 < n" and cs: "cs = fst (classic_pass n Ss)" and i: "Suc i < length cs"
  shows "\<exists>b. c_hi (cs ! i) = Some b \<and> c_lo (cs ! Suc i) = Some b"
  by (rule ranges_consecutive[OF n classic_chunks[OF cs] i])

theorem classic_union_on_completion:
  assumes n: "0 < n" and complete: "snd (classic_pass n Ss) = Completed"
  shows "covered (fst (classic_pass n Ss)) = UNIV"
proof -
  have "snd (bounded_pass n (Suc (length Ss)) None Ss) = Completed"
    using complete by (simp add: classic_special)
  then have "covered (fst (bounded_pass n (Suc (length Ss)) None Ss)) = UNIV"
    by (rule union_on_completion[OF n])
  then show ?thesis by (simp add: classic_special)
qed

theorem classic_union_in_progress:
  assumes n: "0 < n" and run: "snd (classic_pass n Ss) = Running f"
  shows "covered (fst (classic_pass n Ss)) = {k. \<not> above_lo f k}"
proof -
  have "snd (bounded_pass n (Suc (length Ss)) None Ss) = Running f"
    using run by (simp add: classic_special)
  then have "covered (fst (bounded_pass n (Suc (length Ss)) None Ss)) = {k. \<not> above_lo f k}"
    by (rule union_in_progress[OF n])
  then show ?thesis by (simp add: classic_special)
qed

theorem classic_range_sound:
  assumes n: "0 < n" and cs: "cs = fst (classic_pass n Ss)"
      and i: "i < length cs" and fin: "finite (Ss ! i)"
      and k: "k \<in> chunk_keys (cs ! i)" and present: "k \<in> Ss ! i"
  shows "k \<in> set (c_rows (cs ! i))"
  by (rule range_sound[OF n classic_chunks[OF cs] i fin k present])

theorem classic_empty_table_single_range:
  fixes Ss :: "'k::linorder set list"
  assumes n: "0 < n"
  shows "classic_pass n ({} # Ss) =
           ([\<lparr>c_lo = None, c_hi = None, c_rows = []\<rparr>], Completed)"
proof -
  have "page ({} :: 'k set) None n = []" by (simp add: page_def smallest_def)
  then show ?thesis using n by (simp add: classic_pass_def)
qed

subsection \<open>The terminal rule is necessary\<close>

text \<open>
  A full page cannot tell whether more keys exist above its last key: adding
  any key above it to the source leaves the page unchanged. So any rule that
  closed a full page open above would be wrong on one of the two sources,
  whenever such a key exists in the key type. On a key type with a greatest
  element, a full page ending in that element is exact when closed open above,
  which the premise @{text above} of the theorems below excludes.
\<close>

lemma take_insort_above:
  fixes xs :: "'k::linorder list"
  assumes "n \<le> length xs" and "\<forall>x \<in> set (take n xs). x < k"
  shows "take n (insort k xs) = take n xs"
  using assms
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have yk: "\<not> k \<le> y" using Cons.prems(2) Suc by (simp add: not_le)
    have "take m (insort k ys) = take m ys"
      using Cons.IH[of m] Cons.prems Suc by simp
    then show ?thesis using yk Suc by simp
  qed
qed

theorem full_page_hides_higher_keys:
  assumes fin: "finite S" and n: "0 < n" and full: "length (page S lo n) = n"
      and above: "last (page S lo n) < k"
  shows "page (insert k S) lo n = page S lo n"
proof (cases "k \<in> S")
  case True
  then show ?thesis by (simp add: insert_absorb)
next
  case False
  let ?A = "{x \<in> S. above_lo lo x}"
  let ?xs = "sorted_list_of_set ?A"
  have ne: "page S lo n \<noteq> []" using full n by auto
  have k_above: "above_lo lo k"
    using page_last_above[OF ne] above by (cases lo) auto
  have ins: "{x \<in> insert k S. above_lo lo x} = insert k ?A"
    using k_above by auto
  have finA: "finite ?A" using fin by simp
  have kA: "k \<notin> ?A" using False by simp
  have sl: "sorted_list_of_set (insert k ?A) = insort k ?xs"
    by (rule sorted_list_of_set_insert[OF finA kA])
  have len: "n \<le> length ?xs"
    using full by (simp add: page_def smallest_def)
  have below: "\<forall>x \<in> set (take n ?xs). x < k"
  proof
    fix x assume x: "x \<in> set (take n ?xs)"
    then have "x \<in> set (page S lo n)" by (simp add: page_def smallest_def)
    then have "x \<le> last (page S lo n)"
      by (rule sorted_le_last[OF smallest_sorted[of n ?A, folded page_def]])
    then show "x < k" using above by (rule le_less_trans)
  qed
  have "page (insert k S) lo n = take n (insort k ?xs)"
    using ins sl by (simp add: page_def smallest_def)
  also have "\<dots> = take n ?xs" by (rule take_insort_above[OF len below])
  also have "\<dots> = page S lo n" by (simp add: page_def smallest_def)
  finally show ?thesis .
qed

corollary open_above_after_full_page_unsound:
  assumes fin: "finite S" and n: "0 < n" and full: "length (page S lo n) = n"
      and above: "last (page S lo n) < k"
  shows "\<not> chunk_exact (insert k S)
            \<lparr>c_lo = lo, c_hi = None, c_rows = page (insert k S) lo n\<rparr>"
proof
  assume ex: "chunk_exact (insert k S)
                \<lparr>c_lo = lo, c_hi = None, c_rows = page (insert k S) lo n\<rparr>"
  have same: "page (insert k S) lo n = page S lo n"
    by (rule full_page_hides_higher_keys[OF fin n full above])
  have ne: "page S lo n \<noteq> []" using full n by auto
  have k_above: "above_lo lo k"
    using page_last_above[OF ne] above by (cases lo) auto
  have "k \<in> set (page S lo n)"
    using ex same k_above by (simp add: chunk_exact_def chunk_keys_def)
  then have "k \<le> last (page S lo n)"
    by (rule sorted_le_last[OF smallest_sorted[of n "{x \<in> S. above_lo lo x}", folded page_def]])
  with above show False by simp
qed

text \<open>
  The concrete counterexample of the design: chunk limit 2, previous last key
  10, present keys 11, 12 and 13. The page returns 11 and 12, a full page. An
  open-above range after it contains the present key 13, which the page did
  not return, so the record would certify 13 absent.
\<close>

theorem terminal_rule_necessary:
  fixes S :: "nat set" and r :: "nat chunk"
  assumes S: "S = {11, 12, 13}"
      and r: "r = \<lparr>c_lo = Some 10, c_hi = None, c_rows = page S (Some 10) 2\<rparr>"
  shows "c_rows r = [11, 12] \<and> 13 \<in> S \<and> 13 \<in> chunk_keys r \<and> 13 \<notin> set (c_rows r)"
proof -
  have p: "page S (Some 10) 2 = [11, 12]"
    unfolding page_def S by (rule smallest_eqI[where xs = "[11, 12, 13]"]) auto
  show ?thesis using S r p by (simp add: chunk_keys_def)
qed

text \<open>
  The same full page arises from the source with keys 11 and 12 only, where
  an open-above range would be correct. The read cannot tell the two apart.
\<close>

lemma terminal_rule_page_without_13: "page {11, 12 :: nat} (Some 10) 2 = [11, 12]"
  unfolding page_def by (rule smallest_eqI[where xs = "[11, 12]"]) auto

lemma terminal_rule_page_with_13: "page {11, 12, 13 :: nat} (Some 10) 2 = [11, 12]"
  unfolding page_def by (rule smallest_eqI[where xs = "[11, 12, 13]"]) auto

subsection \<open>Witnesses: the general statements are not vacuous\<close>

text \<open>
  A completed bounded pass in the spirit of the paper's running example:
  chunk limit 5, recorded maximum 10, two tail reads allowed. Key 12 is
  inserted above the maximum after the first read. The main loop closes its
  short page at 10, and the first tail read returns 12 in a short page, so
  the last range is open above and the pass completes.
\<close>

definition W1 :: "nat set" where "W1 = {1, 2, 3, 5, 6, 8, 9, 10}"
definition W2 :: "nat set" where "W2 = {1, 2, 3, 5, 6, 8, 9, 10, 12}"

definition wit_reads :: "nat set list" where "wit_reads = [W1, W2, W2]"

lemma W1_bpage: "bpage W1 None 10 5 = [1, 2, 3, 5, 6]"
  unfolding bpage_def W1_def
  by (rule smallest_eqI[where xs = "[1, 2, 3, 5, 6, 8, 9, 10]"]) auto

lemma W2_bpage: "bpage W2 (Some 6) 10 5 = [8, 9, 10]"
  unfolding bpage_def W2_def
  by (rule smallest_eqI[where xs = "[8, 9, 10]"]) auto

lemma W2_page: "page W2 (Some 10) 5 = [12]"
  unfolding page_def W2_def
  by (rule smallest_eqI[where xs = "[12]"]) auto

lemma wit_completed:
  "bounded_pass 5 2 (Some 10) wit_reads =
     ([\<lparr>c_lo = None, c_hi = Some 6, c_rows = [1, 2, 3, 5, 6]\<rparr>,
       \<lparr>c_lo = Some 6, c_hi = Some 10, c_rows = [8, 9, 10]\<rparr>,
       \<lparr>c_lo = Some 10, c_hi = None, c_rows = [12]\<rparr>], Completed)"
  by (simp add: wit_reads_def bounded_pass_def W1_bpage W2_bpage W2_page tail_scan_pos_Cons)

lemma wit_completed_covers: "covered (fst (bounded_pass 5 2 (Some 10) wit_reads)) = UNIV"
  using union_on_completion[of 5 2 "Some 10" wit_reads] wit_completed by simp

text \<open>
  A pass stopped by the tail-read limit: chunk limit 2, recorded maximum 3,
  one tail read allowed, keys 1 to 6 present throughout. The tail read returns
  a full page ending at 5, so the pass stops with every key above 5 uncovered,
  although key 6 is present.
\<close>

definition W3 :: "nat set" where "W3 = {1, 2, 3, 4, 5, 6}"

definition wit_reads_limit :: "nat set list" where "wit_reads_limit = [W3, W3, W3]"

lemma W3_bpage_first: "bpage W3 None 3 2 = [1, 2]"
  unfolding bpage_def W3_def
  by (rule smallest_eqI[where xs = "[1, 2, 3]"]) auto

lemma W3_bpage_second: "bpage W3 (Some 2) 3 2 = [3]"
  unfolding bpage_def W3_def
  by (rule smallest_eqI[where xs = "[3]"]) auto

lemma W3_page_tail: "page W3 (Some 3) 2 = [4, 5]"
  unfolding page_def W3_def
  by (rule smallest_eqI[where xs = "[4, 5, 6]"]) auto

lemma wit_limit:
  "bounded_pass 2 1 (Some 3) wit_reads_limit =
     ([\<lparr>c_lo = None, c_hi = Some 2, c_rows = [1, 2]\<rparr>,
       \<lparr>c_lo = Some 2, c_hi = Some 3, c_rows = [3]\<rparr>,
       \<lparr>c_lo = Some 3, c_hi = Some 5, c_rows = [4, 5]\<rparr>], Tail_Limit (Some 5))"
  by (simp add: wit_reads_limit_def bounded_pass_def W3_bpage_first W3_bpage_second
                W3_page_tail tail_scan_pos_Cons)

lemma wit_limit_uncovered:
  "- covered (fst (bounded_pass 2 1 (Some 3) wit_reads_limit)) = {k. 5 < k}"
  using uncovered_on_limit[of 2 1 "Some 3" wit_reads_limit "Some 5"] wit_limit by simp

lemma wit_limit_key6:
  "6 \<in> W3 \<and> 6 \<notin> covered (fst (bounded_pass 2 1 (Some 3) wit_reads_limit))"
proof -
  have "(6::nat) \<in> - covered (fst (bounded_pass 2 1 (Some 3) wit_reads_limit))"
    unfolding wit_limit_uncovered by simp
  then show ?thesis by (simp add: W3_def)
qed

subsection \<open>Bridge: the ranges of a pass as the domains of a capture contract\<close>

text \<open>
  A coordinate space of the contract core whose key type is linearly
  ordered. Each chunk @{text i} of a pass becomes one unit: its domain is the
  chunk's range, its bracket runs from the low watermark @{text "lw i"} to the
  high watermark @{text "hw i"}, and its refresh is what the read at the
  coordinate @{text "rc i"} returned, with absence for every key of the range
  the read did not return.
\<close>

locale ordered_key_space = coordinate_space L den
  for L :: "('k::linorder, 'v) event list" and den :: "'c \<Rightarrow> nat"
begin

definition pass_units ::
  "('k, 'v) state \<Rightarrow> 'k chunk list \<Rightarrow> (nat \<Rightarrow> 'c) \<Rightarrow> (nat \<Rightarrow> 'c) \<Rightarrow> (nat \<Rightarrow> 'c)
     \<Rightarrow> ('k, 'v, 'c) cunit list" where
  "pass_units \<sigma>0 cs lw rc hw =
     map (\<lambda>i. \<lparr>u_dom = chunk_keys (cs ! i), u_lo = lw i, u_hi = hw i,
               u_refresh = (\<lambda>k. if k \<in> set (c_rows (cs ! i))
                                 then state_after \<sigma>0 (pfx (rc i)) k else None)\<rparr>)
         [0..<length cs]"

text \<open>
  The assumptions, in order.

  \<^item> The chunk limit is positive, and the chunks are those of a pass.
  \<^item> Each read's coordinate lies inside its chunk's bracket, and each
    bracket ends by the frontier @{text f}.
  \<^item> The source state each read saw is the set of keys present at its
    coordinate, and it is finite.

  The scope of the contract is the set of keys the pass covered. The pass
  need not be complete.
\<close>

theorem pass_contract:
  fixes \<sigma>0 :: "('k, 'v) state"
  assumes n: "0 < n" and cs: "cs = fst (bounded_pass n T Mo Ss)"
      and lw_rc: "\<And>i. i < length cs \<Longrightarrow> lw i \<sqsubseteq> rc i"
      and rc_hw: "\<And>i. i < length cs \<Longrightarrow> rc i \<sqsubseteq> hw i"
      and hw_f: "\<And>i. i < length cs \<Longrightarrow> hw i \<sqsubseteq> f"
      and cut: "\<And>i. i < length cs \<Longrightarrow> Ss ! i = {k. state_after \<sigma>0 (pfx (rc i)) k \<noteq> None}"
      and fin: "\<And>i. i < length cs \<Longrightarrow> finite (Ss ! i)"
  shows "capture_contract L den \<sigma>0 (pass_units \<sigma>0 cs lw rc hw) (covered cs) f"
proof -
  let ?us = "pass_units \<sigma>0 cs lw rc hw"
  have len: "length ?us = length cs" by (simp add: pass_units_def)
  have dom: "u_dom (?us ! i) = chunk_keys (cs ! i)" if "i < length cs" for i
    using that by (simp add: pass_units_def)
  have lo: "u_lo (?us ! i) = lw i" if "i < length cs" for i
    using that by (simp add: pass_units_def)
  have hi: "u_hi (?us ! i) = hw i" if "i < length cs" for i
    using that by (simp add: pass_units_def)
  have refresh: "u_refresh (?us ! i) k =
                   (if k \<in> set (c_rows (cs ! i)) then state_after \<sigma>0 (pfx (rc i)) k else None)"
    if "i < length cs" for i k
    using that by (simp add: pass_units_def)
  have unit_at: "\<exists>i < length cs. u = ?us ! i" if "u \<in> set ?us" for u
    using that len by (metis in_set_conv_nth)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case 1
    have "(\<Union>u\<in>set ?us. u_dom u) = (\<Union>i\<in>{0..<length cs}. chunk_keys (cs ! i))"
      by (simp add: pass_units_def)
    also have "\<dots> = covered cs"
    proof (rule set_eqI)
      fix k
      show "k \<in> (\<Union>i\<in>{0..<length cs}. chunk_keys (cs ! i)) \<longleftrightarrow> k \<in> covered cs"
      proof
        assume "k \<in> (\<Union>i\<in>{0..<length cs}. chunk_keys (cs ! i))"
        then obtain i where i: "i < length cs" and k: "k \<in> chunk_keys (cs ! i)" by auto
        show "k \<in> covered cs"
          unfolding covered_def using nth_mem[OF i] k by blast
      next
        assume "k \<in> covered cs"
        then obtain c where c: "c \<in> set cs" and k: "k \<in> chunk_keys c"
          unfolding covered_def by blast
        obtain i where i: "i < length cs" and ci: "cs ! i = c"
          using c by (auto simp: in_set_conv_nth)
        show "k \<in> (\<Union>i\<in>{0..<length cs}. chunk_keys (cs ! i))"
          using i ci k by auto
      qed
    qed
    finally show ?case .
  next
    case (2 i j)
    have i: "i < length cs" and j: "j < length cs" using 2 len by simp_all
    have "chunk_keys (cs ! i) \<inter> chunk_keys (cs ! j) = {}"
      by (rule ranges_disjoint[OF n cs i j \<open>i \<noteq> j\<close>])
    then show ?case using dom[OF i] dom[OF j] by simp
  next
    case (3 u)
    obtain i where i: "i < length cs" and u: "u = ?us ! i" using unit_at[OF 3] by blast
    have "lw i \<sqsubseteq> hw i" using cle_trans[OF lw_rc[OF i] rc_hw[OF i]] .
    then show ?case using u lo[OF i] hi[OF i] by simp
  next
    case (4 u)
    obtain i where i: "i < length cs" and u: "u = ?us ! i" using unit_at[OF 4] by blast
    show ?case using u hi[OF i] hw_f[OF i] by simp
  next
    case (5 u k)
    obtain i where i: "i < length cs" and u: "u = ?us ! i" using unit_at[OF 5(1)] by blast
    have k: "k \<in> chunk_keys (cs ! i)" using 5(2) u dom[OF i] by simp
    have same: "u_refresh u k = state_after \<sigma>0 (pfx (rc i)) k"
    proof (cases "k \<in> set (c_rows (cs ! i))")
      case True
      then show ?thesis using u refresh[OF i] by simp
    next
      case False
      have "k \<notin> Ss ! i" by (rule range_absent[OF n cs i fin[OF i] k False])
      then have "state_after \<sigma>0 (pfx (rc i)) k = None" using cut[OF i] by simp
      then show ?thesis using False u refresh[OF i] by simp
    qed
    have "u_lo u \<sqsubseteq> rc i \<and> rc i \<sqsubseteq> u_hi u \<and> u_refresh u k = state_after \<sigma>0 (pfx (rc i)) k"
      using u lo[OF i] hi[OF i] lw_rc[OF i] rc_hw[OF i] same by simp
    then show ?case by (rule exI[where x = "rc i"])
  qed
qed

text \<open>
  A completed pass covers every key, so its contract has the whole key space
  as scope. With at least one tail read configured, a pass stopped by the
  tail-read limit yields a contract over exactly the keys at or below the
  last key its last read returned.
\<close>

corollary completed_pass_contract:
  fixes \<sigma>0 :: "('k, 'v) state"
  assumes n: "0 < n" and complete: "snd (bounded_pass n T Mo Ss) = Completed"
      and cs: "cs = fst (bounded_pass n T Mo Ss)"
      and lw_rc: "\<And>i. i < length cs \<Longrightarrow> lw i \<sqsubseteq> rc i"
      and rc_hw: "\<And>i. i < length cs \<Longrightarrow> rc i \<sqsubseteq> hw i"
      and hw_f: "\<And>i. i < length cs \<Longrightarrow> hw i \<sqsubseteq> f"
      and cut: "\<And>i. i < length cs \<Longrightarrow> Ss ! i = {k. state_after \<sigma>0 (pfx (rc i)) k \<noteq> None}"
      and fin: "\<And>i. i < length cs \<Longrightarrow> finite (Ss ! i)"
  shows "capture_contract L den \<sigma>0 (pass_units \<sigma>0 cs lw rc hw) UNIV f"
proof -
  have "covered cs = UNIV" using union_on_completion[OF n complete] cs by simp
  then show ?thesis using pass_contract[OF n cs lw_rc rc_hw hw_f cut fin] by simp
qed

corollary limited_pass_contract:
  fixes \<sigma>0 :: "('k, 'v) state"
  assumes n: "0 < n" and T: "0 < T" and stop: "snd (bounded_pass n T Mo Ss) = Tail_Limit fr"
      and cs: "cs = fst (bounded_pass n T Mo Ss)"
      and lw_rc: "\<And>i. i < length cs \<Longrightarrow> lw i \<sqsubseteq> rc i"
      and rc_hw: "\<And>i. i < length cs \<Longrightarrow> rc i \<sqsubseteq> hw i"
      and hw_f: "\<And>i. i < length cs \<Longrightarrow> hw i \<sqsubseteq> f"
      and cut: "\<And>i. i < length cs \<Longrightarrow> Ss ! i = {k. state_after \<sigma>0 (pfx (rc i)) k \<noteq> None}"
      and fin: "\<And>i. i < length cs \<Longrightarrow> finite (Ss ! i)"
  shows "capture_contract L den \<sigma>0 (pass_units \<sigma>0 cs lw rc hw)
           {k. k \<le> last (c_rows (last cs))} f"
proof -
  have "covered cs = {k. k \<le> last (c_rows (last cs))}"
    by (rule union_on_limit_last_returned[OF n T stop cs refl])
  then show ?thesis using pass_contract[OF n cs lw_rc rc_hw hw_f cut fin] by simp
qed

end  (* locale ordered_key_space *)

text \<open>
  The bridge is not vacuous: an empty log with every coordinate at its start,
  a source holding the keys of @{const W2}, and a completed pass that reads
  that source three times. Since every coordinate is the start of the log,
  the three bracket conditions are the same trivial fact.
\<close>

interpretation wit_space: ordered_key_space "[] :: (nat, unit) event list" "\<lambda>_ :: nat. 0 :: nat"
  by unfold_locales simp

definition wit_source :: "(nat, unit) state" where
  "wit_source k = (if k \<in> W2 then Some () else None)"

lemma W2_bpage_first: "bpage W2 None 10 5 = [1, 2, 3, 5, 6]"
  unfolding bpage_def W2_def
  by (rule smallest_eqI[where xs = "[1, 2, 3, 5, 6, 8, 9, 10]"]) auto

lemma wit_bridge_pass:
  "bounded_pass 5 2 (Some 10) [W2, W2, W2] =
     ([\<lparr>c_lo = None, c_hi = Some 6, c_rows = [1, 2, 3, 5, 6]\<rparr>,
       \<lparr>c_lo = Some 6, c_hi = Some 10, c_rows = [8, 9, 10]\<rparr>,
       \<lparr>c_lo = Some 10, c_hi = None, c_rows = [12]\<rparr>], Completed)"
  by (simp add: bounded_pass_def W2_bpage_first W2_bpage W2_page tail_scan_pos_Cons)

lemma wit_bridge_contract:
  "capture_contract [] (\<lambda>_ :: nat. 0 :: nat) wit_source
     (wit_space.pass_units wit_source (fst (bounded_pass 5 2 (Some 10) [W2, W2, W2]))
        (\<lambda>_. 0) (\<lambda>_. 0) (\<lambda>_. 0))
     UNIV 0"
proof (rule wit_space.completed_pass_contract)
  let ?cs = "fst (bounded_pass 5 2 (Some 10) [W2, W2, W2])"
  have len: "length ?cs = 3" using wit_bridge_pass by simp
  have src: "{k. state_after wit_source (wit_space.pfx 0) k \<noteq> None} = W2"
    by (simp add: wit_space.pfx_def wit_source_def)
  show "0 < (5::nat)" by simp
  show "snd (bounded_pass 5 2 (Some 10) [W2, W2, W2]) = Completed"
    using wit_bridge_pass by simp
  show "?cs = fst (bounded_pass 5 2 (Some 10) [W2, W2, W2])" by (rule refl)
  show "\<And>i. i < length ?cs \<Longrightarrow> wit_space.cle 0 0" by (simp add: wit_space.cle_def)
  show "\<And>i. i < length ?cs \<Longrightarrow> wit_space.cle 0 0" by (simp add: wit_space.cle_def)
  show "\<And>i. i < length ?cs \<Longrightarrow> wit_space.cle 0 0" by (simp add: wit_space.cle_def)
  show "\<And>i. i < length ?cs \<Longrightarrow>
          [W2, W2, W2] ! i = {k. state_after wit_source (wit_space.pfx 0) k \<noteq> None}"
  proof -
    fix i assume "i < length ?cs"
    then have "i < 3" using len by simp
    then have "[W2, W2, W2] ! i = W2" by (auto simp: less_Suc_eq nth_Cons')
    then show "[W2, W2, W2] ! i = {k. state_after wit_source (wit_space.pfx 0) k \<noteq> None}"
      using src by simp
  qed
  show "\<And>i. i < length ?cs \<Longrightarrow> finite ([W2, W2, W2] ! i)"
  proof -
    fix i assume "i < length ?cs"
    then have "i < 3" using len by simp
    then have "[W2, W2, W2] ! i = W2" by (auto simp: less_Suc_eq nth_Cons')
    then show "finite ([W2, W2, W2] ! i)" by (simp add: W2_def)
  qed
qed

end
