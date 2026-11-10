(*  Title:   DBLog_Run_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory DBLog_Run_Core
  imports
    Dual_Write_Layer0.Source_History
    Dual_Write_Layer0.Replay
    Dual_Write_Layer0.Scope
    "HOL-Library.Multiset"
    "HOL-Library.Sublist"
begin

section \<open>Carrier-independent Layer 0/1 core: chunk-read records and the canonical clean prefix\<close>

text \<open>
  Layer 0 / Layer 1 carrier-independent core.

  This theory collects the ``pure'' building blocks of the Layer 1 run
  substrate that reference no run/chunk carrier: the Layer 0 self-contained
  @{text chunk_read_record}, the canonical-clean-prefix construction
  (@{text canonical_clean_prefix} and its normalized companion
  @{text canonical_clean_prefix_normalized}) together with the
  normalization lemmas culminating in
  @{text apply_canonical_clean_prefix_normalized_eq}, and the
  @{text source_key_coord_slice} per-key / per-coordinate filtering helper.

  These building blocks are factored out here, below the run carrier, so
  that \<^emph>\<open>both\<close> the global theory @{text DBLog_Run} (which defines the concrete
  run carrier, its accessors, and the @{text chunks_list} lemmas) \<^emph>\<open>and\<close> the
  @{text dblog_run_substrate} locale rest on the \<^emph>\<open>same\<close>
  carrier-independent definitions.
\<close>

subsection \<open>Chunk-read record (Layer 0 self-contained)\<close>

text \<open>
  @{text "('k, 'v) chunk_read_record"} is the Layer 0 self-contained
  record carrying the per-chunk evidence the canonical-clean-prefix
  construction's chunk-read step consumes:

    \<^item> @{text crr_domain} \<open>::\<close> @{text "'k set"} --- the chunk's
        claimed key set (paper @{text domain} field; Isabelle
        selector prefixed to avoid shadowing standard library
        names);
    \<^item> @{text crr_read_coord} \<open>::\<close> @{text src_coord} --- the
        source coordinate at which the chunk read executed (paper
        @{text read_coord} field);
    \<^item> @{text crr_observation} \<open>::\<close> @{text "'k \<Rightarrow> 'v option option"}
        --- the per-key observation, where the outer option
        distinguishes "key outside @{text domain}" from "observation
        recorded for an in-domain key" and the inner option
        distinguishes "value found" (@{text "Some v"}) from "no row
        found" (@{term None}) (paper @{text observation} field).

  Paper "Auxiliary Layer 0 definitions" / "Canonical clean prefix"
  / "ChunkReadRecord".
\<close>

record ('k, 'v) chunk_read_record =
  crr_domain      :: "'k set"
  crr_read_coord  :: src_coord
  crr_observation :: "'k \<Rightarrow> 'v option option"

subsection \<open>Canonical clean prefix (Layer 0 building block)\<close>

text \<open>
  Paper "Auxiliary Layer 0 definitions" / "Canonical clean prefix".
  The Layer 0 construction the Layer 1 @{text clean_prefix_of}
  accessor is defined in terms of. Its inputs are typed --- chunk-read
  records, observed-CDC pairs, scope, frontier --- and the paper
  states finiteness premises on them.

  The construction is a real Isabelle @{command definition} mirroring
  the paper's 4-step construction:

    \<^enum> Step 1 (chunk-read Refresh emission). For each
        @{text chunk_read} in @{text chunk_reads} and each
        @{text k} in @{text "crr_domain chunk_read"} with
        @{text "crr_observation chunk_read k = Some m"}, emit
        @{text "Refresh k m (crr_read_coord chunk_read)"}. The
        @{text "crr_domain"} set enumeration uses
        @{const sorted_list_of_set} (requires @{class linorder}
        on the @{text 'k} type variable; surfaces the implicit
        deterministic-enumeration assumption the paper makes when
        it speaks of "for each k in domain").

    \<^enum> Step 2 (Cdc emission, scope+frontier filter). For each
        @{text "(c, e)"} in @{text cdc_events} with
        @{text "key_of e \<in> scope"} and @{text "c \<le> frontier"},
        emit @{text "Cdc c e"}.

    \<^enum> Step 3 (interleave by source coordinate). Stable
        @{const sort_key} by @{const cdc_coord}: at any coord
        @{text c}, the Cdcs (input order: @{text cdc_events} list) come
        before the Refreshes (input order: @{text chunk_reads} list). The
        Cdc-before-Refresh same-coord convention is realized by
        placing the Cdc-events list \<^emph>\<open>first\<close> in the concatenated
        input to @{const sort_key}; @{const sort_key} is stable,
        so same-coord same-type relative order is preserved.

    \<^enum> Step 4 (retain duplicate stutters). The construction
        does not deduplicate; same-coord same-key duplicates are
        preserved. Apply's per-key fold semantics (latest-event-wins,
        @{text apply_latest_event_wins}) handles intra-batch
        duplicates at the state level.

  The suppression-dominance step is split into a raw form (this
  @{text canonical_clean_prefix}) and a normalized form
  (@{text canonical_clean_prefix_normalized}); the two produce
  Apply-equivalent per-key states --- proved below as
  @{text apply_canonical_clean_prefix_normalized_eq} (paper
  "Suppression dominance" / "Apply state-equivalence remark"). The
  Layer 1 definitional equality picks the raw form; deployments may
  pre-normalize and remain wellformed under the same predicate.

  Five properties of @{text "clean_prefix_of(R)"} --- refresh-generated,
  cdc-generated, no-future-cdcs, no-extra-events, coord-ordered --- are
  derived as separate supporting lemmas in
  @{text DBLog_Run_Substrate_Layer2} (four are
  consumed by the per-key replay-equality proof; the no-future-CDCs
  bound is recorded as a standalone sanity fact).
\<close>

text \<open>
  Helper accessors used by the construction's interleave + the
  normalized companion's suppression filter. @{const event_key}
  and @{const is_refresh} live in theory @{text Replay} as Layer 0
  projectors on @{typ "('k, 'v) replay_event"}; this theory
  imports them transitively.
\<close>

text \<open>
  Step 1 builder: per @{text chunk_read} record, emit one Refresh per
  in-domain key with an observation. The
  @{const sorted_list_of_set} enumeration requires @{class linorder}
  on the @{text 'k} type variable and a finite
  @{text "crr_domain"} (the latter is a paper-level construction
  premise; if violated, @{const sorted_list_of_set} returns
  @{term "[]"} and the construction emits no Refreshes for that
  chunk read).
\<close>

definition chunk_read_refreshes
  :: "('k :: linorder, 'v) chunk_read_record \<Rightarrow> ('k, 'v) replay_event list"
where
  "chunk_read_refreshes r =
     List.map_filter
       (\<lambda>k. case crr_observation r k of
              Some m \<Rightarrow> Some (Refresh k m (crr_read_coord r))
            | None   \<Rightarrow> None)
       (sorted_list_of_set (crr_domain r))"

text \<open>
  Step 2 builder: filter @{text cdc_events} by scope + frontier
  and lift to @{text "Cdc c e"} replay events. Preserves input
  list order.
\<close>

definition cdc_event_replays
  :: "'k set \<Rightarrow> src_coord
       \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list
       \<Rightarrow> ('k, 'v) replay_event list"
where
  "cdc_event_replays scope frontier es =
     List.map_filter
       (\<lambda>p. if key_of (snd p) \<in> scope \<and> fst p \<le> frontier
            then Some (Cdc (fst p) (snd p))
            else None)
       es"

text \<open>
  The construction proper. Steps 1+2 generate the Refresh and Cdc
  event lists; step 3 interleaves them by source coordinate via
  stable @{const sort_key}; step 4 is implicit (no deduplication).
  The Cdc-event list is placed \<^emph>\<open>first\<close> in the @{const sort_key} input
  so that, at any same source coordinate, Cdcs precede Refreshes
  (the same-coord read convention from paper "Source state").
\<close>

definition canonical_clean_prefix
  :: "('k :: linorder, 'v) chunk_read_record list
       \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list
       \<Rightarrow> 'k set
       \<Rightarrow> src_coord
       \<Rightarrow> ('k, 'v) replay_event list"
where
  "canonical_clean_prefix chunk_reads cdc_events scope frontier =
     sort_key cdc_coord
       (cdc_event_replays scope frontier cdc_events
        @ concat (map chunk_read_refreshes chunk_reads))"

text \<open>
  Suppression dominance: a Refresh at position @{text i} is
  dominated when some later position carries a non-Refresh
  (i.e., a Cdc) event for the same key at a strictly later source
  coordinate. Cdc events are never themselves dominated.
\<close>

definition refresh_dominated
  :: "('k, 'v) replay_event list \<Rightarrow> nat \<Rightarrow> bool"
where
  "refresh_dominated \<sigma> i \<longleftrightarrow>
     i < length \<sigma> \<and> is_refresh (\<sigma> ! i) \<and>
     (\<exists> j. i < j \<and> j < length \<sigma>
            \<and> \<not> is_refresh (\<sigma> ! j)
            \<and> src_lt (cdc_coord (\<sigma> ! i)) (cdc_coord (\<sigma> ! j))
            \<and> event_key (\<sigma> ! j) = event_key (\<sigma> ! i))"

definition canonical_clean_prefix_normalized
  :: "('k :: linorder, 'v) chunk_read_record list
       \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list
       \<Rightarrow> 'k set
       \<Rightarrow> src_coord
       \<Rightarrow> ('k, 'v) replay_event list"
where
  "canonical_clean_prefix_normalized chunk_reads cdc_events scope frontier =
     (let \<sigma> = canonical_clean_prefix chunk_reads cdc_events scope frontier
      in map (\<lambda>i. \<sigma> ! i)
             (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>]))"

subsection \<open>Normalized clean prefix: Apply-equivalence to the raw form\<close>

text \<open>
  Paper "Suppression dominance" / "Apply state-equivalence remark":
  @{const canonical_clean_prefix_normalized} (dominated refreshes
  suppressed) and the raw @{const canonical_clean_prefix} produce the
  same per-key @{const Apply} state. This is the machine-checked
  "proof-facing bridge" the paper relies on when it says a deployment
  may pre-normalize and remain wellformed under the same predicate.

  The argument: @{const Apply} is latest-event-wins per key
  (@{thm [source] apply_eq_apply_filter_key}), so @{term "Apply \<sigma> k"}
  is fixed by the last @{text k}-event of @{text \<sigma>}. A position that
  @{const refresh_dominated} removes is a refresh that has a strictly
  later same-key event, so it is never the last @{text k}-event;
  conversely the last @{text k}-event is never @{const refresh_dominated}
  and therefore survives normalization, in the same final position.
  Hence every key's last event --- and so @{const Apply} --- is
  unchanged.

  Ownership note: this trio is not consumed by the main theorems ---
  the headline ladder uses only the raw @{const canonical_clean_prefix},
  and no definition or proof elsewhere in the development references
  @{const refresh_dominated}, @{const canonical_clean_prefix_normalized},
  or @{text apply_canonical_clean_prefix_normalized_eq}. It is retained
  as the paper's state-equivalence bridge.
\<close>

lemma cpn_filter_swap:
  "filter P (filter Q xs) = filter Q (filter P xs)"
  by (induction xs) auto

lemma cpn_sorted_filter:
  fixes xs :: "nat list"
  shows "sorted xs \<Longrightarrow> sorted (filter P xs)"
  by (induction xs) auto

lemma cpn_sorted_le_last:
  fixes zs :: "nat list"
  assumes "sorted zs" and "zs \<noteq> []" and "z \<in> set zs"
  shows "z \<le> last zs"
proof -
  from \<open>z \<in> set zs\<close> obtain m where m: "m < length zs" "zs ! m = z"
    by (meson in_set_conv_nth)
  have "m \<le> length zs - 1" using m(1) by simp
  moreover have "length zs - 1 < length zs" using \<open>zs \<noteq> []\<close> by simp
  ultimately have "zs ! m \<le> zs ! (length zs - 1)"
    using \<open>sorted zs\<close> sorted_nth_mono by blast
  thus ?thesis using m(2) \<open>zs \<noteq> []\<close> by (simp add: last_conv_nth)
qed

text \<open>
  If two replay-event lists agree on whether they carry any
  @{text k}-event, and (when they do) on the last @{text k}-event,
  then @{const Apply} agrees on @{text k}: @{const Apply} at a key is
  fixed by that key's last event.
\<close>

lemma cpn_apply_eq_of_filter_key_last:
  fixes xs ys :: "('k, 'v) replay_event list" and k :: 'k
  assumes empty_iff:
      "(filter (\<lambda>e. event_key e = k) xs = [])
         = (filter (\<lambda>e. event_key e = k) ys = [])"
  assumes last_eq:
      "filter (\<lambda>e. event_key e = k) xs \<noteq> []
         \<Longrightarrow> last (filter (\<lambda>e. event_key e = k) xs)
              = last (filter (\<lambda>e. event_key e = k) ys)"
  shows "Apply xs k = Apply ys k"
proof -
  have ax: "Apply xs k = Apply (filter (\<lambda>e. event_key e = k) xs) k"
    by (rule apply_eq_apply_filter_key)
  have ay: "Apply ys k = Apply (filter (\<lambda>e. event_key e = k) ys) k"
    by (rule apply_eq_apply_filter_key)
  show ?thesis
  proof (cases "filter (\<lambda>e. event_key e = k) xs = []")
    case True
    with empty_iff have "filter (\<lambda>e. event_key e = k) ys = []" by simp
    with True ax ay show ?thesis by (simp add: Apply_def)
  next
    case False
    with empty_iff have yne: "filter (\<lambda>e. event_key e = k) ys \<noteq> []" by simp
    have xu: "\<forall>e\<in>set (filter (\<lambda>e. event_key e = k) xs). event_key e = k"
      by auto
    have yu: "\<forall>e\<in>set (filter (\<lambda>e. event_key e = k) ys). event_key e = k"
      by auto
    have e1: "Apply (filter (\<lambda>e. event_key e = k) xs) k
              = (case last (filter (\<lambda>e. event_key e = k) xs) of
                   Cdc _ (Insert _ v) \<Rightarrow> Some v
                 | Cdc _ (Update _ v) \<Rightarrow> Some v
                 | Cdc _ (Delete _)   \<Rightarrow> None
                 | Refresh _ m_obs _  \<Rightarrow> m_obs)"
      by (rule apply_filter_uniform_last[OF xu False])
    have e2: "Apply (filter (\<lambda>e. event_key e = k) ys) k
              = (case last (filter (\<lambda>e. event_key e = k) ys) of
                   Cdc _ (Insert _ v) \<Rightarrow> Some v
                 | Cdc _ (Update _ v) \<Rightarrow> Some v
                 | Cdc _ (Delete _)   \<Rightarrow> None
                 | Refresh _ m_obs _  \<Rightarrow> m_obs)"
      by (rule apply_filter_uniform_last[OF yu yne])
    show ?thesis using ax ay e1 e2 last_eq[OF False] by simp
  qed
qed

theorem apply_canonical_clean_prefix_normalized_eq:
  fixes chunk_reads :: "('k :: linorder, 'v) chunk_read_record list"
    and cdc_events  :: "(src_coord \<times> ('k, 'v) source_event) list"
    and scope       :: "'k set"
    and frontier    :: src_coord
  shows "Apply (canonical_clean_prefix_normalized chunk_reads cdc_events scope frontier)
         = Apply (canonical_clean_prefix chunk_reads cdc_events scope frontier)"
proof (intro ext)
  fix k :: 'k
  define \<sigma> where "\<sigma> = canonical_clean_prefix chunk_reads cdc_events scope frontier"
  have norm_unfold:
    "canonical_clean_prefix_normalized chunk_reads cdc_events scope frontier
       = map (\<lambda>i. \<sigma> ! i) (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])"
    by (simp add: canonical_clean_prefix_normalized_def Let_def \<sigma>_def)
  define J  where "J  = filter (\<lambda>i. event_key (\<sigma> ! i) = k) [0..<length \<sigma>]"
  define Jn where "Jn = filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) J"
  have sigma_k: "filter (\<lambda>e. event_key e = k) \<sigma> = map (\<lambda>i. \<sigma> ! i) J"
  proof -
    have "filter (\<lambda>e. event_key e = k) \<sigma>
            = filter (\<lambda>e. event_key e = k) (map (\<lambda>i. \<sigma> ! i) [0..<length \<sigma>])"
      by (simp only: map_nth)
    also have "\<dots> = map (\<lambda>i. \<sigma> ! i)
                      (filter (\<lambda>i. event_key (\<sigma> ! i) = k) [0..<length \<sigma>])"
      by (simp add: filter_map o_def)
    finally show ?thesis by (simp add: J_def)
  qed
  have norm_k: "filter (\<lambda>e. event_key e = k)
                  (map (\<lambda>i. \<sigma> ! i)
                       (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>]))
                = map (\<lambda>i. \<sigma> ! i) Jn"
  proof -
    have "filter (\<lambda>e. event_key e = k)
            (map (\<lambda>i. \<sigma> ! i)
                 (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>]))
          = map (\<lambda>i. \<sigma> ! i)
              (filter (\<lambda>i. event_key (\<sigma> ! i) = k)
                 (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>]))"
      by (simp add: filter_map o_def)
    also have "\<dots> = map (\<lambda>i. \<sigma> ! i) Jn"
      by (subst cpn_filter_swap) (simp add: J_def Jn_def)
    finally show ?thesis .
  qed
  have sortedJ: "sorted J" by (simp add: J_def cpn_sorted_filter)
  have keyJ: "\<And>i. i \<in> set J \<Longrightarrow> i < length \<sigma> \<and> event_key (\<sigma> ! i) = k"
    by (simp add: J_def)
  have crux: "J \<noteq> [] \<Longrightarrow> \<not> refresh_dominated \<sigma> (last J)"
  proof (rule notI)
    assume Jne: "J \<noteq> []" and dom: "refresh_dominated \<sigma> (last J)"
    have lin: "last J \<in> set J" using Jne by simp
    from dom obtain j where j: "last J < j" "j < length \<sigma>"
        "event_key (\<sigma> ! j) = event_key (\<sigma> ! (last J))"
      unfolding refresh_dominated_def by blast
    from keyJ[OF lin] j(3) have "event_key (\<sigma> ! j) = k" by simp
    with j(2) have "j \<in> set J" by (simp add: J_def)
    with sortedJ Jne have "j \<le> last J" by (simp add: cpn_sorted_le_last)
    with j(1) show False by simp
  qed
  have emptyiff:
    "(filter (\<lambda>e. event_key e = k)
        (map (\<lambda>i. \<sigma> ! i)
             (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])) = [])
     = (filter (\<lambda>e. event_key e = k) \<sigma> = [])"
  proof -
    have "(Jn = []) = (J = [])"
    proof
      assume "J = []" thus "Jn = []" by (simp add: Jn_def)
    next
      assume Jnnil: "Jn = []"
      show "J = []"
      proof (rule ccontr)
        assume Jne: "J \<noteq> []"
        have "last J \<in> set Jn"
          using Jne crux[OF Jne] by (simp add: Jn_def)
        with Jnnil show False by simp
      qed
    qed
    thus ?thesis by (simp add: sigma_k norm_k)
  qed
  have lasteq:
    "filter (\<lambda>e. event_key e = k)
       (map (\<lambda>i. \<sigma> ! i)
            (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])) \<noteq> []
     \<Longrightarrow> last (filter (\<lambda>e. event_key e = k)
            (map (\<lambda>i. \<sigma> ! i)
                 (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])))
          = last (filter (\<lambda>e. event_key e = k) \<sigma>)"
  proof -
    assume "filter (\<lambda>e. event_key e = k)
              (map (\<lambda>i. \<sigma> ! i)
                   (filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) [0..<length \<sigma>])) \<noteq> []"
    hence Jnne: "Jn \<noteq> []" by (simp add: norm_k)
    hence Jne: "J \<noteq> []" by (auto simp: Jn_def)
    have lastJn: "last Jn = last J"
    proof -
      have "Jn = filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) (butlast J @ [last J])"
        by (simp add: Jn_def append_butlast_last_id[OF Jne])
      also have "\<dots> = filter (\<lambda>i. \<not> refresh_dominated \<sigma> i) (butlast J) @ [last J]"
        using crux[OF Jne] by simp
      finally show ?thesis by simp
    qed
    have "last (map (\<lambda>i. \<sigma> ! i) Jn) = \<sigma> ! (last Jn)"
      using Jnne by (simp add: last_map)
    also have "\<dots> = \<sigma> ! (last J)" by (simp add: lastJn)
    also have "\<dots> = last (map (\<lambda>i. \<sigma> ! i) J)"
      using Jne by (simp add: last_map)
    finally show ?thesis by (simp add: sigma_k norm_k)
  qed
  show "Apply (canonical_clean_prefix_normalized chunk_reads cdc_events scope frontier) k
        = Apply (canonical_clean_prefix chunk_reads cdc_events scope frontier) k"
    unfolding norm_unfold \<sigma>_def[symmetric]
    by (rule cpn_apply_eq_of_filter_key_last[OF emptyiff lasteq])
qed

subsection \<open>Source key/coordinate slice helper\<close>

text \<open>
  @{text source_key_coord_slice} filters a source/observed event list down
  to the records at one source coordinate carrying one key. It is consumed
  by the WF2 post-read multiplicity clause and the Layer 2 per-key
  replay-equality lemmas; it references no run/chunk accessor.
\<close>

definition source_key_coord_slice
  :: "'k \<Rightarrow> src_coord
      \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list
      \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "source_key_coord_slice k c xs =
     filter (\<lambda>p. hist_coord p = c \<and> key_of (hist_event p) = k) xs"


section \<open>Carrier-independent Layer 2 supporting helpers\<close>

text \<open>
  The pure, carrier-independent
  list / source-history / replay helper lemmas below reference no run/chunk
  accessor. They are collected here so that both the Layer 2 substrate locale
  @{text dblog_run_substrate} (whose Layer 2 lemmas live in
  @{text DBLog_Run_Substrate_Layer2}) and the certificate core
  @{text Virtual_Cut_Core} can reuse them directly.
\<close>

text \<open>
  Auxiliary list lemmas used by
  @{text clean_prefix_of_cdc_order_respects_source_position} and
  @{text clean_prefix_same_coord_refresh_before_cdc_false}:
  \<^const>\<open>filter\<close> preserves the
  strict order of @{text P}-satisfying positions in the underlying list.
  These are generic facts about @{const filter}, @{const take}, and
  @{const nth} on Isabelle lists; they package the standard
  ``position-of-the-$n$-th-survivor'' argument in a form that lemma can
  consume without explicit @{const nths} bookkeeping.

  Three pieces:

    \<^item> @{text filter_take_nth}: for any position @{text i} satisfying
      @{text P}, the @{text "length (filter P (take i xs))"}-th element
      of @{text "filter P xs"} is exactly @{text "xs ! i"}; furthermore
      that index lies strictly below @{text "length (filter P xs)"}.
      This gives the \<^emph>\<open>forward\<close> direction of the position correspondence
      (positions in @{text xs} @{text \<open>\<rightarrow>\<close>} positions in @{text "filter P xs"}).

    \<^item> @{text length_filter_take_mono} / @{text length_filter_take_strict_mono}:
      @{text "length \<circ> filter P \<circ> take \<cdot>"} is monotone
      (resp.\ strictly monotone at any @{text P}-satisfying position)
      in the take-prefix length. The strict version drives the
      @{text "n_i < n_j"} step in
      @{text clean_prefix_of_cdc_order_respects_source_position}
      (in theory @{text DBLog_Run_Substrate_Layer2}).

    \<^item> @{text filter_index_strict_mono}: for any @{text "n < length (filter P xs)"},
      there exists a position @{text "p < length xs"} with
      @{text "xs ! p = filter P xs ! n"} and
      @{text "length (filter P (take p xs)) = n"}. This gives the
      \<^emph>\<open>backward\<close> direction (positions in @{text "filter P xs"} @{text \<open>\<rightarrow>\<close>} positions
      in @{text xs}). The @{text "length (filter P (take p xs)) = n"}
      witness is what lets us recover the original ordering from a
      pair of @{text n}'s via the @{text length_filter_take_mono} contrapositive.
\<close>

lemma filter_take_nth:
  fixes xs :: "'a list" and P :: "'a \<Rightarrow> bool" and i :: nat
  assumes i_lt:  "i < length xs"
      and Pi:    "P (xs ! i)"
  shows "filter P xs ! length (filter P (take i xs)) = xs ! i
       \<and> length (filter P (take i xs)) < length (filter P xs)"
proof -
  have xs_split: "xs = take i xs @ xs ! i # drop (Suc i) xs"
    using i_lt by (simp add: id_take_nth_drop)
  have filter_split:
    "filter P xs = filter P (take i xs) @ xs ! i # filter P (drop (Suc i) xs)"
  proof -
    have "filter P xs = filter P (take i xs @ xs ! i # drop (Suc i) xs)"
      using xs_split by simp
    also have "\<dots> = filter P (take i xs) @ filter P (xs ! i # drop (Suc i) xs)"
      by simp
    also have "filter P (xs ! i # drop (Suc i) xs) = xs ! i # filter P (drop (Suc i) xs)"
      using Pi by simp
    finally show ?thesis by simp
  qed
  have nth_eq:
    "filter P xs ! length (filter P (take i xs)) = xs ! i"
    using filter_split by (simp add: nth_append)
  have len_lt:
    "length (filter P (take i xs)) < length (filter P xs)"
    using filter_split by simp
  show ?thesis using nth_eq len_lt by simp
qed

lemma length_filter_take_mono:
  fixes xs :: "'a list" and P :: "'a \<Rightarrow> bool" and i j :: nat
  assumes "i \<le> j"
  shows "length (filter P (take i xs)) \<le> length (filter P (take j xs))"
proof -
  have take_i_eq: "take i (take j xs) = take i xs"
    using assms by (simp add: min_def take_take)
  have "take i xs @ drop i (take j xs) = take j xs"
    using take_i_eq append_take_drop_id by metis
  hence "filter P (take j xs)
       = filter P (take i xs) @ filter P (drop i (take j xs))"
    by (metis filter_append)
  thus ?thesis by simp
qed

lemma length_filter_take_strict_mono:
  fixes xs :: "'a list" and P :: "'a \<Rightarrow> bool" and i j :: nat
  assumes ij:       "i < j"
      and j_bound:  "j \<le> length xs"
      and Pi:       "P (xs ! i)"
  shows "length (filter P (take i xs)) < length (filter P (take j xs))"
proof -
  have i_bound: "i < length xs" using ij j_bound by linarith
  have suc_i_le_j: "Suc i \<le> j" using ij by simp
  have take_suc_i_eq: "take (Suc i) (take j xs) = take (Suc i) xs"
    using suc_i_le_j by (simp add: min_def take_take)
  have suc_split: "take (Suc i) xs @ drop (Suc i) (take j xs) = take j xs"
    using take_suc_i_eq append_take_drop_id by metis
  have take_suc_i: "take (Suc i) xs = take i xs @ [xs ! i]"
    using i_bound by (simp add: take_Suc_conv_app_nth)
  have decompose:
    "take j xs = take i xs @ [xs ! i] @ drop (Suc i) (take j xs)"
    using suc_split take_suc_i by simp
  have "filter P (take j xs)
      = filter P (take i xs @ [xs ! i] @ drop (Suc i) (take j xs))"
    using decompose by simp
  also have "\<dots> = filter P (take i xs) @ filter P [xs ! i] @ filter P (drop (Suc i) (take j xs))"
    by simp
  also have "filter P [xs ! i] = [xs ! i]" using Pi by simp
  finally have "filter P (take j xs)
              = filter P (take i xs) @ [xs ! i] @ filter P (drop (Suc i) (take j xs))"
    by simp
  thus ?thesis by simp
qed

lemma filter_index_strict_mono:
  fixes xs :: "'a list" and P :: "'a \<Rightarrow> bool" and n :: nat
  assumes "n < length (filter P xs)"
  shows "\<exists> p. p < length xs
           \<and> P (xs ! p)
           \<and> xs ! p = filter P xs ! n
           \<and> length (filter P (take p xs)) = n"
  using assms
proof (induction xs arbitrary: n)
  case Nil
  thus ?case by simp
next
  case (Cons a xs')
  show ?case
  proof (cases "P a")
    case Pa: True
    show ?thesis
    proof (cases n)
      case 0
      have at0: "filter P (a # xs') ! n = a" using Pa 0 by simp
      have "(0 :: nat) < length (a # xs')" by simp
      moreover have "P ((a # xs') ! 0)" using Pa by simp
      moreover have "(a # xs') ! 0 = filter P (a # xs') ! n" using at0 by simp
      moreover have "length (filter P (take 0 (a # xs'))) = n" using 0 by simp
      ultimately show ?thesis by (intro exI[where x = 0]) auto
    next
      case (Suc n')
      have filter_nth_eq:
        "filter P (a # xs') ! n = filter P xs' ! n'"
        using Pa Suc by simp
      have n'_lt: "n' < length (filter P xs')"
        using Cons.prems Pa Suc by simp
      obtain p' where p'_props:
          "p' < length xs'" "P (xs' ! p')"
          "xs' ! p' = filter P xs' ! n'"
          "length (filter P (take p' xs')) = n'"
        using Cons.IH[OF n'_lt] by blast
      have "Suc p' < length (a # xs')" using p'_props by simp
      moreover have "P ((a # xs') ! Suc p')" using p'_props by simp
      moreover have "(a # xs') ! Suc p' = filter P (a # xs') ! n"
        using filter_nth_eq p'_props by simp
      moreover have "length (filter P (take (Suc p') (a # xs'))) = n"
        using Pa Suc p'_props by simp
      ultimately show ?thesis by (intro exI[where x = "Suc p'"]) auto
    qed
  next
    case nPa: False
    have filter_a_eq: "filter P (a # xs') = filter P xs'" using nPa by simp
    have "n < length (filter P xs')"
      using Cons.prems filter_a_eq by simp
    obtain p' where p'_props:
        "p' < length xs'" "P (xs' ! p')"
        "xs' ! p' = filter P xs' ! n"
        "length (filter P (take p' xs')) = n"
      using Cons.IH \<open>n < length (filter P xs')\<close> by blast
    have "Suc p' < length (a # xs')" using p'_props by simp
    moreover have "P ((a # xs') ! Suc p')" using p'_props by simp
    moreover have "(a # xs') ! Suc p' = filter P (a # xs') ! n"
      using filter_a_eq p'_props by simp
    moreover have "length (filter P (take (Suc p') (a # xs'))) = n"
      using nPa p'_props by simp
    ultimately show ?thesis by (intro exI[where x = "Suc p'"]) auto
  qed
qed

lemma subseq_mset_eq_imp_eq:
  fixes xs ys :: "'a list"
  assumes sub: "subseq xs ys"
      and ms:  "mset xs = mset ys"
  shows "xs = ys"
  by (rule subseq_same_length[OF sub mset_eq_length[OF ms]])

lemma subseq_from_strict_mono_nth:
  fixes xs ys :: "'a list"
    and f :: "nat \<Rightarrow> nat"
  assumes mono: "strict_mono f"
      and hit: "\<And>i. i < length xs \<Longrightarrow> f i < length ys \<and> xs ! i = ys ! f i"
  shows "subseq xs ys"
  using assms
proof (induction xs arbitrary: ys f)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(2)[of 0] have f0_lt: "f 0 < length ys"
    and x_eq: "x = ys ! f 0"
    by simp_all
  let ?tail = "drop (Suc (f 0)) ys"
  let ?g = "\<lambda>i. f (Suc i) - Suc (f 0)"

  have g_mono: "strict_mono ?g"
  proof (rule strict_monoI)
    fix i j :: nat
    assume ij: "i < j"
    have f0_lt_i: "f 0 < f (Suc i)"
      using strict_monoD[OF Cons.prems(1), of 0 "Suc i"] by simp
    have "f (Suc i) < f (Suc j)"
      using strict_monoD[OF Cons.prems(1), of "Suc i" "Suc j"] ij by simp
    with f0_lt_i show "?g i < ?g j" by simp
  qed

  have g_hit:
    "\<And>i. i < length xs \<Longrightarrow>
       ?g i < length ?tail \<and> xs ! i = ?tail ! ?g i"
  proof -
    fix i
    assume i_lt: "i < length xs"
    from Cons.prems(2)[of "Suc i"] i_lt
    have fSi_lt: "f (Suc i) < length ys"
      and xs_i: "xs ! i = ys ! f (Suc i)"
      by simp_all
    have f0_lt_fSi: "f 0 < f (Suc i)"
      using strict_monoD[OF Cons.prems(1), of 0 "Suc i"] by simp
    hence fSi_eq: "Suc (f 0) + ?g i = f (Suc i)"
      by simp
    have g_lt: "?g i < length ?tail"
      using fSi_lt fSi_eq by simp
    have tail_nth: "?tail ! ?g i = ys ! f (Suc i)"
      using g_lt fSi_eq by simp
    show "?g i < length ?tail \<and> xs ! i = ?tail ! ?g i"
      using g_lt xs_i tail_nth by simp
  qed

  have tail_sub: "subseq xs ?tail"
    by (rule Cons.IH[OF g_mono g_hit])
  have cons_sub: "subseq (x # xs) (ys ! f 0 # ?tail)"
    using tail_sub x_eq by simp
  have ys_split: "ys = take (f 0) ys @ ys ! f 0 # ?tail"
    using f0_lt by (simp add: id_take_nth_drop)
  have prefixed: "subseq (x # xs) (take (f 0) ys @ (ys ! f 0 # ?tail))"
    by (rule subseq_drop_many[OF cons_sub])
  show ?case
    by (subst ys_split, rule prefixed)
qed

lemma last_filter_index:
  fixes xs :: "'a list"
  assumes nonempty: "filter P xs \<noteq> []"
  shows "\<exists>i. i < length xs
          \<and> P (xs ! i)
          \<and> xs ! i = last (filter P xs)
          \<and> (\<forall>j. i < j \<and> j < length xs \<longrightarrow> \<not> P (xs ! j))"
  using nonempty
proof (induction xs rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc x xs)
  show ?case
  proof (cases "P x")
    case True
    have idx_lt: "length xs < length (xs @ [x])" by simp
    have P_idx: "P ((xs @ [x]) ! length xs)" using True by simp
    have last_idx: "(xs @ [x]) ! length xs = last (filter P (xs @ [x]))"
      using True by simp
    have no_later:
      "\<forall>j. length xs < j \<and> j < length (xs @ [x])
            \<longrightarrow> \<not> P ((xs @ [x]) ! j)"
      by auto
    show ?thesis
      using idx_lt P_idx last_idx no_later
      by (intro exI[where x = "length xs"]) simp
  next
    case False
    note nPx = False
    have filter_xs_nonempty: "filter P xs \<noteq> []"
      using snoc.prems nPx by simp
    obtain i where i_lt_xs: "i < length xs"
      and Pi_xs: "P (xs ! i)"
      and last_xs: "xs ! i = last (filter P xs)"
      and no_later_xs: "\<forall>j. i < j \<and> j < length xs \<longrightarrow> \<not> P (xs ! j)"
      using snoc.IH[OF filter_xs_nonempty] by blast
    have i_lt: "i < length (xs @ [x])" using i_lt_xs by simp
    have Pi: "P ((xs @ [x]) ! i)" using Pi_xs i_lt_xs by (simp add: nth_append)
    have filter_append_eq: "filter P (xs @ [x]) = filter P xs"
      using nPx by simp
    have last_eq: "(xs @ [x]) ! i = last (filter P (xs @ [x]))"
    proof -
      have "(xs @ [x]) ! i = xs ! i"
        using i_lt_xs by (simp add: nth_append)
      also have "\<dots> = last (filter P xs)"
        using last_xs .
      also have "\<dots> = last (filter P (xs @ [x]))"
        using filter_append_eq by simp
      finally show ?thesis .
    qed
    have no_later:
      "\<forall>j. i < j \<and> j < length (xs @ [x]) \<longrightarrow> \<not> P ((xs @ [x]) ! j)"
    proof (intro allI impI)
      fix j
      assume j_assm: "i < j \<and> j < length (xs @ [x])"
      show "\<not> P ((xs @ [x]) ! j)"
      proof (cases "j < length xs")
        case True
        thus ?thesis using no_later_xs j_assm by (simp add: nth_append)
      next
        case False
        hence "j = length xs" using j_assm by simp
        thus ?thesis using nPx by simp
      qed
    qed
    show ?thesis
      using i_lt Pi last_eq no_later by blast
  qed
qed

lemma last_filter_upt_eq:
  fixes P :: "nat \<Rightarrow> bool"
  assumes i_lt: "i < n"
      and Pi: "P i"
      and no_after: "\<forall>j. i < j \<and> j < n \<longrightarrow> \<not> P j"
  shows "filter P [0..<n] \<noteq> [] \<and> last (filter P [0..<n]) = i"
  using i_lt Pi no_after
proof (induction n arbitrary: i)
  case 0
  thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "i = n")
    case True
    have upt: "[0..<Suc n] = [0..<n] @ [n]"
      by (simp add: upt_Suc_append)
    have "filter P [0..<Suc n] = filter P [0..<n] @ [n]"
      using True Suc.prems(2) upt by simp
    thus ?thesis using True by simp
  next
    case False
    hence i_lt_n: "i < n" using Suc.prems(1) by simp
    have Pn_false: "\<not> P n"
      using Suc.prems False by simp
    have no_after_n: "\<forall>j. i < j \<and> j < n \<longrightarrow> \<not> P j"
      using Suc.prems(3) by auto
    have ih: "filter P [0..<n] \<noteq> [] \<and> last (filter P [0..<n]) = i"
      by (rule Suc.IH[OF i_lt_n Suc.prems(2) no_after_n])
    have upt: "[0..<Suc n] = [0..<n] @ [n]"
      by (simp add: upt_Suc_append)
    have "filter P [0..<Suc n] = filter P [0..<n]"
      using Pn_false upt by simp
    thus ?thesis using ih by simp
  qed
qed

lemma append_no_B_before_A:
  fixes xs ys zs :: "'a list"
    and A B :: "'a \<Rightarrow> bool"
    and i j :: nat
  assumes zs_eq: "zs = xs @ ys"
      and xs_A: "\<forall>x \<in> set xs. A x"
      and ys_B: "\<forall>y \<in> set ys. B y"
      and disj: "\<And>z. A z \<Longrightarrow> B z \<Longrightarrow> False"
      and ij: "i < j"
      and j_lt: "j < length zs"
      and zi_B: "B (zs ! i)"
      and zj_A: "A (zs ! j)"
  shows False
proof (cases "i < length xs")
  case True
  hence "A (zs ! i)"
    using zs_eq xs_A by (simp add: nth_append)
  thus False using zi_B disj by blast
next
  case False
  hence j_ge: "length xs \<le> j" using ij by simp
  have "j - length xs < length ys"
    using zs_eq j_lt j_ge by simp
  hence "B (zs ! j)"
    using zs_eq ys_B j_ge by (simp add: nth_append)
  thus False using zj_A disj by blast
qed

lemma wellformed_src_history_coord_mono:
  fixes H :: "('k, 'v) src_history"
  assumes wf_h: "wellformed_src_history H"
      and ij: "i \<le> j"
      and j_lt: "j < length H"
  shows "src_le (hist_coord (H ! i)) (hist_coord (H ! j))"
proof -
  from wf_h have adj:
    "\<forall>i. Suc i < length H
          \<longrightarrow> src_le (hist_coord (H ! i)) (hist_coord (H ! Suc i))"
    unfolding wellformed_src_history_def by blast
  have step:
    "\<And>n. i + n < length H
      \<Longrightarrow> src_le (hist_coord (H ! i)) (hist_coord (H ! (i + n)))"
  proof -
    fix n
    assume bound: "i + n < length H"
    show "src_le (hist_coord (H ! i)) (hist_coord (H ! (i + n)))"
      using bound
    proof (induction n)
      case 0
      show ?case by (simp add: src_le_refl)
    next
      case (Suc n)
      have ih_bound: "i + n < length H" using Suc.prems by simp
      have ih:
        "src_le (hist_coord (H ! i)) (hist_coord (H ! (i + n)))"
        using Suc.IH[OF ih_bound] .
      have adj_step:
        "src_le (hist_coord (H ! (i + n))) (hist_coord (H ! Suc (i + n)))"
        using adj Suc.prems by simp
      have "src_le (hist_coord (H ! i)) (hist_coord (H ! Suc (i + n)))"
        using src_le_trans[OF ih adj_step] .
      thus ?case by (simp add: add_Suc_right)
    qed
  qed
  have j_eq: "j = i + (j - i)" using ij by simp
  show ?thesis
    using step[of "j - i"] j_lt j_eq by simp
qed


text \<open>
  Auxiliary lemma used by @{text clean_prefix_of_per_key_replay_equals_source}:
  the @{const Apply} value at a key
  @{text k} reduces to the per-event constructor effect of the
  @{text k}-event at the @{text "latest"} position, when one such
  position is named.

  Generic fact about @{const Apply} on lists of @{type replay_event}:
  given a position @{text i_max} in a sequence @{text \<sigma>} such that
  @{text "event_key (\<sigma> ! i_max) = k"} and no later position in
  @{text \<sigma>} carries @{text "event_key = k"}, the per-key value
  @{text "Apply \<sigma> k"} equals the per-constructor effect of
  @{text "\<sigma> ! i_max"}: @{term "Some v"} for the @{text Cdc}
  @{text Insert} / @{text Update} shapes, @{term None} for the
  @{text Cdc} @{text Delete} shape, and the observed value
  @{term m_obs} for the @{text Refresh} shape.

  Composes @{thm apply_latest_event_wins} with a list
  decomposition argument: split @{text \<sigma>} at @{text i_max}, observe
  that the suffix @{term "drop (Suc i_max) \<sigma>"} contributes no
  @{text k}-events to the per-key filter (by the @{text i_max}
  latest-position assumption), and conclude that the last element of
  the per-key filter is @{text "\<sigma> ! i_max"}; then apply
  @{thm apply_latest_event_wins} to read off the per-constructor
  case.

  Used twice in the Layer 2 per-key replay-equality proof in
  @{text DBLog_Run_Substrate_Layer2}: once in the
  @{text Cdc} case (where @{text "\<sigma> ! i_max = Cdc c e"}, via the
  @{text Cdc}-case helper lemma) and once
  in the @{text Refresh} case (where
  @{text "\<sigma> ! i_max = Refresh k m c_read"}).
  Lives here, with the other carrier-independent helpers,
  rather than in @{theory Dual_Write_Layer0.Replay}
  because that proof is its only consumer; relocation to that shared theory
  is reasonable if a second consumer ever materializes.
\<close>

lemma apply_at_latest_k_event:
  fixes \<sigma> :: "('k, 'v) replay_event list"
    and k :: 'k
    and i :: nat
  assumes i_lt:    "i < length \<sigma>"
      and i_key:   "event_key (\<sigma> ! i) = k"
      and i_last:  "\<forall> j. i < j \<and> j < length \<sigma> \<longrightarrow> event_key (\<sigma> ! j) \<noteq> k"
  shows "Apply \<sigma> k = (case \<sigma> ! i of
                        Cdc _ (Insert _ v) \<Rightarrow> Some v
                      | Cdc _ (Update _ v) \<Rightarrow> Some v
                      | Cdc _ (Delete _)   \<Rightarrow> None
                      | Refresh _ m_obs _  \<Rightarrow> m_obs)"
proof -
  let ?P = "\<lambda>e :: ('k, 'v) replay_event. event_key e = k"
  let ?\<sigma>_k = "filter ?P \<sigma>"

  \<comment> \<open>Decompose @{text \<sigma>} at position @{text i}.\<close>
  have decomp: "\<sigma> = take i \<sigma> @ [\<sigma> ! i] @ drop (Suc i) \<sigma>"
    using i_lt
    by (metis Cons_nth_drop_Suc append_Cons append_Nil append_take_drop_id)

  \<comment> \<open>The drop part has no k-events.\<close>
  have drop_no_k: "filter ?P (drop (Suc i) \<sigma>) = []"
  proof -
    have "\<forall> e \<in> set (drop (Suc i) \<sigma>). event_key e \<noteq> k"
    proof
      fix e assume e_in: "e \<in> set (drop (Suc i) \<sigma>)"
      then obtain j where j_lt_drop: "j < length (drop (Suc i) \<sigma>)"
                          and e_at: "drop (Suc i) \<sigma> ! j = e"
        by (auto simp: in_set_conv_nth)
      let ?j' = "Suc (i + j)"
      have j'_lt: "?j' < length \<sigma>"
        using j_lt_drop by simp
      have e_eq: "e = \<sigma> ! ?j'"
        using e_at j_lt_drop
        by (simp add: add.commute)
      have i_lt_j': "i < ?j'" by simp
      from i_last i_lt_j' j'_lt
      have "event_key (\<sigma> ! ?j') \<noteq> k" by blast
      thus "event_key e \<noteq> k" using e_eq by simp
    qed
    thus ?thesis by (simp add: filter_empty_conv)
  qed

  \<comment> \<open>Filter splits + drop has no k-events: filter equals
      filter on the prefix, with @{text \<open>[\<sigma> ! i]\<close>} appended.\<close>
  have filter_eq:
    "?\<sigma>_k = filter ?P (take i \<sigma>) @ [\<sigma> ! i]"
  proof -
    have "?\<sigma>_k = filter ?P (take i \<sigma> @ [\<sigma> ! i] @ drop (Suc i) \<sigma>)"
      using decomp by simp
    also have "\<dots> = filter ?P (take i \<sigma>) @ filter ?P [\<sigma> ! i]
                    @ filter ?P (drop (Suc i) \<sigma>)"
      by simp
    also have "filter ?P [\<sigma> ! i] = [\<sigma> ! i]"
      using i_key by simp
    also have "filter ?P (drop (Suc i) \<sigma>) = []"
      by (rule drop_no_k)
    finally show ?thesis by simp
  qed

  have nonempty: "?\<sigma>_k \<noteq> []"
    using filter_eq by simp
  have last_eq: "last ?\<sigma>_k = \<sigma> ! i"
    using filter_eq by simp

  \<comment> \<open>Apply via @{text apply_latest_event_wins}, then read off
      via @{text last_eq}.\<close>
  have apply_eq:
    "Apply \<sigma> k = (case ?\<sigma>_k of
                    []     \<Rightarrow> None
                  | _ # _  \<Rightarrow> (case last ?\<sigma>_k of
                                 Cdc _ (Insert _ v) \<Rightarrow> Some v
                               | Cdc _ (Update _ v) \<Rightarrow> Some v
                               | Cdc _ (Delete _)   \<Rightarrow> None
                               | Refresh _ m_obs _  \<Rightarrow> m_obs))"
    by (rule apply_latest_event_wins)
  also have "\<dots> = (case last ?\<sigma>_k of
                     Cdc _ (Insert _ v) \<Rightarrow> Some v
                   | Cdc _ (Update _ v) \<Rightarrow> Some v
                   | Cdc _ (Delete _)   \<Rightarrow> None
                   | Refresh _ m_obs _  \<Rightarrow> m_obs)"
    using nonempty by (cases ?\<sigma>_k) auto
  also have "\<dots> = (case \<sigma> ! i of
                     Cdc _ (Insert _ v) \<Rightarrow> Some v
                   | Cdc _ (Update _ v) \<Rightarrow> Some v
                   | Cdc _ (Delete _)   \<Rightarrow> None
                   | Refresh _ m_obs _  \<Rightarrow> m_obs)"
    using last_eq by simp
  finally show ?thesis .
qed

text \<open>
  Auxiliary lemma used by @{text clean_prefix_of_per_key_replay_equals_source}:
  if no @{text k}-event in
  @{text "src_history_of R = H"} lies strictly past a coordinate
  @{text c'} and at-or-before the frontier, then
  @{term "Src b0 H f k"} restricted to @{text k} agrees with
  @{term "Src b0 H c' k"}. Generic property of @{const Src} +
  @{const latest_src_event} on histories: when @{term latest_src_event}
  cand-set agrees on the two thresholds (no @{text k}-events in the
  half-open interval @{text "(c', f]"}), the per-key state is identical.

  Used in the @{text Refresh} case of
  @{text clean_prefix_of_per_key_replay_equals_source}: lifts
  @{text refresh_coordinate_match} (Src at chunk-read
  coordinate) to Src at frontier when no later source event for
  @{text k} appears in the half-open interval @{text "(c_read, frontier_of(R)]"}.
\<close>

lemma src_eq_when_no_later_src_event_for_k:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and c' f :: frontier
    and k :: 'k
  assumes c'_le_f: "src_le c' f"
      and no_later:
        "\<forall> i < length H. src_lt c' (hist_coord (H ! i))
                          \<and> src_le (hist_coord (H ! i)) f
                          \<longrightarrow> key_of (hist_event (H ! i)) \<noteq> k"
  shows "Src b0 H f k = Src b0 H c' k"
proof -
  let ?cand_f =
    "filter (\<lambda>i. src_le (hist_coord (H ! i)) f
              \<and> key_of (hist_event (H ! i)) = k)
            [0..<length H]"
  let ?cand_c' =
    "filter (\<lambda>i. src_le (hist_coord (H ! i)) c'
              \<and> key_of (hist_event (H ! i)) = k)
            [0..<length H]"
  let ?Pf  = "\<lambda>i. src_le (hist_coord (H ! i)) f
                  \<and> key_of (hist_event (H ! i)) = k"
  let ?Pc' = "\<lambda>i. src_le (hist_coord (H ! i)) c'
                  \<and> key_of (hist_event (H ! i)) = k"

  \<comment> \<open>The two candidate filters coincide.\<close>
  have cand_eq: "?cand_f = ?cand_c'"
  proof -
    have "\<And>i. i \<in> set [0..<length H] \<Longrightarrow> ?Pf i = ?Pc' i"
    proof -
      fix i assume i_in: "i \<in> set [0..<length H]"
      hence i_lt: "i < length H" by simp
      show "?Pf i = ?Pc' i"
      proof
        assume Pf: "?Pf i"
        hence le_f: "src_le (hist_coord (H ! i)) f"
          and key_eq: "key_of (hist_event (H ! i)) = k"
          by auto
        have "src_le (hist_coord (H ! i)) c'"
        proof (rule ccontr)
          assume "\<not> src_le (hist_coord (H ! i)) c'"
          hence "src_le c' (hist_coord (H ! i))"
                "hist_coord (H ! i) \<noteq> c'"
            using src_le_total
            by (auto simp: less_eq_src_coord_def)
          hence "src_lt c' (hist_coord (H ! i))"
            unfolding src_lt_def by simp
          with no_later i_lt le_f have "key_of (hist_event (H ! i)) \<noteq> k"
            by blast
          with key_eq show False by simp
        qed
        thus "?Pc' i" using key_eq by simp
      next
        assume Pc': "?Pc' i"
        hence le_c': "src_le (hist_coord (H ! i)) c'"
          and key_eq: "key_of (hist_event (H ! i)) = k"
          by auto
        have "src_le (hist_coord (H ! i)) f"
          using le_c' c'_le_f src_le_trans by blast
        thus "?Pf i" using key_eq by simp
      qed
    qed
    thus ?thesis by (rule filter_cong[OF refl])
  qed

  have "latest_src_event H f k = latest_src_event H c' k"
    unfolding latest_src_event_def using cand_eq by simp
  thus ?thesis
    unfolding Src_def by simp
qed


lemma src_frontier_eq_effect_of_last_key_coord_slice:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H  :: "('k, 'v) src_history"
    and f c :: src_coord
    and k  :: 'k
    and e  :: "('k, 'v) source_event"
  assumes wf_h: "wellformed_src_history H"
      and c_le_f: "src_le c f"
      and no_later:
        "\<forall>j < length H.
           src_lt c (hist_coord (H ! j))
           \<and> src_le (hist_coord (H ! j)) f
           \<longrightarrow> key_of (hist_event (H ! j)) \<noteq> k"
      and slice_nonempty: "source_key_coord_slice k c H \<noteq> []"
      and last_slice: "last (source_key_coord_slice k c H) = (c, e)"
  shows "Src b0 H f k = (case e of
                          Insert _ v \<Rightarrow> Some v
                        | Update _ v \<Rightarrow> Some v
                        | Delete _   \<Rightarrow> None)"
proof -
  let ?Q = "\<lambda>p::(src_coord \<times> ('k, 'v) source_event).
              hist_coord p = c \<and> key_of (hist_event p) = k"
  let ?P = "\<lambda>j. src_le (hist_coord (H ! j)) f
                  \<and> key_of (hist_event (H ! j)) = k"

  obtain i where
    i_lt: "i < length H" and
    Q_i: "?Q (H ! i)" and
    H_i_last: "H ! i = last (filter ?Q H)" and
    no_after_same: "\<forall>j. i < j \<and> j < length H \<longrightarrow> \<not> ?Q (H ! j)"
    using last_filter_index[of ?Q H] slice_nonempty
    unfolding source_key_coord_slice_def by blast
  have H_i: "H ! i = (c, e)"
    using H_i_last last_slice
    unfolding source_key_coord_slice_def by simp
  have coord_i: "hist_coord (H ! i) = c"
    using H_i by simp
  have event_i: "hist_event (H ! i) = e"
    using H_i by simp
  have P_i: "?P i"
    using c_le_f Q_i by simp

  have no_after_P: "\<forall>j. i < j \<and> j < length H \<longrightarrow> \<not> ?P j"
  proof (intro allI impI)
    fix j
    assume j_assm: "i < j \<and> j < length H"
    hence i_le_j: "i \<le> j" and j_lt: "j < length H" by auto
    show "\<not> ?P j"
    proof
      assume P_j: "?P j"
      hence j_le_f: "src_le (hist_coord (H ! j)) f"
        and j_key: "key_of (hist_event (H ! j)) = k"
        by auto
      have c_le_j: "src_le c (hist_coord (H ! j))"
        using wellformed_src_history_coord_mono[OF wf_h i_le_j j_lt]
              coord_i
        by simp
      show False
      proof (cases "hist_coord (H ! j) = c")
        case True
        hence "?Q (H ! j)" using j_key by simp
        with no_after_same j_assm show False by blast
      next
        case False
        hence c_lt_j: "src_lt c (hist_coord (H ! j))"
          using c_le_j unfolding src_lt_def by simp
        from no_later j_lt c_lt_j j_le_f
        have "key_of (hist_event (H ! j)) \<noteq> k" by blast
        with j_key show False by simp
      qed
    qed
  qed

  have cand_last:
    "filter ?P [0..<length H] \<noteq> []
     \<and> last (filter ?P [0..<length H]) = i"
    by (rule last_filter_upt_eq[OF i_lt P_i no_after_P])
  hence latest_eq: "latest_src_event H f k = Some i"
    unfolding latest_src_event_def by (simp add: Let_def)

  have "Src b0 H f k =
          (case hist_event (H ! i) of
             Insert _ v \<Rightarrow> Some v
           | Update _ v \<Rightarrow> Some v
           | Delete _   \<Rightarrow> None)"
    unfolding Src_def using latest_eq by simp
  thus ?thesis using event_i by simp
qed

end
