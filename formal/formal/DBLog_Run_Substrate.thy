(*  Title:   DBLog_Run_Substrate.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory DBLog_Run_Substrate
  imports DBLog_Run
begin

section \<open>Layer 1 run substrate as a locale (abstract carrier)\<close>

text \<open>
  The Layer 1 run/chunk interface presented as a \<^emph>\<open>locale\<close> over abstract
  carrier type variables, together with a canonical concrete
  interpretation.

  Theory @{text DBLog_Run} defines the run carrier as a concrete
  single-constructor @{command datatype} (chunks modeled as @{typ nat})
  with definitional accessors, and proves the two
  @{text chunks_list} facts as lemmas. This theory restates the same
  interface abstractly:

    \<^item> the locale @{text dblog_run_substrate} fixes the twelve run/chunk
        accessors over plain type variables @{typ 'run} / @{typ 'chunk}
        (with @{typ "'k::linorder"} for the key type), and assumes only
        the two @{text chunks_list} obligations --- as locale
        assumptions;

    \<^item> the carrier-independent ``pure'' building blocks
        (@{const canonical_clean_prefix}, @{const source_key_coord_slice},
        the @{type chunk_read_record}, and the normalization lemmas) are
        defined in the imported theory @{text DBLog_Run_Core}: they
        reference no accessor, so both this
        locale and the global theory @{text DBLog_Run} reuse them directly;

    \<^item> the carrier-\<^emph>\<open>dependent\<close> Layer 1 definitions
        (@{text clean_prefix_of}, @{text covers_ordinary_cdc},
        @{text row_absence_meaningful}, @{text canonical_chunk_ownership_domain},
        and the seven-clause @{text wellformed_dblog_run}) are restated
        inside the locale with bodies identical to the global ones; the
        Layer 2 source-side soundness lemmas are proved in this locale
        context, in theory @{text DBLog_Run_Substrate_Layer2}.
        The restatement is deliberate: the public Layer 1 surface of
        @{text DBLog_Run} is self-contained (its definitions are stated
        directly over the concrete carrier, with no locale machinery,
        and are imported by this theory), so deriving the global
        constants \<^emph>\<open>from\<close> the locale --- a
        @{command global_interpretation} with @{text \<open>defines\<close>} clauses
        --- is not available here and would invert the layering. The two
        copies are kept honest by the pointwise
        @{text "canonical.X = X"} equalities proved at the end of this
        theory: any drift between the bodies breaks those lemmas, and
        with them the build.

  The companion @{command global_interpretation} @{text canonical}
  instantiates the locale at the concrete public carrier
  @{typ "('k, 'v) run"} through the global accessors.
  The chunk enumeration is realized as @{text "remdups \<circ> rr_chunks_list"},
  so the two locale assumptions hold definitionally for \<^emph>\<open>every\<close>
  carrier value --- the interpretation discharges them with @{method simp},
  introducing no axiom. It exports every locale-proved fact at the
  concrete carrier, which is how the global headline theorems are
  obtained from the locale proofs.

  The locale-fixed names deliberately coincide with the global accessor
  and definition names; inside the locale context they shadow the global
  constants, and the concrete versions are recovered under the
  @{text "canonical."} qualifier from the interpretation.
\<close>

locale dblog_run_substrate =
  fixes scope_of               :: "'run \<Rightarrow> ('k::linorder) set"
    and frontier_of            :: "'run \<Rightarrow> frontier"
    and chunks                 :: "'run \<Rightarrow> 'chunk set"
    and src_history_of         :: "'run \<Rightarrow> ('k, 'v) src_history"
    and chunk_read_result      :: "'run \<Rightarrow> 'chunk \<Rightarrow> 'k \<Rightarrow> 'v option option"
    and cdc_events_of          :: "'run \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
    and chunks_list            :: "'run \<Rightarrow> 'chunk list"
    and chunk_domain           :: "'run \<Rightarrow> 'chunk \<Rightarrow> 'k set"
    and responsible_chunk      :: "'run \<Rightarrow> 'k \<Rightarrow> 'chunk option"
    and chunk_lower_watermark  :: "'run \<Rightarrow> 'chunk \<Rightarrow> src_coord"
    and chunk_upper_watermark  :: "'run \<Rightarrow> 'chunk \<Rightarrow> src_coord"
    and chunk_read_coordinate  :: "'run \<Rightarrow> 'chunk \<Rightarrow> src_coord"
  assumes chunks_list_set:      "set (chunks_list R) = chunks R"
      and chunks_list_distinct: "distinct (chunks_list R)"
begin

text \<open>@{text owns} as an abbreviation over the fixed @{text chunk_domain},
  mirroring the global reader-facing definitional equivalence.\<close>

abbreviation owns :: "'run \<Rightarrow> 'chunk \<Rightarrow> 'k \<Rightarrow> bool"
  where "owns R ch k \<equiv> k \<in> chunk_domain R ch"

text \<open>Global chunk-set finiteness, as a derived fact of the locale.\<close>

lemma chunks_finite: "finite (chunks R)"
  by (metis chunks_list_set List.finite_set)

definition canonical_chunk_ownership_domain :: "'run \<Rightarrow> 'k set"
  where
  "canonical_chunk_ownership_domain R =
     (\<Union>ch \<in> chunks R. chunk_domain R ch)"

text \<open>Layer 1 clean-prefix definitional equality: the run instance of the
  global @{const canonical_clean_prefix} building block.\<close>

definition clean_prefix_of :: "'run \<Rightarrow> ('k, 'v) replay_event list"
  where
  "clean_prefix_of R =
     canonical_clean_prefix
       (map (\<lambda>ch. \<lparr> crr_domain      = chunk_domain R ch,
                    crr_read_coord  = chunk_read_coordinate R ch,
                    crr_observation = chunk_read_result R ch \<rparr>)
            (chunks_list R))
       (cdc_events_of R)
       (scope_of R)
       (frontier_of R)"

definition covers_ordinary_cdc :: "'run \<Rightarrow> 'k \<Rightarrow> frontier \<Rightarrow> bool"
  where
  "covers_ordinary_cdc R k f \<longleftrightarrow>
     (\<exists> ch. responsible_chunk R k = Some ch
            \<and> (\<forall> i. i < length (src_history_of R)
                     \<longrightarrow> src_lt (chunk_read_coordinate R ch)
                                (hist_coord (src_history_of R ! i))
                     \<longrightarrow> src_le (hist_coord (src_history_of R ! i)) f
                     \<longrightarrow> key_of (hist_event (src_history_of R ! i)) = k
                     \<longrightarrow> src_history_of R ! i \<in> set (cdc_events_of R)))"

definition row_absence_meaningful
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> 'run \<Rightarrow> 'chunk \<Rightarrow> 'k \<Rightarrow> bool"
  where
  "row_absence_meaningful b0 H R ch k \<longleftrightarrow>
     (k \<in> chunk_domain R ch
      \<and> Refresh k None (chunk_read_coordinate R ch) \<in> set (clean_prefix_of R)
      \<longrightarrow> Src b0 H (chunk_read_coordinate R ch) k = None)"

text \<open>The seven-clause wellformed-DBLog-run predicate, body identical to the
  global @{text "DBLog_Run.wellformed_dblog_run"}.\<close>

definition wellformed_dblog_run
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'run \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
  where
  "wellformed_dblog_run b0 R H \<longleftrightarrow>
     \<comment> \<open>WF0: source-history binding\<close>
     src_history_of R = H \<and> wellformed_src_history H
   \<and>
     \<comment> \<open>WF1 (a): @{text \<open>\<exists>!\<close>} responsible chunk per in-scope key\<close>
     (\<forall> k \<in> scope_of R. \<exists>! ch. ch \<in> chunks R \<and> owns R ch k)
   \<and>
     \<comment> \<open>WF1 (b): chunk domains are pairwise disjoint\<close>
     (\<forall> ch1 \<in> chunks R. \<forall> ch2 \<in> chunks R.
        ch1 \<noteq> ch2 \<longrightarrow> chunk_domain R ch1 \<inter> chunk_domain R ch2 = {})
   \<and>
     \<comment> \<open>WF1 (c): canonical chunk-ownership domain equals scope\<close>
     canonical_chunk_ownership_domain R = scope_of R
   \<and>
     \<comment> \<open>WF1 (d): @{text responsible_chunk} @{text \<open>\<longleftrightarrow>\<close>} ownership predicate (in scope)\<close>
     (\<forall> k \<in> scope_of R. \<forall> ch.
        responsible_chunk R k = Some ch
          \<longleftrightarrow> ch \<in> chunks R \<and> owns R ch k)
   \<and>
     \<comment> \<open>WF1 (e): out-of-scope keys have no responsible chunk\<close>
     (\<forall> k. k \<notin> scope_of R \<longrightarrow> responsible_chunk R k = None)
   \<and>
     \<comment> \<open>WF1 (f): scope and chunk domains are finite\<close>
     finite (scope_of R)
   \<and> (\<forall> ch \<in> chunks R. finite (chunk_domain R ch))
   \<and>
     \<comment> \<open>WF1 (g): every chunk has a non-empty domain\<close>
     (\<forall> ch \<in> chunks R. chunk_domain R ch \<noteq> {})
   \<and>
     \<comment> \<open>WF2 (coverage): observed CDC reaches every in-scope key
         through the frontier\<close>
     (\<forall> k \<in> scope_of R. covers_ordinary_cdc R k (frontier_of R))
   \<and>
     \<comment> \<open>WF2 (faithfulness): observed CDC events in scope and
         at-or-before frontier are real source events\<close>
     (\<forall> p \<in> set (cdc_events_of R).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R)
        \<longrightarrow> p \<in> set (src_history_of R))
   \<and>
     \<comment> \<open>WF2 (order-preserving sublist): on the in-scope /
         at-or-before-frontier slice, @{text \<open>cdc_events_of(R)\<close>} is an
         order-preserving sublist of @{text \<open>src_history_of(R)\<close>}\<close>
     (\<exists> \<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
        \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> scope_of R
                                 \<and> src_le (hist_coord p) (frontier_of R));
               cdc_in_slice  = filter in_slice (cdc_events_of R);
               hist_in_slice = filter in_slice (src_history_of R)
           in \<forall> i. i < length cdc_in_slice \<longrightarrow>
                   \<iota> i < length hist_in_slice
                 \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i))
   \<and>
     \<comment> \<open>WF2 (post-read same-key/same-coordinate multiplicity)\<close>
     (\<forall> k \<in> scope_of R. \<forall> ch c.
        responsible_chunk R k = Some ch
        \<and> src_lt (chunk_read_coordinate R ch) c
        \<and> src_le c (frontier_of R)
        \<longrightarrow>
          mset (source_key_coord_slice k c (cdc_events_of R))
          = mset (source_key_coord_slice k c (src_history_of R)))
   \<and>
     \<comment> \<open>(no WF3 --- the numbering carries a deliberate gap)\<close>
     \<comment> \<open>WF4: chunk-read evidence (watermark bracketing +
         @{text chunk_read_result} totality on domain + Refresh-event
         agreement with @{text chunk_read_result} on domain)\<close>
     (\<forall> ch \<in> chunks R.
        src_le (chunk_lower_watermark R ch) (chunk_read_coordinate R ch)
      \<and> src_le (chunk_read_coordinate R ch) (chunk_upper_watermark R ch)
      \<and> (\<forall> k \<in> chunk_domain R ch.
           \<exists> m. chunk_read_result R ch k = Some m)
      \<and> (\<forall> k \<in> chunk_domain R ch. \<forall> m.
           chunk_read_result R ch k = Some m
             \<longleftrightarrow> Refresh k m (chunk_read_coordinate R ch)
                  \<in> set (clean_prefix_of R)))
   \<and>
     \<comment> \<open>WF5: chunk-read coordinate at-or-before frontier\<close>
     (\<forall> ch \<in> chunks R.
        src_le (chunk_read_coordinate R ch) (frontier_of R))
   \<and>
     \<comment> \<open>WF6 (main): refresh correctness against
         @{text \<open>Src b0 H (chunk_read_coordinate R ch) k\<close>}.\<close>
     (\<forall> ch \<in> chunks R. \<forall> k \<in> chunk_domain R ch. \<forall> m.
        chunk_read_result R ch k = Some m
          \<longrightarrow> m = Src b0 H (chunk_read_coordinate R ch) k)
   \<and>
     \<comment> \<open>WF6 (row-absence meaningfulness)\<close>
     (\<forall> ch \<in> chunks R. \<forall> k \<in> chunk_domain R ch.
        chunk_read_result R ch k = Some None
          \<longrightarrow> row_absence_meaningful b0 H R ch k)
   \<and>
     \<comment> \<open>WF7 (clean-prefix CDC coherence): forward direction\<close>
     (\<forall> p \<in> set (cdc_events_of R).
        key_of (hist_event p) \<in> scope_of R
        \<and> src_le (hist_coord p) (frontier_of R)
        \<longrightarrow> Cdc (hist_coord p) (hist_event p)
              \<in> set (clean_prefix_of R))
   \<and>
     \<comment> \<open>WF7 (clean-prefix CDC coherence): reverse direction\<close>
     (\<forall> e c. Cdc c e \<in> set (clean_prefix_of R)
                \<and> key_of e \<in> scope_of R
                \<and> src_le c (frontier_of R)
                \<longrightarrow> (c, e) \<in> set (cdc_events_of R))"

end


subsection \<open>Canonical concrete interpretation (at the public @{type run} datatype)\<close>

text \<open>
  The locale is interpreted at the concrete @{type run} datatype (defined in
  @{text DBLog_Run}) through the \<^emph>\<open>global accessors\<close> @{const scope_of} /
  @{const frontier_of} / @{text \<open>\<dots>\<close>} / @{const chunk_read_coordinate}. The two
  @{text chunks_list} obligations are exactly the @{text DBLog_Run} lemmas
  @{thm [source] chunks_list_set} / @{thm [source] chunks_list_distinct}, so the
  interpretation introduces no axiom. Because the locale parameters \<^emph>\<open>are\<close>
  the global accessors, every locale-defined constant coincides with its global
  @{text DBLog_Run} namesake; the @{text "canonical.X = X"} unfold lemmas below
  expose that coincidence to the public headline theorem
  @{text wellformed_run_implies_virtual_cut} in @{text Virtual_Cut}.
\<close>

global_interpretation canonical: dblog_run_substrate
  scope_of frontier_of chunks src_history_of chunk_read_result
  cdc_events_of chunks_list chunk_domain responsible_chunk
  chunk_lower_watermark chunk_upper_watermark chunk_read_coordinate
  by unfold_locales (simp_all add: chunks_list_set chunks_list_distinct)

lemma canonical_canonical_chunk_ownership_domain_eq:
  "canonical.canonical_chunk_ownership_domain = canonical_chunk_ownership_domain"
  by (rule ext)
     (simp add: canonical.canonical_chunk_ownership_domain_def
                canonical_chunk_ownership_domain_def)

lemma canonical_clean_prefix_of_eq:
  "canonical.clean_prefix_of = clean_prefix_of"
  by (rule ext)
     (simp add: canonical.clean_prefix_of_def clean_prefix_of_def)

lemma canonical_covers_ordinary_cdc_eq:
  "canonical.covers_ordinary_cdc = covers_ordinary_cdc"
  by (rule ext)+
     (simp add: canonical.covers_ordinary_cdc_def covers_ordinary_cdc_def)

lemma canonical_row_absence_meaningful_eq:
  "canonical.row_absence_meaningful = row_absence_meaningful"
  by (rule ext)+
     (simp add: canonical.row_absence_meaningful_def row_absence_meaningful_def
                canonical_clean_prefix_of_eq)

lemma canonical_wellformed_dblog_run_eq:
  "canonical.wellformed_dblog_run = wellformed_dblog_run"
  by (rule ext)+
     (simp add: canonical.wellformed_dblog_run_def wellformed_dblog_run_def
                canonical_clean_prefix_of_eq canonical_covers_ordinary_cdc_eq
                canonical_canonical_chunk_ownership_domain_eq
                canonical_row_absence_meaningful_eq)

end
