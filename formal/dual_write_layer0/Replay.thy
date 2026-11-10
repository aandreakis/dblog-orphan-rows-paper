(*  Title:   Replay.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Replay
  imports Source_History
begin

section \<open>Layer 0: replay events and the @{text Apply} semantics\<close>

text \<open>
  Layer 0 replay substrate.

  Replay-side vocabulary:

    \<^item> @{text "('k, 'v) replay_event"}: replay-side event datatype
        with two constructors --- @{text "Cdc c e"} (a replay-side
        CDC event lifted from a source event @{text e} that was
        committed at source coordinate @{text c}) and
        @{text "Refresh k m c"} (a chunk-read refresh whose
        @{text "m :: 'v option"} records the value observed --- or
        its absence, @{term None} --- for key @{text k} at
        chunk-read coordinate @{text c}). The @{text Cdc} constructor
        carries the source coordinate so that the
        canonical-clean-prefix interleaving is total at Layer 0
        without recovering the coordinate from a separate pairing;
    \<^item> @{text cdc_coord} / @{text refresh_coord}: replay-event
        source-coordinate projectors (paper "Auxiliary Layer 0
        definitions" / "Replay-event source-coordinate projectors");
    \<^item> @{text cdc_lift}: trivial inclusion translating a source-
        history pair @{text "(c, e)"} to its replay-side CDC
        counterpart @{text "Cdc c e"} (paper "Auxiliary Layer 0
        definitions" / "CDC lift");
    \<^item> @{text apply_step}: per-event step of @{text Apply} --- the
        source coordinate is carried by the constructor but is
        irrelevant to the per-key state @{text apply_step}
        produces;
    \<^item> @{text Apply}: replay function as the left-fold of
        @{text apply_step} over the replay-event list, starting
        from the empty per-key state (paper "Replay function
        Apply").

  Replay events are a real Isabelle datatype, and @{text apply_step},
  @{text Apply}, @{text cdc_lift}, and the projectors are real
  definitions. The result is a closed-form, total @{text Apply} that
  the Layer 1 and Layer 2 proofs compute against.
\<close>

subsection \<open>Replay event datatype\<close>

datatype ('k, 'v) replay_event
  = Cdc src_coord "('k, 'v) source_event"
  | Refresh 'k "'v option" src_coord

subsection \<open>Source-coordinate projectors\<close>

text \<open>
  @{text cdc_coord} projects the source-event coordinate @{text c}
  from a @{text "Cdc c e"} replay event; @{text refresh_coord}
  projects the chunk-read coordinate @{text c} from a
  @{text "Refresh k m c"} replay event. Paper "Auxiliary Layer 0
  definitions" / "Replay-event source-coordinate projectors" defines
  them on their respective constructors only; here both are extended
  to total functions on @{text replay_event} (returning @{text c} on
  either constructor) so cross-event coordinate comparisons stay
  well-typed without a constructor-case discrimination at every use
  site.
\<close>

fun cdc_coord :: "('k, 'v) replay_event \<Rightarrow> src_coord" where
  "cdc_coord (Cdc c _) = c"
| "cdc_coord (Refresh _ _ c) = c"

fun refresh_coord :: "('k, 'v) replay_event \<Rightarrow> src_coord" where
  "refresh_coord (Cdc c _) = c"
| "refresh_coord (Refresh _ _ c) = c"

subsection \<open>CDC lift\<close>

text \<open>
  Trivial inclusion translating a source-history pair
  @{text "(c, e)"} to the replay-side CDC event @{text "Cdc c e"}.
  Total and injective. The lift is what the canonical-clean-prefix
  construction's CDC step (paper "Canonical clean prefix") emits per
  observed CDC event.
\<close>

definition cdc_lift
  :: "src_coord \<Rightarrow> ('k, 'v) source_event \<Rightarrow> ('k, 'v) replay_event"
where
  "cdc_lift c e = Cdc c e"

subsection \<open>Per-event Apply step\<close>

text \<open>
  Per-event step @{text apply_step}, by case analysis on the replay
  event. The source coordinate is carried by the constructor but is
  irrelevant to the per-key state @{text apply_step} produces:
  source-coordinate consumption happens in the
  canonical-clean-prefix interleaving (paper "Canonical clean
  prefix", step 3) and in the suppression-dominance comparison
  (paper "Suppression dominance"), not inside @{text apply_step}.

  Paper "Replay function Apply" / "Definition (Apply, per-event
  step)".
\<close>

fun apply_step
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) replay_event \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "apply_step m (Cdc _ (Insert k v)) = m(k \<mapsto> v)"
| "apply_step m (Cdc _ (Update k v)) = m(k \<mapsto> v)"
| "apply_step m (Cdc _ (Delete k))   = m(k := None)"
| "apply_step m (Refresh k m_obs _)  = m(k := m_obs)"

subsection \<open>Apply as left-fold of @{text apply_step}\<close>

text \<open>
  Paper "Replay function Apply": @{text "Apply \<sigma>"} is the left-fold
  of @{text apply_step} over @{text \<sigma>} starting from the empty per-key
  state @{term "(\<lambda>k. None)"}.
\<close>

definition Apply
  :: "('k, 'v) replay_event list \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "Apply \<sigma> = foldl apply_step (\<lambda>_. None) \<sigma>"

subsection \<open>Replay-event key + refresh-shape projectors\<close>

text \<open>
  @{text event_key} projects the key affected by a replay event:
  @{text "key_of e"} for @{text "Cdc c e"} (the key affected by the
  underlying source event @{text e}), and @{text "k"} for
  @{text "Refresh k m c"} (the chunk-read's target key directly).
  @{text is_refresh} discriminates the @{text Refresh} constructor.

  Both projectors live here at Layer 0 because they classify
  @{text replay_event}s directly. Their downstream consumers (the
  canonical clean-prefix construction, the wellformedness body,
  and the per-key projection lemmas below) import this theory.
\<close>

fun event_key :: "('k, 'v) replay_event \<Rightarrow> 'k" where
  "event_key (Cdc _ e)        = key_of e"
| "event_key (Refresh k _ _)  = k"

fun is_refresh :: "('k, 'v) replay_event \<Rightarrow> bool" where
  "is_refresh (Cdc _ _)      = False"
| "is_refresh (Refresh _ _ _) = True"

subsection \<open>Apply latest-event-wins per key\<close>

text \<open>
  Paper "Layer 0 and Layer 1 Lemmas" bullet "Apply is
  latest-event-wins per key": for any replay-event
  sequence @{text \<sigma>} and any key @{text k}, the value of
  @{term "Apply \<sigma>"} at @{text k} is the per-event effect of the
  latest event in @{text \<sigma>} affecting @{text k} --- @{term "Some v"}
  for @{text "Cdc c (Insert k v)"} / @{text "Cdc c (Update k v)"} /
  @{text "Refresh k (Some v) c"}; @{term None} for
  @{text "Cdc c (Delete k)"} / @{text "Refresh k None c"};
  @{term None} if no event in @{text \<sigma>} affects @{text k}.

  The proof decomposes into three engine lemmas + a single headline
  case-analysis form:

    \<^enum> @{text apply_step_at_other_key}: @{term apply_step} at a key
        other than @{term "event_key e"} is identity on the input
        map's value at that key;
    \<^enum> @{text apply_step_at_own_key_indep}: @{term apply_step} at
        @{term "event_key e"} depends only on @{text e}, not on the
        input map --- both constructors overwrite the per-key slot
        outright;
    \<^enum> @{text apply_eq_apply_filter_key}: per-key projection
        (Apply at @{text k} equals Apply on the @{text k}-events
        only) by @{text rev_induct} over @{text \<sigma>};
    \<^enum> @{text apply_filter_uniform_last}: on a key-uniform
        non-empty list, Apply equals the per-event effect of the
        last entry.

  Composes downstream at @{text clean_prefix_of_per_key_replay_equals_source}
  (the per-key value-equality form
  of the Layer 2 supporting clean-prefix lemma family) and Lemma
  1.1 / the Layer 2 main theorem. The factored shape states
  semantics-free engine lemmas and combines them at the call site.
\<close>

lemma apply_step_at_other_key:
  fixes m :: "'k \<rightharpoonup> 'v" and e :: "('k, 'v) replay_event" and k :: 'k
  assumes "event_key e \<noteq> k"
  shows "apply_step m e k = m k"
proof (cases e)
  case (Cdc c se)
  with assms have "key_of se \<noteq> k" by simp
  thus ?thesis using Cdc by (cases se) auto
next
  case (Refresh k' m_obs c)
  with assms have "k' \<noteq> k" by simp
  thus ?thesis using Refresh by simp
qed

lemma apply_step_at_own_key_indep:
  fixes m m' :: "'k \<rightharpoonup> 'v" and e :: "('k, 'v) replay_event" and k :: 'k
  assumes "event_key e = k"
  shows "apply_step m e k = apply_step m' e k"
proof (cases e)
  case (Cdc c se)
  with assms have "key_of se = k" by simp
  thus ?thesis using Cdc by (cases se) auto
next
  case (Refresh k' m_obs c)
  with assms have "k' = k" by simp
  thus ?thesis using Refresh by simp
qed

lemma apply_snoc:
  "Apply (\<sigma> @ [e]) = apply_step (Apply \<sigma>) e"
  unfolding Apply_def by simp

lemma apply_eq_apply_filter_key:
  fixes \<sigma> :: "('k, 'v) replay_event list" and k :: 'k
  shows "Apply \<sigma> k = Apply (filter (\<lambda>e. event_key e = k) \<sigma>) k"
proof (induction \<sigma> rule: rev_induct)
  case Nil
  show ?case by (simp add: Apply_def)
next
  case (snoc e \<sigma>)
  show ?case
  proof (cases "event_key e = k")
    case True
    have filt: "filter (\<lambda>e'. event_key e' = k) (\<sigma> @ [e])
                  = filter (\<lambda>e'. event_key e' = k) \<sigma> @ [e]"
      using True by simp
    have "Apply (\<sigma> @ [e]) k = apply_step (Apply \<sigma>) e k"
      by (simp add: apply_snoc)
    also have "\<dots> = apply_step (Apply (filter (\<lambda>e'. event_key e' = k) \<sigma>)) e k"
      using True apply_step_at_own_key_indep by metis
    also have "\<dots> = Apply (filter (\<lambda>e'. event_key e' = k) \<sigma> @ [e]) k"
      by (simp add: apply_snoc)
    finally show ?thesis using filt by simp
  next
    case False
    have filt: "filter (\<lambda>e'. event_key e' = k) (\<sigma> @ [e])
                  = filter (\<lambda>e'. event_key e' = k) \<sigma>"
      using False by simp
    have "Apply (\<sigma> @ [e]) k = apply_step (Apply \<sigma>) e k"
      by (simp add: apply_snoc)
    also have "\<dots> = Apply \<sigma> k"
      using False apply_step_at_other_key by metis
    also have "\<dots> = Apply (filter (\<lambda>e'. event_key e' = k) \<sigma>) k"
      using snoc.IH by simp
    finally show ?thesis using filt by simp
  qed
qed

text \<open>
  Per-event effect on the empty map at the event's own key. For
  any replay event @{text e}, applying @{term apply_step} to the
  empty map @{term "(\<lambda>_. None)"} and projecting at
  @{term "event_key e"} yields the per-constructor effect:
  @{term "Some v"} for the two @{text Insert} / @{text Update}
  shapes, @{term None} for @{text Delete}, and the observed value
  @{term m_obs} for @{text Refresh}.
\<close>

lemma apply_step_empty_at_own_key:
  fixes e :: "('k, 'v) replay_event"
  shows "apply_step (\<lambda>_. None) e (event_key e)
           = (case e of
                Cdc _ (Insert _ v) \<Rightarrow> Some v
              | Cdc _ (Update _ v) \<Rightarrow> Some v
              | Cdc _ (Delete _)   \<Rightarrow> None
              | Refresh _ m_obs _  \<Rightarrow> m_obs)"
proof (cases e)
  case (Cdc c se)
  thus ?thesis by (cases se) auto
next
  case (Refresh k' m_obs c)
  thus ?thesis by simp
qed

lemma apply_filter_uniform_last:
  fixes \<sigma> :: "('k, 'v) replay_event list" and k :: 'k
  assumes uniform: "\<forall> e \<in> set \<sigma>. event_key e = k"
  assumes nonempty: "\<sigma> \<noteq> []"
  shows "Apply \<sigma> k = (case last \<sigma> of
                        Cdc _ (Insert _ v) \<Rightarrow> Some v
                      | Cdc _ (Update _ v) \<Rightarrow> Some v
                      | Cdc _ (Delete _)   \<Rightarrow> None
                      | Refresh _ m_obs _  \<Rightarrow> m_obs)"
  using assms
proof (induction \<sigma> rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc e \<sigma>)
  from snoc.prems(1) have e_key: "event_key e = k" by simp
  from snoc.prems(1) have \<sigma>_uniform: "\<forall> e' \<in> set \<sigma>. event_key e' = k" by simp
  have last_eq: "last (\<sigma> @ [e]) = e" by simp
  have "Apply (\<sigma> @ [e]) k = apply_step (Apply \<sigma>) e k"
    by (simp add: apply_snoc)
  also have "\<dots> = apply_step (\<lambda>_. None) e k"
    using e_key apply_step_at_own_key_indep by metis
  also have "\<dots> = apply_step (\<lambda>_. None) e (event_key e)"
    using e_key by simp
  also have "\<dots> = (case e of
                     Cdc _ (Insert _ v) \<Rightarrow> Some v
                   | Cdc _ (Update _ v) \<Rightarrow> Some v
                   | Cdc _ (Delete _)   \<Rightarrow> None
                   | Refresh _ m_obs _  \<Rightarrow> m_obs)"
    by (rule apply_step_empty_at_own_key)
  finally show ?case using last_eq by simp
qed

theorem apply_latest_event_wins:
  fixes \<sigma> :: "('k, 'v) replay_event list" and k :: 'k
  shows "Apply \<sigma> k = (case filter (\<lambda>e. event_key e = k) \<sigma> of
                        []     \<Rightarrow> None
                      | _ # _  \<Rightarrow> (case last (filter (\<lambda>e. event_key e = k) \<sigma>) of
                                     Cdc _ (Insert _ v) \<Rightarrow> Some v
                                   | Cdc _ (Update _ v) \<Rightarrow> Some v
                                   | Cdc _ (Delete _)   \<Rightarrow> None
                                   | Refresh _ m_obs _  \<Rightarrow> m_obs))"
proof -
  let ?\<sigma>_k = "filter (\<lambda>e. event_key e = k) \<sigma>"
  have proj: "Apply \<sigma> k = Apply ?\<sigma>_k k"
    by (rule apply_eq_apply_filter_key)
  show ?thesis
  proof (cases ?\<sigma>_k)
    case Nil
    hence "Apply ?\<sigma>_k k = None" by (simp add: Apply_def)
    thus ?thesis using proj Nil by simp
  next
    case (Cons e_first \<sigma>_k_tail)
    have nonempty: "?\<sigma>_k \<noteq> []" using Cons by simp
    have uniform: "\<forall> e \<in> set ?\<sigma>_k. event_key e = k" by simp
    have "Apply ?\<sigma>_k k = (case last ?\<sigma>_k of
                            Cdc _ (Insert _ v) \<Rightarrow> Some v
                          | Cdc _ (Update _ v) \<Rightarrow> Some v
                          | Cdc _ (Delete _)   \<Rightarrow> None
                          | Refresh _ m_obs _  \<Rightarrow> m_obs)"
      by (rule apply_filter_uniform_last [OF uniform nonempty])
    thus ?thesis using proj Cons by simp
  qed
qed

subsection \<open>Replay-side CDC events faithfully lift source-side events\<close>

text \<open>
  Paper "Layer 0 and Layer 1 Lemmas" bullet "a replay-side Cdc event
  has the same per-key effect as its source event": for any source
  coordinate @{text c} and any source event @{text e}, the
  replay-side CDC event @{term "cdc_lift c e"} has the same
  per-key effect under @{const apply_step} that @{text e} has
  under @{const Src} at the single-event level:

    @{text "apply_step m (cdc_lift c (Insert k v))"} = @{text "m(k \<mapsto> v)"}
    @{text "apply_step m (cdc_lift c (Update k v))"} = @{text "m(k \<mapsto> v)"}
    @{text "apply_step m (cdc_lift c (Delete k))"}   = @{text "m(k := None)"}

  and for any @{text "m, k'"} with @{text "k' \<noteq> key_of e"},
  @{text "(apply_step m (cdc_lift c e)) k' = m k'"}.

  The lemma is the definitional unfolding of @{const cdc_lift}
  composed with the @{const apply_step} clauses: by
  @{text cdc_lift_def}, @{term "cdc_lift c e = Cdc c e"}, and
  @{const apply_step} on a @{text Cdc} event matches the per-key
  state update directly. The source coordinate @{text c} is
  carried by the @{text Cdc} constructor but does not affect the
  per-key state @{const apply_step} produces, so the lift is
  coordinate-agnostic at the state level.

  Its role is to name the coherence as a standalone,
  paper-aligned fact. No proof in this session consumes it: the
  per-key replay-equality proof
  (@{text clean_prefix_of_per_key_replay_equals_source}) obtains
  the same effect by direct case analysis on the
  event. The at-other-key identity
  is already covered by @{text apply_step_at_other_key} from
  the latest-event-wins subsection above (the @{const event_key} of
  a @{text "Cdc c e"} is @{term "key_of e"}; the at-other-key lemma
  applied to a Cdc event yields the desired identity).
\<close>

theorem cdc_lift_coherence:
  fixes m :: "'k \<rightharpoonup> 'v" and c :: src_coord and e :: "('k, 'v) source_event"
  shows "apply_step m (cdc_lift c e)
           = (case e of
                Insert k v \<Rightarrow> m(k \<mapsto> v)
              | Update k v \<Rightarrow> m(k \<mapsto> v)
              | Delete k   \<Rightarrow> m(k := None))"
  by (cases e) (auto simp: cdc_lift_def)

end
