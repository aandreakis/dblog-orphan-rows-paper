import OrphanAbsence.Replay

/-!
# A full pass followed by a later bracketed read

This file ports the general part of `Orphan_Absence_Composition.thy`
from the Isabelle session `Orphan_Absence`. The fixture of that theory
is ported in `CompositionWitnesses.lean`.

A full pass `P` emits the window-discard stream with enumerated
absences from its consumption start `s0` to its frontier `f1`. A later
bracketed read `R`, whose consumption starts at `f1` and ends at `f2`,
emits its own stream. The sink applies the pass's stream and then the
read's, in order, from an arbitrary initial state. The read is any
capture contract over the same log, so a key-list request built by
`absence_assertion_contract` is one instance and another pass is
another.

* `titems_closes_at_out`, `titems_emission_out`,
  `emission_out_of_scope`, `emission_out_of_scope_replay`: a key
  outside a contract's scope sees only its own log events in that
  contract's emission.
* `PassThenRead`, `composed`: the two reads over one log, and the
  stream the sink applies.
* `pass_then_read_safe`: every key of either scope ends at the source
  state at `f2`, or it is absent there, neither read listed it, no log
  event from `s0` to `f2` mentions it, and the sink keeps its initial
  value.
* `pass_then_read_converges`: under coverage of exactly those keys,
  the sink ends at the source state on both scopes.
* `pass_then_request_converges`, `request_after_pass_converges`: a
  later read that lists every key it reads as absent and untouched
  completes the pass when every key the pass leaves wrong is in its
  scope. For a request whose scope holds every requested key that is
  absent where the request reads it (each batch at its own
  coordinate), it suffices that every key the pass leaves wrong was
  requested.
* `pass_leaves_wrong_iff`: the keys the pass leaves wrong are exactly
  the unlisted keys of its scope that the sink holds, that are absent
  at the pass's frontier, and that no log event during the pass
  mentions.

The Isabelle locale `pass_then_read` becomes the `Prop`-valued
structure `PassThenRead`, in the way the core port turns the locale
`capture_contract` into `CaptureContract`. Its interpretations `P` and
`R` of `capture_contract` are the fields `P` and `R`.
-/

namespace DBLogContract

universe u v w

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-! ## A key outside a contract's scope sees only its own log events -/

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

/-- No close block carries an entry for a key outside the scope.
Isabelle: `titems_closes_at_out`. -/
theorem titems_closes_at_out {svl : CUnit K V C → List K}
    (hsvl : svl_ok2 S units svl) {k : K} (hk : ¬ scope k) (p : Nat) :
    titems_for k (closes_at S units svl p) = [] := by
  have hvanish : ∀ ui ∈ units.zipIdx,
      titems_for k (if S.den ui.1.hi = p
        then close_block S svl ui.1 else []) = [] := by
    rintro ⟨u, i⟩ hui
    obtain ⟨-, -, hgot⟩ := List.mem_zipIdx hui
    have hu_in : u ∈ units := by
      rw [hgot]
      exact List.getElem_mem _
    by_cases hc : S.den u.hi = p
    · rw [if_pos hc, titems_close_block2 hsvl hu_in k,
        if_neg (fun hks => hk (H.dom_sub_scope hu_in (svl2_sub_dom hsvl hu_in hks)))]
    · rw [if_neg hc]
      rfl
  simp only [closes_at, titems_for, List.filter_flatMap]
  exact flatMap_eq_nil_of_forall hvanish

/-- A key outside the scope has only its consumed log events in the
tagged emission, in commit order. Isabelle: `titems_emission_out`,
whose position-list normal form `map (λp. (Suc p, L ! p)) (kposs k a b)`
is here the per-key filter of the tagged segment, as in the core's
`titems_emission_master`. -/
theorem titems_emission_out {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok2 S units svl) {k : K} (hk : ¬ scope k) :
    titems_for k (emission_t S units f svl s0) =
      titems_for k (tagged_seg S (S.den s0) (S.den f)) := by
  have hvanish : ∀ ep ∈ ((S.log.take (S.den f)).drop (S.den s0)).zipIdx (S.den s0),
      titems_for k (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]) =
        titems_for k [(ep.2 + 1, ep.1)] := by
    intro ep _
    rw [titems_append, H.titems_closes_at_out hsvl hk ep.2, List.nil_append]
  simp only [emission_t]
  rw [titems_append, titems_flatMap (k := k), flatMap_congr hvanish,
    flatMap_titems_single, H.titems_closes_at_out hsvl hk (S.den f),
    List.append_nil]
  rfl

/-- A key outside the scope has exactly its window events in the
emission. Isabelle: `emission_out_of_scope`. The assumption
`S.cle s0 f` is kept as the Isabelle statement has it. The Lean proof
does not need it, since the window is the log segment by definition. -/
theorem emission_out_of_scope {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok2 S units svl) (_hs0f : S.cle s0 f) {k : K}
    (hk : ¬ scope k) :
    evs_for k (emission S units f svl s0) = evs_for k (S.win s0 f) := by
  rw [emission, evs_for_map_snd, H.titems_emission_out hsvl hk,
    ← evs_for_map_snd, map_snd_tagged_seg]
  rfl

/-- From any initial state, the emission replays a key outside the
scope as its window does. Isabelle: `emission_out_of_scope_replay`. -/
theorem emission_out_of_scope_replay {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok2 S units svl) (hs0f : S.cle s0 f) {k : K}
    (hk : ¬ scope k) (D : State K V) :
    state_after D (emission S units f svl s0) k = state_after D (S.win s0 f) k :=
  replay_per_key (H.emission_out_of_scope hsvl hs0f hk) D

end CaptureContract

/-! ## Two reads over one log, applied in stream order -/

/-- A full pass and a later bracketed read over one coordinate space
and one initial source state: the pass `P` is a contract over the
units `U1`, the scope `sc1` and the frontier `f1`, the read `R` is a
contract over `U2`, `sc2` and `f2`, the read's frontier is at or after
the pass's, and every unit of the read starts at or after the pass's
frontier. Isabelle: locale `pass_then_read`. -/
structure PassThenRead (S : CoordinateSpace K V C) (σ0 : State K V)
    (U1 : List (CUnit K V C)) (sc1 : K → Prop) (f1 : C)
    (U2 : List (CUnit K V C)) (sc2 : K → Prop) (f2 : C) : Prop where
  /-- The pass. Isabelle: the locale instance `P`. -/
  P : CaptureContract S σ0 U1 sc1 f1
  /-- The later read. Isabelle: the locale instance `R`. -/
  R : CaptureContract S σ0 U2 sc2 f2
  /-- Isabelle: `f1_le_f2`. -/
  f1_le_f2 : S.den f1 ≤ S.den f2
  /-- Isabelle: `f1_le_lo2`. -/
  f1_le_lo2 : ∀ u ∈ U2, S.den f1 ≤ S.den u.lo

/-- The stream the sink applies: the pass's emission from its
consumption start `s0`, followed by the read's emission from the
pass's frontier `f1`. Isabelle: `composed`. -/
def composed (S : CoordinateSpace K V C) (U1 : List (CUnit K V C)) (f1 : C)
    (U2 : List (CUnit K V C)) (f2 : C) (svl1 svl2 : CUnit K V C → List K)
    (s0 : C) : List (Event K V) :=
  emission S U1 f1 svl1 s0 ++ emission S U2 f2 svl2 f1

namespace PassThenRead

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {U1 : List (CUnit K V C)} {sc1 : K → Prop} {f1 : C}
  {U2 : List (CUnit K V C)} {sc2 : K → Prop} {f2 : C}
  (H : PassThenRead S σ0 U1 sc1 f1 U2 sc2 f2)

include H

/-- A key quiet between the two frontiers has the same source value at
both. Isabelle: `src_quiet_mid`. -/
theorem src_quiet_mid {k : K} (h : evs_for k (S.win f1 f2) = []) :
    state_after σ0 (S.pfx f2) k = state_after σ0 (S.pfx f1) k :=
  S.win_invariant_state H.f1_le_f2 (S.cle_refl f2) h σ0

omit H in
/-- When a window carries an event for a key, replaying the window
from any state gives the source value at the window's high edge.
Isabelle: `win_last_src`. -/
theorem win_last_src {a b : C} {k : K} (ab : S.den a ≤ S.den b)
    (ne : evs_for k (S.win a b) ≠ []) (X : State K V) :
    state_after X (S.win a b) k = state_after σ0 (S.pfx b) k := by
  have split := S.evs_for_pfx_split ab k
  have pne : evs_for k (S.pfx b) ≠ [] := by
    rw [split]
    intro h
    exact ne (List.append_eq_nil_iff.mp h).2
  rw [state_after_last_event ne X, state_after_last_event pne σ0,
    getLast_eq_of_eq split pne, List.getLast_append_of_ne_nil _ ne]

/-- Safety of a pass followed by a later read. Every key of either
scope ends at the source state at the read's frontier, or it is absent
there, neither read listed it, no log event from the pass's start to
the read's frontier mentions it, and the sink keeps its initial value.
Isabelle: `pass_then_read_safe`. -/
theorem pass_then_read_safe {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0f1 : S.den s0 ≤ S.den f1)
    {k : K} (hk : sc1 k ∨ sc2 k) (D0 : State K V) :
    state_after D0 (composed S U1 f1 U2 f2 svl1 svl2 s0) k =
        state_after σ0 (S.pfx f2) k ∨
      (state_after D0 (composed S U1 f1 U2 f2 svl1 svl2 s0) k = D0 k ∧
        state_after σ0 (S.pfx f2) k = none ∧
        (sc1 k → k ∉ svl1 (the_unit U1 f1 k)) ∧
        (sc2 k → k ∉ svl2 (the_unit U2 f2 k)) ∧
        evs_for k (S.win s0 f2) = []) := by
  obtain ⟨D1, hD1⟩ : ∃ D1, D1 = state_after D0 (emission S U1 f1 svl1 s0) :=
    ⟨_, rfl⟩
  have final : state_after D0 (composed S U1 f1 U2 f2 svl1 svl2 s0) k =
      state_after D1 (emission S U2 f2 svl2 f1) k := by
    rw [hD1, composed, state_after_append]
  have P_s0lo : ∀ u ∈ U1, S.cle s0 u.lo := s0lo
  have R_s0lo : ∀ u ∈ U2, S.cle f1 u.lo := H.f1_le_lo2
  have s0_f1 : S.cle s0 f1 := s0f1
  have f1_f2 : S.cle f1 f2 := H.f1_le_f2
  have win_split : evs_for k (S.win s0 f2) =
      evs_for k (S.win s0 f1) ++ evs_for k (S.win f1 f2) :=
    S.evs_for_win_split s0_f1 f1_f2 k
  by_cases k2 : sc2 k
  · -- The later read owns the key.
    have R_cut : sink_at S U2 f2 f2 k = state_after σ0 (S.pfx f2) k :=
      H.R.contract_cut k2
    rcases H.R.absent_replay_safe hsvl2 R_s0lo k2 D1 with
      hR | ⟨hRD, hRsink, -, nl2, mid_q⟩
    · left
      rw [final, hR, R_cut]
    · -- The read leaves the key as the pass left it.
      have fin_D1 : state_after D0 (composed S U1 f1 U2 f2 svl1 svl2 s0) k =
          D1 k := final.trans hRD
      have src_none : state_after σ0 (S.pfx f2) k = none :=
        R_cut.symm.trans hRsink
      have src_mid := H.src_quiet_mid mid_q
      by_cases k1 : sc1 k
      · have P_cut : sink_at S U1 f1 f1 k = state_after σ0 (S.pfx f1) k :=
          H.P.contract_cut k1
        rcases H.P.absent_replay_safe hsvl1 P_s0lo k1 D0 with
          hP | ⟨hPD, -, -, nl1, pass_q⟩
        · left
          rw [fin_D1, hD1, hP, P_cut, src_mid]
        · right
          have hD1k : D1 k = D0 k := by
            rw [hD1]
            exact hPD
          refine ⟨fin_D1.trans hD1k, src_none, fun _ => nl1, fun _ => nl2, ?_⟩
          rw [win_split, pass_q, mid_q, List.append_nil]
      · -- Outside the pass's scope, the pass replays the key's events.
        have D1_out : D1 k = state_after D0 (S.win s0 f1) k := by
          rw [hD1]
          exact H.P.emission_out_of_scope_replay hsvl1 s0_f1 k1 D0
        by_cases pass_q : evs_for k (S.win s0 f1) = []
        · right
          have hD1k : D1 k = D0 k := D1_out.trans (state_after_no_events pass_q D0)
          refine ⟨fin_D1.trans hD1k, src_none, fun h1 => absurd h1 k1,
            fun _ => nl2, ?_⟩
          rw [win_split, pass_q, mid_q, List.append_nil]
        · left
          rw [fin_D1, D1_out, win_last_src (σ0 := σ0) s0f1 pass_q D0, src_mid]
  · -- Only the pass owns the key, and the read replays the key's events.
    have k1 : sc1 k := hk.resolve_right k2
    have fin_win : state_after D0 (composed S U1 f1 U2 f2 svl1 svl2 s0) k =
        state_after D1 (S.win f1 f2) k :=
      final.trans (H.R.emission_out_of_scope_replay hsvl2 f1_f2 k2 D1)
    have P_cut : sink_at S U1 f1 f1 k = state_after σ0 (S.pfx f1) k :=
      H.P.contract_cut k1
    by_cases mid_q : evs_for k (S.win f1 f2) = []
    · have fin_D1 : state_after D0 (composed S U1 f1 U2 f2 svl1 svl2 s0) k =
          D1 k := fin_win.trans (state_after_no_events mid_q D1)
      have src_mid := H.src_quiet_mid mid_q
      rcases H.P.absent_replay_safe hsvl1 P_s0lo k1 D0 with
        hP | ⟨hPD, hPsink, -, nl1, pass_q⟩
      · left
        rw [fin_D1, hD1, hP, P_cut, src_mid]
      · right
        have hD1k : D1 k = D0 k := by
          rw [hD1]
          exact hPD
        refine ⟨fin_D1.trans hD1k, ?_, fun _ => nl1, fun h2 => absurd h2 k2, ?_⟩
        · rw [src_mid, ← P_cut]
          exact hPsink
        · rw [win_split, pass_q, mid_q, List.append_nil]
    · left
      exact fin_win.trans (win_last_src H.f1_le_f2 mid_q D1)

/-- Convergence of a pass followed by a later read: under coverage of
every key that the sink holds, that is absent at the read's frontier,
and that no log event from the pass's start to the read's frontier
mentions, the sink ends at the source state on both scopes. Isabelle:
`pass_then_read_converges`. -/
theorem pass_then_read_converges {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0f1 : S.den s0 ≤ S.den f1)
    (cover : ∀ k, (sc1 k ∨ sc2 k) → D0 k ≠ none →
      state_after σ0 (S.pfx f2) k = none → evs_for k (S.win s0 f2) = [] →
      (sc1 k ∧ k ∈ svl1 (the_unit U1 f1 k)) ∨
        (sc2 k ∧ k ∈ svl2 (the_unit U2 f2 k))) :
    ∀ k, (sc1 k ∨ sc2 k) →
      state_after D0 (composed S U1 f1 U2 f2 svl1 svl2 s0) k =
        state_after σ0 (S.pfx f2) k := by
  intro k hk
  rcases H.pass_then_read_safe hsvl1 hsvl2 s0lo s0f1 hk D0 with
    h | ⟨hD, hsrc, hn1, hn2, hq⟩
  · exact h
  · by_cases hD0 : D0 k = none
    · rw [hD, hD0, hsrc]
    · rcases cover k hk hD0 hsrc hq with ⟨h1, hl⟩ | ⟨h2, hl⟩
      · exact absurd hl (hn1 h1)
      · exact absurd hl (hn2 h2)

/-! ## A later read that lists its absent keys completes the pass -/

/-- A later read that lists every key it reads as absent and untouched
completes the pass when every key the pass leaves wrong, with no log
event up to the read's frontier, is in the read's scope. Isabelle:
`pass_then_request_converges`. -/
theorem pass_then_request_converges {svl1 svl2 : CUnit K V C → List K}
    {s0 : C} {D0 : State K V}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0f1 : S.den s0 ≤ S.den f1)
    (lists_absent : ∀ u ∈ U2, ∀ k, absent_untouched S u k → k ∈ svl2 u)
    (in_scope : ∀ k, sc1 k → D0 k ≠ none → sink_at S U1 f1 f1 k = none →
      k ∉ svl1 (the_unit U1 f1 k) → evs_for k (S.win s0 f2) = [] → sc2 k) :
    ∀ k, (sc1 k ∨ sc2 k) →
      state_after D0 (composed S U1 f1 U2 f2 svl1 svl2 s0) k =
        state_after σ0 (S.pfx f2) k := by
  refine H.pass_then_read_converges hsvl1 hsvl2 s0lo s0f1 ?_
  intro k hk held src_none quiet
  have s0_f1 : S.cle s0 f1 := s0f1
  have f1_f2 : S.cle f1 f2 := H.f1_le_f2
  have hsplit := S.evs_for_win_split s0_f1 f1_f2 k
  rw [quiet] at hsplit
  obtain ⟨-, mid_q⟩ := List.append_eq_nil_iff.mp hsplit.symm
  have src_f1 : state_after σ0 (S.pfx f1) k = none :=
    (H.src_quiet_mid mid_q).symm.trans src_none
  by_cases k2 : sc2 k
  · -- The read reads the key as absent and untouched, so it lists it.
    right
    refine ⟨k2, ?_⟩
    obtain ⟨u_in, k_dom⟩ := H.R.the_unit_props k2
    have lo_hi := H.R.bracket_lo_hi _ u_in
    have hi_f2 := H.R.bracket_hi_f _ u_in
    have f1_lo : S.cle f1 (the_unit U2 f2 k).lo := H.f1_le_lo2 _ u_in
    have lo_f2 : S.cle (the_unit U2 f2 k).lo f2 := S.cle_trans lo_hi hi_f2
    have lo_f2_q : evs_for k (S.win (the_unit U2 f2 k).lo f2) = [] := by
      have hs := S.evs_for_win_split f1_lo lo_f2 k
      rw [mid_q] at hs
      exact (List.append_eq_nil_iff.mp hs.symm).2
    have win_q : evs_for k
        (S.win (the_unit U2 f2 k).lo (the_unit U2 f2 k).hi) = [] := by
      have hs := S.evs_for_win_split lo_hi hi_f2 k
      rw [lo_f2_q] at hs
      exact (List.append_eq_nil_iff.mp hs.symm).1
    obtain ⟨c, c_lo, c_hi, honest⟩ := H.R.O2_honest _ u_in k k_dom
    have c_f2 : S.cle c f2 := S.cle_trans c_hi hi_f2
    have hr : (the_unit U2 f2 k).refresh k = none := by
      rw [honest, S.win_invariant_state c_lo c_f2 lo_f2_q σ0,
        ← S.win_invariant_state lo_f2 (S.cle_refl f2) lo_f2_q σ0]
      exact src_none
    exact lists_absent _ u_in k ⟨k_dom, hr, win_q⟩
  · -- Only the pass owns the key, so the pass lists it.
    left
    have k1 : sc1 k := hk.resolve_right k2
    refine ⟨k1, ?_⟩
    have sink_none : sink_at S U1 f1 f1 k = none :=
      (H.P.contract_cut k1).trans src_f1
    exact Classical.byContradiction fun hnl =>
      k2 (in_scope k k1 held sink_none hnl quiet)

/-- The keys a pass leaves wrong are exactly the unlisted keys of its
scope that the sink holds, that are absent at the pass's frontier, and
that no log event during the pass mentions. Isabelle:
`pass_leaves_wrong_iff`. -/
theorem pass_leaves_wrong_iff {svl1 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    {k : K} (k1 : sc1 k) (D0 : State K V) :
    state_after D0 (emission S U1 f1 svl1 s0) k ≠ sink_at S U1 f1 f1 k ↔
      (D0 k ≠ none ∧ sink_at S U1 f1 f1 k = none ∧
        k ∉ svl1 (the_unit U1 f1 k) ∧ evs_for k (S.win s0 f1) = []) := by
  have P_s0lo : ∀ u ∈ U1, S.cle s0 u.lo := s0lo
  constructor
  · intro wrong
    rcases H.P.absent_replay_safe hsvl1 P_s0lo k1 D0 with
      h | ⟨hD, hsink, -, hnl, hq⟩
    · exact absurd h wrong
    · refine ⟨fun hD0 => wrong ?_, hsink, hnl, hq⟩
      rw [hD, hsink, hD0]
  · rintro ⟨held, hsink, hnl, hq⟩ heq
    rw [H.P.unlisted_quiet_key_kept hsvl1 P_s0lo k1 hnl hq D0, hsink] at heq
    exact held heq

/-- A key-list request completes a pass. The request reads each
requested key at its own coordinate `rc k` between the two frontiers
(a request that runs in batches reads each batch at its own
coordinate), its scope holds every requested key that is absent where
it reads it, and every key the pass leaves wrong was requested. Then
the sink ends at the source state on both scopes. Isabelle:
`request_after_pass_converges`, whose set of requested keys `K` is the
predicate `req` here, since `K` names the key type in the port. -/
theorem request_after_pass_converges {svl1 svl2 : CUnit K V C → List K}
    {s0 : C} {D0 : State K V} {req : K → Prop} {rc : K → C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0f1 : S.den s0 ≤ S.den f1)
    (lists_absent : ∀ u ∈ U2, ∀ k, absent_untouched S u k → k ∈ svl2 u)
    (f1_rc : ∀ k, req k → S.den f1 ≤ S.den (rc k))
    (rc_f2 : ∀ k, req k → S.den (rc k) ≤ S.den f2)
    (sc2_abs : ∀ k, req k → state_after σ0 (S.pfx (rc k)) k = none → sc2 k)
    (asked : ∀ k, sc1 k →
      state_after D0 (emission S U1 f1 svl1 s0) k ≠ sink_at S U1 f1 f1 k →
      req k) :
    ∀ k, (sc1 k ∨ sc2 k) →
      state_after D0 (composed S U1 f1 U2 f2 svl1 svl2 s0) k =
        state_after σ0 (S.pfx f2) k := by
  have P_s0lo : ∀ u ∈ U1, S.cle s0 u.lo := s0lo
  refine H.pass_then_request_converges hsvl1 hsvl2 s0lo s0f1 lists_absent ?_
  intro k k1 held sink_none nl quiet
  have s0_f1 : S.cle s0 f1 := s0f1
  have f1_f2 : S.cle f1 f2 := H.f1_le_f2
  have hsplit := S.evs_for_win_split s0_f1 f1_f2 k
  rw [quiet] at hsplit
  obtain ⟨pass_q, mid_q⟩ := List.append_eq_nil_iff.mp hsplit.symm
  have kept := H.P.unlisted_quiet_key_kept hsvl1 P_s0lo k1 nl pass_q D0
  have wrong : state_after D0 (emission S U1 f1 svl1 s0) k ≠
      sink_at S U1 f1 f1 k := by
    rw [kept, sink_none]
    exact held
  have kK : req k := asked k k1 wrong
  have hrc : state_after σ0 (S.pfx (rc k)) k = none := by
    rw [S.win_invariant_state (f1_rc k kK) (rc_f2 k kK) mid_q σ0,
      ← H.P.contract_cut k1]
    exact sink_none
  exact sc2_abs k kK hrc

end PassThenRead

end

end DBLogContract
