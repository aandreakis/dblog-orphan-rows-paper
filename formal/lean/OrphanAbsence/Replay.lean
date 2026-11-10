import OrphanAbsence.Emission

/-!
# Safety, convergence, and coverage from an arbitrary sink state

This file ports the subsections of `Orphan_Absence.thy` that replay
the widened emission from an arbitrary initial sink state `D0`.

* `absent_replay_safe`: for every admissible enumeration and every
  initial state, each scoped key either agrees with the canonical
  replay at the frontier, or it is an absent untouched key that was
  not enumerated and has no consumed event, whose sink value is left
  as it was (a surviving orphan). No other outcome exists: no
  wrong value, no deleted live row.
* `absent_replay`, `absent_replay_cut`: under per-key coverage the
  replay is the canonical replay, and by the cut theorem the source
  state at the frontier.
* `covers`, `self_stabilization`: when the enumeration covers every
  absent untouched key that the sink holds, the replay from `D0`
  equals the source state at the frontier on the whole scope.
* `svl2_exists_covering`, `range_record_converges`: for a sink with
  finitely many rows and finitely many survivors per unit, a covering
  enumeration exists (the sink-expanded range record).
* `partial_enumeration_safe`: a key that is listed, or that the sink
  does not hold, converges, whatever else the enumeration misses.
* `unlisted_quiet_key_kept`, `coverage_necessary`: an unlisted key
  with no consumed event keeps its initial value, so coverage is
  necessary as well as sufficient.
* `sink_read_covers`: a complete sink read taken at a consumed
  position before the frontier provides coverage.

Finiteness transport: HOL's `finite A` holds exactly when `A` is the
set of some list. An assumption `finite {k. P k}` is therefore stated as
the existence of a listing `∃ xs, ∀ k, k ∈ xs ↔ P k`, the same
statement in a logic without a set library, as recorded in
`VERIFICATION.md`.
-/

namespace DBLogContract

universe u v w

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-- Coverage: every absent untouched key that the sink holds, and for
which the consumed stream carries no event, is enumerated by its
unit. Isabelle: `covers`. -/
def covers (S : CoordinateSpace K V C) (units : List (CUnit K V C)) (f : C)
    (svl : CUnit K V C → List K) (D0 : State K V) (s0 : C) : Prop :=
  ∀ u ∈ units, ∀ k, absent_untouched S u k → D0 k ≠ none →
    evs_for k (S.win s0 f) = [] → k ∈ svl u

/-- Every listing has a duplicate-free listing with the same members.
Port-local. It stands where the Isabelle proof of
`svl2_exists_covering` uses `finite_distinct_list`. -/
theorem exists_nodup_listing {α : Type _} (xs : List α) :
    ∃ ys : List α, ys.Nodup ∧ ∀ a, a ∈ ys ↔ a ∈ xs := by
  induction xs with
  | nil => exact ⟨[], List.nodup_nil, fun _ => Iff.rfl⟩
  | cons x xs ih =>
    obtain ⟨ys, hnd, hmem⟩ := ih
    by_cases hx : x ∈ ys
    · refine ⟨ys, hnd, fun a => ?_⟩
      rw [List.mem_cons, ← hmem]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · rw [h]
          exact hx
        · exact h
    · refine ⟨x :: ys, List.nodup_cons.mpr ⟨hx, hnd⟩, fun a => ?_⟩
      rw [List.mem_cons, List.mem_cons, hmem]

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

/-! ## Safety: any admissible enumeration, any initial state -/

/-- Safety. For every scoped key the replay of the widened emission
from an arbitrary initial state `D0` either equals the canonical
replay at the frontier, or the key is an absent untouched key that
was not enumerated and has no consumed event, and the sink keeps
whatever it held. Nothing else can happen. Isabelle:
`absent_replay_safe`. -/
theorem absent_replay_safe {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k) (D0 : State K V) :
    state_after D0 (emission S units f svl s0) k = sink_at S units f f k ∨
      (state_after D0 (emission S units f svl s0) k = D0 k ∧
        sink_at S units f f k = none ∧
        absent_untouched S (the_unit units f k) k ∧
        k ∉ svl (the_unit units f k) ∧
        evs_for k (S.win s0 f) = []) := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  have hs0lo : S.cle s0 (the_unit units f k).lo := hs0 _ u_in
  have hlohi : S.cle (the_unit units f k).lo (the_unit units f k).hi :=
    H.bracket_lo_hi _ u_in
  have hhif : S.cle (the_unit units f k).hi f := H.bracket_hi_f _ u_in
  have hlof : S.cle (the_unit units f k).lo f := S.cle_trans hlohi hhif
  have estream := evs_emission_master2 H hsvl hs0 hk
  -- The window decompositions every case reads off.
  have hA : evs_for k (S.win s0 (the_unit units f k).hi) =
      evs_for k (S.win s0 (the_unit units f k).lo)
      ++ evs_for k (S.win (the_unit units f k).lo (the_unit units f k).hi) :=
    S.evs_for_win_split hs0lo hlohi k
  have hWin : evs_for k (S.win (the_unit units f k).lo f) =
      evs_for k (S.win (the_unit units f k).lo (the_unit units f k).hi)
      ++ evs_for k (S.win (the_unit units f k).hi f) :=
    S.evs_for_win_split hlohi hhif k
  have hAll : evs_for k (S.win s0 f) =
      evs_for k (S.win s0 (the_unit units f k).lo)
      ++ evs_for k (S.win (the_unit units f k).lo f) :=
    S.evs_for_win_split hs0lo hlof k
  by_cases hW : evs_for k (S.win (the_unit units f k).lo f) = []
  · -- No event for the key from the low edge on: the canonical replay
    -- returns the refresh verdict.
    have hM : evs_for k
        (S.win (the_unit units f k).lo (the_unit units f k).hi) = [] := by
      rw [hWin] at hW
      exact (List.append_eq_nil_iff.mp hW).1
    have hW2 : evs_for k (S.win (the_unit units f k).hi f) = [] := by
      rw [hWin] at hW
      exact (List.append_eq_nil_iff.mp hW).2
    have hsink : sink_at S units f f k = (the_unit units f k).refresh k := by
      simp only [sink_at]
      rw [dif_pos hW]
    by_cases hks : k ∈ svl (the_unit units f k)
    · -- Listed: the entry is the key's last stream item.
      left
      have hstream : evs_for k (emission S units f svl s0) =
          evs_for k (S.win s0 (the_unit units f k).hi)
          ++ [⟨k, (the_unit units f k).refresh k⟩] := by
        rw [estream, if_pos hks, hW2]
        simp
      have hne : evs_for k (emission S units f svl s0) ≠ [] := by
        rw [hstream]
        simp
      rw [hsink, state_after_last_event hne D0, getLast_eq_of_eq hstream,
          List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast_singleton]
    · -- Not listed: the verdict is absent, since a present verdict
      -- would make the key a survivor, and survivors are listed.
      have hr : (the_unit units f k).refresh k = none := by
        refine Classical.byContradiction fun hr => hks ?_
        exact svl2_surv hsvl u_in ⟨k_dom, hr, hM⟩
      have hstream : evs_for k (emission S units f svl s0) =
          evs_for k (S.win s0 (the_unit units f k).lo) := by
        rw [estream, if_neg hks, hA, hM, hW2]
        simp
      by_cases hP : evs_for k (S.win s0 (the_unit units f k).lo) = []
      · -- No consumed event at all: the sink keeps its initial value.
        right
        refine ⟨state_after_no_events (hstream.trans hP) D0, hsink.trans hr,
          ⟨k_dom, hr, hM⟩, hks, ?_⟩
        rw [hAll, hP, hW, List.append_nil]
      · -- A consumed event before the low edge: by O2 its image is
        -- the absent verdict, so the stream ends on a delete.
        left
        obtain ⟨c, c_lo, c_hi, honest⟩ := H.O2_honest _ u_in k k_dom
        have hs0c : S.cle s0 c := S.cle_trans hs0lo c_lo
        have hMc : evs_for k (S.win (the_unit units f k).lo c) = [] := by
          have hsp := S.evs_for_win_split c_lo c_hi k
          rw [hM] at hsp
          exact (List.append_eq_nil_iff.mp hsp.symm).1
        have hpfx : evs_for k (S.pfx c) =
            evs_for k (S.pfx s0)
            ++ evs_for k (S.win s0 (the_unit units f k).lo) := by
          rw [S.evs_for_pfx_split hs0c k,
              S.evs_for_win_split hs0lo c_lo k, hMc, List.append_nil]
        have hpfx_ne : evs_for k (S.pfx c) ≠ [] := by
          rw [hpfx]
          intro h
          exact hP (List.append_eq_nil_iff.mp h).2
        have himg : ((evs_for k (S.win s0
            (the_unit units f k).lo)).getLast hP).img = none := by
          have hnone : state_after σ0 (S.pfx c) k = none :=
            honest.symm.trans hr
          rw [state_after_last_event hpfx_ne σ0,
              getLast_eq_of_eq hpfx,
              List.getLast_append_of_ne_nil _ hP] at hnone
          exact hnone
        have hne_em : evs_for k (emission S units f svl s0) ≠ [] := by
          rw [hstream]
          exact hP
        rw [hsink, hr, state_after_last_event hne_em D0,
            getLast_eq_of_eq hstream]
        exact himg
  · -- Some event for the key from the low edge on: the last such
    -- event decides both sides.
    left
    have hsink : sink_at S units f f k =
        ((evs_for k (S.win (the_unit units f k).lo f)).getLast hW).img := by
      simp only [sink_at]
      rw [dif_neg hW]
    by_cases hW2 : evs_for k (S.win (the_unit units f k).hi f) = []
    · -- The last such event is inside the window, so the key is
      -- touched there and therefore not listed.
      have hM : evs_for k
          (S.win (the_unit units f k).lo (the_unit units f k).hi) ≠ [] := by
        intro hM
        apply hW
        rw [hWin, hM, hW2, List.append_nil]
      have hks : k ∉ svl (the_unit units f k) := fun hks =>
        hM (svl2_untouched hsvl u_in hks)
      have hstream : evs_for k (emission S units f svl s0) =
          evs_for k (S.win s0 (the_unit units f k).lo)
          ++ evs_for k (S.win (the_unit units f k).lo
            (the_unit units f k).hi) := by
        rw [estream, if_neg hks, hW2, hA]
        simp
      have hwin : evs_for k (S.win (the_unit units f k).lo f) =
          evs_for k (S.win (the_unit units f k).lo
            (the_unit units f k).hi) := by
        rw [hWin, hW2, List.append_nil]
      have hne_em : evs_for k (emission S units f svl s0) ≠ [] := by
        rw [hstream]
        intro h
        exact hM (List.append_eq_nil_iff.mp h).2
      rw [hsink, state_after_last_event hne_em D0, getLast_eq_of_eq hstream,
          List.getLast_append_of_ne_nil _ hM, getLast_eq_of_eq hwin]
    · -- An event beyond the high edge: the last such event decides
      -- both sides, and the enumerated entry, if any, precedes it.
      have hne_em : evs_for k (emission S units f svl s0) ≠ [] := by
        rw [estream]
        intro h
        exact hW2 (List.append_eq_nil_iff.mp h).2
      rw [hsink, state_after_last_event hne_em D0, getLast_eq_of_eq estream,
          List.getLast_append_of_ne_nil _ hW2, getLast_eq_of_eq hWin,
          List.getLast_append_of_ne_nil _ hW2]

/-! ## Convergence under coverage -/

/-- Convergence for one key under per-key coverage: if the key is
enumerated whenever the sink holds it, it is absent untouched, and
the consumed stream carries no event for it, then the replay from
`D0` is the canonical replay at the frontier. Isabelle:
`absent_replay`. -/
theorem absent_replay {svl : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k)
    (cover : D0 k ≠ none → absent_untouched S (the_unit units f k) k →
      evs_for k (S.win s0 f) = [] → k ∈ svl (the_unit units f k)) :
    state_after D0 (emission S units f svl s0) k = sink_at S units f f k := by
  rcases H.absent_replay_safe hsvl hs0 hk D0 with h | ⟨hD, hsink, habs, hks, hq⟩
  · exact h
  · by_cases hD0 : D0 k = none
    · rw [hD, hsink, hD0]
    · exact absurd (cover hD0 habs hq) hks

/-- The same, composed with the cut theorem: under per-key coverage
the replay from `D0` is the source state at the frontier. Isabelle:
`absent_replay_cut`. -/
theorem absent_replay_cut {svl : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k)
    (cover : D0 k ≠ none → absent_untouched S (the_unit units f k) k →
      evs_for k (S.win s0 f) = [] → k ∈ svl (the_unit units f k)) :
    state_after D0 (emission S units f svl s0) k =
      state_after σ0 (S.pfx f) k :=
  (H.absent_replay hsvl hs0 hk cover).trans (H.contract_cut hk)

/-- Self-stabilization: under coverage the replay of the widened
emission from an arbitrary initial state equals the source state at
the frontier on the whole scope. Isabelle: `self_stabilization`. -/
theorem self_stabilization {svl : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    (cov : covers S units f svl D0 s0) :
    ∀ k, scope k →
      state_after D0 (emission S units f svl s0) k =
        state_after σ0 (S.pfx f) k := by
  intro k hk
  obtain ⟨u_in, -⟩ := H.the_unit_props hk
  exact H.absent_replay_cut hsvl hs0 hk
    (fun hD habs hq => cov _ u_in k habs hD hq)

/-! ## Existence: the sink-expanded enumeration -/

omit H in
/-- A sink with finitely many rows, and finitely many survivors per
unit, admits a covering admissible enumeration: list the survivors
together with the absent untouched keys the sink holds. This is the
range record as the sink applies it. Isabelle: `svl2_exists_covering`,
whose assumptions `finite (survivors u)` and `finite {k. D0 k ≠ None}`
are stated as listings (finiteness transport, see the module docstring). -/
theorem svl2_exists_covering {D0 : State K V} {s0 : C}
    (fin_surv : ∀ u ∈ units, ∃ xs : List K, ∀ k, k ∈ xs ↔ survivors S u k)
    (fin_sink : ∃ ys : List K, ∀ k, k ∈ ys ↔ D0 k ≠ none) :
    ∃ svl : CUnit K V C → List K,
      svl_ok2 S units svl ∧ covers S units f svl D0 s0 := by
  obtain ⟨ys, hys⟩ := fin_sink
  have hlist : ∀ u ∈ units, ∃ zs : List K, zs.Nodup ∧ ∀ k, k ∈ zs ↔
      (survivors S u k ∨ (absent_untouched S u k ∧ D0 k ≠ none)) := by
    intro u hu
    obtain ⟨xs, hxs⟩ := fin_surv u hu
    obtain ⟨zs, hnd, hzs⟩ := exists_nodup_listing
      (xs ++ ys.filter (fun k => decide (absent_untouched S u k)))
    refine ⟨zs, hnd, fun k => ?_⟩
    rw [hzs, List.mem_append, List.mem_filter, hxs, hys, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h2, h1⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h2, h1⟩
  refine ⟨fun u => if h : ∃ zs : List K, zs.Nodup ∧ ∀ k, k ∈ zs ↔
      (survivors S u k ∨ (absent_untouched S u k ∧ D0 k ≠ none))
      then h.choose else [], ?_, ?_⟩
  · intro u hu
    have hex := hlist u hu
    dsimp only
    rw [dif_pos hex]
    obtain ⟨hnd, hmem⟩ := hex.choose_spec
    refine ⟨hnd, fun k hs => (hmem k).mpr (Or.inl hs), fun k hk => ?_⟩
    rcases (hmem k).mp hk with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro u hu k habs hD _
    have hex := hlist u hu
    dsimp only
    rw [dif_pos hex]
    exact (hex.choose_spec.2 k).mpr (Or.inr ⟨habs, hD⟩)

/-- The range record converges: for a sink with finitely many rows,
and finitely many survivors per unit, there is an admissible
enumeration whose emission, replayed from the sink's state, equals the
source state at the frontier on the whole scope. Isabelle:
`range_record_converges` (finiteness transport, see the module docstring). -/
theorem range_record_converges {D0 : State K V} {s0 : C}
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    (fin_surv : ∀ u ∈ units, ∃ xs : List K, ∀ k, k ∈ xs ↔ survivors S u k)
    (fin_sink : ∃ ys : List K, ∀ k, k ∈ ys ↔ D0 k ≠ none) :
    ∃ svl : CUnit K V C → List K, svl_ok2 S units svl ∧
      ∀ k, scope k →
        state_after D0 (emission S units f svl s0) k =
          state_after σ0 (S.pfx f) k := by
  obtain ⟨svl, hok, hcov⟩ :=
    svl2_exists_covering (f := f) (s0 := s0) fin_surv fin_sink
  exact ⟨svl, hok, H.self_stabilization hok hs0 hcov⟩

/-! ## Partial enumerations: completeness equals coverage -/

/-- A connector that lists candidates from a stale or partial sink
read: every key that is listed, or that the sink does not hold,
converges to the source state at the frontier. Together with
`absent_replay_safe`, every live row is kept and the only keys left
wrong are orphans the read did not report. Isabelle:
`partial_enumeration_safe`. -/
theorem partial_enumeration_safe {svl : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k)
    (listed_or_clear : k ∈ svl (the_unit units f k) ∨ D0 k = none) :
    state_after D0 (emission S units f svl s0) k =
      state_after σ0 (S.pfx f) k :=
  H.absent_replay_cut hsvl hs0 hk
    (fun hD _ _ => listed_or_clear.resolve_right hD)

/-! ## Unlisted quiet keys are left alone, and coverage is necessary -/

/-- An unlisted key with no consumed event keeps its initial sink
value. Isabelle: `unlisted_quiet_key_kept`. -/
theorem unlisted_quiet_key_kept {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k)
    (unlisted : k ∉ svl (the_unit units f k))
    (quiet : evs_for k (S.win s0 f) = []) (D0 : State K V) :
    state_after D0 (emission S units f svl s0) k = D0 k := by
  obtain ⟨u_in, -⟩ := H.the_unit_props hk
  have hs0hi : S.cle s0 (the_unit units f k).hi :=
    S.cle_trans (hs0 _ u_in) (H.bracket_lo_hi _ u_in)
  have hsplit := S.evs_for_win_split hs0hi (H.bracket_hi_f _ u_in) k
  rw [quiet] at hsplit
  obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp hsplit.symm
  have hnil : evs_for k (emission S units f svl s0) = [] := by
    rw [evs_emission_master2 H hsvl hs0 hk, if_neg unlisted, h1, h2]
    simp
  exact state_after_no_events hnil D0

/-- Coverage is necessary: if the replay from `D0` converges on the
whole scope, the enumeration covers every absent untouched key that
the sink holds and that the consumed stream leaves untouched.
Isabelle: `coverage_necessary`. -/
theorem coverage_necessary {svl : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    (conv : ∀ k, scope k →
      state_after D0 (emission S units f svl s0) k =
        state_after σ0 (S.pfx f) k) :
    covers S units f svl D0 s0 := by
  intro u hu k habs hD quiet
  obtain ⟨k_dom, hr, -⟩ := habs
  have k_sc : scope k := H.dom_sub_scope hu k_dom
  have u_eq : the_unit units f k = u := H.the_unit_eq hu k_dom
  have hlof : S.cle u.lo f :=
    S.cle_trans (H.bracket_lo_hi u hu) (H.bracket_hi_f u hu)
  have hsplit := S.evs_for_win_split (hs0 u hu) hlof k
  rw [quiet] at hsplit
  have quiet_lo : evs_for k (S.win u.lo f) = [] :=
    (List.append_eq_nil_iff.mp hsplit.symm).2
  have src_none : state_after σ0 (S.pfx f) k = none := by
    rw [← H.contract_cut k_sc]
    simp only [sink_at]
    rw [u_eq, dif_pos quiet_lo]
    exact hr
  refine Classical.byContradiction fun hks => ?_
  have hkept := H.unlisted_quiet_key_kept hsvl hs0 k_sc
    (by rw [u_eq]; exact hks) quiet D0
  have hconv := conv k k_sc
  rw [hkept, src_none] at hconv
  exact hD hconv

omit H in
/-- A complete sink read, taken at any consumed position `g u`
between the consumption start and the frontier, provides coverage:
a key the sink holds at that position with no consumed event is
still at its initial value, so the read reports it. Isabelle:
`sink_read_covers`. -/
theorem sink_read_covers {svl : CUnit K V C → List K} {s0 : C}
    {D0 : State K V} {g : CUnit K V C → C}
    (g_ok : ∀ u ∈ units, S.cle s0 (g u) ∧ S.cle (g u) f)
    (rd : ∀ u k, u ∈ units → absent_untouched S u k →
      state_after D0 (S.win s0 (g u)) k ≠ none → k ∈ svl u) :
    covers S units f svl D0 s0 := by
  intro u hu k habs hD quiet
  obtain ⟨hs0g, hgf⟩ := g_ok u hu
  have hsplit := S.evs_for_win_split hs0g hgf k
  rw [quiet] at hsplit
  have hq : evs_for k (S.win s0 (g u)) = [] :=
    (List.append_eq_nil_iff.mp hsplit.symm).1
  apply rd u k hu habs
  rw [state_after_no_events hq D0]
  exact hD

end CaptureContract

end

end DBLogContract
