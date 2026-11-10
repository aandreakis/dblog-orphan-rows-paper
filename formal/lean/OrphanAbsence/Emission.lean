import DBLogContract.MergeDisciplines

/-!
# Admissible enumerations and the widened emission

This file ports the first two subsections of `Orphan_Absence.thy`
from the Isabelle session `Orphan_Absence`, which builds on the
Generalized DBLog contract core ported in `DBLogContract`. Nothing in
the core is modified. This file only imports it.

The window-discard discipline of the core emits, at a unit's high
edge, one entry `⟨k, u.refresh k⟩` per enumerated key, and the core
enumerates exactly the survivors: keys read as present and untouched
inside the bracket. Absence is then represented by omission, which is
sound only for a replay that starts from the empty state. The
`Orphan_Absence` session widens the enumeration: a key read as absent
and untouched inside the bracket may also be listed, and its entry
`⟨k, none⟩` is an explicit absence (the absent event, or, expanded at
the sink, the range record).

* `replay_per_key`: replay depends on a key's own events only, from
  any initial state, so a keyed absent event needs only per-key order.
* `absent_untouched` and `svl_ok2`: the absent untouched keys of a
  unit and the admissible enumerations, which list every survivor and
  nothing outside the survivors and the absent untouched keys.
* `titems_close_block2`, `titems_closes_at2`,
  `titems_emission_master2`: the per-key shape of the widened
  emission. It is the shape of the core's Lemma 6.1, now under the
  widened enumeration.

The port follows the conventions of `DBLogContract`, recorded in its
`VERIFICATION.md`: sets of keys are predicates, the logic is
classical, and the definitions are noncomputable.
-/

namespace DBLogContract

universe u v w

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-! ## Replay depends on a key's own events only -/

/-- Per-key transport neutrality: two emitted streams with the same
events for `k` replay to the same value at `k`, from any initial
state. A keyed absent event therefore needs only per-key order.
Isabelle: `replay_per_key`. -/
theorem replay_per_key {k : K} {Sq' Sq : List (Event K V)}
    (h : evs_for k Sq' = evs_for k Sq) (D0 : State K V) :
    state_after D0 Sq' k = state_after D0 Sq k := by
  by_cases he : evs_for k Sq = []
  · rw [state_after_no_events (h.trans he) D0, state_after_no_events he D0]
  · have he' : evs_for k Sq' ≠ [] := fun h0 => he (h.symm.trans h0)
    rw [state_after_last_event he' D0, state_after_last_event he D0,
      getLast_eq_of_eq h he']

/-! ## Admissible enumerations -/

/-- The absent untouched keys of a unit: keys of its domain that the
refresh reports absent and that its own window leaves untouched.
Isabelle: `absent_untouched`, stated there as a set. -/
def absent_untouched (S : CoordinateSpace K V C) (u : CUnit K V C) :
    K → Prop :=
  fun k => u.dom k ∧ u.refresh k = none ∧
    evs_for k (S.win u.lo u.hi) = []

/-- An admissible enumeration: for every unit of the family, a
duplicate-free listing that contains every survivor and nothing
outside the survivors and the absent untouched keys. Isabelle:
`svl_ok2`, whose two set inclusions are stated here pointwise. -/
def svl_ok2 (S : CoordinateSpace K V C) (units : List (CUnit K V C))
    (svl : CUnit K V C → List K) : Prop :=
  ∀ u ∈ units, (svl u).Nodup ∧
    (∀ k, survivors S u k → k ∈ svl u) ∧
    (∀ k, k ∈ svl u → survivors S u k ∨ absent_untouched S u k)

/-- Survivors lie in the unit's domain. Isabelle: `survivors_sub_dom`
of `Merge_Disciplines.thy`. The Lean core does not carry it, so it is
stated here. -/
theorem survivors_sub_dom {S : CoordinateSpace K V C} {u : CUnit K V C}
    {k : K} (h : survivors S u k) : u.dom k :=
  h.1

/-- Absent untouched keys lie in the unit's domain. Isabelle:
`absent_untouched_sub_dom`. -/
theorem absent_untouched_sub_dom {S : CoordinateSpace K V C}
    {u : CUnit K V C} {k : K} (h : absent_untouched S u k) : u.dom k :=
  h.1

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

omit H in
/-- The core's survivor enumerations are admissible. Isabelle:
`svl_ok_imp_ok2`. -/
theorem svl_ok_imp_ok2 {svl : CUnit K V C → List K}
    (hsvl : svl_ok S units svl) : svl_ok2 S units svl := by
  intro u hu
  obtain ⟨hnd, hmem⟩ := hsvl u hu
  exact ⟨hnd, fun k hk => (hmem k).mpr hk,
    fun k hk => Or.inl ((hmem k).mp hk)⟩

omit H in
/-- An admissible listing is duplicate-free. Isabelle:
`svl2_distinct`. -/
theorem svl2_distinct {svl : CUnit K V C → List K}
    (hsvl : svl_ok2 S units svl) {u : CUnit K V C} (hu : u ∈ units) :
    (svl u).Nodup :=
  (hsvl u hu).1

omit H in
/-- An admissible listing stays inside the unit's domain. Isabelle:
`svl2_sub_dom`, stated there as set inclusion. -/
theorem svl2_sub_dom {svl : CUnit K V C → List K}
    (hsvl : svl_ok2 S units svl) {u : CUnit K V C} (hu : u ∈ units)
    {k : K} (hk : k ∈ svl u) : u.dom k := by
  rcases (hsvl u hu).2.2 k hk with h | h
  · exact survivors_sub_dom h
  · exact absent_untouched_sub_dom h

omit H in
/-- Every listed key is untouched by its unit's own window.
Isabelle: `svl2_untouched`. -/
theorem svl2_untouched {svl : CUnit K V C → List K}
    (hsvl : svl_ok2 S units svl) {u : CUnit K V C} (hu : u ∈ units)
    {k : K} (hk : k ∈ svl u) : evs_for k (S.win u.lo u.hi) = [] := by
  rcases (hsvl u hu).2.2 k hk with h | h
  · exact h.2.2
  · exact h.2.2

omit H in
/-- Every survivor is listed. Isabelle: `svl2_surv`. -/
theorem svl2_surv {svl : CUnit K V C → List K}
    (hsvl : svl_ok2 S units svl) {u : CUnit K V C} (hu : u ∈ units)
    {k : K} (hk : survivors S u k) : k ∈ svl u :=
  (hsvl u hu).2.1 k hk

/-! ## Per-key characterization of the widened emission -/

omit H in
/-- The per-key content of one close block under an admissible
enumeration. Isabelle: `titems_close_block2`. -/
theorem titems_close_block2 {svl : CUnit K V C → List K}
    (hsvl : svl_ok2 S units svl) {u : CUnit K V C} (hu : u ∈ units) (k : K) :
    titems_for k (close_block S svl u) =
      if k ∈ svl u then [(S.den u.hi, ⟨k, u.refresh k⟩)] else [] := by
  have hnd : (svl u).Nodup := svl2_distinct hsvl hu
  simp only [titems_for, close_block, List.filter_map]
  have hpred : ((fun x : Nat × Event K V => decide (x.2.key = k)) ∘
      fun k' => ((S.den u.hi, ⟨k', u.refresh k'⟩) : Nat × Event K V)) =
      fun k' => decide (k' = k) := by
    funext k'
    rfl
  rw [hpred, nodup_filter_eq hnd k]
  by_cases hk : k ∈ svl u
  · rw [if_pos hk, if_pos hk]
    rfl
  · rw [if_neg hk, if_neg hk]
    rfl

/-- The per-key content of the close blocks due at one position under
an admissible enumeration: only the owning unit can contribute, and
only at its own high edge. Isabelle: `titems_closes_at2`. -/
theorem titems_closes_at2 {svl : CUnit K V C → List K}
    (hsvl : svl_ok2 S units svl) {k : K} (hk : scope k) (p : Nat) :
    titems_for k (closes_at S units svl p) =
      if S.den (the_unit units f k).hi = p ∧ k ∈ svl (the_unit units f k)
      then [(p, ⟨k, (the_unit units f k).refresh k⟩)] else [] := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  obtain ⟨i₀, hi₀, hgi₀⟩ := List.mem_iff_getElem.mp u_in
  have hmem : ((the_unit units f k, i₀) : CUnit K V C × Nat) ∈
      units.zipIdx := by
    rw [List.mem_iff_getElem]
    refine ⟨i₀, by rw [List.length_zipIdx]; exact hi₀, ?_⟩
    rw [List.getElem_zipIdx, Nat.zero_add]
    exact congrArg (fun u => (u, i₀)) hgi₀
  have hvanish : ∀ ui ∈ units.zipIdx,
      ui ≠ (the_unit units f k, i₀) →
      titems_for k (if S.den ui.1.hi = p
        then close_block S svl ui.1 else []) = [] := by
    rintro ⟨u, i⟩ hui hne
    obtain ⟨-, hilen, hgot⟩ := List.mem_zipIdx hui
    by_cases hc : S.den u.hi = p
    · rw [if_pos hc]
      have hu_in : u ∈ units := by
        rw [hgot]
        exact List.getElem_mem _
      rw [titems_close_block2 hsvl hu_in k]
      by_cases hks : k ∈ svl u
      · exfalso
        have hdom : u.dom k := svl2_sub_dom hsvl hu_in hks
        have hueq : u = the_unit units f k :=
          H.covering_unit_unique hu_in hdom u_in k_dom
        have hieq : i = i₀ := by
          have hgot' : units[i]'(by omega) = u := by
            have hg := hgot
            simp only [Nat.sub_zero] at hg
            exact hg.symm
          exact H.the_unit_position_unique hk
            (i := i) (j := i₀) (by omega) (hgot'.trans hueq) hi₀ hgi₀
        exact hne (by rw [hueq, hieq])
      · rw [if_neg hks]
    · rw [if_neg hc]
      rfl
  have hflat : titems_for k (closes_at S units svl p) =
      titems_for k (if S.den (the_unit units f k).hi = p
        then close_block S svl (the_unit units f k) else []) := by
    simp only [closes_at, titems_for, List.filter_flatMap]
    rw [flatMap_single (nodup_zipIdx units 0) hmem]
    intro x hx hne
    exact hvanish x hx hne
  rw [hflat]
  by_cases hc : S.den (the_unit units f k).hi = p
  · rw [if_pos hc, titems_close_block2 hsvl u_in k]
    by_cases hks : k ∈ svl (the_unit units f k)
    · rw [if_pos hks, if_pos ⟨hc, hks⟩, hc]
    · rw [if_neg hks, if_neg (fun h => hks h.2)]
  · rw [if_neg hc, if_neg (fun h => hc h.1)]
    rfl

/-- The master per-key characterization of the widened emission. A
key's occurrences are first its consumed events before its unit's
high edge, in commit order. Then, exactly if the key is enumerated,
comes one entry carrying the unit's refresh verdict, tagged with the
close position (a row for a survivor, an absent event for an absent
untouched key). Last come its events beyond the high edge, in commit
order. Isabelle: `titems_emission_master2`, whose position-list
normal form `map (λp. (Suc p, L ! p)) (kposs k a b)` is here the
per-key filter of the tagged segment, as in the core's
`titems_emission_master`. -/
theorem titems_emission_master2 {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k) :
    titems_for k (emission_t S units f svl s0) =
      titems_for k (tagged_seg S (S.den s0) (S.den (the_unit units f k).hi))
      ++ (if k ∈ svl (the_unit units f k)
          then [(S.den (the_unit units f k).hi,
                 ⟨k, (the_unit units f k).refresh k⟩)] else [])
      ++ titems_for k
          (tagged_seg S (S.den (the_unit units f k).hi) (S.den f)) := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  have hs0lo : S.den s0 ≤ S.den (the_unit units f k).lo := hs0 _ u_in
  have hlohi : S.den (the_unit units f k).lo ≤
      S.den (the_unit units f k).hi := H.bracket_lo_hi _ u_in
  have hhif : S.den (the_unit units f k).hi ≤ S.den f :=
    H.bracket_hi_f _ u_in
  have hflen : S.den f ≤ S.log.length := S.den_le_len f
  have hs0hp : S.den s0 ≤ S.den (the_unit units f k).hi :=
    Nat.le_trans hs0lo hlohi
  have hhplen : S.den (the_unit units f k).hi ≤ S.log.length :=
    Nat.le_trans hhif hflen
  have hsplit := seg_split S hs0hp hhif hflen
  have hlenA : ((S.log.take (S.den (the_unit units f k).hi)).drop
      (S.den s0)).length = S.den (the_unit units f k).hi - S.den s0 :=
    seg_length S hhplen
  have hAvanish : ∀ ep ∈ ((S.log.take (S.den (the_unit units f k).hi)).drop
      (S.den s0)).zipIdx (S.den s0),
      titems_for k (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]) =
        titems_for k [(ep.2 + 1, ep.1)] := by
    rintro ⟨e, p⟩ hep
    obtain ⟨h1, h2, -⟩ := List.mem_zipIdx hep
    rw [hlenA] at h2
    have hne : S.den (the_unit units f k).hi ≠ p := by omega
    rw [titems_append, titems_closes_at2 H hsvl hk p,
        if_neg (fun h => hne h.1), List.nil_append]
  have hBvanish : ∀ (B₀ : List (Event K V)),
      ∀ ep ∈ B₀.zipIdx (S.den (the_unit units f k).hi + 1),
      titems_for k (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]) =
        titems_for k [(ep.2 + 1, ep.1)] := by
    intro B₀
    rintro ⟨e, p⟩ hep
    obtain ⟨h1, -, -⟩ := List.mem_zipIdx hep
    have hne : S.den (the_unit units f k).hi ≠ p := by omega
    rw [titems_append, titems_closes_at2 H hsvl hk p,
        if_neg (fun h => hne h.1), List.nil_append]
  have hAeq : ((((S.log.take (S.den (the_unit units f k).hi)).drop
        (S.den s0)).zipIdx (S.den s0)).flatMap
        (fun ep => titems_for k
          (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]))) =
      titems_for k
        (tagged_seg S (S.den s0) (S.den (the_unit units f k).hi)) := by
    rw [flatMap_congr hAvanish, flatMap_titems_single]
    rfl
  have hkey : titems_for k (emission_t S units f svl s0) =
      (((S.log.take (S.den (the_unit units f k).hi)).drop
        (S.den s0)).zipIdx (S.den s0)).flatMap
        (fun ep => titems_for k
          (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]))
      ++ (((S.log.take (S.den f)).drop
        (S.den (the_unit units f k).hi)).zipIdx
          (S.den (the_unit units f k).hi)).flatMap
        (fun ep => titems_for k
          (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]))
      ++ titems_for k (closes_at S units svl (S.den f)) := by
    simp only [emission_t]
    rw [hsplit, List.zipIdx_append, hlenA,
        show S.den s0 + (S.den (the_unit units f k).hi - S.den s0) =
          S.den (the_unit units f k).hi from by omega,
        List.flatMap_append, titems_append, titems_append,
        titems_flatMap (k := k), titems_flatMap (k := k)]
  rw [hkey, hAeq]
  rcases Nat.lt_or_ge (S.den (the_unit units f k).hi) (S.den f) with hlt | hge
  · -- Strictly inside: the B-part opens exactly at the high edge.
    have hBne : (S.log.take (S.den f)).drop
        (S.den (the_unit units f k).hi) ≠ [] := by
      refine List.ne_nil_of_length_pos ?_
      rw [seg_length S hflen]
      omega
    obtain ⟨e₀, B', hB⟩ := List.exists_cons_of_ne_nil hBne
    have hBeq : ((((S.log.take (S.den f)).drop
          (S.den (the_unit units f k).hi)).zipIdx
          (S.den (the_unit units f k).hi)).flatMap
          (fun ep => titems_for k
            (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]))) =
        (if k ∈ svl (the_unit units f k)
          then [(S.den (the_unit units f k).hi,
                 ⟨k, (the_unit units f k).refresh k⟩)] else [])
        ++ titems_for k
            (tagged_seg S (S.den (the_unit units f k).hi) (S.den f)) := by
      have htag : titems_for k
          (tagged_seg S (S.den (the_unit units f k).hi) (S.den f)) =
          titems_for k [((S.den (the_unit units f k).hi + 1, e₀) :
            Nat × Event K V)] ++
          titems_for k ((B'.zipIdx (S.den (the_unit units f k).hi + 1)).map
            (fun ep => (ep.2 + 1, ep.1))) := by
        show titems_for k ((((S.log.take (S.den f)).drop
            (S.den (the_unit units f k).hi)).zipIdx
              (S.den (the_unit units f k).hi)).map
            (fun ep => (ep.2 + 1, ep.1))) = _
        rw [hB, List.zipIdx_cons, List.map_cons]
        exact titems_cons k _ _
      rw [hB, List.zipIdx_cons, List.flatMap_cons, titems_append,
          titems_closes_at2 H hsvl hk (S.den (the_unit units f k).hi),
          flatMap_congr (hBvanish B'), flatMap_titems_single, htag]
      by_cases hks : k ∈ svl (the_unit units f k)
      · rw [if_pos (⟨rfl, hks⟩ :
            S.den (the_unit units f k).hi = S.den (the_unit units f k).hi ∧
              k ∈ svl (the_unit units f k)), if_pos hks,
            List.append_assoc]
      · rw [if_neg (fun h => hks h.2), if_neg hks, List.nil_append,
            List.nil_append]
    rw [hBeq, titems_closes_at2 H hsvl hk (S.den f),
        if_neg (fun h => by omega : ¬(S.den (the_unit units f k).hi =
          S.den f ∧ k ∈ svl (the_unit units f k))),
        List.append_nil, List.append_assoc]
  · -- At the frontier: the B-part is empty and the unit closes after
    -- the last consumed event.
    have hpf : S.den (the_unit units f k).hi = S.den f := by omega
    have hBnil : (S.log.take (S.den f)).drop
        (S.den (the_unit units f k).hi) = [] := by
      refine List.eq_nil_of_length_eq_zero ?_
      rw [seg_length S hflen]
      omega
    have hTagNil : titems_for k
        (tagged_seg S (S.den (the_unit units f k).hi) (S.den f)) = [] := by
      rw [hpf, tagged_seg_self]
      rfl
    rw [hBnil, hTagNil, titems_closes_at2 H hsvl hk (S.den f)]
    by_cases hks : k ∈ svl (the_unit units f k)
    · rw [if_pos (⟨hpf, hks⟩ :
          S.den (the_unit units f k).hi = S.den f ∧
            k ∈ svl (the_unit units f k)), if_pos hks, hpf]
      simp
    · rw [if_neg (fun h => hks h.2), if_neg hks]
      simp

/-- The plain-stream reading of the widened master characterization:
a key's events in the emission are its consumed events before the
high edge, then its enumerated entry if any, then its events beyond
the high edge. Port-local step. The Isabelle proofs that use
`titems_emission_master2` perform it inline (the fact `master` in
`absent_replay_safe` and `unlisted_quiet_key_kept`). -/
theorem evs_emission_master2 {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k) :
    evs_for k (emission S units f svl s0) =
      evs_for k (S.win s0 (the_unit units f k).hi)
      ++ (if k ∈ svl (the_unit units f k)
          then [⟨k, (the_unit units f k).refresh k⟩] else [])
      ++ evs_for k (S.win (the_unit units f k).hi f) := by
  have h1 : (titems_for k (tagged_seg S (S.den s0)
      (S.den (the_unit units f k).hi))).map Prod.snd =
      evs_for k (S.win s0 (the_unit units f k).hi) := by
    rw [← evs_for_map_snd, map_snd_tagged_seg]
    rfl
  have h2 : (titems_for k (tagged_seg S (S.den (the_unit units f k).hi)
      (S.den f))).map Prod.snd =
      evs_for k (S.win (the_unit units f k).hi f) := by
    rw [← evs_for_map_snd, map_snd_tagged_seg]
    rfl
  rw [emission, evs_for_map_snd, titems_emission_master2 H hsvl hs0 hk,
      List.map_append, List.map_append, h1, h2]
  by_cases hks : k ∈ svl (the_unit units f k)
  · rw [if_pos hks, if_pos hks]
    rfl
  · rw [if_neg hks, if_neg hks]
    rfl

end CaptureContract

end

end DBLogContract
