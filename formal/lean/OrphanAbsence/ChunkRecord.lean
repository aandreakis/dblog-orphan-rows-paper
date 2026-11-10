import OrphanAbsence.Replay

/-!
# The chunk record: a key range with its selected and changed keys

This file ports the chunk-record subsection of `Orphan_Absence.thy`.
The paper's chunk info record names a key range, the unit's domain, and two
key lists, the selected keys the read returned and the changed keys
touched inside the bracket, whose union is the except set below. A sink
applies it by deleting every key it holds in the range that is on
neither list, and by upserting the surviving returned rows. Stated in
those terms, the keys the sink deletes are exactly the absent untouched
keys it holds, so the record is the covering enumeration of
`Replay.lean`. An except set that over-approximates inside the range
still yields an admissible enumeration, hence a safe one, a robustness
result the paper does not rely on, since its two lists are exact.

* `except_keys`, `dom_minus_except`: the except set of a unit, and
  the range minus the except set is exactly the absent untouched set.
* `record_enum`, `record_enum_ok2`, `record_enum_covers`: the keys a
  sink applying the record touches form an admissible enumeration,
  and a covering one when the except set is exact.
* `chunk_record_converges`: applying the chunk record converges from
  an arbitrary sink state.
* `except_overapprox_safe`: with any except set that contains the
  exact one, the safety theorem still holds.
-/

namespace DBLogContract

universe u v w

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-- The except set of a unit: the keys of its domain that the read
returned, together with the keys of its domain touched inside the
bracket. Isabelle: `except_keys`, stated there as a union of two
sets. -/
def except_keys (S : CoordinateSpace K V C) (u : CUnit K V C) : K → Prop :=
  fun k => (u.dom k ∧ u.refresh k ≠ none) ∨
    (u.dom k ∧ evs_for k (S.win u.lo u.hi) ≠ [])

/-- The range minus the except set is exactly the absent untouched
set. Isabelle: `dom_minus_except`, stated there as a set equality and
here pointwise. -/
theorem dom_minus_except (S : CoordinateSpace K V C) (u : CUnit K V C)
    (k : K) :
    (u.dom k ∧ ¬ except_keys S u k) ↔ absent_untouched S u k := by
  constructor
  · rintro ⟨hdom, hnot⟩
    refine ⟨hdom, ?_, ?_⟩
    · exact Classical.byContradiction fun hr => hnot (Or.inl ⟨hdom, hr⟩)
    · exact Classical.byContradiction fun hw => hnot (Or.inr ⟨hdom, hw⟩)
  · rintro ⟨hdom, hr, hw⟩
    refine ⟨hdom, ?_⟩
    rintro (⟨-, hr'⟩ | ⟨-, hw'⟩)
    · exact hr' hr
    · exact hw' hw

/-- The keys a sink applying a chunk record with except set `E`
writes, given its state `D`: the survivors (the returned rows that
the bracket leaves untouched), together with the keys of the range
outside `E` that the sink holds (the deletes). Isabelle:
`record_enum`, stated there with set union, difference, and
intersection. -/
def record_enum (S : CoordinateSpace K V C) (u : CUnit K V C)
    (E : K → Prop) (D : State K V) : K → Prop :=
  fun k => survivors S u k ∨ ((u.dom k ∧ ¬ E k) ∧ D k ≠ none)

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

omit H in
/-- A listing of the record's keys is an admissible enumeration for
any except set that contains the exact one. Isabelle:
`record_enum_ok2`. -/
theorem record_enum_ok2 {svl : CUnit K V C → List K}
    {E : CUnit K V C → K → Prop} {D0 : State K V}
    (E_sup : ∀ u ∈ units, ∀ k, except_keys S u k → E u k)
    (svl_set : ∀ u ∈ units, (svl u).Nodup ∧
      ∀ k, k ∈ svl u ↔ record_enum S u (E u) D0 k) :
    svl_ok2 S units svl := by
  intro u hu
  obtain ⟨hnd, hmem⟩ := svl_set u hu
  refine ⟨hnd, fun k hs => (hmem k).mpr (Or.inl hs), fun k hk => ?_⟩
  rcases (hmem k).mp hk with h | ⟨⟨hdom, hnE⟩, -⟩
  · exact Or.inl h
  · exact Or.inr ((dom_minus_except S u k).mp
      ⟨hdom, fun hex => hnE (E_sup u hu k hex)⟩)

omit H in
/-- With the exact except set, a listing of the record's keys
covers. Isabelle: `record_enum_covers`. -/
theorem record_enum_covers {svl : CUnit K V C → List K}
    {D0 : State K V} {s0 : C}
    (svl_set : ∀ u ∈ units,
      ∀ k, k ∈ svl u ↔ record_enum S u (except_keys S u) D0 k) :
    covers S units f svl D0 s0 := by
  intro u hu k habs hD _
  exact (svl_set u hu k).mpr
    (Or.inr ⟨(dom_minus_except S u k).mpr habs, hD⟩)

/-- Applying the chunk record converges: replayed from an arbitrary
sink state, the emission that lists the record's keys equals the
source state at the frontier on the whole scope. Isabelle:
`chunk_record_converges`. -/
theorem chunk_record_converges {svl : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    (svl_set : ∀ u ∈ units, (svl u).Nodup ∧
      ∀ k, k ∈ svl u ↔ record_enum S u (except_keys S u) D0 k) :
    ∀ k, scope k →
      state_after D0 (emission S units f svl s0) k =
        state_after σ0 (S.pfx f) k :=
  H.self_stabilization (record_enum_ok2 (fun _ _ _ h => h) svl_set) hs0
    (record_enum_covers (fun u hu => (svl_set u hu).2))

/-- An except set that over-approximates inside the range is still
safe: every scoped key either agrees with the canonical replay at the
frontier, or is an unlisted absent untouched key with no consumed
event whose sink value is left as it was. Isabelle:
`except_overapprox_safe`. -/
theorem except_overapprox_safe {svl : CUnit K V C → List K} {s0 : C}
    {E : CUnit K V C → K → Prop} {D0 : State K V}
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    (E_sup : ∀ u ∈ units, ∀ k, except_keys S u k → E u k)
    (svl_set : ∀ u ∈ units, (svl u).Nodup ∧
      ∀ k, k ∈ svl u ↔ record_enum S u (E u) D0 k)
    {k : K} (hk : scope k) :
    state_after D0 (emission S units f svl s0) k = sink_at S units f f k ∨
      (state_after D0 (emission S units f svl s0) k = D0 k ∧
        sink_at S units f f k = none ∧
        absent_untouched S (the_unit units f k) k ∧
        k ∉ svl (the_unit units f k) ∧
        evs_for k (S.win s0 f) = []) :=
  H.absent_replay_safe (record_enum_ok2 E_sup svl_set) hs0 hk D0

end CaptureContract

end

end DBLogContract
