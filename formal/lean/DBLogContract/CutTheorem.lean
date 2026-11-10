import DBLogContract.ContractBase

/-!
# Capture plans, the contract, and the contract-level cut theorem

This file is a port of `Cut_Theorem.thy` from the Isabelle
development that accompanies the paper: capture plans as finite
families of units, the source-side contract, the canonical per-key
replay, the contract-level cut theorem (paper Theorem 1), and
Corollaries 1 to 3.

Obligation placement, carried over from the Isabelle source
unchanged:

* O1 (coverage and disjointness) and O2 (bracket-local per-key
  existential honesty) are fields of `CaptureContract` below,
  together with the bracket ordering and the frontier bound.
  Operational DBLog instances obtain refreshes from committed reads;
  they do not expose in-progress writes. When transaction labels are
  retained, the operational O2 witness is a transaction boundary.
  This transaction-free core stores only the per-key equality needed
  by the proof and does not license an interior replay prefix as a
  dirty-read state.
* O3 (domain completeness) is carried by the representation plus
  O2: a refresh is a total function, so every key of the unit
  yields exactly one value-or-absence verdict, and O2 quantifies
  over all keys of the unit's domain. A scan that silently missed a
  key cannot discharge O2 unless that key was genuinely absent at
  an in-bracket coordinate.
* O4 (declared external assertions) has no core-level content: it
  disciplines how an instance may discharge bracket and honesty
  premises and surfaces in the instance theories, never here.
* O5 (representation agreement) is carried by typing: refresh
  values and log images land in the same key and value types by
  construction.
* S-OBS: the log of the coordinate space is the committed history
  the capture consumes, and the fold below is defined from it
  directly, so the core theorem needs no separate observability
  premise. Because `sink_at` never mentions the frontier parameter,
  the fold-level results are frontier-parametric; each corollary
  states its observation scoping exactly as the paper does.
-/

namespace DBLogContract

universe u v w

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-- One unit of a capture plan: a domain of keys, a bracket given by
its low and high coordinates, and the refresh, the read result as
one value-or-absence verdict per key. Domains and scopes are
predicates on keys, the direct Lean reading of the Isabelle
`'k set`. Isabelle: record `cunit` with fields `u_dom`, `u_lo`,
`u_hi`, `u_refresh`. Paper: the unit `(D_i, lo_i, hi_i, R_i)` of
Definition 3.1. -/
structure CUnit (K : Type u) (V : Type v) (C : Type w) where
  dom : K → Prop
  lo : C
  hi : C
  refresh : State K V

/-- The unit that owns key `k`: the definite description "the member
of `units` whose domain contains `k`". Under O1 the owning unit
exists and is unique (`CaptureContract.the_unit_props`,
`CaptureContract.covering_unit_unique`). Like the Isabelle `THE`,
the definition is total: when no owning unit exists it returns a
degenerate unit at the frontier, and no ported statement depends on
that branch. Isabelle: `the_unit`, defined with `THE`; ported with
classical choice, as recorded in VERIFICATION.md. -/
def the_unit (units : List (CUnit K V C)) (f : C) (k : K) : CUnit K V C :=
  if h : ∃ u, u ∈ units ∧ u.dom k then h.choose
  else { dom := fun _ => False, lo := f, hi := f, refresh := fun _ => none }

/-- The canonical replay, per key, evaluated at a coordinate `g`
(the emission truncated at `g`): the last event for the key in the
half-open window from the owning unit's low bracket edge to `g`
wins; absent any such event, the unit's refresh verdict stands.
Refreshes are placed at the low edge and later events win. At
`g = f` this is the paper's Section 3 replay; at general `g` it is
Definition 4.1 (replay at a coordinate). Isabelle: `sink_at`. -/
def sink_at (S : CoordinateSpace K V C) (units : List (CUnit K V C))
    (f : C) (g : C) (k : K) : Option V :=
  if h : evs_for k (S.win (the_unit units f k).lo g) = []
  then (the_unit units f k).refresh k
  else ((evs_for k (S.win (the_unit units f k).lo g)).getLast h).img

/-- Helper: `getLast` respects list equality. Port-local. -/
theorem getLast_eq_of_eq {α : Type u} {l l' : List α}
    (heq : l = l') (h : l ≠ []) :
    l.getLast h = l'.getLast (heq ▸ h) := by
  subst heq
  rfl

/-- Case A of the per-key argument, shared by the cut theorem and
Corollary 1's engine: when some event for `k` lies in the window
from the owning unit's low edge to `g`, the last such event decides
both the replay and the source state, and the refresh is never
consulted. Port-local helper; the Isabelle source inlines this
reasoning in `contract_cut_at` and
`shared_witness_trajectory_at`. -/
theorem sink_at_case_events {S : CoordinateSpace K V C}
    {units : List (CUnit K V C)} {f g : C} {k : K} (σ0 : State K V)
    (lo_g : S.cle (the_unit units f k).lo g)
    (hw : evs_for k (S.win (the_unit units f k).lo g) ≠ []) :
    sink_at S units f g k = state_after σ0 (S.pfx g) k := by
  have split := S.evs_for_pfx_split lo_g k
  have hne : evs_for k (S.pfx g) ≠ [] := by
    rw [split]
    intro hcontra
    exact hw (List.append_eq_nil_iff.mp hcontra).2
  have hlast : (evs_for k (S.pfx g)).getLast hne =
      (evs_for k (S.win (the_unit units f k).lo g)).getLast hw := by
    rw [getLast_eq_of_eq split]
    exact List.getLast_append_of_ne_nil _ hw
  simp only [sink_at]
  rw [dif_neg hw, state_after_last_event hne, hlast]

/-- The source-side contract over a coordinate space, an initial
state, a unit family, a scope, and a frontier. The fields are the
Isabelle locale assumptions of `capture_contract`: O1 as coverage
plus pairwise disjointness of unit domains by family position,
bracket ordering, every bracket's high edge at or below the
frontier, and O2 as bracket-local per-key existential honesty.
Paper: Definition 3.2 over the plan shape of Definition 3.1. -/
structure CaptureContract (S : CoordinateSpace K V C) (σ0 : State K V)
    (units : List (CUnit K V C)) (scope : K → Prop) (f : C) : Prop where
  O1_cover : ∀ k, scope k ↔ ∃ u, u ∈ units ∧ u.dom k
  O1_disjoint : ∀ i j, (hi : i < units.length) → (hj : j < units.length) →
    i ≠ j → ∀ k, (units[i]'hi).dom k → (units[j]'hj).dom k → False
  bracket_lo_hi : ∀ u ∈ units, S.cle u.lo u.hi
  bracket_hi_f : ∀ u ∈ units, S.cle u.hi f
  O2_honest : ∀ u ∈ units, ∀ k, u.dom k →
    ∃ c, S.cle u.lo c ∧ S.cle c u.hi ∧
      u.refresh k = state_after σ0 (S.pfx c) k

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

/-- A unit's domain lies inside the scope. Isabelle:
`dom_sub_scope`, stated there as set inclusion. -/
theorem dom_sub_scope {u : CUnit K V C} {k : K}
    (hu : u ∈ units) (hk : u.dom k) : scope k :=
  (H.O1_cover k).mpr ⟨u, hu, hk⟩

/-- O1 makes the covering unit unique. Isabelle:
`covering_unit_unique`. -/
theorem covering_unit_unique {u u' : CUnit K V C} {k : K}
    (hu : u ∈ units) (hku : u.dom k)
    (hu' : u' ∈ units) (hku' : u'.dom k) : u = u' := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hu'
  have hij : i ≠ j := by
    intro h
    subst h
    rw [hiu] at hju
    exact hne hju
  exact H.O1_disjoint i j hi hj hij k (hiu.symm ▸ hku) (hju.symm ▸ hku')

/-- For a scoped key the owning unit is a member and owns the key.
Isabelle: `the_unit_props`. -/
theorem the_unit_props {k : K} (hk : scope k) :
    the_unit units f k ∈ units ∧ (the_unit units f k).dom k := by
  have hex : ∃ u, u ∈ units ∧ u.dom k := (H.O1_cover k).mp hk
  simp only [the_unit]
  rw [dif_pos hex]
  exact hex.choose_spec

/-- The owning unit is the covering unit: `the_unit` returns exactly
the member that owns the key. Port-local corollary of uniqueness;
in the Isabelle source this is the `the_equality` step inside
`the_unit_props`. -/
theorem the_unit_eq {u : CUnit K V C} {k : K}
    (hu : u ∈ units) (hku : u.dom k) :
    the_unit units f k = u := by
  have hex : ∃ u', u' ∈ units ∧ u'.dom k := ⟨u, hu, hku⟩
  simp only [the_unit]
  rw [dif_pos hex]
  exact H.covering_unit_unique hex.choose_spec.1 hex.choose_spec.2 hu hku

/-- The owning unit occupies a unique family position. Isabelle:
`the_unit_position_unique`. -/
theorem the_unit_position_unique {k : K} (hk : scope k)
    {i j : Nat} (hi : i < units.length)
    (hiu : units[i]'hi = the_unit units f k)
    (hj : j < units.length)
    (hju : units[j]'hj = the_unit units f k) : i = j := by
  refine Classical.byContradiction fun hne => ?_
  have hdom : (the_unit units f k).dom k := (H.the_unit_props hk).2
  exact H.O1_disjoint i j hi hj hne k (hiu ▸ hdom) (hju ▸ hdom)

/-- The frontier-parametric workhorse: at any coordinate `g` that
bounds every unit's high bracket edge, the canonical replay equals
the source state. The proof is per-key local, exactly the paper's
proof of Theorem 1: Case A (some event for the key after its unit's
low edge): the last such event wins the fold and is also the last
event for the key in the whole prefix. Case B (no such event): O2
supplies an in-bracket honest coordinate and window invariance
propagates its value to `g`. Nothing couples distinct units beyond
O1 disjointness and the shared bound. Isabelle:
`contract_cut_at`. -/
theorem contract_cut_at {g : C} (bound : ∀ u ∈ units, S.cle u.hi g)
    {k : K} (hk : scope k) :
    sink_at S units f g k = state_after σ0 (S.pfx g) k := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  have lo_hi : S.cle (the_unit units f k).lo (the_unit units f k).hi :=
    H.bracket_lo_hi _ u_in
  have hi_g : S.cle (the_unit units f k).hi g := bound _ u_in
  have lo_g : S.cle (the_unit units f k).lo g := S.cle_trans lo_hi hi_g
  by_cases hw : evs_for k (S.win (the_unit units f k).lo g) = []
  · -- Case B: no event for the key after the low edge.
    obtain ⟨c, c_lo, c_hi, honest⟩ := H.O2_honest _ u_in k k_dom
    have c_g : S.cle c g := S.cle_trans c_hi hi_g
    simp only [sink_at]
    rw [dif_pos hw, honest, S.win_invariant_state c_lo c_g hw σ0]
    exact (S.win_invariant_state lo_g (S.cle_refl g) hw σ0).symm
  · -- Case A: the last in-window event for the key decides both sides.
    exact sink_at_case_events σ0 lo_g hw

/-- THE theorem (paper Theorem 1, the cut theorem): the replay of
the emission is exactly the source state at the frontier, on every
key of the scope. Isabelle: `contract_cut`. -/
theorem contract_cut {k : K} (hk : scope k) :
    sink_at S units f f k = state_after σ0 (S.pfx f) k :=
  H.contract_cut_at H.bracket_hi_f hk

/-- Theorem 1 stated over the whole scope. Isabelle:
`contract_cut_scope`. -/
theorem contract_cut_scope :
    ∀ k, scope k → sink_at S units f f k = state_after σ0 (S.pfx f) k :=
  fun _ hk => H.contract_cut hk

/-- The engine lemma for Corollary 1, frontier-parametric: with one
coordinate `cstar` that is a shared read witness for the whole plan
(inside every bracket, and every refresh honest at it), the replay
at every `g` above `cstar` equals the source state at `g`: the sink
trajectory coincides with the source trajectory from the witness
onward. Case A keys never consult the refresh; Case B keys are
quiet from the witness to `g`, so the witness value is the `g`
value. Isabelle: `shared_witness_trajectory_at`. -/
theorem shared_witness_trajectory_at {cstar g : C}
    (wit_bracket : ∀ u ∈ units, S.cle u.lo cstar ∧ S.cle cstar u.hi)
    (wit_honest : ∀ u ∈ units, ∀ k, u.dom k →
      u.refresh k = state_after σ0 (S.pfx cstar) k)
    (cg : S.cle cstar g) {k : K} (hk : scope k) :
    sink_at S units f g k = state_after σ0 (S.pfx g) k := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  have lo_cs : S.cle (the_unit units f k).lo cstar := (wit_bracket _ u_in).1
  have lo_g : S.cle (the_unit units f k).lo g := S.cle_trans lo_cs cg
  by_cases hw : evs_for k (S.win (the_unit units f k).lo g) = []
  · -- Case B: quiet from the low edge, hence quiet from the witness.
    have quiet_cs_g : evs_for k (S.win cstar g) = [] := by
      have hsplit := S.evs_for_win_split lo_cs cg k
      rw [hw] at hsplit
      exact (List.append_eq_nil_iff.mp hsplit.symm).2
    simp only [sink_at]
    rw [dif_pos hw, wit_honest _ u_in k k_dom]
    exact (S.win_invariant_state cg (S.cle_refl g) quiet_cs_g σ0).symm
  · -- Case A: as in the cut theorem.
    exact sink_at_case_events σ0 lo_g hw

set_option linter.unusedVariables false in
/-- Corollary 1 (paper Corollary 1, shared witness) exactly as the
paper scopes it: the trajectory claim runs from the consistency
onset `cstar` up to the observation frontier `f`. Beyond `f` it
extends exactly as far as observation is extended (Corollary 2's
premise), never for free. The premise `cle g f` scopes the claim to
what the capture has observed; the frontier-parametric engine above
is what discharges it. Isabelle: `shared_witness_trajectory`. -/
theorem shared_witness_trajectory {cstar g : C}
    (wit_bracket : ∀ u ∈ units, S.cle u.lo cstar ∧ S.cle cstar u.hi)
    (wit_honest : ∀ u ∈ units, ∀ k, u.dom k →
      u.refresh k = state_after σ0 (S.pfx cstar) k)
    (cg : S.cle cstar g) (gf : S.cle g f) {k : K} (hk : scope k) :
    sink_at S units f g k = state_after σ0 (S.pfx g) k :=
  H.shared_witness_trajectory_at wit_bracket wit_honest cg hk

/-- Corollary 2 (paper Corollary 2, continuation under extended
observation): if observation holds with the frontier replaced by a
later `f'`, replay to `f'` equals the source state there; pure log
replay preserves the cut. The extension premise `cle f f'` is
genuine: it is what makes every bracket bound `f'`. A capture that
stops observing at `f` claims nothing beyond `f`. Isabelle:
`continuation`. -/
theorem continuation {f' : C} (ff' : S.cle f f') {k : K} (hk : scope k) :
    sink_at S units f f' k = state_after σ0 (S.pfx f') k :=
  H.contract_cut_at (fun u hu => S.cle_trans (H.bracket_hi_f u hu) ff') hk

end CaptureContract

/-- Corollary 3 (paper Corollary 3, mixing): two contract instances
over the same source and coordinate space with disjoint scopes union
to a contract instance, with units appended and scopes joined; its
cut is then the cut theorem applied to the union. Heterogeneous
bootstrap is the theorem's normal case, not a special case.
Isabelle: `mixing_union`, proved in the `coordinate_space`
context. -/
theorem mixing_union {S : CoordinateSpace K V C} {σ0 : State K V}
    {us1 us2 : List (CUnit K V C)} {sc1 sc2 : K → Prop} {f : C}
    (A : CaptureContract S σ0 us1 sc1 f)
    (B : CaptureContract S σ0 us2 sc2 f)
    (disj : ∀ k, sc1 k → sc2 k → False) :
    CaptureContract S σ0 (us1 ++ us2) (fun k => sc1 k ∨ sc2 k) f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- O1_cover
    intro k
    constructor
    · rintro (h1 | h2)
      · obtain ⟨u, hu, hk⟩ := (A.O1_cover k).mp h1
        exact ⟨u, List.mem_append.mpr (Or.inl hu), hk⟩
      · obtain ⟨u, hu, hk⟩ := (B.O1_cover k).mp h2
        exact ⟨u, List.mem_append.mpr (Or.inr hu), hk⟩
    · rintro ⟨u, hu, hk⟩
      rcases List.mem_append.mp hu with h | h
      · exact Or.inl ((A.O1_cover k).mpr ⟨u, h, hk⟩)
      · exact Or.inr ((B.O1_cover k).mpr ⟨u, h, hk⟩)
  · -- O1_disjoint: four cases on which side each position falls.
    intro i j hi hj hne k hki hkj
    have hlen : (us1 ++ us2).length = us1.length + us2.length :=
      List.length_append
    by_cases hil : i < us1.length
    · by_cases hjl : j < us1.length
      · rw [List.getElem_append_left hil] at hki
        rw [List.getElem_append_left hjl] at hkj
        exact A.O1_disjoint i j hil hjl hne k hki hkj
      · rw [List.getElem_append_left hil] at hki
        rw [List.getElem_append_right (Nat.le_of_not_lt hjl)] at hkj
        have h1 : sc1 k := A.dom_sub_scope (List.getElem_mem _) hki
        have h2 : sc2 k := B.dom_sub_scope (List.getElem_mem _) hkj
        exact disj k h1 h2
    · by_cases hjl : j < us1.length
      · rw [List.getElem_append_right (Nat.le_of_not_lt hil)] at hki
        rw [List.getElem_append_left hjl] at hkj
        have h1 : sc1 k := A.dom_sub_scope (List.getElem_mem _) hkj
        have h2 : sc2 k := B.dom_sub_scope (List.getElem_mem _) hki
        exact disj k h1 h2
      · rw [List.getElem_append_right (Nat.le_of_not_lt hil)] at hki
        rw [List.getElem_append_right (Nat.le_of_not_lt hjl)] at hkj
        have hb1 : i - us1.length < us2.length := by omega
        have hb2 : j - us1.length < us2.length := by omega
        have hne' : i - us1.length ≠ j - us1.length := by omega
        exact B.O1_disjoint _ _ hb1 hb2 hne' k hki hkj
  · -- bracket_lo_hi
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · exact A.bracket_lo_hi u h
    · exact B.bracket_lo_hi u h
  · -- bracket_hi_f
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · exact A.bracket_hi_f u h
    · exact B.bracket_hi_f u h
  · -- O2_honest
    intro u hu k hk
    rcases List.mem_append.mp hu with h | h
    · exact A.O2_honest u h k hk
    · exact B.O2_honest u h k hk

/-- The shared-witness lift for mixing: Corollary 1's bracket
premise over the union decomposes over the append, so one witness
shared by all members of both plans is a shared witness for the
composite. With distinct witnesses the decomposition is unavailable
and only the theorem's frontier conclusion remains. Isabelle:
`mixing_shared_witness_lift`. -/
theorem mixing_shared_witness_lift {S : CoordinateSpace K V C}
    {us1 us2 : List (CUnit K V C)} {cstar : C}
    (h1 : ∀ u ∈ us1, S.cle u.lo cstar ∧ S.cle cstar u.hi)
    (h2 : ∀ u ∈ us2, S.cle u.lo cstar ∧ S.cle cstar u.hi) :
    ∀ u ∈ us1 ++ us2, S.cle u.lo cstar ∧ S.cle cstar u.hi := by
  intro u hu
  rcases List.mem_append.mp hu with h | h
  · exact h1 u h
  · exact h2 u h

/-- The honesty half of the shared-witness lift: refresh honesty at
the shared witness likewise decomposes over the append. Isabelle:
`mixing_shared_honesty_lift`. -/
theorem mixing_shared_honesty_lift {S : CoordinateSpace K V C}
    {σ0 : State K V} {us1 us2 : List (CUnit K V C)} {cstar : C}
    (h1 : ∀ u ∈ us1, ∀ k, u.dom k →
      u.refresh k = state_after σ0 (S.pfx cstar) k)
    (h2 : ∀ u ∈ us2, ∀ k, u.dom k →
      u.refresh k = state_after σ0 (S.pfx cstar) k) :
    ∀ u ∈ us1 ++ us2, ∀ k, u.dom k →
      u.refresh k = state_after σ0 (S.pfx cstar) k := by
  intro u hu
  rcases List.mem_append.mp hu with h | h
  · exact h1 u h
  · exact h2 u h

end

end DBLogContract
