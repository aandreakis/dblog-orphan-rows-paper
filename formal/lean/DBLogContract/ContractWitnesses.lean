import DBLogContract.MergeDisciplines

/-!
# The torn-read witness

This file ports fixture 1 of `Contract_Witnesses.thy` from the
Isabelle development: the torn read, the paper's Proposition 1. The
countermodel is constructed concretely and its failure fact is
proved, so the port exercises the contract exactly as the paper
does.

The construction, over an initially empty store and the two-event
history `L_w`: one unit covers keys 1 and 2 with the bracket from
coordinate 0 to coordinate 2, and its refresh reports key 1 absent
and key 2 present with value 2. The read of key 1 happened before
the first event committed and the read of key 2 after the second
committed, so the scan is torn across the entire history.

* `wit_torn_contract`: the instance satisfies the contract. O2 is
  discharged per key at different in-bracket coordinates: key 1 at
  coordinate 0, key 2 at coordinate 2.
* `fix_torn_no_single_witness`: provably no single in-bracket
  coordinate is honest for both keys. An obligation demanding one
  read point per unit rejects this instance.
* `wit_torn_cut`: the cut still holds, evaluated concretely: the
  replay at the frontier is exactly the source state there on both
  keys.

This file also ports the central fixtures 2 and 3 of
`Contract_Witnesses.thy`. The derived latest-high trajectory of
Lemma 4.2 remains Isabelle-only, as does the first member's explicit
one-unit result in Proposition 2. The section's worked example is
illustrative and is not mechanized here:

* Fixture 2, the tablesync shape (the paper's Proposition 2): two
  point-bracket units, each honest at its own distinct witness,
  whose composite provably admits no trajectory onset before its
  latest high edge. The
  trajectory property fails at the intermediate coordinate
  (`fix_sync_trajectory_breaks`, `fix_sync_no_early_onset`) while
  the second member alone explicitly satisfies Corollary 1 on its own scope
  (`wit_sync_memberB_T3`).
* Fixture 3, the amortized shared bracket: one bracket shared by
  two units with one shared read witness, lifted to the full
  trajectory property by Corollary 1 (`wit_shared_bracket_T3`), so
  amortization preserves the tier.

This file also ports fixture 4 (the surviving refresh under
window-discard): a unit whose refresh entry survives its window and
must override a pre-window consumed event in the emitted stream,
the equivalence theorem's subtlest path, evaluated concretely
(`wit_surv_svl_ok`, `wit_surv_replay_theorem`,
`wit_surv_replay_value`). The range-merge discipline, the five
instance studies, and the degradation theory remain Isabelle-only.
-/

namespace DBLogContract

noncomputable section

/-- The witness log: two events over natural-number keys and
values, key 1 taking value 1, then key 2 taking value 2. Isabelle:
`L_w`. -/
def L_w : List (Event Nat Nat) := [⟨1, some 1⟩, ⟨2, some 2⟩]

/-- The witness denotation: coordinate `c` denotes the prefix of
length `min c 2`. Isabelle: `den_w`. -/
def den_w (c : Nat) : Nat := min c 2

/-- The initially empty store. Isabelle: `s0_w`. -/
def s0_w : State Nat Nat := fun _ => none

/-- The witness coordinate space over `L_w`. Isabelle: the
interpretation `wc` of `coordinate_space`. -/
def wc : CoordinateSpace Nat Nat Nat where
  log := L_w
  den := den_w
  den_le_len := fun c => by
    show min c 2 ≤ L_w.length
    rw [show L_w.length = 2 from rfl]
    omega

/-- Every coordinate denotes one of the three prefixes. Isabelle:
`den_w_cases`. -/
theorem den_w_cases (c : Nat) : den_w c = 0 ∨ den_w c = 1 ∨ den_w c = 2 := by
  simp only [den_w]
  omega

/-- The torn unit: keys 1 and 2, bracket from coordinate 0 to
coordinate 2, refresh reporting key 1 absent and key 2 present with
value 2. Isabelle: `torn_unit`. -/
def torn_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 1 ∨ k = 2
  lo := 0
  hi := 2
  refresh := fun k => if k = 2 then some 2 else none

/- Concrete evaluations of the per-key fold over the witness log.
The definitions from the general theory are classical, so these are
proved by rewriting the conditionals, not by computation. -/

private theorem state_L_w_1 : state_after s0_w L_w 1 = some 1 := by
  show apply_ev (apply_ev s0_w ⟨1, some 1⟩) ⟨2, some 2⟩ 1 = some 1
  simp [apply_ev]

private theorem state_L_w_2 : state_after s0_w L_w 2 = some 2 := by
  show apply_ev (apply_ev s0_w ⟨1, some 1⟩) ⟨2, some 2⟩ 2 = some 2
  simp [apply_ev]

private theorem state_take1_2 : state_after s0_w (L_w.take 1) 2 = none := by
  show apply_ev s0_w ⟨1, some 1⟩ 2 = none
  simp [apply_ev, s0_w]

/-- The torn instance satisfies the contract: the positive half of
the paper's Proposition 1. O2 is discharged per key at different
in-bracket coordinates: key 1 is honest at coordinate 0, key 2 at
coordinate 2. Isabelle: the `torn` interpretation, exported as
`wit_torn_contract`. -/
theorem wit_torn_contract :
    CaptureContract wc s0_w [torn_unit] (fun k => k = 1 ∨ k = 2) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- O1: the single unit covers the scope.
    intro k
    constructor
    · intro hk
      exact ⟨torn_unit, List.mem_singleton.mpr rfl, hk⟩
    · rintro ⟨u, hu, hk⟩
      rw [List.mem_singleton.mp hu] at hk
      exact hk
  · -- O1: a one-unit family is trivially disjoint.
    intro i j hi hj hne k _ _
    simp only [List.length_cons, List.length_nil] at hi hj
    omega
  · -- Bracket ordering.
    intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w torn_unit.lo ≤ den_w torn_unit.hi
    decide
  · -- Every bracket sits at or below the frontier.
    intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w torn_unit.hi ≤ den_w 2
    decide
  · -- O2: per-key honesty at per-key coordinates.
    intro u hu k hk
    rw [List.mem_singleton.mp hu]
    rcases (List.mem_singleton.mp hu ▸ hk : torn_unit.dom k) with h1 | h2
    · -- Key 1 is honest at coordinate 0, before the first event.
      subst h1
      refine ⟨0, ?_, ?_, ?_⟩
      · show den_w 0 ≤ den_w 0
        decide
      · show den_w 0 ≤ den_w torn_unit.hi
        decide
      · -- refresh 1 = none, and the state at the empty prefix is empty.
        rfl
    · -- Key 2 is honest at coordinate 2, after the second event.
      subst h2
      refine ⟨2, ?_, ?_, ?_⟩
      · show den_w 0 ≤ den_w 2
        decide
      · show den_w 2 ≤ den_w torn_unit.hi
        decide
      · -- refresh 2 = some 2, the state after the full log.
        exact state_L_w_2.symm

/-- Proposition 1's strictness half: no single in-bracket coordinate
is honest for both keys of the torn unit. Key 1's absence verdict is
honest only before the first event; key 2's presence verdict only
after the second. An obligation demanding one read point per unit
rejects this instance; the contract admits it, and the cut still
holds (`wit_torn_cut`). Together with
`CaptureContract.contract_cut`, the sufficiency half, this is the
paper's Proposition 1. Isabelle: `fix_torn_no_single_witness`. -/
theorem fix_torn_no_single_witness :
    ¬ ∃ c, wc.cle torn_unit.lo c ∧ wc.cle c torn_unit.hi ∧
      ∀ k, torn_unit.dom k →
        torn_unit.refresh k = state_after s0_w (wc.pfx c) k := by
  rintro ⟨c, -, -, honest⟩
  have h1 : (none : Option Nat) = state_after s0_w (wc.pfx c) 1 :=
    honest 1 (Or.inl rfl)
  have h2 : (some 2 : Option Nat) = state_after s0_w (wc.pfx c) 2 :=
    honest 2 (Or.inr rfl)
  have hp : wc.pfx c = L_w.take (den_w c) := rfl
  rcases den_w_cases c with hd | hd | hd
  · -- At the empty prefix, key 2 is absent, contradicting its verdict.
    rw [hp, hd] at h2
    simp [s0_w] at h2
  · -- After one event, key 2 is still absent.
    rw [hp, hd, state_take1_2] at h2
    simp at h2
  · -- After both events, key 1 is present, contradicting its verdict.
    rw [hp, hd] at h1
    rw [show state_after s0_w (L_w.take 2) 1 = some 1 from state_L_w_1] at h1
    simp at h1

/-- For both scoped keys the owning unit is the torn unit.
Isabelle: `wit_torn_the_unit`. -/
theorem wit_torn_the_unit {k : Nat} (hk : k = 1 ∨ k = 2) :
    the_unit [torn_unit] 2 k = torn_unit :=
  wit_torn_contract.the_unit_eq (List.mem_singleton.mpr rfl) hk

/-- The cut holds at the torn instance, evaluated concretely: the
replay at the frontier equals the source state there on both keys,
although the torn refresh is honest at no single coordinate.
Isabelle: `wit_torn_cut` (its two conclusions, as one
conjunction). -/
theorem wit_torn_cut :
    sink_at wc [torn_unit] 2 2 1 = some 1 ∧
    sink_at wc [torn_unit] 2 2 2 = some 2 := by
  have c1 := wit_torn_contract.contract_cut (k := 1) (Or.inl rfl)
  have c2 := wit_torn_contract.contract_cut (k := 2) (Or.inr rfl)
  rw [c1, c2]
  constructor
  · exact state_L_w_1
  · exact state_L_w_2

/-! ## Fixture 2: the tablesync shape (paper Proposition 2) -/

/-- The first tablesync unit: key 1 behind a point bracket at
coordinate 0, read before anything commits, honestly reporting
key 1 absent. Isabelle: `syncA`. -/
def syncA : CUnit Nat Nat Nat where
  dom := fun k => k = 1
  lo := 0
  hi := 0
  refresh := fun _ => none

/-- The second tablesync unit: key 2 behind a point bracket at
coordinate 2, read at the end of history, honestly reporting key 2
present with value 2. Isabelle: `syncB`. -/
def syncB : CUnit Nat Nat Nat where
  dom := fun k => k = 2
  lo := 2
  hi := 2
  refresh := fun k => if k = 2 then some 2 else none

private theorem state_take1_1 : state_after s0_w (L_w.take 1) 1 = some 1 := by
  show apply_ev s0_w ⟨1, some 1⟩ 1 = some 1
  simp [apply_ev]

/-- The tablesync composite satisfies the contract; its cut at the
frontier therefore holds by the cut theorem. Isabelle: the `sync`
interpretation, exported as `wit_sync_contract`. -/
theorem wit_sync_contract :
    CaptureContract wc s0_w [syncA, syncB] (fun k => k = 1 ∨ k = 2) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- O1: the two units cover the scope.
    intro k
    constructor
    · rintro (h1 | h2)
      · exact ⟨syncA, List.mem_cons.mpr (Or.inl rfl), h1⟩
      · exact ⟨syncB, List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), h2⟩
    · rintro ⟨u, hu, hk⟩
      rcases List.mem_cons.mp hu with h | h
      · rw [h] at hk
        exact Or.inl hk
      · rw [List.mem_singleton.mp h] at hk
        exact Or.inr hk
  · -- O1: distinct positions own disjoint keys.
    intro i j hi hj hne k h1 h2
    simp only [List.length_cons, List.length_nil] at hi hj
    have hcase : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
    rcases hcase with ⟨hi0, hj1⟩ | ⟨hi1, hj0⟩
    · subst hi0; subst hj1
      have e1 : k = 1 := h1
      have e2 : k = 2 := h2
      omega
    · subst hi1; subst hj0
      have e1 : k = 2 := h1
      have e2 : k = 1 := h2
      omega
  · -- Point brackets are ordered.
    intro u hu
    rcases List.mem_cons.mp hu with h | h
    · rw [h]; show den_w 0 ≤ den_w 0; decide
    · rw [List.mem_singleton.mp h]; show den_w 2 ≤ den_w 2; decide
  · -- Both brackets sit at or below the frontier.
    intro u hu
    rcases List.mem_cons.mp hu with h | h
    · rw [h]; show den_w 0 ≤ den_w 2; decide
    · rw [List.mem_singleton.mp h]; show den_w 2 ≤ den_w 2; decide
  · -- O2: each unit honest at its own point coordinate.
    intro u hu k hk
    rcases List.mem_cons.mp hu with h | h
    · rw [h] at hk ⊢
      have hk1 : k = 1 := hk
      subst hk1
      exact ⟨0, by show den_w 0 ≤ den_w 0; decide,
        by show den_w 0 ≤ den_w 0; decide, rfl⟩
    · rw [List.mem_singleton.mp h] at hk ⊢
      have hk2 : k = 2 := hk
      subst hk2
      exact ⟨2, by show den_w 2 ≤ den_w 2; decide,
        by show den_w 2 ≤ den_w 2; decide, state_L_w_2.symm⟩

/-- Key 2's owning unit in the composite is the second point unit.
Isabelle: `wit_sync_the_unit_2`. -/
theorem wit_sync_the_unit_2 : the_unit [syncA, syncB] 2 2 = syncB :=
  wit_sync_contract.the_unit_eq
    (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))) rfl

/-- The composite breaks the source-trajectory property at the
intermediate coordinate 1: unit B's refresh, honest at its own
witness at the log end, already shows key 2 present, while the
source at coordinate 1 does not. Isabelle:
`fix_sync_trajectory_breaks`. -/
theorem fix_sync_trajectory_breaks :
    sink_at wc [syncA, syncB] 2 1 2 ≠ state_after s0_w (wc.pfx 1) 2 := by
  have hs : sink_at wc [syncA, syncB] 2 1 2 = some 2 := by
    simp only [sink_at, wit_sync_the_unit_2]
    rw [dif_pos (by rfl : evs_for 2 (wc.win syncB.lo 1) = [])]
    rfl
  have ht : state_after s0_w (wc.pfx 1) 2 = none := state_take1_2
  rw [hs, ht]
  simp

/-- An equivalent fixture-specific helper for Proposition 2. Every onset
at or below coordinate 1 makes Corollary 1's trajectory claim fail at
the intermediate coordinate. The paper's exact existential
strict-below-frontier statement and the complete bundle remain
Isabelle-only. Isabelle helper: `fix_sync_no_early_onset`. -/
theorem fix_sync_no_early_onset :
    ¬ ∃ cstar, wc.cle cstar 1 ∧
      ∀ g, wc.cle cstar g → wc.cle g 2 →
        ∀ k, (k = 1 ∨ k = 2) →
          sink_at wc [syncA, syncB] 2 g k =
            state_after s0_w (wc.pfx g) k := by
  rintro ⟨cstar, cs, traj⟩
  have h12 : wc.cle (1 : Nat) 2 := by show den_w 1 ≤ den_w 2; decide
  have := traj 1 cs h12 2 (Or.inr rfl)
  exact fix_sync_trajectory_breaks this

/-- The second member alone, as a one-unit plan on its own scope,
satisfies Corollary 1's premises at its own witness (the log end)
and so carries the full trajectory property there. Port-local
statement of the Isabelle `syncBo` interpretation's content,
consumed by `wit_sync_memberB_T3`. -/
theorem sync_memberB_contract :
    CaptureContract wc s0_w [syncB] (fun k => k = 2) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro hk
      exact ⟨syncB, List.mem_singleton.mpr rfl, hk⟩
    · rintro ⟨u, hu, hk⟩
      rw [List.mem_singleton.mp hu] at hk
      exact hk
  · intro i j hi hj hne k _ _
    simp only [List.length_cons, List.length_nil] at hi hj
    omega
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2; decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2; decide
  · intro u hu k hk
    rw [List.mem_singleton.mp hu] at hk ⊢
    have hk2 : k = 2 := hk
    subst hk2
    exact ⟨2, by show den_w 2 ≤ den_w 2; decide,
      by show den_w 2 ≤ den_w 2; decide, state_L_w_2.symm⟩

/-- The second tablesync member alone is Corollary 1's case on its own
scope: from its witness onward, the one-unit plan's replay
tracks the source. Isabelle: `wit_sync_memberB_T3`. -/
theorem wit_sync_memberB_T3 {g : Nat} (h2g : wc.cle 2 g) (hg2 : wc.cle g 2)
    {k : Nat} (hk : k = 2) :
    sink_at wc [syncB] 2 g k = state_after s0_w (wc.pfx g) k := by
  refine sync_memberB_contract.shared_witness_trajectory
    (cstar := 2) ?_ ?_ h2g hg2 hk
  · intro u hu
    rw [List.mem_singleton.mp hu]
    exact ⟨by show den_w 2 ≤ den_w 2; decide,
      by show den_w 2 ≤ den_w 2; decide⟩
  · intro u hu k' hk'
    rw [List.mem_singleton.mp hu] at hk' ⊢
    have : k' = 2 := hk'
    subst this
    exact state_L_w_2.symm

/-! ## Fixture 3: the amortized shared bracket with a shared witness -/

/-- The first shared-bracket unit: key 1 under the full bracket
from coordinate 0 to coordinate 2, refresh reporting key 1 present
with value 1. Isabelle: `shrC`. -/
def shrC : CUnit Nat Nat Nat where
  dom := fun k => k = 1
  lo := 0
  hi := 2
  refresh := fun k => if k = 1 then some 1 else none

/-- The second shared-bracket unit: key 2 under the same bracket,
refresh reporting key 2 absent. Isabelle: `shrD`. -/
def shrD : CUnit Nat Nat Nat where
  dom := fun k => k = 2
  lo := 0
  hi := 2
  refresh := fun _ => none

/-- One bracket amortized over both units with ONE shared read
witness at coordinate 1: the composite satisfies the contract, O2
discharged for both keys at the same coordinate. Isabelle: the
`shr` interpretation, exported as the contract fact behind
`wit_shared_bracket_T3`. -/
theorem wit_shr_contract :
    CaptureContract wc s0_w [shrC, shrD] (fun k => k = 1 ∨ k = 2) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · rintro (h1 | h2)
      · exact ⟨shrC, List.mem_cons.mpr (Or.inl rfl), h1⟩
      · exact ⟨shrD, List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), h2⟩
    · rintro ⟨u, hu, hk⟩
      rcases List.mem_cons.mp hu with h | h
      · rw [h] at hk
        exact Or.inl hk
      · rw [List.mem_singleton.mp h] at hk
        exact Or.inr hk
  · intro i j hi hj hne k h1 h2
    simp only [List.length_cons, List.length_nil] at hi hj
    have hcase : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
    rcases hcase with ⟨hi0, hj1⟩ | ⟨hi1, hj0⟩
    · subst hi0; subst hj1
      have e1 : k = 1 := h1
      have e2 : k = 2 := h2
      omega
    · subst hi1; subst hj0
      have e1 : k = 2 := h1
      have e2 : k = 1 := h2
      omega
  · intro u hu
    rcases List.mem_cons.mp hu with h | h
    · rw [h]; show den_w 0 ≤ den_w 2; decide
    · rw [List.mem_singleton.mp h]; show den_w 0 ≤ den_w 2; decide
  · intro u hu
    rcases List.mem_cons.mp hu with h | h
    · rw [h]; show den_w 2 ≤ den_w 2; decide
    · rw [List.mem_singleton.mp h]; show den_w 2 ≤ den_w 2; decide
  · -- O2: BOTH keys honest at the shared coordinate 1.
    intro u hu k hk
    rcases List.mem_cons.mp hu with h | h
    · rw [h] at hk ⊢
      have hk1 : k = 1 := hk
      subst hk1
      exact ⟨1, by show den_w 0 ≤ den_w 1; decide,
        by show den_w 1 ≤ den_w 2; decide, state_take1_1.symm⟩
    · rw [List.mem_singleton.mp h] at hk ⊢
      have hk2 : k = 2 := hk
      subst hk2
      exact ⟨1, by show den_w 0 ≤ den_w 1; decide,
        by show den_w 1 ≤ den_w 2; decide, state_take1_2.symm⟩

/-- The amortized shared bracket lifts to the full trajectory
property: with the one shared read witness at coordinate 1,
Corollary 1 applies to the composite, so the sink trajectory
tracks the source from the witness onward. Amortization preserved
the tier. Isabelle: `wit_shared_bracket_T3`. -/
theorem wit_shared_bracket_T3 {g : Nat} (h1g : wc.cle 1 g) (hg2 : wc.cle g 2)
    {k : Nat} (hk : k = 1 ∨ k = 2) :
    sink_at wc [shrC, shrD] 2 g k = state_after s0_w (wc.pfx g) k := by
  refine wit_shr_contract.shared_witness_trajectory
    (cstar := 1) ?_ ?_ h1g hg2 hk
  · intro u hu
    rcases List.mem_cons.mp hu with h | h
    · rw [h]
      exact ⟨by show den_w 0 ≤ den_w 1; decide,
        by show den_w 1 ≤ den_w 2; decide⟩
    · rw [List.mem_singleton.mp h]
      exact ⟨by show den_w 0 ≤ den_w 1; decide,
        by show den_w 1 ≤ den_w 2; decide⟩
  · intro u hu k' hk'
    rcases List.mem_cons.mp hu with h | h
    · rw [h] at hk' ⊢
      have : k' = 1 := hk'
      subst this
      exact state_take1_1.symm
    · rw [List.mem_singleton.mp h] at hk' ⊢
      have : k' = 2 := hk'
      subst this
      exact state_take1_2.symm

/-! ## Fixture 4: a surviving refresh under window-discard -/

/-- The second witness log: key 3 takes value 7 before the bracket,
key 1 takes value 1 inside it. Isabelle: `L_s`. -/
def L_s : List (Event Nat Nat) := [⟨3, some 7⟩, ⟨1, some 1⟩]

/-- The coordinate space over `L_s`. Isabelle: the interpretation
`sc`. -/
def sc : CoordinateSpace Nat Nat Nat where
  log := L_s
  den := den_w
  den_le_len := fun c => by
    show min c 2 ≤ L_s.length
    rw [show L_s.length = 2 from rfl]
    omega

/-- The surviving-refresh unit: key 3 behind the bracket from
coordinate 1 to coordinate 2, refresh reporting key 3 present with
value 7. Its window contains no event for key 3, so the refresh
survives and is emitted at the close, after the pre-window event.
Isabelle: `surv_unit`. -/
def surv_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 3
  lo := 1
  hi := 2
  refresh := fun k => if k = 3 then some 7 else none

private theorem state_Ls_take1_3 :
    state_after s0_w (L_s.take 1) 3 = some 7 := by
  show apply_ev s0_w ⟨3, some 7⟩ 3 = some 7
  simp [apply_ev]

private theorem evs_win_s_3 : evs_for 3 (sc.win surv_unit.lo 2) = [] := by
  show evs_for 3 [(⟨1, some 1⟩ : Event Nat Nat)] = []
  simp [evs_for]

/-- The surviving-refresh instance satisfies the contract, O2
discharged at coordinate 1. Isabelle: the `surv` interpretation. -/
theorem wit_surv_contract :
    CaptureContract sc s0_w [surv_unit] (fun k => k = 3) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro hk
      exact ⟨surv_unit, List.mem_singleton.mpr rfl, hk⟩
    · rintro ⟨u, hu, hk⟩
      rw [List.mem_singleton.mp hu] at hk
      exact hk
  · intro i j hi hj hne k _ _
    simp only [List.length_cons, List.length_nil] at hi hj
    omega
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 1 ≤ den_w 2; decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2; decide
  · intro u hu k hk
    rw [List.mem_singleton.mp hu] at hk ⊢
    have hk3 : k = 3 := hk
    subst hk3
    exact ⟨1, by show den_w 1 ≤ den_w 1; decide,
      by show den_w 1 ≤ den_w 2; decide, state_Ls_take1_3.symm⟩

/-- The constant enumeration listing key 3 is a lawful survivor
enumeration for the surviving-refresh plan: key 3 is read as
present and its window is quiet. Isabelle: `wit_surv_svl_ok`. -/
theorem wit_surv_svl_ok : svl_ok sc [surv_unit] (fun _ => [3]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_⟩
  intro k
  constructor
  · intro hk
    have hk3 : k = 3 := List.mem_singleton.mp hk
    subst hk3
    exact ⟨rfl, by simp [surv_unit], evs_win_s_3⟩
  · intro hs
    have hk3 : k = 3 := hs.1
    subst hk3
    exact List.mem_singleton.mpr rfl

/-- Key 3's owning unit. Isabelle: `wit_surv_the_unit`. -/
theorem wit_surv_the_unit : the_unit [surv_unit] 2 3 = surv_unit :=
  wit_surv_contract.the_unit_eq (List.mem_singleton.mpr rfl) rfl

/-- The equivalence theorem at the fixture: the emitted stream,
with the surviving refresh emitted at the window close AFTER the
pre-window event for its key, replays to the canonical sink.
Isabelle: `wit_surv_replay_theorem`. -/
theorem wit_surv_replay_theorem :
    stream_replay (emission sc [surv_unit] 2 (fun _ => [3]) 0) 3 =
      sink_at sc [surv_unit] 2 2 3 := by
  refine wit_surv_contract.window_discard_replay wit_surv_svl_ok ?_ rfl
  intro u hu
  rw [List.mem_singleton.mp hu]
  show den_w 0 ≤ den_w 1
  decide

/-- The concrete value: both sides evaluate to the surviving
refresh verdict. Isabelle: `wit_surv_replay_value`. -/
theorem wit_surv_replay_value :
    stream_replay (emission sc [surv_unit] 2 (fun _ => [3]) 0) 3 =
      some 7 := by
  rw [wit_surv_replay_theorem]
  simp only [sink_at, wit_surv_the_unit]
  rw [dif_pos evs_win_s_3]
  rfl

end

end DBLogContract
