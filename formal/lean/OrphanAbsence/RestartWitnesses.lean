import OrphanAbsence.Restart
import OrphanAbsence.InterleavedWitnesses

/-!
# Fixtures: an orphan stays removed, a live row stays live

This file ports the fixtures of `Orphan_Absence_Restart.thy`. The orphan
and re-insert fixtures use the witness log `L_s = [⟨3, some 7⟩, ⟨1, some 1⟩]`
of the core's coordinate space `sc`, with `den_w c = min c 2`. The
transient fixture has its own log `L_t`, denotation `den_t` and space
`tc`.

* The orphan fixture. The pass is the orphan pass of `Witnesses.lean`.
  Its one chunk owns keys 3 and 4 with the bracket from 1 to 2, and the
  sink holds the orphan key 4. The connector committed offset 1 and
  crashed at position 2, after the close. It re-executes the chunk with
  the bracket from 2 to 2 (`rx_unit`), which does not list key 4. The
  close entry delivered before the crash does, and the orphan stays
  removed (`wit_restart_orphan_stays_removed`).
* The same pass crashed at position 1, before its chunk closes. The
  orphan stays, in the second branch of `restart_safe`
  (`wit_restart_before_close_second_branch`), and the coverage
  assumption of `restart_converges` fails for it
  (`wit_restart_before_close_cover_fails`).
* The re-insert fixture. A chunk lists key 1 as absent at its close at
  position 1. Key 1 is then inserted at position 1. The connector
  committed offset 0 and re-executes the chunk at position 2. The live
  row is kept (`wit_restart_live_row_kept`).
* The transient fixture. While the re-delivered segment is applied, the
  sink holds a deleted row that the log has inserted again
  (`wit_restart_transient_mid`). It ends at the source value
  (`wit_restart_transient_end`).

The Isabelle interpretations `rx`, `rj`, `tr1` and `tr2` of
`capture_contract` are the theorems `wit_rx_contract`, `wit_rj_contract`,
`wit_tr1_contract` and `wit_tr2_contract`. The lemma `ri_contract` and
the interpretation `ri` built from it state one fact, which is the
theorem `ri_contract`. The interpretations `rs`, `rs0`, `rt` and `rtr` of
`pass_restart` are the theorems `wit_rs_instance`, `wit_rs0_instance`,
`wit_rt_instance` and `wit_rtr_instance`. The interpretation `tc` of
`coordinate_space` is the definition `tc`, as the core port defines `sc`.
The interpreted constants, such as `rs.restart_stream` and
`orph.the_unit`, are the general constants applied to the fixture's
space and unit families. A scope `{3, 4}` is the predicate
`fun k => k = 3 ∨ k = 4`, and the empty scope is `fun _ => False`.

Like `Witnesses.lean`, this file does not make classical decidability a
local instance, so `decide` evaluates the concrete comparisons.
-/

namespace DBLogContract

noncomputable section

/-! ## Fixtures: an orphan stays removed, a live row stays live -/

/-- The re-executed chunk of the orphan fixture: keys 3 and 4 behind the
zero-width bracket at coordinate 2, refresh reporting key 3 present with
value 7 and key 4 absent. Isabelle: `rx_unit`. -/
def rx_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 3 ∨ k = 4
  lo := 2
  hi := 2
  refresh := fun k => if k = 3 then some 7 else none

/-- Key 3 holds value 7 at the end of `L_s`. Port-local, a concrete
evaluation of the per-key fold. -/
private theorem rs_state_pfx2_3 : state_after s0_w (sc.pfx 2) 3 = some 7 := by
  show apply_ev (apply_ev s0_w ⟨3, some 7⟩) ⟨1, some 1⟩ 3 = some 7
  simp [apply_ev]

/-- Key 1 holds value 1 at the end of `L_s`. Port-local, a concrete
evaluation of the per-key fold. -/
private theorem rs_state_pfx2_1 : state_after s0_w (sc.pfx 2) 1 = some 1 := by
  show apply_ev (apply_ev s0_w ⟨3, some 7⟩) ⟨1, some 1⟩ 1 = some 1
  simp [apply_ev]

/-- The re-executed chunk of the orphan fixture is a contract over the
scope `{3, 4}` with frontier 2, O2 discharged for both keys at
coordinate 2. Isabelle: the interpretation `rx`. -/
theorem wit_rx_contract :
    CaptureContract sc s0_w [rx_unit] (fun k => k = 3 ∨ k = 4) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro hk
      exact ⟨rx_unit, List.mem_singleton.mpr rfl, hk⟩
    · rintro ⟨u, hu, hk⟩
      rw [List.mem_singleton.mp hu] at hk
      exact hk
  · intro i j hi hj hne k _ _
    simp only [List.length_cons, List.length_nil] at hi hj
    omega
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2
    decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2
    decide
  · intro u hu k hk
    rw [List.mem_singleton.mp hu] at hk ⊢
    refine ⟨2, by show den_w 2 ≤ den_w 2; decide,
      by show den_w 2 ≤ den_w 2; decide, ?_⟩
    rcases hk with h3 | h4
    · subst h3
      exact rs_state_pfx2_3.symm
    · subst h4
      exact (src_4_none 2).symm

/-- The orphan pass, committed at 1 and crashed at 2, with its chunk
re-executed as `rx_unit`, is a `PassRestart` instance. Isabelle: the
interpretation `rs`. -/
theorem wit_rs_instance :
    PassRestart sc s0_w [orph_unit] (fun k => k = 3 ∨ k = 4) 2
      [rx_unit] (fun k => k = 3 ∨ k = 4) 2 1 2 := by
  refine ⟨wit_orph_contract, wit_rx_contract, ?_, ?_, ?_, ?_, ?_⟩
  · show den_w 1 ≤ den_w 2
    decide
  · show den_w 2 ≤ den_w 2
    decide
  · show den_w 2 ≤ den_w 2
    decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2
    decide
  · intro u hu late
    rw [List.mem_singleton.mp hu] at late
    exact absurd late (by show ¬ den_w 2 < den_w 2; decide)

/-- Listing key 3 is an admissible enumeration for the re-executed
chunk. It is the core's survivor-only enumeration. Isabelle:
`rx_svl_ok2`. -/
theorem rx_svl_ok2 : svl_ok2 sc [rx_unit] (fun _ => [3]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · rintro k ⟨hdom, hr, -⟩
    rcases hdom with h | h
    · subst h
      simp
    · subst h
      exact absurd rfl hr
  · intro k hk
    have hk' : k = 3 := by simpa using hk
    subst hk'
    exact Or.inl ⟨Or.inl rfl, by simp [rx_unit], rfl⟩

/-- The stream, computed: the pass's emission up to the crash, here all
of it with the absent entry for key 4 at its close, the event at
position 1 again, and the re-executed chunk's entry for key 3.
Isabelle: `wit_restart_stream_orphan`. -/
theorem wit_restart_stream_orphan :
    restart_stream sc [orph_unit] 2 [rx_unit] 2 1 2 (fun _ => [3, 4]) (fun _ => [3]) 0 =
      [⟨3, some 7⟩, ⟨1, some 1⟩, ⟨3, some 7⟩, ⟨4, none⟩, ⟨1, some 1⟩, ⟨3, some 7⟩] := by
  simp [restart_stream, emission, emission_t, closes_at, close_block, sc, L_s, den_w,
    orph_unit, rx_unit, List.zipIdx]

/-- The orphan stays removed, through the convergence theorem: key 4 is
listed by the close entry of its unit in the pass, which closed at the
crash. Isabelle: `wit_restart_orphan_stays_removed`. -/
theorem wit_restart_orphan_stays_removed :
    state_after D0_o
        (restart_stream sc [orph_unit] 2 [rx_unit] 2 1 2 (fun _ => [3, 4]) (fun _ => [3]) 0)
        4 = none := by
  have s0cmt : den_w 0 ≤ den_w 1 := by decide
  have conv := wit_rs_instance.restart_converges (D0 := D0_o)
    orph_svl_ok2 rx_svl_ok2 orph_s0lo_den s0cmt (by
      intro k _ held _ _
      have k4 : k = 4 := by
        by_cases h : k = 4
        · exact h
        · exact absurd (by simp [D0_o, h] : D0_o k = none) held
      subst k4
      refine Or.inl ⟨Or.inr rfl, ?_, by simp⟩
      show min _ 2 ≤ min 2 2
      omega)
  rw [conv 4 (Or.inl (Or.inr rfl))]
  exact src_4_none 2

/-- The orphan pass, committed at 1 and crashed at 1, before its chunk
closes, with the same re-executed chunk, is a `PassRestart` instance.
Isabelle: the interpretation `rs0`. -/
theorem wit_rs0_instance :
    PassRestart sc s0_w [orph_unit] (fun k => k = 3 ∨ k = 4) 2
      [rx_unit] (fun k => k = 3 ∨ k = 4) 2 1 1 := by
  refine ⟨wit_orph_contract, wit_rx_contract, ?_, ?_, ?_, ?_, ?_⟩
  · show den_w 1 ≤ den_w 1
    decide
  · show den_w 1 ≤ den_w 2
    decide
  · show den_w 1 ≤ den_w 2
    decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 1 ≤ den_w 2
    decide
  · intro u hu _ k hk
    rw [List.mem_singleton.mp hu] at hk
    exact hk

/-- The stream of the crash before the close, computed: the absent entry
for key 4 is never delivered, nothing is re-delivered, and the
re-executed chunk does not list key 4. Isabelle:
`wit_restart_stream_before_close`. -/
theorem wit_restart_stream_before_close :
    restart_stream sc [orph_unit] 2 [rx_unit] 2 1 1 (fun _ => [3, 4]) (fun _ => [3]) 0 =
      [⟨3, some 7⟩, ⟨1, some 1⟩, ⟨3, some 7⟩] := by
  simp [restart_stream, emission, emission_t, closes_at, close_block, sc, L_s, den_w,
    orph_unit, rx_unit, List.zipIdx]

/-- A crash before the close keeps the orphan. Isabelle:
`wit_restart_before_close_keeps_orphan`. -/
theorem wit_restart_before_close_keeps_orphan :
    state_after D0_o
        (restart_stream sc [orph_unit] 2 [rx_unit] 2 1 1 (fun _ => [3, 4]) (fun _ => [3]) 0)
        4 = some 9 := by
  rw [wit_restart_stream_before_close]
  simp [state_after, apply_ev, D0_o]

/-- The orphan is in the second branch of `restart_safe`: the sink keeps
its value, the key is absent at the frontier, no close delivered before
the crash lists it, the re-executed chunk does not list it, and no log
event mentions it. Isabelle: `wit_restart_before_close_second_branch`,
whose memberships `4 ∈ {3, 4}` in the scopes are stated as
`4 = 3 ∨ 4 = 4`. -/
theorem wit_restart_before_close_second_branch :
    state_after D0_o
        (restart_stream sc [orph_unit] 2 [rx_unit] 2 1 1 (fun _ => [3, 4]) (fun _ => [3]) 0)
        4 = D0_o 4 ∧
      state_after s0_w (sc.pfx 2) 4 = none ∧
      (((4 : Nat) = 3 ∨ (4 : Nat) = 4) →
        den_w (the_unit [orph_unit] 2 4).hi ≤ den_w 1 →
        (4 : Nat) ∉ (fun _ => [3, 4]) (the_unit [orph_unit] 2 4)) ∧
      (((4 : Nat) = 3 ∨ (4 : Nat) = 4) →
        (4 : Nat) ∉ (fun _ => [3]) (the_unit [rx_unit] 2 4)) ∧
      evs_for 4 (sc.win 0 2) = [] := by
  have the4 : the_unit [orph_unit] 2 4 = orph_unit :=
    wit_orph_contract.the_unit_eq (List.mem_singleton.mpr rfl) (Or.inr rfl)
  have quiet : evs_for 4 (sc.win 0 2) = [] := by
    show evs_for 4 [(⟨3, some 7⟩ : Event Nat Nat), ⟨1, some 1⟩] = []
    simp [evs_for]
  refine ⟨?_, src_4_none 2, ?_, ?_, quiet⟩
  · rw [wit_restart_before_close_keeps_orphan]
    rfl
  · intro _ late
    rw [the4] at late
    exact absurd late (by show ¬ den_w 2 ≤ den_w 1; decide)
  · intro _ h
    simp at h

/-- The coverage assumption of `restart_converges` fails for the orphan:
the sink holds key 4, the key is absent and quiet, and neither the
pass's close before the crash nor the re-executed chunk lists it.
Isabelle: `wit_restart_before_close_cover_fails`, whose memberships
`4 ∈ {3, 4}` in the scopes are stated as `4 = 3 ∨ 4 = 4`. -/
theorem wit_restart_before_close_cover_fails :
    D0_o 4 ≠ none ∧
      state_after s0_w (sc.pfx 2) 4 = none ∧
      evs_for 4 (sc.win 0 2) = [] ∧
      ¬ ((((4 : Nat) = 3 ∨ (4 : Nat) = 4) ∧
            den_w (the_unit [orph_unit] 2 4).hi ≤ den_w 1 ∧
            (4 : Nat) ∈ (fun _ => [3, 4]) (the_unit [orph_unit] 2 4)) ∨
          (((4 : Nat) = 3 ∨ (4 : Nat) = 4) ∧
            (4 : Nat) ∈ (fun _ => [3]) (the_unit [rx_unit] 2 4))) := by
  have the4 : the_unit [orph_unit] 2 4 = orph_unit :=
    wit_orph_contract.the_unit_eq (List.mem_singleton.mpr rfl) (Or.inr rfl)
  have quiet : evs_for 4 (sc.win 0 2) = [] := by
    show evs_for 4 [(⟨3, some 7⟩ : Event Nat Nat), ⟨1, some 1⟩] = []
    simp [evs_for]
  refine ⟨by simp [D0_o], src_4_none 2, quiet, ?_⟩
  rintro (⟨_, late, _⟩ | ⟨_, h⟩)
  · rw [the4] at late
    exact absurd late (by show ¬ den_w 2 ≤ den_w 1; decide)
  · simp at h

/-- The chunk of the re-insert fixture: key 1 behind the zero-width
bracket at coordinate 1, refresh reporting key 1 absent. Isabelle:
`ri_unit`. -/
def ri_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 1
  lo := 1
  hi := 1
  refresh := fun _ => none

/-- The re-executed chunk of the re-insert fixture: key 1 behind the
zero-width bracket at coordinate 2, refresh reporting key 1 present with
value 1. Isabelle: `rj_unit`. -/
def rj_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 1
  lo := 2
  hi := 2
  refresh := fun k => if k = 1 then some 1 else none

/-- The initial sink state with a stale row: key 1 held with value 9.
Isabelle: `D0_r`. -/
def D0_r : State Nat Nat := fun k => if k = 1 then some 9 else none

/-- The chunk of the re-insert fixture is a one-unit contract over scope
`{1}` with frontier 2, by `absence_assertion_contract` with the
observation coordinate 1. Isabelle: `ri_contract`, and the
interpretation `ri` that it justifies. -/
theorem ri_contract : CaptureContract sc s0_w [ri_unit] (fun k => k = 1) 2 := by
  refine absence_assertion_contract sc (c := 1) ?_ ?_ ?_ ?_
  · show den_w 1 ≤ den_w 1
    decide
  · show den_w 1 ≤ den_w 1
    decide
  · show den_w 1 ≤ den_w 2
    decide
  · intro k hk
    have hk1 : k = 1 := hk
    subst hk1
    show apply_ev s0_w ⟨3, some 7⟩ 1 = none
    simp [apply_ev, s0_w]

/-- The re-executed chunk of the re-insert fixture is a contract over the
scope `{1}` with frontier 2, O2 discharged at coordinate 2. Isabelle:
the interpretation `rj`. -/
theorem wit_rj_contract : CaptureContract sc s0_w [rj_unit] (fun k => k = 1) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro hk
      exact ⟨rj_unit, List.mem_singleton.mpr rfl, hk⟩
    · rintro ⟨u, hu, hk⟩
      rw [List.mem_singleton.mp hu] at hk
      exact hk
  · intro i j hi hj hne k _ _
    simp only [List.length_cons, List.length_nil] at hi hj
    omega
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2
    decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2
    decide
  · intro u hu k hk
    rw [List.mem_singleton.mp hu] at hk ⊢
    refine ⟨2, by show den_w 2 ≤ den_w 2; decide,
      by show den_w 2 ≤ den_w 2; decide, ?_⟩
    have hk1 : k = 1 := hk
    subst hk1
    exact rs_state_pfx2_1.symm

/-- The re-insert pass, committed at 0 and crashed at 2, with its chunk
re-executed as `rj_unit`, is a `PassRestart` instance. Isabelle: the
interpretation `rt`. -/
theorem wit_rt_instance :
    PassRestart sc s0_w [ri_unit] (fun k => k = 1) 2 [rj_unit] (fun k => k = 1) 2 0 2 := by
  refine ⟨ri_contract, wit_rj_contract, ?_, ?_, ?_, ?_, ?_⟩
  · show den_w 0 ≤ den_w 2
    decide
  · show den_w 2 ≤ den_w 2
    decide
  · show den_w 2 ≤ den_w 2
    decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2
    decide
  · intro u hu late
    rw [List.mem_singleton.mp hu] at late
    exact absurd late (by show ¬ den_w 2 < den_w 1; decide)

/-- Listing key 1 is an admissible enumeration for the chunk of the
re-insert fixture: key 1 is absent and untouched. Isabelle:
`ri_svl_ok2`. -/
theorem ri_svl_ok2 : svl_ok2 sc [ri_unit] (fun _ => [1]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · rintro k ⟨-, hr, -⟩
    exact absurd rfl hr
  · intro k hk
    have hk' : k = 1 := by simpa using hk
    subst hk'
    exact Or.inr ⟨rfl, rfl, rfl⟩

/-- Listing key 1 is an admissible enumeration for the re-executed
chunk of the re-insert fixture: key 1 is a survivor. Isabelle:
`rj_svl_ok2`. -/
theorem rj_svl_ok2 : svl_ok2 sc [rj_unit] (fun _ => [1]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · rintro k ⟨hdom, -, -⟩
    have hk1 : k = 1 := hdom
    subst hk1
    simp
  · intro k hk
    have hk' : k = 1 := by simpa using hk
    subst hk'
    exact Or.inl ⟨rfl, by simp [rj_unit], rfl⟩

/-- The stream, computed. For key 1: the absent entry at the close, the
insert, the insert again, and the re-executed chunk's entry with the
live value. Isabelle: `wit_restart_stream_insert`. -/
theorem wit_restart_stream_insert :
    restart_stream sc [ri_unit] 2 [rj_unit] 2 0 2 (fun _ => [1]) (fun _ => [1]) 0 =
      [⟨3, some 7⟩, ⟨1, none⟩, ⟨1, some 1⟩, ⟨3, some 7⟩, ⟨1, some 1⟩, ⟨1, some 1⟩] := by
  simp [restart_stream, emission, emission_t, closes_at, close_block, sc, L_s, den_w,
    ri_unit, rj_unit, List.zipIdx]

/-- The live row is kept, through the convergence theorem. Isabelle:
`wit_restart_live_row_kept`. -/
theorem wit_restart_live_row_kept :
    state_after D0_r
        (restart_stream sc [ri_unit] 2 [rj_unit] 2 0 2 (fun _ => [1]) (fun _ => [1]) 0)
        1 = some 1 := by
  have s0lo : ∀ u ∈ [ri_unit], den_w 0 ≤ den_w u.lo := by
    intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 0 ≤ den_w 1
    decide
  have conv := wit_rt_instance.restart_converges (D0 := D0_r)
    ri_svl_ok2 rj_svl_ok2 s0lo (Nat.le_refl _) (by
      intro k hk _ _ _
      have k1 : k = 1 := hk.elim id id
      subst k1
      refine Or.inl ⟨rfl, ?_, by simp⟩
      show min _ 2 ≤ min 2 2
      omega)
  rw [conv 1 (Or.inl rfl)]
  exact rs_state_pfx2_1

/-! ## Fixture: the sink can hold an older value while the segment is re-delivered -/

/-- The transient log: key 5 is set to 1, deleted, and set to 2.
Isabelle: `L_t`. -/
def L_t : List (Event Nat Nat) := [⟨5, some 1⟩, ⟨5, none⟩, ⟨5, some 2⟩]

/-- The transient denotation: coordinate `c` denotes the prefix of length
`min c 3`. Isabelle: `den_t`. -/
def den_t (c : Nat) : Nat := min c 3

/-- The coordinate space over `L_t`. Isabelle: the interpretation `tc`
of `coordinate_space`. -/
def tc : CoordinateSpace Nat Nat Nat where
  log := L_t
  den := den_t
  den_le_len := fun c => by
    show min c 3 ≤ L_t.length
    rw [show L_t.length = 3 from rfl]
    omega

/-- The transient chunk: key 5 behind the zero-width bracket at
coordinate 3, refresh reporting key 5 present with value 2. Isabelle:
`tr_unit`. -/
def tr_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 5
  lo := 3
  hi := 3
  refresh := fun k => if k = 5 then some 2 else none

/-- Key 5 holds value 2 at the end of `L_t`. Port-local, a concrete
evaluation of the per-key fold. It is the content of
`wit_transient_source`, which the Isabelle theory states after the
contract that needs it. -/
private theorem tc_state_pfx3_5 : state_after s0_w (tc.pfx 3) 5 = some 2 := by
  show apply_ev (apply_ev (apply_ev s0_w ⟨5, some 1⟩) ⟨5, none⟩) ⟨5, some 2⟩ 5 = some 2
  simp [apply_ev]

/-- The transient chunk is a contract over the scope `{5}` with frontier
3, O2 discharged at coordinate 3. Isabelle: the interpretation `tr1`. -/
theorem wit_tr1_contract : CaptureContract tc s0_w [tr_unit] (fun k => k = 5) 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro hk
      exact ⟨tr_unit, List.mem_singleton.mpr rfl, hk⟩
    · rintro ⟨u, hu, hk⟩
      rw [List.mem_singleton.mp hu] at hk
      exact hk
  · intro i j hi hj hne k _ _
    simp only [List.length_cons, List.length_nil] at hi hj
    omega
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_t 3 ≤ den_t 3
    decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_t 3 ≤ den_t 3
    decide
  · intro u hu k hk
    rw [List.mem_singleton.mp hu] at hk ⊢
    refine ⟨3, by show den_t 3 ≤ den_t 3; decide,
      by show den_t 3 ≤ den_t 3; decide, ?_⟩
    have hk5 : k = 5 := hk
    subst hk5
    exact tc_state_pfx3_5.symm

/-- No chunk is re-executed: the empty family is a contract over the
empty scope with frontier 3. Isabelle: the interpretation `tr2`. -/
theorem wit_tr2_contract : CaptureContract tc s0_w [] (fun _ => False) 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro h
      exact h.elim
    · rintro ⟨u, hu, -⟩
      cases hu
  · intro i j hi _ _ _ _ _
    simp only [List.length_nil] at hi
    omega
  · intro u hu
    cases hu
  · intro u hu
    cases hu
  · intro u hu
    cases hu

/-- The transient pass, committed at 0 and crashed at 3, after its close,
with no re-executed chunk, is a `PassRestart` instance. Isabelle: the
interpretation `rtr`. -/
theorem wit_rtr_instance :
    PassRestart tc s0_w [tr_unit] (fun k => k = 5) 3 [] (fun _ => False) 3 0 3 := by
  refine ⟨wit_tr1_contract, wit_tr2_contract, ?_, ?_, ?_, ?_, ?_⟩
  · show den_t 0 ≤ den_t 3
    decide
  · show den_t 3 ≤ den_t 3
    decide
  · show den_t 3 ≤ den_t 3
    decide
  · intro u hu
    cases hu
  · intro u hu late
    rw [List.mem_singleton.mp hu] at late
    exact absurd late (by show ¬ den_t 3 < den_t 3; decide)

/-- Listing key 5 is an admissible enumeration for the transient chunk.
Isabelle: `tr1_svl_ok2`. -/
theorem tr1_svl_ok2 : svl_ok2 tc [tr_unit] (fun _ => [5]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · rintro k ⟨hdom, -, -⟩
    have hk5 : k = 5 := hdom
    subst hk5
    simp
  · intro k hk
    have hk' : k = 5 := by simpa using hk
    subst hk'
    exact Or.inl ⟨rfl, by simp [tr_unit], rfl⟩

/-- The empty enumeration is admissible for the empty family. Isabelle:
`tr2_svl_ok2`. -/
theorem tr2_svl_ok2 : svl_ok2 tc [] (fun _ => []) := by
  intro u hu
  cases hu

/-- The stream, computed. It has seven items: the pass's whole emission
with the close entry for key 5, then the whole log a second time.
Isabelle: `wit_restart_stream_transient`. -/
theorem wit_restart_stream_transient :
    restart_stream tc [tr_unit] 3 [] 3 0 3 (fun _ => [5]) (fun _ => []) 0 =
      [⟨5, some 1⟩, ⟨5, none⟩, ⟨5, some 2⟩, ⟨5, some 2⟩,
        ⟨5, some 1⟩, ⟨5, none⟩, ⟨5, some 2⟩] := by
  simp [restart_stream, emission, emission_t, closes_at, close_block, tc, L_t, den_t,
    tr_unit, List.zipIdx]

/-- The source holds key 5 with value 2 at the end of the log. Isabelle:
`wit_transient_source`. -/
theorem wit_transient_source : state_after s0_w (tc.pfx 3) 5 = some 2 :=
  tc_state_pfx3_5

/-- After six items of the stream the sink has key 5 deleted, while the
source holds 2. Isabelle: `wit_restart_transient_mid`. -/
theorem wit_restart_transient_mid :
    state_after s0_w
        ((restart_stream tc [tr_unit] 3 [] 3 0 3 (fun _ => [5]) (fun _ => []) 0).take 6)
        5 = none := by
  rw [wit_restart_stream_transient]
  simp [state_after, apply_ev]

/-- At the end of the stream the sink holds the source value, as
`restart_converges` states. Isabelle: `wit_restart_transient_end`. -/
theorem wit_restart_transient_end :
    state_after s0_w (restart_stream tc [tr_unit] 3 [] 3 0 3 (fun _ => [5]) (fun _ => []) 0)
      5 = some 2 := by
  have s0lo : ∀ u ∈ [tr_unit], den_t 0 ≤ den_t u.lo := by
    intro u hu
    rw [List.mem_singleton.mp hu]
    show den_t 0 ≤ den_t 3
    decide
  have conv := wit_rtr_instance.restart_converges (D0 := s0_w)
    tr1_svl_ok2 tr2_svl_ok2 s0lo (Nat.le_refl _) (by
      intro k _ held _ _
      exact absurd rfl held)
  rw [conv 5 (Or.inl rfl)]
  exact wit_transient_source

end

end DBLogContract
