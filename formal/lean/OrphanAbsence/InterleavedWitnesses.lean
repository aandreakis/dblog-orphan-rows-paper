import OrphanAbsence.Interleaved
import OrphanAbsence.ContractUnits
import OrphanAbsence.Witnesses
import OrphanAbsence.CompositionWitnesses

/-!
# Fixtures: a request served inside the pass removes the orphan

This file ports the fixtures of `Orphan_Absence_Interleaved.thy`. The
pass of the orphan fixture of `Witnesses.lean`, run with the core's
survivor-only enumeration from coordinate 0 to frontier 2, leaves the
orphan key 4 in the sink. Its one chunk owns keys 3 and 4 with the
bracket from coordinate 1 to coordinate 2 and closes at position 2.
Three requests for key 4 are served inside the pass's span, each the
one-unit contract of `absence_assertion_contract`.

* `rqb_unit`: bracket from 0 to 1, read at 1. It closes before the
  chunk does (`wit_request_before_close`).
* `rq_unit` of `CompositionWitnesses.lean`: bracket from 2 to 2, read
  at 2. It closes at the pass's frontier, after the chunk at the same
  position (`wit_request_after_close`). Its stream is the sequential
  composition of that theory (`wit_after_close_is_composition`).
* `rqo_unit`: bracket from 0 to 2, read at 1. Its window overlaps the
  chunk's window (`rqo_overlaps_chunk`, `wit_request_overlapping_chunk`).

The Isabelle lemmas `rqb_contract` and `rqo_contract` and the
interpretations `rqb` and `rqo` built from them state one fact each,
so each is one theorem here, as `rq_contract` in
`CompositionWitnesses.lean`. The interpretations `pwb`, `pwa` and
`pwo` of `pass_with_request` are the theorems `wit_pwb_instance`,
`wit_pwa_instance` and `wit_pwo_instance`.

Like `Witnesses.lean`, this file does not make classical decidability a
local instance, so `decide` evaluates the concrete comparisons. Set
equalities such as `rqb.absent_untouched rqb_unit = {4}` are stated
pointwise.
-/

namespace DBLogContract

noncomputable section

/-- The request that closes before the chunk: key 4 behind the bracket
from coordinate 0 to coordinate 1, refresh reporting key 4 absent.
Isabelle: `rqb_unit`. -/
def rqb_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 4
  lo := 0
  hi := 1
  refresh := fun _ => none

/-- The request whose window overlaps the chunk's: key 4 behind the
bracket from coordinate 0 to coordinate 2, refresh reporting key 4
absent. Isabelle: `rqo_unit`. -/
def rqo_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 4
  lo := 0
  hi := 2
  refresh := fun _ => none

/-- Key 4 is absent at every coordinate of the fixture log, since no
event of `L_s` mentions it. Isabelle: `src_4_none`. -/
theorem src_4_none (c : Nat) : state_after s0_w (sc.pfx c) 4 = none := by
  have h : evs_for 4 (sc.pfx c) = [] := by
    refine List.filter_eq_nil_iff.mpr (fun x hx => ?_)
    have hx' : x ∈ L_s := List.mem_of_mem_take hx
    have hx'' : x = ⟨3, some 7⟩ ∨ x = ⟨1, some 1⟩ := by
      simpa [L_s] using hx'
    rcases hx'' with rfl | rfl <;> simp
  rw [state_after_no_events h s0_w]
  rfl

/-- The request that closes before the chunk is a one-unit contract
over scope `{4}` with frontier 2, by `absence_assertion_contract` with
the observation coordinate 1. Isabelle: `rqb_contract`, and the
interpretation `rqb` that it justifies. -/
theorem rqb_contract : CaptureContract sc s0_w [rqb_unit] (fun k => k = 4) 2 := by
  refine absence_assertion_contract sc (c := 1) ?_ ?_ ?_ ?_
  · show den_w 0 ≤ den_w 1
    decide
  · show den_w 1 ≤ den_w 1
    decide
  · show den_w 1 ≤ den_w 2
    decide
  · intro k hk
    have hk4 : k = 4 := hk
    subst hk4
    exact src_4_none 1

/-- The request whose window overlaps the chunk's is a one-unit
contract over scope `{4}` with frontier 2, by
`absence_assertion_contract` with the observation coordinate 1.
Isabelle: `rqo_contract`, and the interpretation `rqo` that it
justifies. -/
theorem rqo_contract : CaptureContract sc s0_w [rqo_unit] (fun k => k = 4) 2 := by
  refine absence_assertion_contract sc (c := 1) ?_ ?_ ?_ ?_
  · show den_w 0 ≤ den_w 1
    decide
  · show den_w 1 ≤ den_w 2
    decide
  · show den_w 2 ≤ den_w 2
    decide
  · intro k hk
    have hk4 : k = 4 := hk
    subst hk4
    exact src_4_none 1

/-- The orphan pass with the request that closes before the chunk is a
`PassWithRequest` instance. Isabelle: the interpretation `pwb`. -/
theorem wit_pwb_instance :
    PassWithRequest sc s0_w [orph_unit] (fun k => k = 3 ∨ k = 4) 2
      [rqb_unit] (fun k => k = 4) :=
  ⟨wit_orph_contract, rqb_contract⟩

/-- The orphan pass with the request that closes at the frontier is a
`PassWithRequest` instance. Isabelle: the interpretation `pwa`. -/
theorem wit_pwa_instance :
    PassWithRequest sc s0_w [orph_unit] (fun k => k = 3 ∨ k = 4) 2
      [rq_unit] (fun k => k = 4) :=
  ⟨wit_orph_contract, rq_contract⟩

/-- The orphan pass with the request whose window overlaps the chunk's
is a `PassWithRequest` instance. Isabelle: the interpretation `pwo`. -/
theorem wit_pwo_instance :
    PassWithRequest sc s0_w [orph_unit] (fun k => k = 3 ∨ k = 4) 2
      [rqo_unit] (fun k => k = 4) :=
  ⟨wit_orph_contract, rqo_contract⟩

/-- The absent untouched keys of the request that closes before the
chunk are exactly key 4. Isabelle: `rqb_absent_untouched`, stated
there as a set equality. -/
theorem rqb_absent_untouched (k : Nat) :
    absent_untouched sc rqb_unit k ↔ k = 4 := by
  have hwin : evs_for 4 (sc.win rqb_unit.lo rqb_unit.hi) = [] := by
    show evs_for 4 [(⟨3, some 7⟩ : Event Nat Nat)] = []
    simp [evs_for]
  constructor
  · rintro ⟨hdom, -, -⟩
    exact hdom
  · intro h
    subst h
    exact ⟨rfl, rfl, hwin⟩

/-- Listing key 4 is an admissible enumeration for the request that
closes before the chunk. Isabelle: `rqb_svl_ok2`. -/
theorem rqb_svl_ok2 : svl_ok2 sc [rqb_unit] (fun _ => [4]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · rintro k ⟨-, hr, -⟩
    exact absurd rfl hr
  · intro k hk
    have hk' : k = 4 := by simpa using hk
    exact Or.inr ((rqb_absent_untouched k).mpr hk')

/-- The absent untouched keys of the request whose window overlaps the
chunk's are exactly key 4. Isabelle: `rqo_absent_untouched`, stated
there as a set equality. -/
theorem rqo_absent_untouched (k : Nat) :
    absent_untouched sc rqo_unit k ↔ k = 4 := by
  have hwin : evs_for 4 (sc.win rqo_unit.lo rqo_unit.hi) = [] := by
    show evs_for 4 [(⟨3, some 7⟩ : Event Nat Nat), ⟨1, some 1⟩] = []
    simp [evs_for]
  constructor
  · rintro ⟨hdom, -, -⟩
    exact hdom
  · intro h
    subst h
    exact ⟨rfl, rfl, hwin⟩

/-- Listing key 4 is an admissible enumeration for the request whose
window overlaps the chunk's. Isabelle: `rqo_svl_ok2`. -/
theorem rqo_svl_ok2 : svl_ok2 sc [rqo_unit] (fun _ => [4]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · rintro k ⟨-, hr, -⟩
    exact absurd rfl hr
  · intro k hk
    have hk' : k = 4 := by simpa using hk
    exact Or.inr ((rqo_absent_untouched k).mpr hk')

/-- Consumption starts at coordinate 0, at or below the chunk's low
edge, stated with the denotation. Isabelle: `orph_s0lo_den`. -/
theorem orph_s0lo_den : ∀ u ∈ [orph_unit], den_w 0 ≤ den_w u.lo := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  show den_w 0 ≤ den_w 1
  decide

/-- The stream of the request that closes before the chunk, computed.
The request's absent entry for key 4 precedes the log event at
position 1 and the chunk's close entry for key 3. Isabelle:
`wit_stream_before_close`. -/
theorem wit_stream_before_close :
    inter sc [orph_unit] 2 [rqb_unit] (fun _ => [3]) (fun _ => [4]) 0 =
      [⟨3, some 7⟩, ⟨4, none⟩, ⟨1, some 1⟩, ⟨3, some 7⟩] := by
  simp [inter, inter_t, closes_at, close_block, sc, L_s, den_w, orph_unit, rqb_unit,
    List.zipIdx]

/-- The stream of the request that closes at the frontier, computed.
The request's absent entry for key 4 comes last. Isabelle:
`wit_stream_after_close`. -/
theorem wit_stream_after_close :
    inter sc [orph_unit] 2 [rq_unit] (fun _ => [3]) (fun _ => [4]) 0 =
      [⟨3, some 7⟩, ⟨1, some 1⟩, ⟨3, some 7⟩, ⟨4, none⟩] := by
  simp [inter, inter_t, closes_at, close_block, sc, L_s, den_w, orph_unit, rq_unit,
    List.zipIdx]

/-- The stream of the request that closes at the frontier is exactly
the sequential composition of `Composition.lean`. Isabelle:
`wit_after_close_is_composition`. -/
theorem wit_after_close_is_composition :
    inter sc [orph_unit] 2 [rq_unit] (fun _ => [3]) (fun _ => [4]) 0 =
      composed sc [orph_unit] 2 [rq_unit] 2 (fun _ => [3]) (fun _ => [4]) 0 := by
  have h : composed sc [orph_unit] 2 [rq_unit] 2 (fun _ => [3]) (fun _ => [4]) 0 =
      [⟨3, some 7⟩, ⟨1, some 1⟩, ⟨3, some 7⟩, ⟨4, none⟩] := by
    simp [composed, emission, emission_t, closes_at, close_block, sc, L_s, den_w,
      orph_unit, rq_unit, List.zipIdx]
  rw [wit_stream_after_close, h]

/-- A request that closes before the chunk does removes the orphan.
Isabelle: `wit_request_before_close`. -/
theorem wit_request_before_close :
    state_after D0_o (inter sc [orph_unit] 2 [rqb_unit] (fun _ => [3]) (fun _ => [4]) 0) 4 =
      none := by
  have s0lo2 : ∀ u ∈ [rqb_unit], den_w 0 ≤ den_w u.lo := by
    intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 0 ≤ den_w 0
    decide
  have conv := wit_pwb_instance.pass_with_request_converges (D0 := D0_o)
    orph_svl_ok2_core rqb_svl_ok2 orph_s0lo_den s0lo2 (by
      intro k _ held _ _
      have k4 : k = 4 := by
        by_cases h : k = 4
        · exact h
        · exact absurd (by simp [D0_o, h] : D0_o k = none) held
      subst k4
      exact Or.inr ⟨rfl, by simp⟩)
  rw [conv 4 (Or.inr rfl)]
  exact src_4_none 2

/-- A request that closes after the chunk, through the request
corollary: the request asks for key 4, read at coordinate 2, and the
pass leaves no other key wrong, because it lists key 3. Isabelle:
`wit_request_after_close`. -/
theorem wit_request_after_close :
    state_after D0_o (inter sc [orph_unit] 2 [rq_unit] (fun _ => [3]) (fun _ => [4]) 0) 4 =
      none := by
  have s0lo2 : ∀ u ∈ [rq_unit], den_w 0 ≤ den_w u.lo := by
    intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 0 ≤ den_w 2
    decide
  have lists : ∀ u ∈ [rq_unit], ∀ k, absent_untouched sc u k →
      k ∈ (fun _ => [4]) u := by
    intro u hu k hk
    rw [List.mem_singleton.mp hu] at hk
    rw [(rq_absent_untouched k).mp hk]
    simp
  have s0_rc : ∀ k : Nat, k = 4 → den_w 0 ≤ den_w ((fun _ => (2 : Nat)) k) := by
    intro _ _
    show den_w 0 ≤ den_w 2
    decide
  have rc_f1 : ∀ k : Nat, k = 4 → den_w ((fun _ => (2 : Nat)) k) ≤ den_w 2 :=
    fun _ _ => Nat.le_refl _
  have sc2_abs : ∀ k : Nat, k = 4 →
      state_after s0_w (sc.pfx ((fun _ => (2 : Nat)) k)) k = none → k = 4 :=
    fun _ hk _ => hk
  have asked : ∀ k, (k = 3 ∨ k = 4) →
      state_after D0_o (emission sc [orph_unit] 2 (fun _ => [3]) 0) k ≠
        sink_at sc [orph_unit] 2 2 k → k = 4 := by
    intro k k1 wrong
    have hnl :=
      ((wit_pwa_instance.pass_leaves_wrong_iff orph_svl_ok2_core orph_s0lo_den k1
        D0_o).mp wrong).2.2.1
    rcases k1 with h3 | h4
    · subst h3
      exact (hnl (by simp)).elim
    · exact h4
  have conv := wit_pwa_instance.request_in_pass_converges (D0 := D0_o)
    (req := fun k => k = 4) (rc := fun _ => 2)
    orph_svl_ok2_core rq_svl_ok2 orph_s0lo_den s0lo2 lists s0_rc rc_f1 sc2_abs asked
  rw [conv 4 (Or.inr rfl)]
  exact src_4_none 2

/-- The window of the request `rqo_unit` overlaps the chunk's window:
neither closes before the other opens. Isabelle: `rqo_overlaps_chunk`. -/
theorem rqo_overlaps_chunk :
    ¬ (den_w rqo_unit.hi ≤ den_w orph_unit.lo ∨ den_w orph_unit.hi ≤ den_w rqo_unit.lo) := by
  show ¬ (den_w 2 ≤ den_w 1 ∨ den_w 2 ≤ den_w 0)
  decide

/-- A request whose window overlaps the chunk's window removes the
orphan too. Isabelle: `wit_request_overlapping_chunk`. -/
theorem wit_request_overlapping_chunk :
    state_after D0_o (inter sc [orph_unit] 2 [rqo_unit] (fun _ => [3]) (fun _ => [4]) 0) 4 =
      none := by
  have s0lo2 : ∀ u ∈ [rqo_unit], den_w 0 ≤ den_w u.lo := by
    intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 0 ≤ den_w 0
    decide
  have conv := wit_pwo_instance.pass_with_request_converges (D0 := D0_o)
    orph_svl_ok2_core rqo_svl_ok2 orph_s0lo_den s0lo2 (by
      intro k _ held _ _
      have k4 : k = 4 := by
        by_cases h : k = 4
        · exact h
        · exact absurd (by simp [D0_o, h] : D0_o k = none) held
      subst k4
      exact Or.inr ⟨rfl, by simp⟩)
  rw [conv 4 (Or.inr rfl)]
  exact src_4_none 2

end

end DBLogContract
