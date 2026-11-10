import OrphanAbsence.Composition
import OrphanAbsence.ContractUnits
import OrphanAbsence.Witnesses

/-!
# Fixture: a request completes a pass that left an orphan

This file ports the fixture of `Orphan_Absence_Composition.thy`. The
pass of the orphan fixture of `Witnesses.lean`, run with the core's
survivor-only enumeration, leaves the orphan key 4 in the sink. A later
request for key 4, read at coordinate 2 where key 4 is absent, is the
one-unit contract of `absence_assertion_contract`, and the composed
stream removes the orphan.

* `rq_unit`, `rq_contract`: the request's unit and its contract. The
  Isabelle lemma `rq_contract` and the interpretation `rq` built from it
  state the same fact, so both are `rq_contract` here.
* `wit_pr_instance`: the pass and the request form a `PassThenRead`
  instance. Isabelle: the interpretation `pr`.
* `wit_request_completes_pass`: the composed stream removes the orphan,
  through `pass_then_read_converges`.
* `wit_request_after_pass`: the same result through
  `request_after_pass_converges`. The request asks for key 4, read at
  coordinate 2, and the pass leaves no other key wrong, because it lists
  key 3.

Like `Witnesses.lean`, this file does not make classical decidability a
local instance, so `decide` evaluates the concrete comparisons. Set
equalities such as `rq.survivors rq_unit = {}` are stated pointwise.
-/

namespace DBLogContract

noncomputable section

/-- The request's unit: key 4 behind the zero-width bracket at
coordinate 2, refresh reporting key 4 absent. Isabelle: `rq_unit`. -/
def rq_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 4
  lo := 2
  hi := 2
  refresh := fun _ => none

/- Concrete evaluation of the per-key fold over `L_s`. -/

private theorem rq_state_pfx2_4 : state_after s0_w (sc.pfx 2) 4 = none := by
  show apply_ev (apply_ev s0_w ⟨3, some 7⟩) ⟨1, some 1⟩ 4 = none
  simp [apply_ev, s0_w]

/-- The request is a one-unit contract over scope `{4}` with frontier
2, by `absence_assertion_contract` with the observation coordinate 2.
Isabelle: `rq_contract`, and the interpretation `rq` that it
justifies. -/
theorem rq_contract : CaptureContract sc s0_w [rq_unit] (fun k => k = 4) 2 := by
  refine absence_assertion_contract sc (c := 2) ?_ ?_ ?_ ?_
  · show den_w 2 ≤ den_w 2
    decide
  · show den_w 2 ≤ den_w 2
    decide
  · show den_w 2 ≤ den_w 2
    decide
  · intro k hk
    have hk4 : k = 4 := hk
    subst hk4
    exact rq_state_pfx2_4

/-- The orphan pass followed by the request is a `PassThenRead`
instance. Isabelle: the interpretation `pr`. -/
theorem wit_pr_instance :
    PassThenRead sc s0_w [orph_unit] (fun k => k = 3 ∨ k = 4) 2
      [rq_unit] (fun k => k = 4) 2 := by
  refine ⟨wit_orph_contract, rq_contract, ?_, ?_⟩
  · show den_w 2 ≤ den_w 2
    decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2
    decide

/-- Key 4 is untouched by the request's empty window. Isabelle:
`rq_win_4`. -/
theorem rq_win_4 : evs_for 4 (sc.win rq_unit.lo rq_unit.hi) = [] := rfl

/-- The request's unit has no survivors. Isabelle: `rq_survivors`,
stated there as `rq.survivors rq_unit = {}`. -/
theorem rq_survivors (k : Nat) : ¬ survivors sc rq_unit k := by
  rintro ⟨-, hr, -⟩
  exact hr rfl

/-- The absent untouched keys of the request's unit are exactly key 4.
Isabelle: `rq_absent_untouched`, stated there as a set equality. -/
theorem rq_absent_untouched (k : Nat) :
    absent_untouched sc rq_unit k ↔ k = 4 := by
  constructor
  · rintro ⟨hdom, -, -⟩
    exact hdom
  · intro h
    subst h
    exact ⟨rfl, rfl, rq_win_4⟩

/-- Listing key 4 is an admissible enumeration for the request.
Isabelle: `rq_svl_ok2`. -/
theorem rq_svl_ok2 : svl_ok2 sc [rq_unit] (fun _ => [4]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · intro k hk
    exact absurd hk (rq_survivors k)
  · intro k hk
    have hk' : k = 4 := by simpa using hk
    exact Or.inr ((rq_absent_untouched k).mpr hk')

/-- The composed stream of the survivor-only pass and the request
removes the orphan. Isabelle: `wit_request_completes_pass`. -/
theorem wit_request_completes_pass :
    state_after D0_o
      (composed sc [orph_unit] 2 [rq_unit] 2 (fun _ => [3]) (fun _ => [4]) 0) 4 =
      none := by
  have s0lo : ∀ u ∈ [orph_unit], sc.den 0 ≤ sc.den u.lo := by
    intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 0 ≤ den_w 1
    decide
  have s0f1 : sc.den 0 ≤ sc.den 2 := by
    show den_w 0 ≤ den_w 2
    decide
  have conv := wit_pr_instance.pass_then_read_converges (D0 := D0_o)
    orph_svl_ok2_core rq_svl_ok2 s0lo s0f1 (by
      intro k _ held _ _
      have k4 : k = 4 := by
        by_cases h : k = 4
        · exact h
        · exact absurd (by simp [D0_o, h] : D0_o k = none) held
      subst k4
      exact Or.inr ⟨rfl, by simp⟩)
  rw [conv 4 (Or.inr rfl)]
  exact rq_state_pfx2_4

/-- The same result through the request corollary: the request asks for
key 4, read at coordinate 2, and the pass leaves no other key wrong,
because it lists key 3. Isabelle: `wit_request_after_pass`. -/
theorem wit_request_after_pass :
    state_after D0_o
      (composed sc [orph_unit] 2 [rq_unit] 2 (fun _ => [3]) (fun _ => [4]) 0) 4 =
      none := by
  have s0lo : ∀ u ∈ [orph_unit], sc.den 0 ≤ sc.den u.lo := by
    intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 0 ≤ den_w 1
    decide
  have s0f1 : sc.den 0 ≤ sc.den 2 := by
    show den_w 0 ≤ den_w 2
    decide
  have lists : ∀ u ∈ [rq_unit], ∀ k, absent_untouched sc u k →
      k ∈ (fun _ => [4]) u := by
    intro u hu k hk
    rw [List.mem_singleton.mp hu] at hk
    rw [(rq_absent_untouched k).mp hk]
    simp
  have asked : ∀ k, (k = 3 ∨ k = 4) →
      state_after D0_o (emission sc [orph_unit] 2 (fun _ => [3]) 0) k ≠
        sink_at sc [orph_unit] 2 2 k → k = 4 := by
    intro k k1 wrong
    have hnl :=
      ((wit_pr_instance.pass_leaves_wrong_iff orph_svl_ok2_core s0lo k1 D0_o).mp
        wrong).2.2.1
    rcases k1 with h3 | h4
    · subst h3
      exact (hnl (by simp)).elim
    · exact h4
  have conv := wit_pr_instance.request_after_pass_converges (D0 := D0_o)
    (req := fun k => k = 4) (rc := fun _ => 2)
    orph_svl_ok2_core rq_svl_ok2 s0lo s0f1 lists
    (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ hk _ => hk) asked
  rw [conv 4 (Or.inr rfl)]
  exact rq_state_pfx2_4

end

end DBLogContract
