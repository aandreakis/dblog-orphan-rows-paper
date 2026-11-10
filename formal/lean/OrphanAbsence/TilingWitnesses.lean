import OrphanAbsence.Tiling

/-!
# Fixtures: the terminal rule, a completed pass, a stopped pass

This file ports the concrete examples of `Orphan_Absence_Tiling.thy`,
from its subsections "The terminal rule is necessary" and "Witnesses".
The keys are natural numbers.

* `terminal_rule_necessary`: chunk limit 2, previous last key 10, present
  keys 11, 12 and 13. The page returns 11 and 12, a full page. An
  open-above range after it contains the present key 13, which the page
  did not return. The same page arises from the source with keys 11 and
  12 only (`terminal_rule_page_without_13`,
  `terminal_rule_page_with_13`).
* `wit_completed`: a completed bounded pass with chunk limit 5, recorded
  maximum 10 and two tail reads allowed. Key 12 is inserted above the
  maximum after the first read. Its ranges cover every key
  (`wit_completed_covers`).
* `wit_limit`: a pass stopped by the tail-read limit, with chunk limit 2,
  recorded maximum 3 and one tail read allowed. Every key above 5 is
  uncovered (`wit_limit_uncovered`), although key 6 is present
  (`wit_limit_key6`).

A concrete set such as `{1, 2, 3, 5, 6, 8, 9, 10}` is the predicate of
membership in the list `[1, 2, 3, 5, 6, 8, 9, 10]`. The values of the
classical definition `page` are proved through `smallest_eqI`, as the
Isabelle theory does. Like the other fixture modules, this file does not
make classical decidability a local instance, so `decide` evaluates the
concrete comparisons. Set equalities are stated pointwise.
-/

namespace DBLogContract

namespace Tiling

noncomputable section

/-! ## The terminal rule is necessary -/

/-- The concrete counterexample of the design: a full page closed open
above would certify the present key 13 absent. The assumption
`S = {11, 12, 13}` is stated pointwise. Isabelle:
`terminal_rule_necessary`. -/
theorem terminal_rule_necessary {S : Nat → Prop} {r : Chunk Nat}
    (hS : ∀ k, S k ↔ k ∈ [11, 12, 13])
    (hr : r = { c_lo := some 10, c_hi := none, c_rows := page S (some 10) 2 }) :
    r.c_rows = [11, 12] ∧ S 13 ∧ chunk_keys r 13 ∧ 13 ∉ r.c_rows := by
  have p : page S (some 10) 2 = [11, 12] := by
    unfold page
    apply smallest_eqI (xs := [11, 12, 13])
    · decide
    · intro k
      rw [hS]
      simp only [List.mem_cons, List.not_mem_nil, or_false, above_lo_Some]
      omega
    · rfl
  subst hr
  refine ⟨p, (hS 13).mpr (by decide), ?_, ?_⟩
  · show above_lo (some 10) 13 ∧ upto_hi none 13
    exact ⟨(above_lo_Some 10 13).mpr (by decide), trivial⟩
  · show 13 ∉ page S (some 10) 2
    rw [p]
    decide

/-- On the source with keys 11 and 12 only the page is the same. HOL's
`{11, 12 :: nat}` is membership in `[11, 12]`. Isabelle:
`terminal_rule_page_without_13`. -/
theorem terminal_rule_page_without_13 :
    page (fun k => k ∈ [11, 12]) (some 10) 2 = [11, 12] := by
  unfold page
  apply smallest_eqI (xs := [11, 12])
  · decide
  · intro k
    simp only [List.mem_cons, List.not_mem_nil, or_false, above_lo_Some]
    omega
  · rfl

/-- On the source with keys 11, 12 and 13 the page returns 11 and 12.
Isabelle: `terminal_rule_page_with_13`. -/
theorem terminal_rule_page_with_13 :
    page (fun k => k ∈ [11, 12, 13]) (some 10) 2 = [11, 12] := by
  unfold page
  apply smallest_eqI (xs := [11, 12, 13])
  · decide
  · intro k
    simp only [List.mem_cons, List.not_mem_nil, or_false, above_lo_Some]
    omega
  · rfl

/-! ## Witnesses: the general statements are not vacuous -/

/-- The source at the first read: `{1, 2, 3, 5, 6, 8, 9, 10}`. Isabelle:
`W1`. -/
def W1 : Nat → Prop := fun k => k ∈ [1, 2, 3, 5, 6, 8, 9, 10]

/-- The source after key 12 is inserted: `{1, 2, 3, 5, 6, 8, 9, 10, 12}`.
Isabelle: `W2`. -/
def W2 : Nat → Prop := fun k => k ∈ [1, 2, 3, 5, 6, 8, 9, 10, 12]

/-- The source states of the three reads. Isabelle: `wit_reads`. -/
def wit_reads : List (Nat → Prop) := [W1, W2, W2]

/-- Isabelle: `W1_bpage`. -/
theorem W1_bpage : bpage W1 none 10 5 = [1, 2, 3, 5, 6] := by
  unfold bpage
  apply smallest_eqI (xs := [1, 2, 3, 5, 6, 8, 9, 10])
  · decide
  · intro k
    simp only [W1, List.mem_cons, List.not_mem_nil, or_false, above_lo_None, true_and]
    omega
  · rfl

/-- Isabelle: `W2_bpage`. -/
theorem W2_bpage : bpage W2 (some 6) 10 5 = [8, 9, 10] := by
  unfold bpage
  apply smallest_eqI (xs := [8, 9, 10])
  · decide
  · intro k
    simp only [W2, List.mem_cons, List.not_mem_nil, or_false, above_lo_Some]
    omega
  · rfl

/-- Isabelle: `W2_page`. -/
theorem W2_page : page W2 (some 10) 5 = [12] := by
  unfold page
  apply smallest_eqI (xs := [12])
  · decide
  · intro k
    simp only [W2, List.mem_cons, List.not_mem_nil, or_false, above_lo_Some]
    omega
  · rfl

/-- A concrete value of the total `last`. Port-local. -/
private theorem last_1_6 : last [1, 2, 3, 5, 6] = 6 := rfl

/-- A concrete value of the total `last`. Port-local. -/
private theorem last_1_2 : last [1, 2] = 2 := rfl

/-- A concrete value of the total `last`. Port-local. -/
private theorem last_4_5 : last [4, 5] = 5 := rfl

/-- The completed bounded pass: the main loop closes its short page at 10,
and the first tail read returns 12 in a short page. Isabelle:
`wit_completed`. -/
theorem wit_completed :
    bounded_pass 5 2 (some 10) wit_reads =
      ([{ c_lo := none, c_hi := some 6, c_rows := [1, 2, 3, 5, 6] },
        { c_lo := some 6, c_hi := some 10, c_rows := [8, 9, 10] },
        { c_lo := some 10, c_hi := none, c_rows := [12] }], .Completed) := by
  simp [wit_reads, bounded_pass, bounded_scan, W1_bpage, W2_bpage, W2_page,
    tail_scan_pos_Cons, last_1_6]

/-- The completed pass covers every key. The set equality
`covered (...) = UNIV` is stated pointwise. Isabelle:
`wit_completed_covers`. -/
theorem wit_completed_covers : ∀ k, covered (bounded_pass 5 2 (some 10) wit_reads).1 k :=
  union_on_completion (by decide) (by rw [wit_completed])

/-- The source of the stopped pass: `{1, 2, 3, 4, 5, 6}`. Isabelle: `W3`. -/
def W3 : Nat → Prop := fun k => k ∈ [1, 2, 3, 4, 5, 6]

/-- The source states of the three reads of the stopped pass. Isabelle:
`wit_reads_limit`. -/
def wit_reads_limit : List (Nat → Prop) := [W3, W3, W3]

/-- Isabelle: `W3_bpage_first`. -/
theorem W3_bpage_first : bpage W3 none 3 2 = [1, 2] := by
  unfold bpage
  apply smallest_eqI (xs := [1, 2, 3])
  · decide
  · intro k
    simp only [W3, List.mem_cons, List.not_mem_nil, or_false, above_lo_None, true_and]
    omega
  · rfl

/-- Isabelle: `W3_bpage_second`. -/
theorem W3_bpage_second : bpage W3 (some 2) 3 2 = [3] := by
  unfold bpage
  apply smallest_eqI (xs := [3])
  · decide
  · intro k
    simp only [W3, List.mem_cons, List.not_mem_nil, or_false, above_lo_Some]
    omega
  · rfl

/-- Isabelle: `W3_page_tail`. -/
theorem W3_page_tail : page W3 (some 3) 2 = [4, 5] := by
  unfold page
  apply smallest_eqI (xs := [4, 5, 6])
  · decide
  · intro k
    simp only [W3, List.mem_cons, List.not_mem_nil, or_false, above_lo_Some]
    omega
  · rfl

/-- The pass stopped by the tail-read limit: the tail read returns a full
page ending at 5. Isabelle: `wit_limit`. -/
theorem wit_limit :
    bounded_pass 2 1 (some 3) wit_reads_limit =
      ([{ c_lo := none, c_hi := some 2, c_rows := [1, 2] },
        { c_lo := some 2, c_hi := some 3, c_rows := [3] },
        { c_lo := some 3, c_hi := some 5, c_rows := [4, 5] }], .Tail_Limit (some 5)) := by
  simp [wit_reads_limit, bounded_pass, bounded_scan, W3_bpage_first, W3_bpage_second,
    W3_page_tail, last_1_2, last_4_5, tail_scan]

/-- Every key above 5 is uncovered. The set equality
`- covered (...) = {k. 5 < k}` is stated pointwise. Isabelle:
`wit_limit_uncovered`. -/
theorem wit_limit_uncovered :
    ∀ k, ¬ covered (bounded_pass 2 1 (some 3) wit_reads_limit).1 k ↔ 5 < k := by
  intro k
  rw [uncovered_on_limit (f := some 5) (by decide) (by rw [wit_limit]) k]
  rfl

/-- Key 6 is present but not covered. Isabelle: `wit_limit_key6`. -/
theorem wit_limit_key6 :
    W3 6 ∧ ¬ covered (bounded_pass 2 1 (some 3) wit_reads_limit).1 6 := by
  refine ⟨show 6 ∈ [1, 2, 3, 4, 5, 6] by decide, ?_⟩
  exact (wit_limit_uncovered 6).mpr (by decide)

end

end Tiling

end DBLogContract
