import OrphanAbsence.Replay
import DBLogContract.ContractWitnesses

/-!
# Fixtures: an orphan removed, and the read-at-high unit

This file ports the two fixtures of `Orphan_Absence.thy`. Both reuse
the witness log `L_s` and the coordinate space `sc` of the core's
fixture 4: `L_s = [⟨3, some 7⟩, ⟨1, some 1⟩]`, `den_w c = min c 2`,
and the empty initial store `s0_w`.

* The orphan fixture: one unit owns keys 3 and 4 with the bracket
  from coordinate 1 to coordinate 2. Key 3 is read as present with
  value 7, key 4 as absent. The sink starts with an orphan: it holds
  key 4 with value 9 (`D0_o`). Enumerating key 4 as an absent entry
  removes the orphan (`wit_orphan_removed`) and keeps the live row
  (`wit_orphan_present_kept`). The survivor-only enumeration of the
  core leaves the orphan in place (`wit_orphan_kept_by_omission`).
* The read-at-high fixture: Flink CDC folds the window's events into
  the chunk image and emits the merged image at the high watermark,
  so its unit reads the source at the high watermark itself. The
  bracket is zero-width and the window is empty. The contract admits
  this (`bracket_lo_hi` is not strict), no key is excluded, the
  survivors are the present keys, and the absent keys of the range are
  exactly the keys missing from the merged image. The same orphan is
  removed by enumerating it (`wit_read_at_hi_orphan_removed`).

The Isabelle interpretations `orph` and `rah` of `capture_contract`
become the theorems `wit_orph_contract` and `wit_rah_contract`, as
the core port does for its fixtures. Set equalities such as
`orph.survivors orph_unit = {3}` are stated pointwise. The concrete
evaluations are proved by rewriting, since the general definitions
are classical.
-/

namespace DBLogContract

noncomputable section

/-! ## The orphan fixture -/

/-- The orphan unit: keys 3 and 4, bracket from coordinate 1 to
coordinate 2, refresh reporting key 3 present with value 7 and key 4
absent. Isabelle: `orph_unit`. -/
def orph_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 3 ∨ k = 4
  lo := 1
  hi := 2
  refresh := fun k => if k = 3 then some 7 else none

/-- The initial sink state with an orphan: key 4 held with value 9.
Isabelle: `D0_o`. -/
def D0_o : State Nat Nat := fun k => if k = 4 then some 9 else none

/- Concrete evaluations of the per-key fold over `L_s`. -/

private theorem state_sc_pfx1_3 : state_after s0_w (sc.pfx 1) 3 = some 7 := by
  show apply_ev s0_w ⟨3, some 7⟩ 3 = some 7
  simp [apply_ev]

private theorem state_sc_pfx1_4 : state_after s0_w (sc.pfx 1) 4 = none := by
  show apply_ev s0_w ⟨3, some 7⟩ 4 = none
  simp [apply_ev, s0_w]

private theorem state_sc_pfx2_3 : state_after s0_w (sc.pfx 2) 3 = some 7 := by
  show apply_ev (apply_ev s0_w ⟨3, some 7⟩) ⟨1, some 1⟩ 3 = some 7
  simp [apply_ev]

private theorem state_sc_pfx2_4 : state_after s0_w (sc.pfx 2) 4 = none := by
  show apply_ev (apply_ev s0_w ⟨3, some 7⟩) ⟨1, some 1⟩ 4 = none
  simp [apply_ev, s0_w]

/-- The orphan instance satisfies the contract, O2 discharged for
both keys at coordinate 1. Isabelle: the `orph` interpretation. -/
theorem wit_orph_contract :
    CaptureContract sc s0_w [orph_unit] (fun k => k = 3 ∨ k = 4) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro hk
      exact ⟨orph_unit, List.mem_singleton.mpr rfl, hk⟩
    · rintro ⟨u, hu, hk⟩
      rw [List.mem_singleton.mp hu] at hk
      exact hk
  · intro i j hi hj hne k _ _
    simp only [List.length_cons, List.length_nil] at hi hj
    omega
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 1 ≤ den_w 2
    decide
  · intro u hu
    rw [List.mem_singleton.mp hu]
    show den_w 2 ≤ den_w 2
    decide
  · intro u hu k hk
    rw [List.mem_singleton.mp hu] at hk ⊢
    refine ⟨1, by show den_w 1 ≤ den_w 1; decide,
      by show den_w 1 ≤ den_w 2; decide, ?_⟩
    rcases hk with h3 | h4
    · subst h3
      exact state_sc_pfx1_3.symm
    · subst h4
      exact state_sc_pfx1_4.symm

/-- Key 4 is untouched by the orphan unit's window. Isabelle:
`orph_win_4`. -/
theorem orph_win_4 : evs_for 4 (sc.win orph_unit.lo orph_unit.hi) = [] := by
  show evs_for 4 [(⟨1, some 1⟩ : Event Nat Nat)] = []
  simp [evs_for]

/-- Key 3 is untouched by the orphan unit's window. Isabelle:
`orph_win_3`. -/
theorem orph_win_3 : evs_for 3 (sc.win orph_unit.lo orph_unit.hi) = [] := by
  show evs_for 3 [(⟨1, some 1⟩ : Event Nat Nat)] = []
  simp [evs_for]

/-- The survivors of the orphan unit are exactly key 3. Isabelle:
`orph_survivors`, stated there as a set equality. -/
theorem orph_survivors (k : Nat) : survivors sc orph_unit k ↔ k = 3 := by
  constructor
  · rintro ⟨hdom, hr, -⟩
    rcases hdom with h | h
    · exact h
    · subst h
      exact absurd rfl hr
  · intro h
    subst h
    exact ⟨Or.inl rfl, by simp [orph_unit], orph_win_3⟩

/-- The absent untouched keys of the orphan unit are exactly key 4.
Isabelle: `orph_absent_untouched`, stated there as a set equality. -/
theorem orph_absent_untouched (k : Nat) :
    absent_untouched sc orph_unit k ↔ k = 4 := by
  constructor
  · rintro ⟨hdom, hr, -⟩
    rcases hdom with h | h
    · subst h
      simp [orph_unit] at hr
    · exact h
  · intro h
    subst h
    exact ⟨Or.inr rfl, rfl, orph_win_4⟩

/-- Listing both keys is an admissible enumeration. Isabelle:
`orph_svl_ok2`. -/
theorem orph_svl_ok2 : svl_ok2 sc [orph_unit] (fun _ => [3, 4]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · intro k hk
    rw [(orph_survivors k).mp hk]
    simp
  · intro k hk
    have hk' : k = 3 ∨ k = 4 := by simpa using hk
    rcases hk' with h | h
    · exact Or.inl ((orph_survivors k).mpr h)
    · exact Or.inr ((orph_absent_untouched k).mpr h)

/-- Listing both keys covers the orphan sink. Isabelle:
`orph_covers`. -/
theorem orph_covers : covers sc [orph_unit] 2 (fun _ => [3, 4]) D0_o 0 := by
  intro u hu k habs _ _
  rw [List.mem_singleton.mp hu] at habs
  rw [(orph_absent_untouched k).mp habs]
  simp

/-- Consumption starts at coordinate 0, at or below the unit's low
edge. Isabelle: `orph_s0lo`. -/
theorem orph_s0lo : ∀ u ∈ [orph_unit], sc.cle 0 u.lo := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  show den_w 0 ≤ den_w 1
  decide

/-- With the absent entry enumerated, the orphan is gone. Isabelle:
`wit_orphan_removed`. -/
theorem wit_orphan_removed :
    state_after D0_o (emission sc [orph_unit] 2 (fun _ => [3, 4]) 0) 4 =
      none := by
  rw [wit_orph_contract.self_stabilization orph_svl_ok2 orph_s0lo orph_covers
    4 (Or.inr rfl)]
  exact state_sc_pfx2_4

/-- With the absent entry enumerated, the live row is kept. Isabelle:
`wit_orphan_present_kept`. -/
theorem wit_orphan_present_kept :
    state_after D0_o (emission sc [orph_unit] 2 (fun _ => [3, 4]) 0) 3 =
      some 7 := by
  rw [wit_orph_contract.self_stabilization orph_svl_ok2 orph_s0lo orph_covers
    3 (Or.inl rfl)]
  exact state_sc_pfx2_3

/-- The survivor-only enumeration of the core is admissible too.
Isabelle: `orph_svl_ok2_core`. -/
theorem orph_svl_ok2_core : svl_ok2 sc [orph_unit] (fun _ => [3]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · intro k hk
    rw [(orph_survivors k).mp hk]
    simp
  · intro k hk
    have hk' : k = 3 := by simpa using hk
    exact Or.inl ((orph_survivors k).mpr hk')

/-- The survivor-only enumeration of the core keeps the orphan.
Isabelle: `wit_orphan_kept_by_omission`. -/
theorem wit_orphan_kept_by_omission :
    state_after D0_o (emission sc [orph_unit] 2 (fun _ => [3]) 0) 4 =
      some 9 := by
  have quiet : evs_for 4 (sc.win 0 2) = [] := by
    show evs_for 4 [(⟨3, some 7⟩ : Event Nat Nat), ⟨1, some 1⟩] = []
    simp [evs_for]
  rw [wit_orph_contract.unlisted_quiet_key_kept orph_svl_ok2_core orph_s0lo
    (Or.inr rfl) (by simp) quiet D0_o]
  rfl

/-! ## The read-at-high fixture (Flink CDC): a zero-width bracket -/

/-- The read-at-high unit: keys 3 and 4 behind the zero-width bracket
at coordinate 2, refresh reporting key 3 present with value 7 and
key 4 absent. Isabelle: `rah_unit`. -/
def rah_unit : CUnit Nat Nat Nat where
  dom := fun k => k = 3 ∨ k = 4
  lo := 2
  hi := 2
  refresh := fun k => if k = 3 then some 7 else none

/-- The read-at-high instance satisfies the contract, O2 discharged
for both keys at the high edge itself. Isabelle: the `rah`
interpretation. -/
theorem wit_rah_contract :
    CaptureContract sc s0_w [rah_unit] (fun k => k = 3 ∨ k = 4) 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    constructor
    · intro hk
      exact ⟨rah_unit, List.mem_singleton.mpr rfl, hk⟩
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
      exact state_sc_pfx2_3.symm
    · subst h4
      exact state_sc_pfx2_4.symm

/-- The zero-width window is empty. Isabelle: `rah_win_empty`. -/
theorem rah_win_empty : sc.win rah_unit.lo rah_unit.hi = [] := rfl

/-- The survivors of the read-at-high unit are exactly key 3, the
present key. Isabelle: `rah_survivors`, stated there as a set
equality. -/
theorem rah_survivors (k : Nat) : survivors sc rah_unit k ↔ k = 3 := by
  constructor
  · rintro ⟨hdom, hr, -⟩
    rcases hdom with h | h
    · exact h
    · subst h
      exact absurd rfl hr
  · intro h
    subst h
    refine ⟨Or.inl rfl, by simp [rah_unit], ?_⟩
    rw [rah_win_empty]
    rfl

/-- The absent untouched keys of the read-at-high unit are exactly
key 4, the key missing from the merged image. Isabelle:
`rah_absent_untouched`, stated there as a set equality. -/
theorem rah_absent_untouched (k : Nat) :
    absent_untouched sc rah_unit k ↔ k = 4 := by
  constructor
  · rintro ⟨hdom, hr, -⟩
    rcases hdom with h | h
    · subst h
      simp [rah_unit] at hr
    · exact h
  · intro h
    subst h
    refine ⟨Or.inr rfl, rfl, ?_⟩
    rw [rah_win_empty]
    rfl

/-- Listing both keys is an admissible enumeration. Isabelle:
`rah_svl_ok2`. -/
theorem rah_svl_ok2 : svl_ok2 sc [rah_unit] (fun _ => [3, 4]) := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  refine ⟨by simp, ?_, ?_⟩
  · intro k hk
    rw [(rah_survivors k).mp hk]
    simp
  · intro k hk
    have hk' : k = 3 ∨ k = 4 := by simpa using hk
    rcases hk' with h | h
    · exact Or.inl ((rah_survivors k).mpr h)
    · exact Or.inr ((rah_absent_untouched k).mpr h)

/-- Listing both keys covers the orphan sink. Isabelle:
`rah_covers`. -/
theorem rah_covers : covers sc [rah_unit] 2 (fun _ => [3, 4]) D0_o 0 := by
  intro u hu k habs _ _
  rw [List.mem_singleton.mp hu] at habs
  rw [(rah_absent_untouched k).mp habs]
  simp

/-- Consumption starts at coordinate 0, at or below the unit's low
edge. Isabelle: `rah_s0lo`. -/
theorem rah_s0lo : ∀ u ∈ [rah_unit], sc.cle 0 u.lo := by
  intro u hu
  rw [List.mem_singleton.mp hu]
  show den_w 0 ≤ den_w 2
  decide

/-- With the window empty, the range minus the emitted keys is the
whole absent set, and the orphan is gone. Isabelle:
`wit_read_at_hi_orphan_removed`. -/
theorem wit_read_at_hi_orphan_removed :
    state_after D0_o (emission sc [rah_unit] 2 (fun _ => [3, 4]) 0) 4 =
      none := by
  rw [wit_rah_contract.self_stabilization rah_svl_ok2 rah_s0lo rah_covers
    4 (Or.inr rfl)]
  exact state_sc_pfx2_4

/-- The live row is kept. Isabelle: `wit_read_at_hi_present_kept`. -/
theorem wit_read_at_hi_present_kept :
    state_after D0_o (emission sc [rah_unit] 2 (fun _ => [3, 4]) 0) 3 =
      some 7 := by
  rw [wit_rah_contract.self_stabilization rah_svl_ok2 rah_s0lo rah_covers
    3 (Or.inl rfl)]
  exact state_sc_pfx2_3

end

end DBLogContract
