import OrphanAbsence.Tiling
import OrphanAbsence.TilingWitnesses

/-!
# Bridge: the ranges of a pass as the domains of a capture contract

This file ports the last subsection of `Orphan_Absence_Tiling.thy`. Each
chunk `i` of a pass becomes one unit of a capture contract of the core.
Its domain is the chunk's range, its bracket runs from the low watermark
`lw i` to the high watermark `hw i`, and its refresh is what the read at
the coordinate `rc i` returned, with absence for every key of the range
the read did not return. The tiling gives the coverage and disjointness
obligation O1, and the exactness of each range gives the validity
obligation O2 at the read's own cut.

* `pass_units`: the units of a pass.
* `pass_contract`: the units form a contract whose scope is the set of
  keys the pass covered.
* `completed_pass_contract`, `limited_pass_contract`: the scope of a
  completed pass is every key, and the scope of a pass stopped by the
  tail-read limit is the keys at or below the last key its last read
  returned.
* `wit_bridge_contract`: the bridge is not vacuous.

The Isabelle locale `ordered_key_space` is a coordinate space over a
linearly ordered key type. Its parameters `L` and `den` are the
coordinate space `S : CoordinateSpace K V C` of the core, and its sort
constraint is the instance `[Linorder K]`. The locale adds no
assumption, so it has no separate Lean declaration. Its interpretation
`wit_space` is the concrete coordinate space `wit_space`.
-/

namespace DBLogContract

namespace Tiling

universe u v w

section General

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w} [Linorder K]

noncomputable section

/-- The units of a pass. Unit `i` has the range of chunk `i` as its
domain, the bracket from `lw i` to `hw i`, and as its refresh the source
state at the coordinate `rc i` on the keys the read returned, with
absence on every other key. The Isabelle definition maps over
`[0..<length cs]` with `cs ! i`. The port traverses `cs.zipIdx`, which
pairs each chunk with its position, so the list is the same entry for
entry. The locale parameters are the coordinate space `S`. Isabelle:
`ordered_key_space.pass_units`. -/
def pass_units (S : CoordinateSpace K V C) (σ0 : State K V) (cs : List (Chunk K))
    (lw rc hw : Nat → C) : List (CUnit K V C) :=
  cs.zipIdx.map (fun ci =>
    { dom := chunk_keys ci.1
      lo := lw ci.2
      hi := hw ci.2
      refresh := fun k =>
        if k ∈ ci.1.c_rows then state_after σ0 (S.pfx (rc ci.2)) k else none })

/-- A pass has one unit per chunk. Port-local. -/
private theorem pass_units_length {S : CoordinateSpace K V C} {σ0 : State K V}
    {cs : List (Chunk K)} {lw rc hw : Nat → C} :
    (pass_units S σ0 cs lw rc hw).length = cs.length := by
  simp [pass_units]

/-- The bound of a unit's position as a chunk position. Port-local. -/
private theorem pass_units_bound {S : CoordinateSpace K V C} {σ0 : State K V}
    {cs : List (Chunk K)} {lw rc hw : Nat → C} {i : Nat}
    (hi : i < (pass_units S σ0 cs lw rc hw).length) : i < cs.length := by
  rw [pass_units_length] at hi
  exact hi

/-- The bound of a chunk's position as a unit position. Port-local. -/
private theorem pass_units_bound' {S : CoordinateSpace K V C} {σ0 : State K V}
    {cs : List (Chunk K)} {lw rc hw : Nat → C} {i : Nat}
    (hi : i < cs.length) : i < (pass_units S σ0 cs lw rc hw).length := by
  rw [pass_units_length]
  exact hi

/-- The unit at a position. Port-local. -/
private theorem pass_units_getElem {S : CoordinateSpace K V C} {σ0 : State K V}
    {cs : List (Chunk K)} {lw rc hw : Nat → C} {i : Nat}
    (hi : i < (pass_units S σ0 cs lw rc hw).length) :
    (pass_units S σ0 cs lw rc hw)[i]'hi =
      { dom := chunk_keys (cs[i]'(pass_units_bound hi))
        lo := lw i
        hi := hw i
        refresh := fun k =>
          if k ∈ (cs[i]'(pass_units_bound hi)).c_rows
          then state_after σ0 (S.pfx (rc i)) k else none } := by
  simp [pass_units, List.getElem_map, List.getElem_zipIdx]

/-- Every unit is the unit at some chunk position. Port-local. -/
private theorem pass_units_mem {S : CoordinateSpace K V C} {σ0 : State K V}
    {cs : List (Chunk K)} {lw rc hw : Nat → C} {u : CUnit K V C}
    (hu : u ∈ pass_units S σ0 cs lw rc hw) :
    ∃ i, ∃ hi : i < cs.length,
      u = { dom := chunk_keys (cs[i]'hi)
            lo := lw i
            hi := hw i
            refresh := fun k =>
              if k ∈ (cs[i]'hi).c_rows then state_after σ0 (S.pfx (rc i)) k else none } := by
  obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.mp hu
  refine ⟨i, pass_units_bound hi, ?_⟩
  rw [← hiu, pass_units_getElem]

/-- The units of a pass form a capture contract whose scope is the set of
keys the pass covered. The assumptions, in order: the chunk limit is
positive, and the chunks are those of a pass. Each read's coordinate lies
inside its chunk's bracket, and each bracket ends by the frontier `f`.
The source state each read saw is the set of keys present at its
coordinate, and it is finite. The Isabelle set equality `cut` is stated
pointwise. Isabelle: `ordered_key_space.pass_contract`. -/
theorem pass_contract [Nonempty K] {S : CoordinateSpace K V C} {σ0 : State K V}
    {n T : Nat} {Mo : Option K} {Ss : List (K → Prop)} {cs : List (Chunk K)}
    {lw rc hw : Nat → C} {f : C}
    (hn : 0 < n) (hcs : cs = (bounded_pass n T Mo Ss).1)
    (lw_rc : ∀ i, i < cs.length → S.cle (lw i) (rc i))
    (rc_hw : ∀ i, i < cs.length → S.cle (rc i) (hw i))
    (hw_f : ∀ i, i < cs.length → S.cle (hw i) f)
    (cut : ∀ i (hi : i < cs.length) k,
      (Ss[i]'(pass_read_bound hcs hi)) k ↔ state_after σ0 (S.pfx (rc i)) k ≠ none)
    (fin : ∀ i (hi : i < cs.length), finite (Ss[i]'(pass_read_bound hcs hi))) :
    CaptureContract S σ0 (pass_units S σ0 cs lw rc hw) (covered cs) f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- O1_cover
    intro k
    constructor
    · rintro ⟨c, hc, hk⟩
      obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hc
      have hi' : i < (pass_units S σ0 cs lw rc hw).length := pass_units_bound' hi
      refine ⟨_, List.getElem_mem hi', ?_⟩
      rw [pass_units_getElem]
      show chunk_keys (cs[i]'hi) k
      rw [hci]
      exact hk
    · rintro ⟨u, hu, hk⟩
      obtain ⟨i, hi, rfl⟩ := pass_units_mem hu
      exact ⟨cs[i]'hi, List.getElem_mem hi, hk⟩
  · -- O1_disjoint
    intro i j hi hj hij k hki hkj
    rw [pass_units_getElem] at hki hkj
    exact ranges_disjoint hn hcs (pass_units_bound hi) (pass_units_bound hj) hij k hki hkj
  · -- bracket_lo_hi
    intro u hu
    obtain ⟨i, hi, rfl⟩ := pass_units_mem hu
    exact S.cle_trans (lw_rc i hi) (rc_hw i hi)
  · -- bracket_hi_f
    intro u hu
    obtain ⟨i, hi, rfl⟩ := pass_units_mem hu
    exact hw_f i hi
  · -- O2_honest
    intro u hu k hk
    obtain ⟨i, hi, rfl⟩ := pass_units_mem hu
    refine ⟨rc i, lw_rc i hi, rc_hw i hi, ?_⟩
    show (if k ∈ (cs[i]'hi).c_rows then state_after σ0 (S.pfx (rc i)) k else none) =
      state_after σ0 (S.pfx (rc i)) k
    by_cases hrow : k ∈ (cs[i]'hi).c_rows
    · rw [if_pos hrow]
    · rw [if_neg hrow]
      have absent := range_absent hn hcs hi (fin i hi) hk hrow
      have hnone : ¬ state_after σ0 (S.pfx (rc i)) k ≠ none :=
        fun h => absent ((cut i hi k).mpr h)
      exact (Classical.not_not.mp hnone).symm

/-- A completed pass covers every key, so its contract has the whole key
space as scope. HOL's `UNIV` is the predicate `fun _ => True`. Isabelle:
`ordered_key_space.completed_pass_contract`. -/
theorem completed_pass_contract [Nonempty K] {S : CoordinateSpace K V C} {σ0 : State K V}
    {n T : Nat} {Mo : Option K} {Ss : List (K → Prop)} {cs : List (Chunk K)}
    {lw rc hw : Nat → C} {f : C}
    (hn : 0 < n) (complete : (bounded_pass n T Mo Ss).2 = .Completed)
    (hcs : cs = (bounded_pass n T Mo Ss).1)
    (lw_rc : ∀ i, i < cs.length → S.cle (lw i) (rc i))
    (rc_hw : ∀ i, i < cs.length → S.cle (rc i) (hw i))
    (hw_f : ∀ i, i < cs.length → S.cle (hw i) f)
    (cut : ∀ i (hi : i < cs.length) k,
      (Ss[i]'(pass_read_bound hcs hi)) k ↔ state_after σ0 (S.pfx (rc i)) k ≠ none)
    (fin : ∀ i (hi : i < cs.length), finite (Ss[i]'(pass_read_bound hcs hi))) :
    CaptureContract S σ0 (pass_units S σ0 cs lw rc hw) (fun _ => True) f := by
  have hcov : covered cs = fun _ => True := by
    funext k
    apply propext
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rw [hcs]
    exact union_on_completion hn complete k
  rw [← hcov]
  exact pass_contract hn hcs lw_rc rc_hw hw_f cut fin

/-- With at least one tail read configured, a pass stopped by the
tail-read limit yields a contract over exactly the keys at or below the
last key its last read returned. Isabelle's `last (c_rows (last cs))` is
the total `last`. Isabelle: `ordered_key_space.limited_pass_contract`. -/
theorem limited_pass_contract [Nonempty K] {S : CoordinateSpace K V C} {σ0 : State K V}
    {n T : Nat} {Mo fr : Option K} {Ss : List (K → Prop)} {cs : List (Chunk K)}
    {lw rc hw : Nat → C} {f : C}
    (hn : 0 < n) (hT : 0 < T) (stop : (bounded_pass n T Mo Ss).2 = .Tail_Limit fr)
    (hcs : cs = (bounded_pass n T Mo Ss).1)
    (lw_rc : ∀ i, i < cs.length → S.cle (lw i) (rc i))
    (rc_hw : ∀ i, i < cs.length → S.cle (rc i) (hw i))
    (hw_f : ∀ i, i < cs.length → S.cle (hw i) f)
    (cut : ∀ i (hi : i < cs.length) k,
      (Ss[i]'(pass_read_bound hcs hi)) k ↔ state_after σ0 (S.pfx (rc i)) k ≠ none)
    (fin : ∀ i (hi : i < cs.length), finite (Ss[i]'(pass_read_bound hcs hi))) :
    CaptureContract S σ0 (pass_units S σ0 cs lw rc hw)
      (fun k => k ≤ last (last cs).c_rows) f := by
  have hcov : covered cs = fun k => k ≤ last (last cs).c_rows := by
    funext k
    exact propext (union_on_limit_last_returned hn hT stop hcs rfl k)
  rw [← hcov]
  exact pass_contract hn hcs lw_rc rc_hw hw_f cut fin

end

end General

/-! ## The bridge is not vacuous -/

/-- The coordinate space of the bridge witness: the empty log over natural
keys and unit values, with every natural-number coordinate at its start.
Isabelle: the interpretation `wit_space` of `ordered_key_space`, whose
proof obligation is the field `den_le_len`. -/
def wit_space : CoordinateSpace Nat Unit Nat where
  log := []
  den := fun _ => 0
  den_le_len := fun _ => Nat.le_refl 0

/-- The source of the bridge witness: the keys of `W2`, each with the unit
value. Isabelle: `wit_source`. -/
noncomputable def wit_source : State Nat Unit :=
  fun k => @ite _ (W2 k) (Classical.propDecidable _) (some ()) none

/-- Isabelle: `W2_bpage_first`. -/
theorem W2_bpage_first : bpage W2 none 10 5 = [1, 2, 3, 5, 6] := by
  unfold bpage
  apply smallest_eqI (xs := [1, 2, 3, 5, 6, 8, 9, 10])
  · decide
  · intro k
    simp only [W2, List.mem_cons, List.not_mem_nil, or_false, above_lo_None, true_and]
    omega
  · rfl

/-- A concrete value of the total `last`. Port-local. -/
private theorem last_1_6' : last [1, 2, 3, 5, 6] = 6 := rfl

/-- A completed pass that reads the source of `W2` three times. Isabelle:
`wit_bridge_pass`. -/
theorem wit_bridge_pass :
    bounded_pass 5 2 (some 10) [W2, W2, W2] =
      ([{ c_lo := none, c_hi := some 6, c_rows := [1, 2, 3, 5, 6] },
        { c_lo := some 6, c_hi := some 10, c_rows := [8, 9, 10] },
        { c_lo := some 10, c_hi := none, c_rows := [12] }], .Completed) := by
  simp [bounded_pass, bounded_scan, W2_bpage_first, W2_bpage, W2_page, tail_scan_pos_Cons,
    last_1_6']

/-- The bridge witness: the completed pass over the source of `W2`, with
every coordinate at the start of the empty log, is a capture contract
over every key. HOL's `UNIV` is the predicate `fun _ => True`. Isabelle:
`wit_bridge_contract`. -/
theorem wit_bridge_contract :
    CaptureContract wit_space wit_source
      (pass_units wit_space wit_source (bounded_pass 5 2 (some 10) [W2, W2, W2]).1
        (fun _ => 0) (fun _ => 0) (fun _ => 0))
      (fun _ => True) 0 := by
  have len : (bounded_pass 5 2 (some 10) [W2, W2, W2]).1.length = 3 := by
    rw [wit_bridge_pass]
    rfl
  have src : ∀ k, state_after wit_source (wit_space.pfx 0) k ≠ none ↔ W2 k := by
    intro k
    show wit_source k ≠ none ↔ W2 k
    simp only [wit_source]
    by_cases h : W2 k
    · rw [if_pos h]
      exact ⟨fun _ => h, fun _ => Option.some_ne_none ()⟩
    · rw [if_neg h]
      exact ⟨fun hn => absurd rfl hn, fun hw => absurd hw h⟩
  have reads : ∀ (i : Nat) (h : i < [W2, W2, W2].length), [W2, W2, W2][i] = W2 := by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases i with _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · omega
  refine completed_pass_contract (by decide) (by rw [wit_bridge_pass]) rfl
    (fun _ _ => Nat.le_refl 0) (fun _ _ => Nat.le_refl 0) (fun _ _ => Nat.le_refl 0) ?_ ?_
  · intro i hi k
    rw [reads i (pass_read_bound rfl hi), src k]
  · intro i hi
    rw [reads i (pass_read_bound rfl hi)]
    exact ⟨[1, 2, 3, 5, 6, 8, 9, 10, 12], fun _ => Iff.rfl⟩

end Tiling

end DBLogContract
