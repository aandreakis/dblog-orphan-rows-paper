import DBLogContract.CutTheorem

/-!
# A certified absence is a unit, and a unit splits for late absences

This file ports the two subsections of `Orphan_Absence.thy` stated in
the `coordinate_space` context.

* `absence_assertion_contract`: the tail assertion of the design. A
  key set observed empty at a coordinate inside a bracket forms a
  one-unit capture contract with the absent refresh. The design uses
  it for the keys above the observed maximum (and above the last
  returned key), so that its domain is disjoint from every chunk
  range.
* `late_absence_split`: the design emits a chunk's surviving rows at
  its high watermark and its absence entries at a later position. In
  the contract this is a unit replaced by two: the present keys keep
  the original bracket, the absent keys get the bracket widened to
  the emission position. The read witness of O2 lies in the original
  bracket, hence in the widened one, so both halves are honest, and
  the halves partition the domain, so the plan is still a strict
  partition.

The Isabelle proof of `late_absence_split` maps family positions
through three index lemmas (`split_index_subset`, `split_index_ne`,
`split_index_bound`). The port instead reads O1's positional
disjointness as pairwise disjointness along the list
(`O1_disjoint_iff_pairwise`, port-local) and decomposes it over the
append. The statement is unchanged.
-/

namespace DBLogContract

universe u v w

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-- A certified absence is a unit of the contract: a key set `T`
observed empty at a coordinate `c` inside the bracket from `lo` to
`hi`, with `hi` at or below the frontier, is a one-unit capture
contract over scope `T` whose refresh reports every key absent.
Isabelle: `absence_assertion_contract`, proved in the
`coordinate_space` context. -/
theorem absence_assertion_contract (S : CoordinateSpace K V C)
    {σ0 : State K V} {T : K → Prop} {lo c hi f : C}
    (lo_c : S.cle lo c) (c_hi : S.cle c hi) (hi_f : S.cle hi f)
    (empty : ∀ k, T k → state_after σ0 (S.pfx c) k = none) :
    CaptureContract S σ0
      [{ dom := T, lo := lo, hi := hi, refresh := fun _ => none }] T f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- O1: the single unit covers the scope.
    intro k
    constructor
    · intro hk
      exact ⟨_, List.mem_singleton.mpr rfl, hk⟩
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
    exact S.cle_trans lo_c c_hi
  · -- The bracket sits at or below the frontier.
    intro u hu
    rw [List.mem_singleton.mp hu]
    exact hi_f
  · -- O2: every key of `T` is honest at the observation coordinate.
    intro u hu k hk
    rw [List.mem_singleton.mp hu] at hk ⊢
    exact ⟨c, lo_c, c_hi, (empty k hk).symm⟩

/-- O1's positional disjointness (`CaptureContract.O1_disjoint`) is
pairwise disjointness of the unit domains along the family list.
Port-local. It replaces the index bookkeeping of the Isabelle proof
of `late_absence_split`. -/
theorem O1_disjoint_iff_pairwise (l : List (CUnit K V C)) :
    (∀ i j, (hi : i < l.length) → (hj : j < l.length) → i ≠ j →
      ∀ k, (l[i]'hi).dom k → (l[j]'hj).dom k → False) ↔
    l.Pairwise (fun a b => ∀ k, a.dom k → b.dom k → False) := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    exact h i j hi hj (Nat.ne_of_lt hij)
  · intro h i j hi hj hne k hki hkj
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact h i j hi hj hlt k hki hkj
    · exact h j i hj hi hgt k hkj hki

/-- Splitting a unit for late absences: replacing a unit of a
contract by its present half, with the original bracket, followed by
its absent half, with the bracket widened to a later coordinate `q`
at or below the frontier, again gives a contract over the same scope.
Isabelle: `late_absence_split`, proved in the `coordinate_space`
context, whose `defines` of the two halves are written out here as
record updates. -/
theorem late_absence_split {S : CoordinateSpace K V C} {σ0 : State K V}
    {us1 us2 : List (CUnit K V C)} {u : CUnit K V C} {sc : K → Prop}
    {f q : C}
    (cc : CaptureContract S σ0 (us1 ++ u :: us2) sc f)
    (hi_q : S.cle u.hi q) (q_f : S.cle q f) :
    CaptureContract S σ0
      (us1 ++ { u with dom := fun k => u.dom k ∧ u.refresh k ≠ none } ::
        { u with dom := fun k => u.dom k ∧ u.refresh k = none, hi := q } ::
          us2) sc f := by
  generalize hu1 : ({ u with
      dom := fun k => u.dom k ∧ u.refresh k ≠ none } : CUnit K V C) = u1
  generalize hu2 : ({ u with
      dom := fun k => u.dom k ∧ u.refresh k = none
      hi := q } : CUnit K V C) = u2
  have d1 : ∀ k, u1.dom k ↔ (u.dom k ∧ u.refresh k ≠ none) := by
    intro k
    subst hu1
    exact Iff.rfl
  have d2 : ∀ k, u2.dom k ↔ (u.dom k ∧ u.refresh k = none) := by
    intro k
    subst hu2
    exact Iff.rfl
  have lo1 : u1.lo = u.lo := by subst hu1; rfl
  have hi1 : u1.hi = u.hi := by subst hu1; rfl
  have rf1 : u1.refresh = u.refresh := by subst hu1; rfl
  have lo2 : u2.lo = u.lo := by subst hu2; rfl
  have hi2 : u2.hi = q := by subst hu2; rfl
  have rf2 : u2.refresh = u.refresh := by subst hu2; rfl
  have u_in : u ∈ us1 ++ u :: us2 :=
    List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have in_old_l : ∀ {x}, x ∈ us1 → x ∈ us1 ++ u :: us2 := fun h =>
    List.mem_append.mpr (Or.inl h)
  have in_old_r : ∀ {x}, x ∈ us2 → x ∈ us1 ++ u :: us2 := fun h =>
    List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
  have in_new_l : ∀ {x}, x ∈ us1 → x ∈ us1 ++ u1 :: u2 :: us2 := fun h =>
    List.mem_append.mpr (Or.inl h)
  have in_new_r : ∀ {x}, x ∈ us2 → x ∈ us1 ++ u1 :: u2 :: us2 := fun h =>
    List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr h)))))
  have u1_in : u1 ∈ us1 ++ u1 :: u2 :: us2 :=
    List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have u2_in : u2 ∈ us1 ++ u1 :: u2 :: us2 :=
    List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_cons.mpr (Or.inl rfl)))))
  -- Every member of the new family is an old member or one of the halves.
  have cases_new : ∀ {x}, x ∈ us1 ++ u1 :: u2 :: us2 →
      x ∈ us1 ∨ x ∈ us2 ∨ x = u1 ∨ x = u2 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- O1 coverage: the two halves cover exactly the old unit's domain.
    intro k
    rw [cc.O1_cover k]
    constructor
    · rintro ⟨x, hx, hkx⟩
      rcases List.mem_append.mp hx with h | h
      · exact ⟨x, in_new_l h, hkx⟩
      · rcases List.mem_cons.mp h with h | h
        · rw [h] at hkx
          by_cases hr : u.refresh k = none
          · exact ⟨u2, u2_in, (d2 k).mpr ⟨hkx, hr⟩⟩
          · exact ⟨u1, u1_in, (d1 k).mpr ⟨hkx, hr⟩⟩
        · exact ⟨x, in_new_r h, hkx⟩
    · rintro ⟨x, hx, hkx⟩
      rcases cases_new hx with h | h | h | h
      · exact ⟨x, in_old_l h, hkx⟩
      · exact ⟨x, in_old_r h, hkx⟩
      · rw [h] at hkx
        exact ⟨u, u_in, ((d1 k).mp hkx).1⟩
      · rw [h] at hkx
        exact ⟨u, u_in, ((d2 k).mp hkx).1⟩
  · -- O1 disjointness, read pairwise along the list.
    refine (O1_disjoint_iff_pairwise _).mpr ?_
    have hold := (O1_disjoint_iff_pairwise _).mp cc.O1_disjoint
    rw [List.pairwise_append, List.pairwise_cons] at hold
    obtain ⟨h1, ⟨hu, h2⟩, hcross⟩ := hold
    rw [List.pairwise_append, List.pairwise_cons, List.pairwise_cons]
    refine ⟨h1, ⟨?_, ?_, h2⟩, ?_⟩
    · -- The present half against the absent half and the later units.
      intro b hb k hk1 hkb
      rcases List.mem_cons.mp hb with hb | hb
      · rw [hb] at hkb
        exact ((d1 k).mp hk1).2 ((d2 k).mp hkb).2
      · exact hu b hb k ((d1 k).mp hk1).1 hkb
    · -- The absent half against the later units.
      intro b hb k hk2 hkb
      exact hu b hb k ((d2 k).mp hk2).1 hkb
    · -- The earlier units against both halves and the later units.
      intro a ha b hb k hka hkb
      rcases List.mem_cons.mp hb with hb | hb
      · rw [hb] at hkb
        exact hcross a ha u (List.mem_cons.mpr (Or.inl rfl)) k hka
          ((d1 k).mp hkb).1
      · rcases List.mem_cons.mp hb with hb | hb
        · rw [hb] at hkb
          exact hcross a ha u (List.mem_cons.mpr (Or.inl rfl)) k hka
            ((d2 k).mp hkb).1
        · exact hcross a ha b (List.mem_cons.mpr (Or.inr hb)) k hka hkb
  · -- Bracket ordering: the widened bracket still starts at the low edge.
    intro x hx
    rcases cases_new hx with h | h | h | h
    · exact cc.bracket_lo_hi x (in_old_l h)
    · exact cc.bracket_lo_hi x (in_old_r h)
    · rw [h, lo1, hi1]
      exact cc.bracket_lo_hi u u_in
    · rw [h, lo2, hi2]
      exact S.cle_trans (cc.bracket_lo_hi u u_in) hi_q
  · -- Every bracket sits at or below the frontier.
    intro x hx
    rcases cases_new hx with h | h | h | h
    · exact cc.bracket_hi_f x (in_old_l h)
    · exact cc.bracket_hi_f x (in_old_r h)
    · rw [h, hi1]
      exact cc.bracket_hi_f u u_in
    · rw [h, hi2]
      exact q_f
  · -- O2: the old read witness lies in both brackets.
    intro x hx k hk
    rcases cases_new hx with h | h | h | h
    · exact cc.O2_honest x (in_old_l h) k hk
    · exact cc.O2_honest x (in_old_r h) k hk
    · rw [h] at hk ⊢
      rw [lo1, hi1, rf1]
      exact cc.O2_honest u u_in k ((d1 k).mp hk).1
    · rw [h] at hk ⊢
      rw [lo2, hi2, rf2]
      obtain ⟨c, c_lo, c_hi, hon⟩ := cc.O2_honest u u_in k ((d2 k).mp hk).1
      exact ⟨c, c_lo, S.cle_trans c_hi hi_q, hon⟩

end

end DBLogContract
