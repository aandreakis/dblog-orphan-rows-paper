import OrphanAbsence.Redelivery
import OrphanAbsence.Witnesses

/-!
# Fixtures: a doubled delivery, out-of-order delivery, partitioned topics

This file ports the fixtures of `Orphan_Absence_Replay.thy`.

* The orphan fixture of `Witnesses.lean`, delivered twice in full: the
  orphan at key 4 is still removed and key 3 still ends at 7
  (`wit_redelivered_orphan_removed`, `wit_redelivered_present_kept`).
  The doubled stream is a redelivery through the suffix instance of
  the delivery class.
* Out-of-order delivery of one key's events is outside the class. A
  stale event delivered after a newer one changes the state
  (`out_of_order_redelivery_differs`), so that stream is not a
  redelivery (`out_of_order_not_redelivered`).
* Two keys on two partitions, applied in the other order, meet the
  per-key hypothesis and replay like the emission
  (`wit_partition_reorder_per_key`, `wit_partition_reorder_replay`,
  `wit_partitioned_delivery`).
* A partition delivered with a rewind inside it, applied after the
  other partition (`rw_E`, `rw_part`, `rw_T`, `rw_S` and their four
  lemmas). The applied stream is not a redelivery of the emission, yet
  the partition lemma gives the per-key hypothesis for every key.
* The per-key hypothesis is asked for the key in question only
  (`wit_own_key_only`). A compacted read is not a per-key redelivery
  (`compacted_read_not_per_key_redelivery`).

Like `Witnesses.lean`, this file does not make classical decidability
a local instance, so the conditionals of `rw_part` and `rw_T` and the
filter of `wit_rewind_parts` use the decidable equality of `Nat`. The
general theorems are stated with the classical instance. The two
instances give the same Boolean values, and the proofs bridge them
where a lemma is applied.
-/

namespace DBLogContract

noncomputable section

/-! ## The orphan fixture, delivered twice in full -/

/- Concrete evaluations of the per-key fold over `L_s`. -/

/-- Port-local. Key 4 is absent at coordinate 2 of the fixture log. -/
private theorem rd_state_pfx2_4 : state_after s0_w (sc.pfx 2) 4 = none := by
  show apply_ev (apply_ev s0_w ⟨3, some 7⟩) ⟨1, some 1⟩ 4 = none
  simp [apply_ev, s0_w]

/-- Port-local. Key 3 holds 7 at coordinate 2 of the fixture log. -/
private theorem rd_state_pfx2_3 : state_after s0_w (sc.pfx 2) 3 = some 7 := by
  show apply_ev (apply_ev s0_w ⟨3, some 7⟩) ⟨1, some 1⟩ 3 = some 7
  simp [apply_ev]

/-- Port-local. The orphan fixture's emission followed by itself is a
redelivery of the emission, through the suffix instance. -/
private theorem rd_doubled_redelivered :
    redelivered (emission sc [orph_unit] 2 (fun _ => [3, 4]) 0)
      (emission sc [orph_unit] 2 (fun _ => [3, 4]) 0 ++
        emission sc [orph_unit] 2 (fun _ => [3, 4]) 0) := by
  have red := redelivered_suffix
    (redelivered_refl (emission sc [orph_unit] 2 (fun _ => [3, 4]) 0)) 0
  rw [List.drop_zero] at red
  exact red

/-- Delivered twice in full, the orphan fixture still removes the
orphan. Isabelle: `wit_redelivered_orphan_removed`. -/
theorem wit_redelivered_orphan_removed :
    state_after D0_o (emission sc [orph_unit] 2 (fun _ => [3, 4]) 0 ++
      emission sc [orph_unit] 2 (fun _ => [3, 4]) 0) 4 = none := by
  rw [wit_orph_contract.self_stabilization_at_least_once orph_svl_ok2
    orph_s0lo orph_covers rd_doubled_redelivered 4 (Or.inr rfl)]
  exact rd_state_pfx2_4

/-- Delivered twice in full, the orphan fixture still keeps the live
row. Isabelle: `wit_redelivered_present_kept`. -/
theorem wit_redelivered_present_kept :
    state_after D0_o (emission sc [orph_unit] 2 (fun _ => [3, 4]) 0 ++
      emission sc [orph_unit] 2 (fun _ => [3, 4]) 0) 3 = some 7 := by
  rw [wit_orph_contract.self_stabilization_at_least_once orph_svl_ok2
    orph_s0lo orph_covers rd_doubled_redelivered 3 (Or.inl rfl)]
  exact rd_state_pfx2_3

/-! ## Out-of-order delivery is outside the class -/

/-- A stale event delivered after a newer one for the same key, with no
later re-read of the newer one, changes the state. Isabelle:
`out_of_order_redelivery_differs`. -/
theorem out_of_order_redelivery_differs :
    state_after (fun _ => none)
        [(⟨1, some 1⟩ : Event Nat Nat), ⟨1, some 2⟩, ⟨1, some 1⟩] ≠
      state_after (fun _ => none) [(⟨1, some 1⟩ : Event Nat Nat), ⟨1, some 2⟩] := by
  intro eq
  have stale : state_after (fun _ => none)
      [(⟨1, some 1⟩ : Event Nat Nat), ⟨1, some 2⟩, ⟨1, some 1⟩] 1 = some 1 := by
    show apply_ev (apply_ev (apply_ev (fun _ => none) ⟨1, some 1⟩) ⟨1, some 2⟩)
      ⟨1, some 1⟩ 1 = some 1
    simp [apply_ev]
  have fresh : state_after (fun _ => none)
      [(⟨1, some 1⟩ : Event Nat Nat), ⟨1, some 2⟩] 1 = some 2 := by
    show apply_ev (apply_ev (fun _ => none) ⟨1, some 1⟩) ⟨1, some 2⟩ 1 = some 2
    simp [apply_ev]
  have h1 := congrFun eq 1
  rw [stale, fresh] at h1
  exact absurd (Option.some.inj h1) (by decide)

/-- So that stream is not a redelivery. Isabelle:
`out_of_order_not_redelivered`. -/
theorem out_of_order_not_redelivered :
    ¬ redelivered [(⟨1, some 1⟩ : Event Nat Nat), ⟨1, some 2⟩]
      [(⟨1, some 1⟩ : Event Nat Nat), ⟨1, some 2⟩, ⟨1, some 1⟩] := by
  intro h
  exact out_of_order_redelivery_differs (redelivered_replay h (fun _ => none))

/-! ## Two keys on two partitions -/

/-- Port-local. Swapping the events of two different keys leaves every
key's events unchanged. -/
private theorem reorder_evs_eq (k : Nat) :
    evs_for k [(⟨2, some 2⟩ : Event Nat Nat), ⟨1, some 1⟩] =
      evs_for k [(⟨1, some 1⟩ : Event Nat Nat), ⟨2, some 2⟩] := by
  simp only [evs_for_cons, evs_for_nil]
  by_cases h1 : (1 : Nat) = k
  · subst h1
    simp
  · by_cases h2 : (2 : Nat) = k
    · subst h2
      simp
    · simp [h1, h2]

/-- The sink applies key 2's event before key 1's. Each key's events are
unchanged, so the per-key hypothesis holds with the empty chain of
hops. Isabelle: `wit_partition_reorder_per_key`. -/
theorem wit_partition_reorder_per_key (k : Nat) :
    redelivered (evs_for k [(⟨1, some 1⟩ : Event Nat Nat), ⟨2, some 2⟩])
      (evs_for k [(⟨2, some 2⟩ : Event Nat Nat), ⟨1, some 1⟩]) := by
  rw [reorder_evs_eq k]
  exact redelivered_refl _

/-- The reordered stream replays like the emission from every initial
state. Isabelle: `wit_partition_reorder_replay`. -/
theorem wit_partition_reorder_replay (D : State Nat Nat) :
    state_after D [(⟨2, some 2⟩ : Event Nat Nat), ⟨1, some 1⟩] =
      state_after D [(⟨1, some 1⟩ : Event Nat Nat), ⟨2, some 2⟩] :=
  redelivered_per_key_replay wit_partition_reorder_per_key D

/-- The same reordering obtained from the partition lemma: each key is
its own partition, each partition is delivered exactly once, and the
sink applies key 2's partition first. Isabelle:
`wit_partitioned_delivery`. -/
theorem wit_partitioned_delivery (k : Nat) :
    redelivered (evs_for k [(⟨1, some 1⟩ : Event Nat Nat), ⟨2, some 2⟩])
      (evs_for k [(⟨2, some 2⟩ : Event Nat Nat), ⟨1, some 1⟩]) := by
  refine partitioned_delivery_per_key (part := fun k => k)
    (T := fun p => evs_for p [(⟨1, some 1⟩ : Event Nat Nat), ⟨2, some 2⟩])
    (fun p => redelivered_refl _) ?_ k
  intro k'
  show evs_for k' [(⟨2, some 2⟩ : Event Nat Nat), ⟨1, some 1⟩] =
    evs_for k' (evs_for k' [(⟨1, some 1⟩ : Event Nat Nat), ⟨2, some 2⟩])
  rw [evs_for_idem]
  exact reorder_evs_eq k'

/-! ## A partition delivered with a rewind inside it -/

/-- The emission: keys 1, 2 and 3, one event each. Isabelle: `rw_E`. -/
def rw_E : List (Event Nat Nat) := [⟨1, some 1⟩, ⟨2, some 2⟩, ⟨3, some 3⟩]

/-- The partition map: key 2 on partition 1, every other key on
partition 0. Isabelle: `rw_part`. -/
def rw_part (k : Nat) : Nat := if k = 2 then 1 else 0

/-- The partitions' deliveries: partition 0 reads key 1's event twice,
partition 1 is read once, and the other partitions are empty.
Isabelle: `rw_T`. -/
def rw_T (p : Nat) : List (Event Nat Nat) :=
  if p = 0 then [⟨1, some 1⟩, ⟨1, some 1⟩, ⟨3, some 3⟩]
  else if p = 1 then [⟨2, some 2⟩] else []

/-- The stream the sink applies: partition 1's delivery first, then
partition 0's. Isabelle: `rw_S`. -/
def rw_S : List (Event Nat Nat) :=
  [⟨2, some 2⟩, ⟨1, some 1⟩, ⟨1, some 1⟩, ⟨3, some 3⟩]

/-- Each partition's delivery is a redelivery of the emission's events
on that partition. Isabelle: `wit_rewind_parts`. -/
theorem wit_rewind_parts (p : Nat) :
    redelivered (List.filter (fun e => decide (rw_part e.key = p)) rw_E) (rw_T p) := by
  by_cases h0 : p = 0
  · subst h0
    have h1 : at_least_once [(⟨1, some 1⟩ : Event Nat Nat), ⟨3, some 3⟩]
        (List.take 1 [(⟨1, some 1⟩ : Event Nat Nat), ⟨3, some 3⟩] ++
          List.drop 0 [(⟨1, some 1⟩ : Event Nat Nat), ⟨3, some 3⟩]) :=
      at_least_once_rewind_once (by decide) (by decide)
    have hF : List.filter (fun e => decide (rw_part e.key = 0)) rw_E =
        [⟨1, some 1⟩, ⟨3, some 3⟩] := rfl
    have hT : rw_T 0 = [⟨1, some 1⟩, ⟨1, some 1⟩, ⟨3, some 3⟩] := rfl
    rw [hF, hT]
    exact redelivered_hop (redelivered_refl _) h1
  · by_cases h1 : p = 1
    · subst h1
      have hF : List.filter (fun e => decide (rw_part e.key = 1)) rw_E =
          [⟨2, some 2⟩] := rfl
      have hT : rw_T 1 = [⟨2, some 2⟩] := rfl
      rw [hF, hT]
      exact redelivered_refl _
    · have hF : List.filter (fun e => decide (rw_part e.key = p)) rw_E = [] := by
        simp only [rw_E, rw_part, List.filter_cons, List.filter_nil]
        simp [Ne.symm h0, Ne.symm h1]
      have hT : rw_T p = [] := by
        simp only [rw_T]
        rw [if_neg h0, if_neg h1]
      rw [hF, hT]
      exact redelivered_refl _

/-- For every key, the sink's events for that key are that key's events
in its own partition's delivery. Isabelle: `wit_rewind_interleave`. -/
theorem wit_rewind_interleave (k' : Nat) :
    evs_for k' rw_S = evs_for k' (rw_T (rw_part k')) := by
  by_cases h2 : k' = 2
  · subst h2
    have hT : rw_T (rw_part 2) = [⟨2, some 2⟩] := rfl
    rw [hT]
    simp [rw_S, evs_for_cons]
  · have hp : rw_part k' = 0 := by
      simp only [rw_part]
      rw [if_neg h2]
    have hT : rw_T 0 = [⟨1, some 1⟩, ⟨1, some 1⟩, ⟨3, some 3⟩] := rfl
    rw [hp, hT]
    show evs_for k' ((⟨2, some 2⟩ : Event Nat Nat) ::
      [⟨1, some 1⟩, ⟨1, some 1⟩, ⟨3, some 3⟩]) = _
    rw [evs_for_cons, if_neg (fun h => h2 h.symm)]

/-- The applied stream is not a redelivery of the emission, since it
starts with a different item. Isabelle: `wit_rewind_not_redelivered`. -/
theorem wit_rewind_not_redelivered : ¬ redelivered rw_E rw_S := by
  intro h
  obtain ⟨_, hhd, _⟩ := redelivered_hd_last h (List.cons_ne_nil _ _)
  have heq : (⟨2, some 2⟩ : Event Nat Nat) = ⟨1, some 1⟩ := hhd
  injection heq with hk
  exact absurd hk (by decide)

/-- The partition lemma gives the per-key hypothesis for every key.
Isabelle: `wit_partitioned_delivery_rewind`. -/
theorem wit_partitioned_delivery_rewind (k : Nat) :
    redelivered (evs_for k rw_E) (evs_for k rw_S) := by
  refine partitioned_delivery_per_key (part := rw_part) (T := rw_T) ?_
    wit_rewind_interleave k
  intro p
  have hf : List.filter (fun e => @decide (rw_part e.key = p)
        (Classical.propDecidable _)) rw_E =
      List.filter (fun e => decide (rw_part e.key = p)) rw_E :=
    List.filter_congr fun _ _ => decide_eq_decide.mpr Iff.rfl
  rw [hf]
  exact wit_rewind_parts p

/-! ## The per-key hypothesis for one's own keys, and a compacted read -/

/-- A sink that drops key 9's event still meets the per-key hypothesis
for key 1. Isabelle: `wit_own_key_only`. -/
theorem wit_own_key_only :
    redelivered (evs_for 1 [(⟨1, some 1⟩ : Event Nat Nat), ⟨9, some 9⟩])
      (evs_for 1 [(⟨1, some 1⟩ : Event Nat Nat)]) := by
  have h : evs_for 1 [(⟨1, some 1⟩ : Event Nat Nat), ⟨9, some 9⟩] =
      evs_for 1 [(⟨1, some 1⟩ : Event Nat Nat)] := by
    simp [evs_for_cons]
  rw [h]
  exact redelivered_refl _

/-- A fresh consumer of a compacted topic that reads only a key's delete
is not a per-key redelivery, since a redelivery starts with the
stream's first item. Isabelle: `compacted_read_not_per_key_redelivery`. -/
theorem compacted_read_not_per_key_redelivery :
    ¬ redelivered (evs_for 4 [(⟨4, some 5⟩ : Event Nat Nat), ⟨4, none⟩])
      (evs_for 4 [(⟨4, none⟩ : Event Nat Nat)]) := by
  intro h
  have e1 : evs_for 4 [(⟨4, some 5⟩ : Event Nat Nat), ⟨4, none⟩] =
      [⟨4, some 5⟩, ⟨4, none⟩] := by
    simp [evs_for_cons]
  have e2 : evs_for 4 [(⟨4, none⟩ : Event Nat Nat)] = [⟨4, none⟩] := by
    simp [evs_for_cons]
  rw [e1, e2] at h
  obtain ⟨_, hhd, _⟩ := redelivered_hd_last h (List.cons_ne_nil _ _)
  have heq : (⟨4, none⟩ : Event Nat Nat) = ⟨4, some 5⟩ := hhd
  injection heq with _ himg
  exact absurd himg (by decide)

end

end DBLogContract
