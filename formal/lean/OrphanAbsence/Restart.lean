import OrphanAbsence.Interleaved

/-!
# The stream a sink sees across a connector restart

This file ports the general part of `Orphan_Absence_Restart.thy` from
the Isabelle session `Orphan_Absence`, up to and including
`pass_restart_after_frontier`. The fixtures of that theory are ported
in `RestartWitnesses.lean`.

A connector runs a pass `P1` with consumption start `s0`. It crashes
after it has emitted everything up to the log position `crash`. It had
committed its offset at the coordinate `cmt`. On restart it delivers the
log events from `cmt` to the crash a second time, without close entries.
It re-executes at least every chunk of `P1` that had not closed by the
crash, and the re-executed chunks form a second contract `P2` over the
same log. The sink applies `P1`'s emission up to the crash, the
re-delivered segment and `P2`'s emission, in this order, to one state.

* Items of a pass's emission: `emission_t_item_cases`, the tag bounds
  `emission_t_tag_le` and `emission_t_tag_ge`, `emission_t_event_in`,
  `emission_item_honest`, `close_entry_in_emission` and
  `unlisted_quiet_absent_at`.
* `PassRestart`, `restart_stream`, `cut_t`, `resumed_t`: the pass and
  its restart over one log, the stream the sink applies, and its two
  parts as position-tagged lists.
* `restart_cut_prefix`, `cut_blocks`, `restart_at_frontier`,
  `restart_at_frontier_read_after`: the part before the crash is the
  pass's emission run up to the crash.
* `restart_safe`, `restart_converges`: safety and convergence at the
  second contract's frontier.
* `pass_restart_after_frontier`: a crash after the pass's frontier is
  the same structure with the crash as the frontier.

Transport, as in `VERIFICATION.md` and `Interleaved.lean`. The Isabelle
segment `map (λq. L ! q) [den cmt..<den crash]` is the log segment
`(S.log.take (S.den crash)).drop (S.den cmt)`. The tagged segment
`map (λq. (Suc q, L ! q)) [den cmt..<den crash]` is
`tagged_seg S (S.den cmt) (S.den crash)`. Both are the same lists entry
for entry, because the crash denotes a prefix of the log. A list over
the positions `[den s0..<den crash]` traverses the consumed segment with
`zipIdx`, as the core's `emission_t` does. A log event `L ! q` is the
bounded `S.log[q]`, with the bound taken from the statement's own
assumptions. An `obtains` statement is the disjunction of its cases.
The locale `pass_restart` is the `Prop`-valued structure `PassRestart`.
-/

namespace DBLogContract

universe u v w

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-! ## Items of a pass's emission: cases, tags, values -/

/-- An item of a pass's timed emission is a log event of the consumed
segment, or a close entry at a consumed position or at the frontier.
Isabelle: `emission_t_item_cases`, stated in the `capture_plan` context.
It is an `obtains` statement, stated here as the disjunction of its two
cases. The log event at position `q` is the bounded `S.log[q]`, in range
because `q < S.den f`. -/
theorem emission_t_item_cases {S : CoordinateSpace K V C}
    {units : List (CUnit K V C)} {f : C} {svl : CUnit K V C → List K} {s0 : C}
    {x : Nat × Event K V} (hx : x ∈ emission_t S units f svl s0) :
    (∃ q, S.den s0 ≤ q ∧ ∃ h2 : q < S.den f,
        x = (q + 1, S.log[q]'(Nat.lt_of_lt_of_le h2 (S.den_le_len f)))) ∨
      (∃ q, (S.den s0 ≤ q ∧ q < S.den f ∨ q = S.den f) ∧
        x ∈ closes_at S units svl q) := by
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨ep, hep, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨h1, h2, he⟩ := mem_seg_zipIdx hep
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr ⟨ep.2, Or.inl ⟨h1, h2⟩, hx⟩
    · left
      refine ⟨ep.2, h1, h2, ?_⟩
      rw [List.mem_singleton.mp hx, he]
  · exact Or.inr ⟨S.den f, Or.inr rfl, hx⟩

/-- Every tag of a pass's timed emission is at most the frontier.
Isabelle: `emission_t_tag_le`, stated in the `capture_plan` context. -/
theorem emission_t_tag_le {S : CoordinateSpace K V C}
    {units : List (CUnit K V C)} {f : C} {svl : CUnit K V C → List K} {s0 : C}
    {x : Nat × Event K V} (hx : x ∈ emission_t S units f svl s0) :
    x.1 ≤ S.den f := by
  rcases emission_t_item_cases hx with ⟨q, -, h2, rfl⟩ | ⟨q, hq, hc⟩
  · exact h2
  · rw [closes_at_tag hc]
    omega

/-- Every item is tagged at or after the consumption start, except the
close entries at the frontier when the consumption start lies beyond
it. Isabelle: `emission_t_tag_ge`, stated in the `capture_plan`
context. -/
theorem emission_t_tag_ge {S : CoordinateSpace K V C}
    {units : List (CUnit K V C)} {f : C} {svl : CUnit K V C → List K} {s0 : C}
    {x : Nat × Event K V} (hx : x ∈ emission_t S units f svl s0) :
    S.den s0 ≤ x.1 ∨ x.1 = S.den f := by
  rcases emission_t_item_cases hx with ⟨q, h1, -, rfl⟩ | ⟨q, hq, hc⟩
  · exact Or.inl (Nat.le_succ_of_le h1)
  · rw [closes_at_tag hc]
    omega

/-- Every log event of the consumed segment is an item of the pass's
timed emission, tagged one after its position. Isabelle:
`emission_t_event_in`, stated in the `capture_plan` context. The log
event at position `q` is the bounded `S.log[q]`, in range because
`q < S.den f`. -/
theorem emission_t_event_in {S : CoordinateSpace K V C}
    {units : List (CUnit K V C)} {f : C} {svl : CUnit K V C → List K} {s0 : C}
    {q : Nat} (h1 : S.den s0 ≤ q) (h2 : q < S.den f) :
    (q + 1, S.log[q]'(Nat.lt_of_lt_of_le h2 (S.den_le_len f))) ∈
      emission_t S units f svl s0 := by
  refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, seg_zipIdx_mem h1 h2, ?_⟩)
  simp

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

/-- Every item of a pass's emission carries the source value of its key
at its own tag: a log event by `event_honest`, a close entry by
`listed_entry_honest`. Isabelle: `emission_item_honest`. -/
theorem emission_item_honest {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok2 S units svl) {x : Nat × Event K V}
    (hx : x ∈ emission_t S units f svl s0) :
    x.2.img = state_after σ0 (S.log.take x.1) x.2.key := by
  rcases emission_t_item_cases hx with ⟨q, -, h2, rfl⟩ | ⟨q, -, hc⟩
  · exact event_honest _ rfl σ0
  · obtain ⟨u, hu, k', hk', rfl, -⟩ := closes_at_item hc
    exact H.listed_entry_honest hsvl hu hk'

/-- A unit that closes at or after the consumption start has its close
entries in the emission. Isabelle: `close_entry_in_emission`. -/
theorem close_entry_in_emission {svl : CUnit K V C → List K} {s0 : C}
    {u : CUnit K V C} {k : K} (hu : u ∈ units) (listed : k ∈ svl u)
    (s0hi : S.den s0 ≤ S.den u.hi) :
    ((S.den u.hi, ⟨k, u.refresh k⟩) : Nat × Event K V) ∈
      emission_t S units f svl s0 := by
  have in_closes : ((S.den u.hi, ⟨k, u.refresh k⟩) : Nat × Event K V) ∈
      closes_at S units svl (S.den u.hi) := by
    obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.mp hu
    refine List.mem_flatMap.mpr ⟨(u, i), ?_, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi, hiu]
    · rw [if_pos rfl]
      exact List.mem_map.mpr ⟨k, listed, rfl⟩
  have hi_f : S.den u.hi ≤ S.den f := H.bracket_hi_f u hu
  rcases Nat.lt_or_ge (S.den u.hi) (S.den f) with hlt | hge
  · refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, seg_zipIdx_mem s0hi hlt, ?_⟩)
    exact List.mem_append_left _ in_closes
  · have heq : S.den u.hi = S.den f := Nat.le_antisymm hi_f hge
    refine List.mem_append_right _ ?_
    rw [← heq]
    exact in_closes

/-- The form of `unlisted_quiet_absent` at any coordinate `g` at or after
the key's own close. A key of the scope that the enumeration does not
list, and that no log event from `s0` to `g` mentions, is absent at `g`.
Only the key's own unit enters. Isabelle: `unlisted_quiet_absent_at`. Its
proof uses the core's `contract_cut_unit`, which the Lean core does not
carry. The proof here runs the same two steps for the key's own unit
inline. -/
theorem unlisted_quiet_absent_at {svl : CUnit K V C → List K} {s0 g : C}
    (hsvl : svl_ok2 S units svl) {k : K} (hk : scope k)
    (s0lo : S.cle s0 (the_unit units f k).lo)
    (hi_g : S.cle (the_unit units f k).hi g)
    (unlisted : k ∉ svl (the_unit units f k))
    (quiet : evs_for k (S.win s0 g) = []) :
    state_after σ0 (S.pfx g) k = none := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  have lo_hi : S.cle (the_unit units f k).lo (the_unit units f k).hi :=
    H.bracket_lo_hi _ u_in
  have lo_g : S.cle (the_unit units f k).lo g := S.cle_trans lo_hi hi_g
  have quiet_lo_g : evs_for k (S.win (the_unit units f k).lo g) = [] := by
    have hs := S.evs_for_win_split s0lo lo_g k
    rw [quiet] at hs
    exact (List.append_eq_nil_iff.mp hs.symm).2
  have quiet_win : evs_for k
      (S.win (the_unit units f k).lo (the_unit units f k).hi) = [] := by
    have hs := S.evs_for_win_split lo_hi hi_g k
    rw [quiet_lo_g] at hs
    exact (List.append_eq_nil_iff.mp hs.symm).1
  have refresh_none : (the_unit units f k).refresh k = none := by
    refine Classical.byContradiction fun hr => unlisted ?_
    exact svl2_surv hsvl u_in ⟨k_dom, hr, quiet_win⟩
  obtain ⟨c, c_lo, c_hi, honest⟩ := H.O2_honest _ u_in k k_dom
  have c_g : S.cle c g := S.cle_trans c_hi hi_g
  rw [S.win_invariant_state lo_g (S.cle_refl g) quiet_lo_g σ0,
    ← S.win_invariant_state c_lo c_g quiet_lo_g σ0, ← honest]
  exact refresh_none

end CaptureContract

/-- A window without a log event of the key at any of its positions has
no event of the key. Isabelle: `evs_for_win_quiet`, stated in the
`coordinate_space` context. The log event `L ! q` is the bounded
`S.log[q]`, in range because `q < S.den b`. -/
theorem evs_for_win_quiet (S : CoordinateSpace K V C) {a b : C} {k : K}
    (quiet : ∀ q, S.den a ≤ q → ∀ h : q < S.den b,
      (S.log[q]'(Nat.lt_of_lt_of_le h (S.den_le_len b))).key ≠ k) :
    evs_for k (S.win a b) = [] := by
  refine List.filter_eq_nil_iff.mpr (fun e he => ?_)
  obtain ⟨q, h1, h2, rfl⟩ := mem_seg_pos he
  intro key
  exact quiet q h1 h2 (of_decide_eq_true key)

/-- On a list in tag order, keeping the items tagged at most `h` keeps a
prefix. Isabelle: `filter_tag_le_sorted`, for a linear order, with
`sorted` as `List.Pairwise (· ≤ ·)`. The filter decides its comparison
with the classical instance, which gives the same list. -/
theorem filter_tag_le_sorted {α : Type _} {β : Type _} [LE α] [Std.IsLinearOrder α]
    {S : List (α × β)} {h : α}
    (hs : List.Pairwise (· ≤ ·) (S.map Prod.fst)) :
    S.filter (fun x => decide (x.1 ≤ h)) = S.takeWhile (fun x => decide (x.1 ≤ h)) := by
  induction S with
  | nil => rfl
  | cons x S ih =>
    rw [List.map_cons, List.pairwise_cons] at hs
    obtain ⟨x_le, sS⟩ := hs
    by_cases hx : x.1 ≤ h
    · rw [List.filter_cons_of_pos (by simpa using hx),
        List.takeWhile_cons_of_pos (by simpa using hx), ih sS]
    · rw [List.filter_cons_of_neg (by simpa using hx),
        List.takeWhile_cons_of_neg (by simpa using hx)]
      refine List.filter_eq_nil_iff.mpr (fun y hy hyh => hx ?_)
      have hxy : x.1 ≤ y.1 := x_le y.1 (List.mem_map_of_mem hy)
      exact Std.IsPreorder.le_trans _ _ _ hxy (of_decide_eq_true hyh)

/-! ## A pass interrupted by a crash, and its restart, over one log -/

/-- A pass interrupted by a crash, and its restart, over one coordinate
space and one initial source state. The pass `P1` is a contract over the
units `U1`, the scope `sc1` and the frontier `f1`. The re-executed
chunks form the contract `P2` over `U2`, `sc2` and `f2`. The coordinate
`cmt` is the committed offset, and `crash` the position up to which `P1`
had emitted. The assumptions are stated with `S.den` exactly as the
Isabelle locale states them with `den`. The inclusion of `reexec` is
read pointwise. Isabelle: locale `pass_restart`. -/
structure PassRestart (S : CoordinateSpace K V C) (σ0 : State K V)
    (U1 : List (CUnit K V C)) (sc1 : K → Prop) (f1 : C)
    (U2 : List (CUnit K V C)) (sc2 : K → Prop) (f2 : C) (cmt crash : C) : Prop where
  /-- The pass as planned. Isabelle: the locale instance `P1`. -/
  P1 : CaptureContract S σ0 U1 sc1 f1
  /-- The re-executed chunks. Isabelle: the locale instance `P2`. -/
  P2 : CaptureContract S σ0 U2 sc2 f2
  /-- The committed offset is at or before the crash. Isabelle:
  `cmt_le_crash`. -/
  cmt_le_crash : S.den cmt ≤ S.den crash
  /-- The crash is at or before the pass's frontier. Isabelle:
  `crash_le_f1`. -/
  crash_le_f1 : S.den crash ≤ S.den f1
  /-- The second contract's frontier is at or after the crash. Isabelle:
  `crash_le_f2`. -/
  crash_le_f2 : S.den crash ≤ S.den f2
  /-- Every re-executed chunk opens at or after the crash. Isabelle:
  `crash_le_lo2`. -/
  crash_le_lo2 : ∀ u ∈ U2, S.den crash ≤ S.den u.lo
  /-- Every unit of the pass whose close lies after the crash is re-read
  by the second contract: its domain lies in the second scope.
  Isabelle: `reexec`, whose inclusion `u_dom u ⊆ sc2` is stated here
  pointwise. -/
  reexec : ∀ u ∈ U1, S.den crash < S.den u.hi → ∀ k, u.dom k → sc2 k

/-- The stream the sink sees, as a plain event list: the pass's emission
cut at the crash, then the log segment from `cmt` to the crash, then the
second contract's emission from the crash. Isabelle: `restart_stream`.
Its segment `map (λq. L ! q) [den cmt..<den crash]` is the log segment
`(S.log.take (S.den crash)).drop (S.den cmt)`, the same list entry for
entry. -/
def restart_stream (S : CoordinateSpace K V C) (U1 : List (CUnit K V C)) (f1 : C)
    (U2 : List (CUnit K V C)) (f2 : C) (cmt crash : C)
    (svl1 svl2 : CUnit K V C → List K) (s0 : C) : List (Event K V) :=
  ((emission_t S U1 f1 svl1 s0).filter (fun x => decide (x.1 ≤ S.den crash))).map
      Prod.snd ++
    ((S.log.take (S.den crash)).drop (S.den cmt) ++ emission S U2 f2 svl2 crash)

/-- The part delivered before the crash, as a timed list. Isabelle:
`cut_t`. -/
def cut_t (S : CoordinateSpace K V C) (U1 : List (CUnit K V C)) (f1 : C)
    (crash : C) (svl1 : CUnit K V C → List K) (s0 : C) : List (Nat × Event K V) :=
  (emission_t S U1 f1 svl1 s0).filter (fun x => decide (x.1 ≤ S.den crash))

/-- The part delivered after the restart, as a timed list. Isabelle:
`resumed_t`. Its tagged segment
`map (λq. (Suc q, L ! q)) [den cmt..<den crash]` is
`tagged_seg S (S.den cmt) (S.den crash)`, the same list entry for
entry. -/
def resumed_t (S : CoordinateSpace K V C) (U2 : List (CUnit K V C)) (f2 : C)
    (cmt crash : C) (svl2 : CUnit K V C → List K) : List (Nat × Event K V) :=
  tagged_seg S (S.den cmt) (S.den crash) ++ emission_t S U2 f2 svl2 crash

namespace PassRestart

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {U1 : List (CUnit K V C)} {sc1 : K → Prop} {f1 : C}
  {U2 : List (CUnit K V C)} {sc2 : K → Prop} {f2 : C} {cmt crash : C}
  (H : PassRestart S σ0 U1 sc1 f1 U2 sc2 f2 cmt crash)

include H

omit H in
/-- The stream is the two timed parts with the tags dropped. Isabelle:
`restart_stream_timed`. -/
theorem restart_stream_timed (svl1 svl2 : CUnit K V C → List K) (s0 : C) :
    restart_stream S U1 f1 U2 f2 cmt crash svl1 svl2 s0 =
      (cut_t S U1 f1 crash svl1 s0).map Prod.snd ++
        (resumed_t S U2 f2 cmt crash svl2).map Prod.snd := by
  simp only [restart_stream, cut_t, resumed_t, emission, List.map_append,
    map_snd_tagged_seg]

/-! ### The part before the crash is the pass's emission run up to the crash -/

omit H in
/-- The part before the crash is a prefix of the pass's emission.
Isabelle: `restart_cut_prefix`. -/
theorem restart_cut_prefix (svl1 : CUnit K V C → List K) (s0 : C) :
    ((emission_t S U1 f1 svl1 s0).filter (fun x => decide (x.1 ≤ S.den crash))).map
        Prod.snd <+: emission S U1 f1 svl1 s0 := by
  have same : (fun x : Nat × Event K V => decide (x.1 ≤ S.den crash)) =
      (fun x => @decide (x.1 ≤ S.den crash) (Classical.propDecidable _)) :=
    funext fun _ => decide_eq_decide.mpr Iff.rfl
  rw [same, filter_tag_le_sorted (emission_t_sorted S U1 f1 svl1 s0)]
  exact (List.takeWhile_prefix _).map Prod.snd

/-- When the consumption start is at or before the crash, the part
before the crash is block by block the emission of the pass with the
crash in place of the frontier: the close blocks at the positions from
`s0` to the crash, and the log events at the positions from `s0` to just
before the crash. Isabelle: `cut_blocks`, whose list over the positions
`[den s0..<den crash]` traverses the consumed segment with `zipIdx`, as
the core's `emission_t` does. -/
theorem cut_blocks {svl1 : CUnit K V C → List K} {s0 : C}
    (s0c : S.den s0 ≤ S.den crash) :
    cut_t S U1 f1 crash svl1 s0 =
      (((S.log.take (S.den crash)).drop (S.den s0)).zipIdx (S.den s0)).flatMap
          (fun ep => closes_at S U1 svl1 ep.2 ++ [(ep.2 + 1, ep.1)])
        ++ closes_at S U1 svl1 (S.den crash) := by
  have before : ((((S.log.take (S.den crash)).drop (S.den s0)).zipIdx (S.den s0)).flatMap
        (fun ep => closes_at S U1 svl1 ep.2 ++ [(ep.2 + 1, ep.1)])).filter
          (fun x => decide (x.1 ≤ S.den crash)) =
      (((S.log.take (S.den crash)).drop (S.den s0)).zipIdx (S.den s0)).flatMap
        (fun ep => closes_at S U1 svl1 ep.2 ++ [(ep.2 + 1, ep.1)]) := by
    refine List.filter_eq_self.mpr (fun x hx => decide_eq_true ?_)
    obtain ⟨ep, hep, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨-, h2, -⟩ := mem_seg_zipIdx hep
    rcases List.mem_append.mp hx with hx | hx
    · rw [closes_at_tag hx]
      omega
    · rw [List.mem_singleton.mp hx]
      exact h2
  have at_crash : (closes_at S U1 svl1 (S.den crash)).filter
      (fun x => decide (x.1 ≤ S.den crash)) = closes_at S U1 svl1 (S.den crash) :=
    List.filter_eq_self.mpr (fun x hx => decide_eq_true (Nat.le_of_eq (closes_at_tag hx)))
  rcases Nat.lt_or_ge (S.den crash) (S.den f1) with inside | at_end
  · have hsplit := seg_split S s0c H.crash_le_f1 (S.den_le_len f1)
    have hlen := seg_len_den S (S.den s0) crash
    have hcrash : S.den crash < (S.log.take (S.den f1)).length := by
      rw [List.length_take, Nat.min_eq_left (S.den_le_len f1)]
      exact inside
    have hcons : (S.log.take (S.den f1)).drop (S.den crash) =
        (S.log.take (S.den f1))[S.den crash]'hcrash ::
          (S.log.take (S.den f1)).drop (S.den crash + 1) :=
      List.drop_eq_getElem_cons hcrash
    have mid : ∀ e : Event K V,
        (closes_at S U1 svl1 (S.den crash) ++ [(S.den crash + 1, e)]).filter
          (fun x => decide (x.1 ≤ S.den crash)) = closes_at S U1 svl1 (S.den crash) := by
      intro e
      rw [List.filter_append, at_crash]
      have : [((S.den crash + 1, e) : Nat × Event K V)].filter
          (fun x => decide (x.1 ≤ S.den crash)) = [] := by
        refine List.filter_eq_nil_iff.mpr (fun y hy hyc => ?_)
        rw [List.mem_singleton.mp hy] at hyc
        have := of_decide_eq_true hyc
        omega
      rw [this, List.append_nil]
    have after : ((((S.log.take (S.den f1)).drop (S.den crash + 1)).zipIdx
          (S.den crash + 1)).flatMap
          (fun ep => closes_at S U1 svl1 ep.2 ++ [(ep.2 + 1, ep.1)])).filter
            (fun x => decide (x.1 ≤ S.den crash)) = [] := by
      refine List.filter_eq_nil_iff.mpr (fun x hx hxc => ?_)
      have hxc' := of_decide_eq_true hxc
      obtain ⟨ep, hep, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨h1, -, -⟩ := mem_seg_zipIdx hep
      rcases List.mem_append.mp hx with hx | hx
      · rw [closes_at_tag hx] at hxc'
        omega
      · rw [List.mem_singleton.mp hx] at hxc'
        simp only at hxc'
        omega
    have trail : (closes_at S U1 svl1 (S.den f1)).filter
        (fun x => decide (x.1 ≤ S.den crash)) = [] := by
      refine List.filter_eq_nil_iff.mpr (fun x hx hxc => ?_)
      have hxc' := of_decide_eq_true hxc
      rw [closes_at_tag hx] at hxc'
      omega
    simp only [cut_t, emission_t]
    rw [hsplit, List.zipIdx_append, hlen, Nat.add_sub_of_le s0c, hcons,
      List.zipIdx_cons, List.flatMap_append, List.flatMap_cons, List.filter_append,
      List.filter_append, List.filter_append, before, mid, after, trail]
    simp only [List.append_nil]
  · have heq : S.den crash = S.den f1 := Nat.le_antisymm H.crash_le_f1 at_end
    have all : cut_t S U1 f1 crash svl1 s0 = emission_t S U1 f1 svl1 s0 :=
      List.filter_eq_self.mpr (fun x hx =>
        decide_eq_true (heq ▸ emission_t_tag_le hx))
    rw [all, heq]
    rfl

/-- With the committed offset and the crash both at the pass's frontier,
the pass and the re-executed chunks form an instance of
`PassThenRead`. Isabelle: `restart_at_frontier_read_after`. -/
theorem restart_at_frontier_read_after (crash_f1 : S.den crash = S.den f1) :
    PassThenRead S σ0 U1 sc1 f1 U2 sc2 f2 := by
  refine ⟨H.P1, H.P2, ?_, ?_⟩
  · rw [← crash_f1]
    exact H.crash_le_f2
  · intro u hu
    rw [← crash_f1]
    exact H.crash_le_lo2 u hu

omit H in
/-- With the committed offset and the crash both at the pass's frontier,
nothing is re-delivered, and the stream is the pass's emission followed
by the second contract's emission from the pass's frontier. Isabelle:
`restart_at_frontier`. -/
theorem restart_at_frontier {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (cmt_f1 : S.den cmt = S.den f1) (crash_f1 : S.den crash = S.den f1) :
    restart_stream S U1 f1 U2 f2 cmt crash svl1 svl2 s0 =
      emission S U1 f1 svl1 s0 ++ emission S U2 f2 svl2 f1 := by
  have all : (emission_t S U1 f1 svl1 s0).filter (fun x => decide (x.1 ≤ S.den crash)) =
      emission_t S U1 f1 svl1 s0 :=
    List.filter_eq_self.mpr (fun x hx =>
      decide_eq_true (crash_f1 ▸ emission_t_tag_le hx))
  have no_seg : (S.log.take (S.den crash)).drop (S.den cmt) = [] := by
    rw [cmt_f1, crash_f1]
    exact List.drop_eq_nil_of_le (List.length_take_le _ _)
  have same_start : emission S U2 f2 svl2 crash = emission S U2 f2 svl2 f1 := by
    simp only [emission, emission_t, crash_f1]
  rw [restart_stream, all, no_seg, same_start, List.nil_append]
  rfl

/-! ### Tags, values and completeness of the two parts -/

omit H in
/-- An item of the part before the crash is an item of the pass's
emission. Isabelle: `cut_item`. -/
theorem cut_item {svl1 : CUnit K V C → List K} {s0 : C} {x : Nat × Event K V}
    (hx : x ∈ cut_t S U1 f1 crash svl1 s0) : x ∈ emission_t S U1 f1 svl1 s0 :=
  (List.mem_filter.mp hx).1

omit H in
/-- Every tag of the part before the crash is at most the crash.
Isabelle: `cut_tag_le`. -/
theorem cut_tag_le {svl1 : CUnit K V C → List K} {s0 : C} {x : Nat × Event K V}
    (hx : x ∈ cut_t S U1 f1 crash svl1 s0) : x.1 ≤ S.den crash :=
  of_decide_eq_true (List.mem_filter.mp hx).2

omit H in
/-- The part before the crash is in tag order. Isabelle: `cut_sorted`. -/
theorem cut_sorted (svl1 : CUnit K V C → List K) (s0 : C) :
    List.Pairwise (· ≤ ·) ((cut_t S U1 f1 crash svl1 s0).map Prod.fst) :=
  sorted_map_fst_filter (emission_t_sorted S U1 f1 svl1 s0)

/-- Every item of the part before the crash carries the source value of
its key at its own tag. Isabelle: `cut_honest`. -/
theorem cut_honest {svl1 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1) {x : Nat × Event K V}
    (hx : x ∈ cut_t S U1 f1 crash svl1 s0) :
    x.2.img = state_after σ0 (S.log.take x.1) x.2.key :=
  H.P1.emission_item_honest hsvl1 (cut_item hx)

/-- The part before the crash carries every log event from `s0` to the
crash. Isabelle: `cut_complete`, whose `L ! q` is the bounded
`S.log[q]`, in range because `q < S.den crash`. -/
theorem cut_complete {svl1 : CUnit K V C → List K} {s0 : C} {q : Nat} {k : K}
    (s0q : S.den s0 ≤ q) (hq : q < S.den crash)
    (key : (S.log[q]'(Nat.lt_of_lt_of_le hq (S.den_le_len crash))).key = k) :
    (q + 1, S.log[q]'(Nat.lt_of_lt_of_le hq (S.den_le_len crash))) ∈
      titems_for k (cut_t S U1 f1 crash svl1 s0) := by
  have hf1 : q < S.den f1 := Nat.lt_of_lt_of_le hq H.crash_le_f1
  have hin := emission_t_event_in (units := U1) (svl := svl1) s0q hf1
  exact List.mem_filter.mpr
    ⟨List.mem_filter.mpr ⟨hin, decide_eq_true hq⟩, decide_eq_true key⟩

omit H in
/-- An item of the part after the restart is a re-delivered log event
from `cmt` to the crash, or an item of the second contract's emission
from the crash. Isabelle: `resumed_item_cases`. It is an `obtains`
statement, stated here as the disjunction of its two cases. The log
event at position `q` is the bounded `S.log[q]`, in range because
`q < S.den crash`. -/
theorem resumed_item_cases {svl2 : CUnit K V C → List K} {x : Nat × Event K V}
    (hx : x ∈ resumed_t S U2 f2 cmt crash svl2) :
    (∃ q, S.den cmt ≤ q ∧ ∃ h2 : q < S.den crash,
        x = (q + 1, S.log[q]'(Nat.lt_of_lt_of_le h2 (S.den_le_len crash)))) ∨
      x ∈ emission_t S U2 f2 svl2 crash := by
  rcases List.mem_append.mp hx with hx | hx
  · left
    unfold tagged_seg at hx
    obtain ⟨ep, hep, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2, he⟩ := mem_seg_zipIdx hep
    exact ⟨ep.2, h1, h2, by rw [he]⟩
  · exact Or.inr hx

/-- Every tag of the part after the restart is at or after the committed
offset. Isabelle: `resumed_tag_ge`. -/
theorem resumed_tag_ge {svl2 : CUnit K V C → List K} {x : Nat × Event K V}
    (hx : x ∈ resumed_t S U2 f2 cmt crash svl2) : S.den cmt ≤ x.1 := by
  rcases resumed_item_cases hx with ⟨q, h1, -, rfl⟩ | hx
  · exact Nat.le_succ_of_le h1
  · have h := emission_t_tag_ge hx
    have h1 := H.cmt_le_crash
    have h2 := H.crash_le_f2
    omega

/-- Every tag of the part after the restart is at most the second
contract's frontier. Isabelle: `resumed_tag_le`. -/
theorem resumed_tag_le {svl2 : CUnit K V C → List K} {x : Nat × Event K V}
    (hx : x ∈ resumed_t S U2 f2 cmt crash svl2) : x.1 ≤ S.den f2 := by
  rcases resumed_item_cases hx with ⟨q, -, h2, rfl⟩ | hx
  · exact Nat.le_trans h2 H.crash_le_f2
  · exact emission_t_tag_le hx

/-- The part after the restart is in position order: the re-delivered
events are tagged at most the crash, and the second contract's items at
least the crash. Isabelle: `resumed_sorted`. -/
theorem resumed_sorted (svl2 : CUnit K V C → List K) :
    List.Pairwise (· ≤ ·) ((resumed_t S U2 f2 cmt crash svl2).map Prod.fst) := by
  unfold resumed_t
  rw [List.map_append, List.pairwise_append]
  refine ⟨?_, emission_t_sorted S U2 f2 svl2 crash, ?_⟩
  · rw [List.pairwise_map]
    exact (pairwise_tagged_seg S _ _).imp (fun h => Nat.le_of_lt h)
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    have hx2 := (mem_tagged_seg_bounds hx).2
    have hy1 := emission_t_tag_ge hy
    have h2 := H.crash_le_f2
    omega

/-- Every item of the part after the restart carries the source value of
its key at its own tag. Isabelle: `resumed_honest`. -/
theorem resumed_honest {svl2 : CUnit K V C → List K}
    (hsvl2 : svl_ok2 S U2 svl2) {x : Nat × Event K V}
    (hx : x ∈ resumed_t S U2 f2 cmt crash svl2) :
    x.2.img = state_after σ0 (S.log.take x.1) x.2.key := by
  rcases resumed_item_cases hx with ⟨q, -, h2, rfl⟩ | hx
  · exact event_honest _ rfl σ0
  · exact H.P2.emission_item_honest hsvl2 hx

omit H in
/-- The part after the restart carries every log event from `cmt` to
`f2`. Isabelle: `resumed_complete`, whose `L ! q` is the bounded
`S.log[q]`, in range because `q < S.den f2`. -/
theorem resumed_complete {svl2 : CUnit K V C → List K} {q : Nat} {k : K}
    (cq : S.den cmt ≤ q) (hq : q < S.den f2)
    (key : (S.log[q]'(Nat.lt_of_lt_of_le hq (S.den_le_len f2))).key = k) :
    (q + 1, S.log[q]'(Nat.lt_of_lt_of_le hq (S.den_le_len f2))) ∈
      titems_for k (resumed_t S U2 f2 cmt crash svl2) := by
  refine List.mem_filter.mpr ⟨?_, decide_eq_true key⟩
  by_cases hc : q < S.den crash
  · refine List.mem_append_left _ ?_
    unfold tagged_seg
    exact List.mem_map.mpr ⟨_, seg_zipIdx_mem cq hc, rfl⟩
  · exact List.mem_append_right _ (emission_t_event_in (Nat.le_of_not_lt hc) hq)

/-! ### A key with an item ends at the source state -/

/-- If the part after the restart has an item for the key, that part
decides the key, and it ends at the source state at `f2`, from any state
the part before the crash left. Isabelle: `resumed_key_replay`. -/
theorem resumed_key_replay {svl1 svl2 : CUnit K V C → List K} {s0 : C} {k : K}
    (hsvl2 : svl_ok2 S U2 svl2)
    (ne : titems_for k (resumed_t S U2 f2 cmt crash svl2) ≠ []) (D : State K V) :
    state_after D (restart_stream S U1 f1 U2 f2 cmt crash svl1 svl2 s0) k =
      state_after σ0 (S.pfx f2) k := by
  have T_item : ∀ x ∈ titems_for k (resumed_t S U2 f2 cmt crash svl2),
      x ∈ resumed_t S U2 f2 cmt crash svl2 ∧ x.2.key = k := by
    intro x hx
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hx
    exact ⟨h1, of_decide_eq_true h2⟩
  have keyed : ∀ x ∈ titems_for k (resumed_t S U2 f2 cmt crash svl2), x.2.key = k :=
    fun x hx => (T_item x hx).2
  have honest : ∀ x ∈ titems_for k (resumed_t S U2 f2 cmt crash svl2),
      x.2.img = state_after σ0 (S.log.take x.1) k := by
    intro x hx
    have h := H.resumed_honest hsvl2 (T_item x hx).1
    rw [(T_item x hx).2] at h
    exact h
  have sorted : List.Pairwise (· ≤ ·)
      ((titems_for k (resumed_t S U2 f2 cmt crash svl2)).map Prod.fst) :=
    sorted_map_fst_filter (H.resumed_sorted svl2)
  have low : ∀ x ∈ titems_for k (resumed_t S U2 f2 cmt crash svl2), S.den cmt ≤ x.1 :=
    fun x hx => H.resumed_tag_ge (T_item x hx).1
  have high : ∀ x ∈ titems_for k (resumed_t S U2 f2 cmt crash svl2), x.1 ≤ S.den f2 :=
    fun x hx => H.resumed_tag_le (T_item x hx).1
  have complete : ∀ p, S.den cmt ≤ p → p < S.den f2 → ∀ hp : p < S.log.length,
      (S.log[p]'hp).key = k →
        (p + 1, S.log[p]'hp) ∈ titems_for k (resumed_t S U2 f2 cmt crash svl2) :=
    fun _ h1 h2 _ key => resumed_complete h1 h2 key
  have T_self : titems_for k (titems_for k (resumed_t S U2 f2 cmt crash svl2)) =
      titems_for k (resumed_t S U2 f2 cmt crash svl2) :=
    List.filter_eq_self.mpr (fun x hx => decide_eq_true (keyed x hx))
  rw [restart_stream_timed, state_after_append]
  have evs : evs_for k ((resumed_t S U2 f2 cmt crash svl2).map Prod.snd) =
      evs_for k ((titems_for k (resumed_t S U2 f2 cmt crash svl2)).map Prod.snd) := by
    rw [evs_for_map_snd, evs_for_map_snd, T_self]
  rw [replay_per_key evs]
  exact honest_stream_last ne keyed honest sorted low high complete _

/-- If the part after the restart has nothing for the key, but the part
before the crash has, the key has no log event from `cmt` to `f2`, and
the last item of the part before the crash decides. The key ends at the
source state at `f2`. Isabelle: `cut_key_replay`. -/
theorem cut_key_replay {svl1 svl2 : CUnit K V C → List K} {s0 : C} {k : K}
    (hsvl1 : svl_ok2 S U1 svl1) (s0cmt : S.den s0 ≤ S.den cmt)
    (none_after : titems_for k (resumed_t S U2 f2 cmt crash svl2) = [])
    (ne : titems_for k (cut_t S U1 f1 crash svl1 s0) ≠ []) (D : State K V) :
    state_after D (restart_stream S U1 f1 U2 f2 cmt crash svl1 svl2 s0) k =
      state_after σ0 (S.pfx f2) k := by
  have T_item : ∀ x ∈ titems_for k (cut_t S U1 f1 crash svl1 s0),
      x ∈ cut_t S U1 f1 crash svl1 s0 ∧ x.2.key = k := by
    intro x hx
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hx
    exact ⟨h1, of_decide_eq_true h2⟩
  have keyed : ∀ x ∈ titems_for k (cut_t S U1 f1 crash svl1 s0), x.2.key = k :=
    fun x hx => (T_item x hx).2
  have honest : ∀ x ∈ titems_for k (cut_t S U1 f1 crash svl1 s0),
      x.2.img = state_after σ0 (S.log.take x.1) k := by
    intro x hx
    have h := H.cut_honest hsvl1 (T_item x hx).1
    rw [(T_item x hx).2] at h
    exact h
  have sorted : List.Pairwise (· ≤ ·)
      ((titems_for k (cut_t S U1 f1 crash svl1 s0)).map Prod.fst) :=
    sorted_map_fst_filter (cut_sorted svl1 s0)
  have low : ∀ x ∈ titems_for k (cut_t S U1 f1 crash svl1 s0), S.den s0 ≤ x.1 := by
    intro x hx
    have h := emission_t_tag_ge (cut_item (T_item x hx).1)
    have h1 := H.cmt_le_crash
    have h2 := H.crash_le_f1
    omega
  have high : ∀ x ∈ titems_for k (cut_t S U1 f1 crash svl1 s0), x.1 ≤ S.den f2 :=
    fun x hx => Nat.le_trans (cut_tag_le (T_item x hx).1) H.crash_le_f2
  have complete : ∀ p, S.den s0 ≤ p → p < S.den f2 → ∀ hp : p < S.log.length,
      (S.log[p]'hp).key = k →
        (p + 1, S.log[p]'hp) ∈ titems_for k (cut_t S U1 f1 crash svl1 s0) := by
    intro p h1 h2 _ key
    by_cases hc : S.den cmt ≤ p
    · have hin := resumed_complete (U2 := U2) (svl2 := svl2) (crash := crash) hc h2 key
      rw [none_after] at hin
      cases hin
    · have hpc : p < S.den crash := Nat.lt_of_lt_of_le (Nat.lt_of_not_le hc) H.cmt_le_crash
      exact H.cut_complete h1 hpc key
  have T_self : titems_for k (titems_for k (cut_t S U1 f1 crash svl1 s0)) =
      titems_for k (cut_t S U1 f1 crash svl1 s0) :=
    List.filter_eq_self.mpr (fun x hx => decide_eq_true (keyed x hx))
  have evs : evs_for k (restart_stream S U1 f1 U2 f2 cmt crash svl1 svl2 s0) =
      evs_for k ((titems_for k (cut_t S U1 f1 crash svl1 s0)).map Prod.snd) := by
    rw [restart_stream_timed, evs_for_append, evs_for_map_snd, evs_for_map_snd,
      none_after, evs_for_map_snd, T_self, List.map_nil, List.append_nil]
  rw [replay_per_key evs]
  exact honest_stream_last ne keyed honest sorted low high complete D

/-! ### Safety and convergence -/

/-- Safety across a restart. A key of either scope ends at the source
state at `f2`, or the stream has no item for it at all. In the second
case the sink keeps its initial value, the key is absent at `f2`, no
unit of the pass that closed at or before the crash lists it, the second
contract does not list it, and no log event from `s0` to `f2` mentions
it. Isabelle: `restart_safe`. -/
theorem restart_safe {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0cmt : S.den s0 ≤ S.den cmt)
    {k : K} (hk : sc1 k ∨ sc2 k) (D0 : State K V) :
    state_after D0 (restart_stream S U1 f1 U2 f2 cmt crash svl1 svl2 s0) k =
        state_after σ0 (S.pfx f2) k ∨
      (state_after D0 (restart_stream S U1 f1 U2 f2 cmt crash svl1 svl2 s0) k = D0 k ∧
        state_after σ0 (S.pfx f2) k = none ∧
        (sc1 k → S.den (the_unit U1 f1 k).hi ≤ S.den crash →
          k ∉ svl1 (the_unit U1 f1 k)) ∧
        (sc2 k → k ∉ svl2 (the_unit U2 f2 k)) ∧
        evs_for k (S.win s0 f2) = []) := by
  by_cases resumed : titems_for k (resumed_t S U2 f2 cmt crash svl2) = []
  · by_cases cut : titems_for k (cut_t S U1 f1 crash svl1 s0) = []
    · right
      have kept : state_after D0 (restart_stream S U1 f1 U2 f2 cmt crash svl1 svl2 s0) k =
          D0 k := by
        refine state_after_no_events ?_ D0
        rw [restart_stream_timed, evs_for_append, evs_for_map_snd, evs_for_map_snd, cut,
          resumed]
        rfl
      have quiet_from_cmt : ∀ q, S.den cmt ≤ q → ∀ h : q < S.den f2,
          (S.log[q]'(Nat.lt_of_lt_of_le h (S.den_le_len f2))).key ≠ k := by
        intro q h1 h2 key
        have hin := resumed_complete (U2 := U2) (svl2 := svl2) (crash := crash) h1 h2 key
        rw [resumed] at hin
        cases hin
      have quiet_pos : ∀ q, S.den s0 ≤ q → ∀ h : q < S.den f2,
          (S.log[q]'(Nat.lt_of_lt_of_le h (S.den_le_len f2))).key ≠ k := by
        intro q h1 h2
        by_cases hc : q < S.den crash
        · intro key
          have hin := H.cut_complete (svl1 := svl1) h1 hc key
          rw [cut] at hin
          cases hin
        · exact quiet_from_cmt q (Nat.le_trans H.cmt_le_crash (Nat.le_of_not_lt hc)) h2
      have quiet : evs_for k (S.win s0 f2) = [] := evs_for_win_quiet S quiet_pos
      have quiet_crash : evs_for k (S.win crash f2) = [] :=
        evs_for_win_quiet S (fun q h1 h2 =>
          quiet_from_cmt q (Nat.le_trans H.cmt_le_crash h1) h2)
      have P2_unlisted : sc2 k → k ∉ svl2 (the_unit U2 f2 k) := by
        intro k2 listed
        have u_in := (H.P2.the_unit_props k2).1
        have crash_hi : S.den crash ≤ S.den (the_unit U2 f2 k).hi :=
          Nat.le_trans (H.crash_le_lo2 _ u_in) (H.P2.bracket_lo_hi _ u_in)
        have hin := H.P2.close_entry_in_emission (s0 := crash) u_in listed crash_hi
        have hin' : ((S.den (the_unit U2 f2 k).hi, ⟨k, (the_unit U2 f2 k).refresh k⟩) :
            Nat × Event K V) ∈ titems_for k (resumed_t S U2 f2 cmt crash svl2) :=
          List.mem_filter.mpr ⟨List.mem_append_right _ hin, decide_eq_true rfl⟩
        rw [resumed] at hin'
        cases hin'
      have P1_unlisted : sc1 k → S.den (the_unit U1 f1 k).hi ≤ S.den crash →
          k ∉ svl1 (the_unit U1 f1 k) := by
        intro k1 hi_crash listed
        have u_in := (H.P1.the_unit_props k1).1
        have s0_hi : S.den s0 ≤ S.den (the_unit U1 f1 k).hi :=
          Nat.le_trans (s0lo _ u_in) (H.P1.bracket_lo_hi _ u_in)
        have hin := H.P1.close_entry_in_emission (s0 := s0) u_in listed s0_hi
        have hin' : ((S.den (the_unit U1 f1 k).hi, ⟨k, (the_unit U1 f1 k).refresh k⟩) :
            Nat × Event K V) ∈ titems_for k (cut_t S U1 f1 crash svl1 s0) :=
          List.mem_filter.mpr
            ⟨List.mem_filter.mpr ⟨hin, decide_eq_true hi_crash⟩, decide_eq_true rfl⟩
        rw [cut] at hin'
        cases hin'
      have src_none : state_after σ0 (S.pfx f2) k = none := by
        by_cases k2 : sc2 k
        · have P2_lo : ∀ u ∈ U2, S.cle crash u.lo := H.crash_le_lo2
          exact H.P2.unlisted_quiet_absent hsvl2 P2_lo k2 (P2_unlisted k2) quiet_crash
        · have k1 : sc1 k := hk.resolve_right k2
          obtain ⟨u_in, k_dom⟩ := H.P1.the_unit_props k1
          have hi_crash : S.den (the_unit U1 f1 k).hi ≤ S.den crash := by
            refine Nat.le_of_not_lt (fun late => k2 ?_)
            exact H.reexec _ u_in late k k_dom
          have s0_lo : S.cle s0 (the_unit U1 f1 k).lo := s0lo _ u_in
          have hi_f2 : S.cle (the_unit U1 f1 k).hi f2 :=
            Nat.le_trans hi_crash H.crash_le_f2
          exact H.P1.unlisted_quiet_absent_at hsvl1 k1 s0_lo hi_f2
            (P1_unlisted k1 hi_crash) quiet
      exact ⟨kept, src_none, P1_unlisted, P2_unlisted, quiet⟩
    · left
      exact H.cut_key_replay hsvl1 s0cmt resumed cut D0
  · left
    exact H.resumed_key_replay hsvl2 resumed D0

/-- Convergence across a restart. Every key the sink holds that is
absent at `f2` and quiet from `s0` to `f2` must be listed, either by the
close entry of its unit in the pass, when that unit closed at or before
the crash, or by the second contract. Then the sink ends at the source
state at `f2` on both scopes. Isabelle: `restart_converges`. -/
theorem restart_converges {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0cmt : S.den s0 ≤ S.den cmt)
    (cover : ∀ k, (sc1 k ∨ sc2 k) → D0 k ≠ none →
      state_after σ0 (S.pfx f2) k = none → evs_for k (S.win s0 f2) = [] →
      (sc1 k ∧ S.den (the_unit U1 f1 k).hi ≤ S.den crash ∧
          k ∈ svl1 (the_unit U1 f1 k)) ∨
        (sc2 k ∧ k ∈ svl2 (the_unit U2 f2 k))) :
    ∀ k, (sc1 k ∨ sc2 k) →
      state_after D0 (restart_stream S U1 f1 U2 f2 cmt crash svl1 svl2 s0) k =
        state_after σ0 (S.pfx f2) k := by
  intro k hk
  rcases H.restart_safe hsvl1 hsvl2 s0lo s0cmt hk D0 with
    h | ⟨hD, hsrc, hn1, hn2, hq⟩
  · exact h
  · by_cases hD0 : D0 k = none
    · rw [hD, hD0, hsrc]
    · rcases cover k hk hD0 hsrc hq with ⟨h1, hhi, hl⟩ | ⟨h2, hl⟩
      · exact absurd hl (hn1 h1 hhi)
      · exact absurd hl (hn2 h2)

end PassRestart

/-- A crash after the pass's frontier. Every unit of the pass has closed
by the crash, so the pass with the crash as its frontier is a contract
(`contract_with_frontier`), and together with the second contract it is
an instance of `PassRestart`. The assumption `reexec` holds because no
unit of the pass closes after the crash. Isabelle:
`pass_restart_after_frontier`. -/
theorem pass_restart_after_frontier {S : CoordinateSpace K V C} {σ0 : State K V}
    {U1 : List (CUnit K V C)} {sc1 : K → Prop} {f1 : C}
    {U2 : List (CUnit K V C)} {sc2 : K → Prop} {f2 : C} {cmt crash : C}
    (P1 : CaptureContract S σ0 U1 sc1 f1) (P2 : CaptureContract S σ0 U2 sc2 f2)
    (f1_crash : S.den f1 ≤ S.den crash) (cmt_crash : S.den cmt ≤ S.den crash)
    (crash_f2 : S.den crash ≤ S.den f2)
    (crash_lo2 : ∀ u ∈ U2, S.den crash ≤ S.den u.lo) :
    PassRestart S σ0 U1 sc1 crash U2 sc2 f2 cmt crash := by
  have hi_crash : ∀ u ∈ U1, S.den u.hi ≤ S.den crash :=
    fun u hu => Nat.le_trans (P1.bracket_hi_f u hu) f1_crash
  refine ⟨P1.contract_with_frontier hi_crash, P2, cmt_crash, Nat.le_refl _, crash_f2,
    crash_lo2, ?_⟩
  intro u hu late
  exact absurd (hi_crash u hu) (Nat.not_le_of_lt late)

end

end DBLogContract
