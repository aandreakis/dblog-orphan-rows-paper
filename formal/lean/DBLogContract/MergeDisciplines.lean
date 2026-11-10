import DBLogContract.CutTheorem

/-!
# Emitted streams and the window-discard equivalence

This file is a port of `Merge_Disciplines.thy` from the Isabelle
development: the stream substrate and the discharge of the
window-discard equivalence obligation. In paper terms it carries
Definition 6.1 (stream replay), Definition 6.2 (survivors and the
window-discard emission), Lemma 6.1 (the per-key shape of the
discard emission), Theorem 2 (window-discard equivalence: the
emitted stream replays to the canonical sink, so "the log wins" is
a theorem), and Theorem 3 (window-discard per-key monotonicity).

Stream model, as in the source: an emitted stream is a list of
events replayed by the same per-key fold as the source dynamics but
starting from the EMPTY map. A key never emitted denotes absence,
so absence by omission is the absence verdict; refresh entries for
absent keys are never emitted, while delete events are. The
emission is built occurrence-tagged: an event at log position `p`
carries tag `p + 1` (the state version after it commits), and a
unit's surviving refresh entries are emitted when the unit's window
closes, tagged with the close position. Tags make the monotonicity
claim a sortedness statement. The consumption-start premise
`s0 ⊑ u.lo` for every unit is S-OBS's clause for this discipline,
and the construction is single-pass.

Position transport, recorded also in VERIFICATION.md: the Isabelle
source enumerates positions `[a..<b]` and indexes the log with the
junk-total `!`. The port carries the same data junk-free: consumed
segments are traversed with `zipIdx`, which pairs each event with
its absolute position, and `closes_at` traverses the unit family
with `zipIdx` where the source maps over `[0..<length units]` and
indexes. The resulting lists are the same, entry for entry.
-/

namespace DBLogContract

universe u v w

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-- Replay of an emitted stream: the per-key fold from the EMPTY
map (paper Definition 6.1). Isabelle: `stream_replay`. -/
def stream_replay (Sq : List (Event K V)) : State K V :=
  state_after (fun _ => none) Sq

/-- Survivors of a unit: keys of its domain that are present in the
refresh AND untouched by the unit's own window (paper Definition
6.2). Isabelle: `survivors`, stated there as a set. -/
def survivors (S : CoordinateSpace K V C) (u : CUnit K V C) : K → Prop :=
  fun k => u.dom k ∧ u.refresh k ≠ none ∧
    evs_for k (S.win u.lo u.hi) = []

/-- A survivor enumeration is lawful when, for every unit of the
family, it is a duplicate-free listing of exactly that unit's
survivors. Isabelle: `svl_ok`. -/
def svl_ok (S : CoordinateSpace K V C) (units : List (CUnit K V C))
    (svl : CUnit K V C → List K) : Prop :=
  ∀ u ∈ units, (svl u).Nodup ∧ ∀ k, k ∈ svl u ↔ survivors S u k

/-- A unit's close block: one refresh entry per survivor, tagged
with the close position, the denotation of the unit's high edge.
Isabelle: `close_block`. -/
def close_block (S : CoordinateSpace K V C)
    (svl : CUnit K V C → List K) (u : CUnit K V C) :
    List (Nat × Event K V) :=
  (svl u).map (fun k => (S.den u.hi, ⟨k, u.refresh k⟩))

/-- All close blocks due at position `p`: the blocks of the units
whose high edge denotes `p`, in family order. Isabelle:
`closes_at`, which maps over `[0..<length units]` and indexes; the
port traverses `units.zipIdx`, producing the same list. -/
def closes_at (S : CoordinateSpace K V C) (units : List (CUnit K V C))
    (svl : CUnit K V C → List K) (p : Nat) : List (Nat × Event K V) :=
  units.zipIdx.flatMap (fun ui =>
    if S.den ui.1.hi = p then close_block S svl ui.1 else [])

/-- The consumed log segment between two positions, tagged with
absolute positions and the occurrence tag `p + 1`. Port-local
normal form; in the Isabelle source this list appears as
`map (λp. (Suc p, L ! p)) [a..<b]` filtered per key. -/
def tagged_seg (S : CoordinateSpace K V C) (a b : Nat) :
    List (Nat × Event K V) :=
  (((S.log.take b).drop a).zipIdx a).map (fun ep => (ep.2 + 1, ep.1))

/-- The tagged window-discard emission from consumption start `s0`
to the frontier: a single pass over the consumed segment; every
event is passed through at its own position; the close blocks due
at a position are emitted immediately before the event at that
position; units whose high edge sits at the frontier close after
the last consumed event (paper Definition 6.2). Isabelle:
`emission_t`. -/
def emission_t (S : CoordinateSpace K V C) (units : List (CUnit K V C))
    (f : C) (svl : CUnit K V C → List K) (s0 : C) :
    List (Nat × Event K V) :=
  (((S.log.take (S.den f)).drop (S.den s0)).zipIdx (S.den s0)).flatMap
    (fun ep => closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)])
  ++ closes_at S units svl (S.den f)

/-- The plain window-discard emission: the tagged emission with the
tags dropped. Isabelle: `emission`. -/
def emission (S : CoordinateSpace K V C) (units : List (CUnit K V C))
    (f : C) (svl : CUnit K V C → List K) (s0 : C) :
    List (Event K V) :=
  (emission_t S units f svl s0).map Prod.snd

/-- The tagged items of one key, in stream order. Isabelle:
`titems_for`. -/
def titems_for (k : K) (Sq : List (Nat × Event K V)) :
    List (Nat × Event K V) :=
  Sq.filter (fun x => decide (x.2.key = k))

/-! ## Port-local list helpers -/

theorem evs_for_map_snd (k : K) (Sq : List (Nat × Event K V)) :
    evs_for k (Sq.map Prod.snd) = (titems_for k Sq).map Prod.snd := by
  simp [evs_for, titems_for, List.filter_map]
  rfl

theorem map_fst_zipIdx {α : Type _} (l : List α) (n : Nat) :
    (l.zipIdx n).map Prod.fst = l := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih => simp [List.zipIdx, ih]

theorem pairwise_zipIdx_lt {α : Type _} (l : List α) (n : Nat) :
    List.Pairwise (fun a b => a.2 < b.2) (l.zipIdx n) := by
  induction l generalizing n with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    rw [List.zipIdx_cons, List.pairwise_cons]
    refine ⟨?_, ih (n + 1)⟩
    rintro ⟨e, i⟩ ha
    obtain ⟨h1, -, -⟩ := List.mem_zipIdx ha
    show n < i
    omega

theorem nodup_zipIdx {α : Type _} (l : List α) (n : Nat) :
    (l.zipIdx n).Nodup := by
  have h := pairwise_zipIdx_lt l n
  exact h.imp (fun hlt => by
    intro heq
    rw [heq] at hlt
    omega)

theorem flatMap_eq_nil_of_forall {α : Type _} {β : Type _}
    {xs : List α} {g : α → List β} (h : ∀ x ∈ xs, g x = []) :
    xs.flatMap g = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, h x (List.mem_cons.mpr (Or.inl rfl)), List.nil_append]
    exact ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

/-- Port-local single-source lemma (the Isabelle
`concat_map_upt_single` in element form): over a duplicate-free
list, if every element other than one produces the empty list, the
flat map is that one element's output. -/
theorem flatMap_single {α : Type _} {β : Type _}
    {xs : List α} {g : α → List β} {x₀ : α}
    (hnd : xs.Nodup) (h₀ : x₀ ∈ xs)
    (hz : ∀ x ∈ xs, x ≠ x₀ → g x = []) :
    xs.flatMap g = g x₀ := by
  induction xs with
  | nil => cases h₀
  | cons x xs ih =>
    rcases List.mem_cons.mp h₀ with hx | hx
    · subst hx
      have hnotin : x₀ ∉ xs := (List.nodup_cons.mp hnd).1
      rw [List.flatMap_cons,
          flatMap_eq_nil_of_forall (fun y hy =>
            hz y (List.mem_cons.mpr (Or.inr hy))
              (fun hyx => hnotin (hyx ▸ hy))),
          List.append_nil]
    · have hne : x ≠ x₀ := by
        intro h
        exact (List.nodup_cons.mp hnd).1 (h ▸ hx)
      rw [List.flatMap_cons, hz x (List.mem_cons.mpr (Or.inl rfl)) hne,
          List.nil_append]
      exact ih (List.nodup_cons.mp hnd).2 hx
        (fun y hy => hz y (List.mem_cons.mpr (Or.inr hy)))

/-- Port-local (the Isabelle `distinct_filter_eq`): filtering a
duplicate-free list for one element. -/
theorem nodup_filter_eq {α : Type _} {xs : List α} (hnd : xs.Nodup) (k : α) :
    xs.filter (fun x => decide (x = k)) =
      if k ∈ xs then [k] else [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnotin, hnd'⟩
    by_cases hxk : x = k
    · subst hxk
      rw [if_pos (List.mem_cons.mpr (Or.inl rfl))]
      rw [List.filter_cons, if_pos (by simp)]
      rw [ih hnd', if_neg hnotin]
    · rw [List.filter_cons, if_neg (by simp [hxk])]
      rw [ih hnd']
      by_cases hk : k ∈ xs
      · rw [if_pos hk, if_pos (List.mem_cons.mpr (Or.inr hk))]
      · rw [if_neg hk, if_neg (by
          intro h
          rcases List.mem_cons.mp h with h | h
          · exact hxk h.symm
          · exact hk h)]

/-- The tags-dropped tagged segment is the log segment itself.
Port-local. -/
theorem map_snd_tagged_seg (S : CoordinateSpace K V C) (a b : Nat) :
    (tagged_seg S a b).map Prod.snd = (S.log.take b).drop a := by
  simp only [tagged_seg, List.map_map]
  have : (Prod.snd ∘ fun ep : Event K V × Nat => (ep.2 + 1, ep.1)) =
      Prod.fst := by
    funext ep
    rfl
  rw [this, map_fst_zipIdx]

/-- Tagged segments compose at an intermediate position. Port-local;
the Isabelle counterpart is `kposs_split` with `upt_split`. -/
theorem tagged_seg_split (S : CoordinateSpace K V C) {a b c : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ S.log.length) :
    tagged_seg S a c = tagged_seg S a b ++ tagged_seg S b c := by
  have hb : b ≤ S.log.length := Nat.le_trans hbc hc
  have hsplit : (S.log.take c).drop a =
      ((S.log.take b).drop a) ++ ((S.log.take c).drop b) := by
    have h1 : S.log.take b ++ (S.log.take c).drop b = S.log.take c := by
      have h2 : (S.log.take c).take b = S.log.take b := by
        rw [List.take_take, Nat.min_eq_left hbc]
      rw [← h2, List.take_append_drop]
    calc (S.log.take c).drop a
        = (S.log.take b ++ (S.log.take c).drop b).drop a := by rw [h1]
      _ = (S.log.take b).drop a ++
            ((S.log.take c).drop b).drop (a - (S.log.take b).length) := by
          rw [List.drop_append]
      _ = (S.log.take b).drop a ++ ((S.log.take c).drop b) := by
          rw [List.length_take, Nat.min_eq_left hb,
              show a - b = 0 from by omega, List.drop_zero]
  simp only [tagged_seg]
  rw [hsplit, List.zipIdx_append, List.map_append]
  have hlen : ((S.log.take b).drop a).length = b - a := by
    rw [List.length_drop, List.length_take, Nat.min_eq_left hb]
  rw [hlen, show a + (b - a) = b from by omega]

/-- Log-segment split at an intermediate position. Port-local. -/
theorem seg_split (S : CoordinateSpace K V C) {a b c : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ S.log.length) :
    (S.log.take c).drop a =
      ((S.log.take b).drop a) ++ ((S.log.take c).drop b) := by
  have hb : b ≤ S.log.length := Nat.le_trans hbc hc
  have h1 : S.log.take b ++ (S.log.take c).drop b = S.log.take c := by
    have h2 : (S.log.take c).take b = S.log.take b := by
      rw [List.take_take, Nat.min_eq_left hbc]
    rw [← h2, List.take_append_drop]
  calc (S.log.take c).drop a
      = (S.log.take b ++ (S.log.take c).drop b).drop a := by rw [h1]
    _ = (S.log.take b).drop a ++
          ((S.log.take c).drop b).drop (a - (S.log.take b).length) := by
        rw [List.drop_append]
    _ = (S.log.take b).drop a ++ ((S.log.take c).drop b) := by
        rw [List.length_take, Nat.min_eq_left hb,
            show a - b = 0 from by omega, List.drop_zero]

/-- Log-segment length. Port-local. -/
theorem seg_length (S : CoordinateSpace K V C) {a b : Nat}
    (hb : b ≤ S.log.length) :
    ((S.log.take b).drop a).length = b - a := by
  rw [List.length_drop, List.length_take, Nat.min_eq_left hb]

theorem flatMap_congr {α : Type _} {β : Type _}
    {xs : List α} {g g' : α → List β}
    (h : ∀ x ∈ xs, g x = g' x) : xs.flatMap g = xs.flatMap g' := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.flatMap_cons,
        h x (List.mem_cons.mpr (Or.inl rfl)),
        ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- The empty tagged segment. Port-local. -/
theorem tagged_seg_self (S : CoordinateSpace K V C) (a : Nat) :
    tagged_seg S a a = [] := by
  have hlen : (((S.log.take a).drop a).zipIdx a).length = 0 := by
    rw [List.length_zipIdx, List.length_drop, List.length_take]
    omega
  simp only [tagged_seg]
  rw [List.eq_nil_of_length_eq_zero hlen]
  rfl

theorem titems_append (k : K) (L₁ L₂ : List (Nat × Event K V)) :
    titems_for k (L₁ ++ L₂) = titems_for k L₁ ++ titems_for k L₂ :=
  List.filter_append _ _

theorem titems_flatMap {α : Type _} (k : K) {g : α → List (Nat × Event K V)}
    {xs : List α} :
    titems_for k (xs.flatMap g) =
      xs.flatMap (fun x => titems_for k (g x)) :=
  List.filter_flatMap

theorem titems_cons (k : K) (x : Nat × Event K V)
    (L : List (Nat × Event K V)) :
    titems_for k (x :: L) = titems_for k [x] ++ titems_for k L := by
  simp only [titems_for, List.filter_cons, List.filter_nil]
  by_cases h : x.2.key = k
  · rw [if_pos (decide_eq_true h), if_pos (decide_eq_true h)]
    rfl
  · rw [if_neg (fun hc => h (of_decide_eq_true hc)),
        if_neg (fun hc => h (of_decide_eq_true hc))]
    rfl

/-- Flat-mapping single tagged items is the tagged projection.
Port-local. -/
theorem flatMap_titems_single (k : K) (L : List (Event K V × Nat)) :
    L.flatMap (fun ep => titems_for k [((ep.2 + 1, ep.1) : Nat × Event K V)]) =
      titems_for k (L.map (fun ep => (ep.2 + 1, ep.1))) := by
  induction L with
  | nil => rfl
  | cons ep L ih =>
    rw [List.flatMap_cons, List.map_cons, ih, ← titems_cons k _ _]

/-- Position bounds of a tagged-segment item. Port-local; the
Isabelle counterpart is `kposs_bounds`. -/
theorem mem_tagged_seg_bounds {S : CoordinateSpace K V C} {a b : Nat}
    {x : Nat × Event K V} (hx : x ∈ tagged_seg S a b) :
    a < x.1 ∧ x.1 ≤ b := by
  simp only [tagged_seg, List.mem_map] at hx
  obtain ⟨⟨e, p⟩, hep, hxe⟩ := hx
  obtain ⟨h1, h2, -⟩ := List.mem_zipIdx hep
  have hlen : ((S.log.take b).drop a).length ≤ b - a := by
    rw [List.length_drop, List.length_take]
    omega
  subst hxe
  simp only
  omega

/-- Tags strictly ascend along a tagged segment. Port-local; the
Isabelle counterpart is `kposs_sorted` with `sorted_map_Suc`. -/
theorem pairwise_tagged_seg (S : CoordinateSpace K V C) (a b : Nat) :
    List.Pairwise (fun x y => x.1 < y.1) (tagged_seg S a b) := by
  simp only [tagged_seg]
  rw [List.pairwise_map]
  exact (pairwise_zipIdx_lt _ a).imp (fun h => by
    simp only
    omega)

/-! ## Per-key characterization of the emission -/

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

omit H in
/-- A lawful survivor enumeration exists whenever each unit's
survivors admit a duplicate-free listing. Isabelle: `svl_exists`,
whose finiteness premise is HOL's `finite`; a listing premise is
the same statement in a set-library-free logic, as recorded in
VERIFICATION.md. -/
theorem svl_exists
    (hfin : ∀ u ∈ units, ∃ xs : List K, xs.Nodup ∧
      ∀ k, k ∈ xs ↔ survivors S u k) :
    ∃ svl : CUnit K V C → List K, svl_ok S units svl := by
  refine ⟨fun u => if h : ∃ xs : List K, xs.Nodup ∧
      (∀ k, k ∈ xs ↔ survivors S u k) then h.choose else [], ?_⟩
  intro u hu
  have hex := hfin u hu
  dsimp only
  rw [dif_pos hex]
  exact hex.choose_spec

omit H in
/-- The per-key content of one close block. Isabelle:
`titems_close_block`. -/
theorem titems_close_block {svl : CUnit K V C → List K}
    (hsvl : svl_ok S units svl) {u : CUnit K V C} (hu : u ∈ units) (k : K) :
    titems_for k (close_block S svl u) =
      if k ∈ svl u then [(S.den u.hi, ⟨k, u.refresh k⟩)] else [] := by
  have hnd : (svl u).Nodup := (hsvl u hu).1
  simp only [titems_for, close_block, List.filter_map]
  have hpred : ((fun x : Nat × Event K V => decide (x.2.key = k)) ∘
      fun k' => ((S.den u.hi, ⟨k', u.refresh k'⟩) : Nat × Event K V)) =
      fun k' => decide (k' = k) := by
    funext k'
    rfl
  rw [hpred, nodup_filter_eq hnd k]
  by_cases hk : k ∈ svl u
  · rw [if_pos hk, if_pos hk]
    rfl
  · rw [if_neg hk, if_neg hk]
    rfl

/-- The per-key content of the close blocks due at one position:
only the owning unit can contribute, and only at its own high
edge. Isabelle: `titems_closes_at`. -/
theorem titems_closes_at {svl : CUnit K V C → List K}
    (hsvl : svl_ok S units svl) {k : K} (hk : scope k) (p : Nat) :
    titems_for k (closes_at S units svl p) =
      if S.den (the_unit units f k).hi = p ∧ k ∈ svl (the_unit units f k)
      then [(p, ⟨k, (the_unit units f k).refresh k⟩)] else [] := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  obtain ⟨i₀, hi₀, hgi₀⟩ := List.mem_iff_getElem.mp u_in
  have hmem : ((the_unit units f k, i₀) : CUnit K V C × Nat) ∈
      units.zipIdx := by
    rw [List.mem_iff_getElem]
    refine ⟨i₀, by rw [List.length_zipIdx]; exact hi₀, ?_⟩
    rw [List.getElem_zipIdx, Nat.zero_add]
    exact congrArg (fun u => (u, i₀)) hgi₀
  have hvanish : ∀ ui ∈ units.zipIdx,
      ui ≠ (the_unit units f k, i₀) →
      titems_for k (if S.den ui.1.hi = p
        then close_block S svl ui.1 else []) = [] := by
    rintro ⟨u, i⟩ hui hne
    obtain ⟨-, hilen, hgot⟩ := List.mem_zipIdx hui
    by_cases hc : S.den u.hi = p
    · rw [if_pos hc]
      have hu_in : u ∈ units := by
        rw [hgot]
        exact List.getElem_mem _
      rw [titems_close_block hsvl hu_in k]
      by_cases hks : k ∈ svl u
      · exfalso
        have hsurv : survivors S u k := ((hsvl u hu_in).2 k).mp hks
        have hueq : u = the_unit units f k :=
          H.covering_unit_unique hu_in hsurv.1 u_in k_dom
        have hieq : i = i₀ := by
          have hgot' : units[i]'(by omega) = u := by
            have hg := hgot
            simp only [Nat.sub_zero] at hg
            exact hg.symm
          exact H.the_unit_position_unique hk
            (i := i) (j := i₀) (by omega) (hgot'.trans hueq) hi₀ hgi₀
        exact hne (by rw [hueq, hieq])
      · rw [if_neg hks]
    · rw [if_neg hc]
      rfl
  have hflat : titems_for k (closes_at S units svl p) =
      titems_for k (if S.den (the_unit units f k).hi = p
        then close_block S svl (the_unit units f k) else []) := by
    simp only [closes_at, titems_for, List.filter_flatMap]
    rw [flatMap_single (nodup_zipIdx units 0) hmem]
    intro x hx hne
    exact hvanish x hx hne
  rw [hflat]
  by_cases hc : S.den (the_unit units f k).hi = p
  · rw [if_pos hc, titems_close_block hsvl u_in k]
    by_cases hks : k ∈ svl (the_unit units f k)
    · rw [if_pos hks, if_pos ⟨hc, hks⟩, hc]
    · rw [if_neg hks, if_neg (fun h => hks h.2)]
  · rw [if_neg hc, if_neg (fun h => hc h.1)]
    rfl

/-- The master per-key characterization of the tagged emission
(paper Lemma 6.1, the per-key shape of the discard emission): a
key's occurrences are its consumed events before its unit's high
edge, in commit order; then, exactly if the key is enumerated as a
survivor, one refresh entry tagged with the close position; then
its events beyond the high edge, in commit order. Isabelle:
`titems_emission_master`, whose position-list normal form
`map (λp. (Suc p, L ! p)) (kposs k a b)` is here the per-key
filter of the tagged segment. -/
theorem titems_emission_master {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k) :
    titems_for k (emission_t S units f svl s0) =
      titems_for k (tagged_seg S (S.den s0) (S.den (the_unit units f k).hi))
      ++ (if k ∈ svl (the_unit units f k)
          then [(S.den (the_unit units f k).hi,
                 ⟨k, (the_unit units f k).refresh k⟩)] else [])
      ++ titems_for k
          (tagged_seg S (S.den (the_unit units f k).hi) (S.den f)) := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  have hs0lo : S.den s0 ≤ S.den (the_unit units f k).lo := hs0 _ u_in
  have hlohi : S.den (the_unit units f k).lo ≤
      S.den (the_unit units f k).hi := H.bracket_lo_hi _ u_in
  have hhif : S.den (the_unit units f k).hi ≤ S.den f :=
    H.bracket_hi_f _ u_in
  have hflen : S.den f ≤ S.log.length := S.den_le_len f
  have hs0hp : S.den s0 ≤ S.den (the_unit units f k).hi :=
    Nat.le_trans hs0lo hlohi
  have hhplen : S.den (the_unit units f k).hi ≤ S.log.length :=
    Nat.le_trans hhif hflen
  have hsplit := seg_split S hs0hp hhif hflen
  have hlenA : ((S.log.take (S.den (the_unit units f k).hi)).drop
      (S.den s0)).length = S.den (the_unit units f k).hi - S.den s0 :=
    seg_length S hhplen
  have hAvanish : ∀ ep ∈ ((S.log.take (S.den (the_unit units f k).hi)).drop
      (S.den s0)).zipIdx (S.den s0),
      titems_for k (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]) =
        titems_for k [(ep.2 + 1, ep.1)] := by
    rintro ⟨e, p⟩ hep
    obtain ⟨h1, h2, -⟩ := List.mem_zipIdx hep
    rw [hlenA] at h2
    have hne : S.den (the_unit units f k).hi ≠ p := by omega
    rw [titems_append, titems_closes_at H hsvl hk p,
        if_neg (fun h => hne h.1), List.nil_append]
  have hBvanish : ∀ (B₀ : List (Event K V)),
      ∀ ep ∈ B₀.zipIdx (S.den (the_unit units f k).hi + 1),
      titems_for k (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]) =
        titems_for k [(ep.2 + 1, ep.1)] := by
    intro B₀
    rintro ⟨e, p⟩ hep
    obtain ⟨h1, -, -⟩ := List.mem_zipIdx hep
    have hne : S.den (the_unit units f k).hi ≠ p := by omega
    rw [titems_append, titems_closes_at H hsvl hk p,
        if_neg (fun h => hne h.1), List.nil_append]
  have hAeq : ((((S.log.take (S.den (the_unit units f k).hi)).drop
        (S.den s0)).zipIdx (S.den s0)).flatMap
        (fun ep => titems_for k
          (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]))) =
      titems_for k
        (tagged_seg S (S.den s0) (S.den (the_unit units f k).hi)) := by
    rw [flatMap_congr hAvanish, flatMap_titems_single]
    rfl
  have hkey : titems_for k (emission_t S units f svl s0) =
      (((S.log.take (S.den (the_unit units f k).hi)).drop
        (S.den s0)).zipIdx (S.den s0)).flatMap
        (fun ep => titems_for k
          (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]))
      ++ (((S.log.take (S.den f)).drop
        (S.den (the_unit units f k).hi)).zipIdx
          (S.den (the_unit units f k).hi)).flatMap
        (fun ep => titems_for k
          (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]))
      ++ titems_for k (closes_at S units svl (S.den f)) := by
    simp only [emission_t]
    rw [hsplit, List.zipIdx_append, hlenA,
        show S.den s0 + (S.den (the_unit units f k).hi - S.den s0) =
          S.den (the_unit units f k).hi from by omega,
        List.flatMap_append, titems_append, titems_append,
        titems_flatMap (k := k), titems_flatMap (k := k)]
  rw [hkey, hAeq]
  rcases Nat.lt_or_ge (S.den (the_unit units f k).hi) (S.den f) with hlt | hge
  · -- Strictly inside: the B-part opens exactly at the high edge.
    have hBne : (S.log.take (S.den f)).drop
        (S.den (the_unit units f k).hi) ≠ [] := by
      refine List.ne_nil_of_length_pos ?_
      rw [seg_length S hflen]
      omega
    obtain ⟨e₀, B', hB⟩ := List.exists_cons_of_ne_nil hBne
    have hBeq : ((((S.log.take (S.den f)).drop
          (S.den (the_unit units f k).hi)).zipIdx
          (S.den (the_unit units f k).hi)).flatMap
          (fun ep => titems_for k
            (closes_at S units svl ep.2 ++ [(ep.2 + 1, ep.1)]))) =
        (if k ∈ svl (the_unit units f k)
          then [(S.den (the_unit units f k).hi,
                 ⟨k, (the_unit units f k).refresh k⟩)] else [])
        ++ titems_for k
            (tagged_seg S (S.den (the_unit units f k).hi) (S.den f)) := by
      have htag : titems_for k
          (tagged_seg S (S.den (the_unit units f k).hi) (S.den f)) =
          titems_for k [((S.den (the_unit units f k).hi + 1, e₀) :
            Nat × Event K V)] ++
          titems_for k ((B'.zipIdx (S.den (the_unit units f k).hi + 1)).map
            (fun ep => (ep.2 + 1, ep.1))) := by
        show titems_for k ((((S.log.take (S.den f)).drop
            (S.den (the_unit units f k).hi)).zipIdx
              (S.den (the_unit units f k).hi)).map
            (fun ep => (ep.2 + 1, ep.1))) = _
        rw [hB, List.zipIdx_cons, List.map_cons]
        exact titems_cons k _ _
      rw [hB, List.zipIdx_cons, List.flatMap_cons, titems_append,
          titems_closes_at H hsvl hk (S.den (the_unit units f k).hi),
          flatMap_congr (hBvanish B'), flatMap_titems_single, htag]
      by_cases hks : k ∈ svl (the_unit units f k)
      · rw [if_pos (⟨rfl, hks⟩ :
            S.den (the_unit units f k).hi = S.den (the_unit units f k).hi ∧
              k ∈ svl (the_unit units f k)), if_pos hks,
            List.append_assoc]
      · rw [if_neg (fun h => hks h.2), if_neg hks, List.nil_append,
            List.nil_append]
    rw [hBeq, titems_closes_at H hsvl hk (S.den f),
        if_neg (fun h => by omega : ¬(S.den (the_unit units f k).hi =
          S.den f ∧ k ∈ svl (the_unit units f k))),
        List.append_nil, List.append_assoc]
  · -- At the frontier: the B-part is empty and the unit closes after
    -- the last consumed event.
    have hpf : S.den (the_unit units f k).hi = S.den f := by omega
    have hBnil : (S.log.take (S.den f)).drop
        (S.den (the_unit units f k).hi) = [] := by
      refine List.eq_nil_of_length_eq_zero ?_
      rw [seg_length S hflen]
      omega
    have hTagNil : titems_for k
        (tagged_seg S (S.den (the_unit units f k).hi) (S.den f)) = [] := by
      rw [hpf, tagged_seg_self]
      rfl
    rw [hBnil, hTagNil, titems_closes_at H hsvl hk (S.den f)]
    by_cases hks : k ∈ svl (the_unit units f k)
    · rw [if_pos (⟨hpf, hks⟩ :
          S.den (the_unit units f k).hi = S.den f ∧
            k ∈ svl (the_unit units f k)), if_pos hks, hpf]
      simp
    · rw [if_neg (fun h => hks h.2), if_neg hks]
      simp

/-- The plain-stream reading of the master characterization.
Port-local step; the Isabelle proof performs it inline. -/
theorem evs_emission_master {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k) :
    evs_for k (emission S units f svl s0) =
      evs_for k (S.win s0 (the_unit units f k).hi)
      ++ (if k ∈ svl (the_unit units f k)
          then [⟨k, (the_unit units f k).refresh k⟩] else [])
      ++ evs_for k (S.win (the_unit units f k).hi f) := by
  have h1 : (titems_for k (tagged_seg S (S.den s0)
      (S.den (the_unit units f k).hi))).map Prod.snd =
      evs_for k (S.win s0 (the_unit units f k).hi) := by
    rw [← evs_for_map_snd, map_snd_tagged_seg]
    rfl
  have h2 : (titems_for k (tagged_seg S (S.den (the_unit units f k).hi)
      (S.den f))).map Prod.snd =
      evs_for k (S.win (the_unit units f k).hi f) := by
    rw [← evs_for_map_snd, map_snd_tagged_seg]
    rfl
  rw [emission, evs_for_map_snd, titems_emission_master H hsvl hs0 hk,
      List.map_append, List.map_append, h1, h2]
  by_cases hks : k ∈ svl (the_unit units f k)
  · rw [if_pos hks, if_pos hks]
    rfl
  · rw [if_neg hks, if_neg hks]
    rfl

/-- The window-discard equivalence theorem (paper Theorem 2): the
emitted stream replays to the canonical sink on every scoped key.
Together with the cut theorem this is "the log wins" as a theorem:
buffer the unit's refresh, discard on any in-window event for a
buffered key, emit survivors at the high edge, and the replay is
exactly the source state at the frontier. Isabelle:
`window_discard_replay`. -/
theorem window_discard_replay {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k) :
    stream_replay (emission S units f svl s0) k = sink_at S units f f k := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  have hs0lo : S.cle s0 (the_unit units f k).lo := hs0 _ u_in
  have hlohi : S.cle (the_unit units f k).lo (the_unit units f k).hi :=
    H.bracket_lo_hi _ u_in
  have hhif : S.cle (the_unit units f k).hi f := H.bracket_hi_f _ u_in
  have hlof : S.cle (the_unit units f k).lo f := S.cle_trans hlohi hhif
  have hs0hi : S.cle s0 (the_unit units f k).hi := S.cle_trans hs0lo hlohi
  have estream := evs_emission_master H hsvl hs0 hk
  have hsurv := (hsvl _ u_in).2 k
  -- The two window decompositions every case reads off.
  have hA : evs_for k (S.win s0 (the_unit units f k).hi) =
      evs_for k (S.win s0 (the_unit units f k).lo)
      ++ evs_for k (S.win (the_unit units f k).lo (the_unit units f k).hi) :=
    S.evs_for_win_split hs0lo hlohi k
  have hWin : evs_for k (S.win (the_unit units f k).lo f) =
      evs_for k (S.win (the_unit units f k).lo (the_unit units f k).hi)
      ++ evs_for k (S.win (the_unit units f k).hi f) :=
    S.evs_for_win_split hlohi hhif k
  simp only [stream_replay, sink_at]
  by_cases hW2 : evs_for k (S.win (the_unit units f k).hi f) = []
  · by_cases hM : evs_for k
        (S.win (the_unit units f k).lo (the_unit units f k).hi) = []
    · -- Quiet window: the sink returns the refresh verdict.
      have hwin_nil : evs_for k (S.win (the_unit units f k).lo f) = [] := by
        rw [hWin, hM, hW2]
        rfl
      rw [dif_pos hwin_nil]
      by_cases hr : (the_unit units f k).refresh k = none
      · -- Absent verdict: no survivor; the stream ends, if anywhere,
        -- on the key's own delete.
        have hks : k ∉ svl (the_unit units f k) := fun hks =>
          (hsurv.mp hks).2.1 hr
        have hstream : evs_for k (emission S units f svl s0) =
            evs_for k (S.win s0 (the_unit units f k).lo) := by
          rw [estream, if_neg hks, hA, hM, hW2]
          simp
        by_cases hP : evs_for k (S.win s0 (the_unit units f k).lo) = []
        · rw [state_after_no_events (hstream.trans hP), hr]
        · obtain ⟨c, c_lo, c_hi, honest⟩ := H.O2_honest _ u_in k k_dom
          have hs0c : S.cle s0 c := S.cle_trans hs0lo c_lo
          have hMc : evs_for k (S.win (the_unit units f k).lo c) = [] := by
            have hsp := S.evs_for_win_split c_lo c_hi k
            rw [hM] at hsp
            exact (List.append_eq_nil_iff.mp hsp.symm).1
          have hpfx : evs_for k (S.pfx c) =
              evs_for k (S.pfx s0)
              ++ evs_for k (S.win s0 (the_unit units f k).lo) := by
            rw [S.evs_for_pfx_split hs0c k,
                S.evs_for_win_split hs0lo c_lo k, hMc, List.append_nil]
          have hpfx_ne : evs_for k (S.pfx c) ≠ [] := by
            rw [hpfx]
            intro h
            exact hP (List.append_eq_nil_iff.mp h).2
          have himg : ((evs_for k (S.win s0
              (the_unit units f k).lo)).getLast hP).img = none := by
            have hnone : state_after σ0 (S.pfx c) k = none :=
              honest.symm.trans hr
            rw [state_after_last_event hpfx_ne σ0,
                getLast_eq_of_eq hpfx,
                List.getLast_append_of_ne_nil _ hP] at hnone
            exact hnone
          have hne_em : evs_for k (emission S units f svl s0) ≠ [] := by
            rw [hstream]
            exact hP
          rw [state_after_last_event hne_em, hr,
              getLast_eq_of_eq hstream]
          exact himg
      · -- Present verdict: the key survives and its refresh entry is
        -- the last stream entry.
        have hks : k ∈ svl (the_unit units f k) :=
          hsurv.mpr ⟨k_dom, hr, hM⟩
        have hstream : evs_for k (emission S units f svl s0) =
            evs_for k (S.win s0 (the_unit units f k).hi)
            ++ [⟨k, (the_unit units f k).refresh k⟩] := by
          rw [estream, if_pos hks, hW2]
          simp
        have hne_em : evs_for k (emission S units f svl s0) ≠ [] := by
          rw [hstream]
          simp
        rw [state_after_last_event hne_em, getLast_eq_of_eq hstream,
            List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _),
            List.getLast_singleton]
    · -- An in-window event and nothing beyond: the last mid-window
      -- event decides both sides.
      have hks : k ∉ svl (the_unit units f k) := fun hks =>
        hM (hsurv.mp hks).2.2
      have hwin : evs_for k (S.win (the_unit units f k).lo f) =
          evs_for k (S.win (the_unit units f k).lo
            (the_unit units f k).hi) := by
        rw [hWin, hW2, List.append_nil]
      have hwin_ne : evs_for k (S.win (the_unit units f k).lo f) ≠ [] := by
        rw [hwin]
        exact hM
      rw [dif_neg hwin_ne]
      have hstream : evs_for k (emission S units f svl s0) =
          evs_for k (S.win s0 (the_unit units f k).lo)
          ++ evs_for k (S.win (the_unit units f k).lo
            (the_unit units f k).hi) := by
        rw [estream, if_neg hks, hW2, hA]
        simp
      have hne_em : evs_for k (emission S units f svl s0) ≠ [] := by
        rw [hstream]
        intro h
        exact hM (List.append_eq_nil_iff.mp h).2
      rw [state_after_last_event hne_em, getLast_eq_of_eq hstream,
          List.getLast_append_of_ne_nil _ hM, getLast_eq_of_eq hwin]
  · -- An event beyond the high edge: the last such event decides
    -- both sides, and the refresh is never consulted.
    have hwin_ne : evs_for k (S.win (the_unit units f k).lo f) ≠ [] := by
      rw [hWin]
      intro h
      exact hW2 (List.append_eq_nil_iff.mp h).2
    rw [dif_neg hwin_ne]
    have hne_em : evs_for k (emission S units f svl s0) ≠ [] := by
      rw [estream]
      intro h
      exact hW2 (List.append_eq_nil_iff.mp h).2
    rw [state_after_last_event hne_em, getLast_eq_of_eq estream,
        List.getLast_append_of_ne_nil _ hW2, getLast_eq_of_eq hWin,
        List.getLast_append_of_ne_nil _ hW2]

/-- Window-discard per-key monotonicity (paper Theorem 3): along
the emitted stream, each key's occurrence tags never decrease, so
no entry replays a key to an older state after a newer one. The
pre-close events carry tags at most the close position and appear
in commit order; the surviving refresh entry carries exactly the
close position; the post-close events follow with larger tags.
Isabelle: `window_discard_monotone`, whose `sorted` is
`List.Pairwise (· ≤ ·)` here. -/
theorem window_discard_monotone {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k) :
    List.Pairwise (· ≤ ·)
      ((titems_for k (emission_t S units f svl s0)).map Prod.fst) := by
  have pwT : ∀ a b : Nat, List.Pairwise (α := Nat) (· ≤ ·)
      ((titems_for k (tagged_seg S a b)).map Prod.fst) := by
    intro a b
    rw [List.pairwise_map]
    exact ((pairwise_tagged_seg S a b).filter _).imp
      (fun h => Nat.le_of_lt h)
  have boundsA : ∀ t ∈ (titems_for k (tagged_seg S (S.den s0)
      (S.den (the_unit units f k).hi))).map Prod.fst,
      t ≤ S.den (the_unit units f k).hi := by
    intro t ht
    obtain ⟨x, hx, hxt⟩ := List.mem_map.mp ht
    have hxb := mem_tagged_seg_bounds (List.mem_filter.mp hx).1
    omega
  have boundsB : ∀ t ∈ (titems_for k (tagged_seg S
      (S.den (the_unit units f k).hi) (S.den f))).map Prod.fst,
      S.den (the_unit units f k).hi < t := by
    intro t ht
    obtain ⟨x, hx, hxt⟩ := List.mem_map.mp ht
    have hxb := mem_tagged_seg_bounds (List.mem_filter.mp hx).1
    omega
  rw [titems_emission_master H hsvl hs0 hk]
  by_cases hks : k ∈ svl (the_unit units f k)
  · rw [if_pos hks, List.map_append, List.map_append,
        List.pairwise_append]
    refine ⟨?_, pwT _ _, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨pwT _ _, by simp, ?_⟩
      intro a ha b hb
      have hb' : b = S.den (the_unit units f k).hi := by
        simpa using hb
      rw [hb']
      exact boundsA a ha
    · intro a ha b hb
      have hbB := boundsB b hb
      rcases List.mem_append.mp ha with h | h
      · have := boundsA a h
        omega
      · have ha' : a = S.den (the_unit units f k).hi := by
          simpa using h
        omega
  · rw [if_neg hks, List.map_append, List.map_append,
        List.pairwise_append]
    refine ⟨?_, pwT _ _, ?_⟩
    · rw [show (([] : List (Nat × Event K V)).map Prod.fst) =
          ([] : List Nat) from rfl, List.append_nil]
      exact pwT _ _
    · intro a ha b hb
      have hbB := boundsB b hb
      have haA : a ∈ (titems_for k (tagged_seg S (S.den s0)
          (S.den (the_unit units f k).hi))).map Prod.fst := by
        simpa using ha
      have := boundsA a haA
      omega

end CaptureContract

end

end DBLogContract
