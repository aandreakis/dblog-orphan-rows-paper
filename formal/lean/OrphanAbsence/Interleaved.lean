import OrphanAbsence.Composition

/-!
# A pass and a request served inside it, over one log

This file ports the general part of `Orphan_Absence_Interleaved.thy`
from the Isabelle session `Orphan_Absence`. The fixtures of that theory
are ported in `InterleavedWitnesses.lean`.

A full pass `P` emits the window-discard stream with enumerated
absences from its consumption start `s0` to its frontier `f1`. A
bracketed read `R`, a repair request, is served while `P` is still
running: every unit of `R` lies inside the span of `P`. The sink
receives one stream. It is the pass's timed emission with the close
blocks of `R` inserted at their own log positions, each log event once.

* Position-tagged lists: `insert_at`, `blocks_sorted`,
  `concat_blocks_insert` and the lemmas around them.
* Source values at log positions: `take_state_quiet`, `event_honest`
  and the key step `honest_stream_last`.
* Close entries: `closes_at_item`, `closes_at_tag`,
  `emission_t_sorted`, `listed_entry_honest`, `unlisted_quiet_absent`,
  `contract_with_frontier`.
* `PassWithRequest`, `inter_t`, `inter`: the pass and the request over
  one log, and the stream the sink applies. `titems_inter`
  characterizes one key's items.
* `pass_with_request_safe`, `pass_with_request_converges`,
  `pass_with_listing_request_converges`, `request_in_pass_converges`:
  safety and convergence.
* `inter_t_rev`, `inter_rev` and the `_rev` and `_any` theorems: the
  same results for the reverse tie order and for any stream in
  position order that carries the same items.

Transport, as in `VERIFICATION.md`. The Isabelle stream is built over
the position range `[den s0..<den f1]` with the junk-total `L ! p`. The
port builds it with `zipIdx` over the consumed log segment, as the
core's `emission_t`, so the two lists are the same entry for entry. A
position range without log access, `[a..<b]`, is `List.range' a (b - a)`.
A free log indexed at a position is read with bounded `getElem`. The
multiset equality `mset xs = mset ys + mset zs` is the permutation
`xs.Perm (ys ++ zs)`. The locale `pass_with_request` is the
`Prop`-valued structure `PassWithRequest`.
-/

namespace DBLogContract

universe u v w

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-! ## Position-tagged lists -/

/-- A list whose entries all equal one value is sorted. Isabelle:
`sorted_const_list`, for a linear order, with `sorted` as
`List.Pairwise (· ≤ ·)`. -/
theorem sorted_const_list {α : Type _} [LE α] [Std.IsLinearOrder α]
    {xs : List α} {c : α} (h : ∀ t, t ∈ xs → t = c) :
    List.Pairwise (· ≤ ·) xs := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    refine List.pairwise_cons.mpr ⟨?_, ih (fun t ht => h t (List.mem_cons_of_mem _ ht))⟩
    intro y hy
    rw [h x List.mem_cons_self, h y (List.mem_cons_of_mem _ hy)]
    exact Std.IsPreorder.le_refl c

/-- Filtering a list keeps its tags in order. Isabelle:
`sorted_map_fst_filter`. The HOL predicate `Q` is a `Bool`-valued
function, as HOL's `bool` is a two-valued type. -/
theorem sorted_map_fst_filter {α : Type _} {β : Type _} [LE α] [Std.IsLinearOrder α]
    {S : List (α × β)} {Q : α × β → Bool}
    (h : List.Pairwise (· ≤ ·) (S.map Prod.fst)) :
    List.Pairwise (· ≤ ·) ((S.filter Q).map Prod.fst) :=
  List.pairwise_map.mpr ((List.pairwise_map.mp h).filter Q)

/-- Every entry of a sorted list is at most its last entry. Isabelle:
`sorted_le_last`, whose `last xs` is `xs.getLast` with the
nonemptiness proof that membership gives. -/
theorem sorted_le_last {α : Type _} [LE α] [Std.IsLinearOrder α]
    {xs : List α} {x : α} (hs : List.Pairwise (· ≤ ·) xs) (hx : x ∈ xs) :
    x ≤ xs.getLast (List.ne_nil_of_mem hx) := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    obtain ⟨y_le, s_ys⟩ := List.pairwise_cons.mp hs
    by_cases hne : ys = []
    · subst hne
      have hxy : x = y := List.mem_singleton.mp hx
      subst hxy
      exact Std.IsPreorder.le_refl x
    · rw [List.getLast_cons hne]
      by_cases hxy : x = y
      · subst hxy
        exact y_le _ (List.getLast_mem hne)
      · have hx' : x ∈ ys := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h hxy
          · exact h
        exact ih s_ys hx'

/-- The block form of `blocks_sorted` over any list `xs` whose
positions, read by `pos`, are the range from `a` to `b`. The Isabelle
range `[a..<b]` is the instance `xs = List.range' a (b - a)`, and the
consumed log segment traversed by `zipIdx` is another. The extra
conjunct is the lower bound that carries the induction. Port-local. -/
theorem blocks_sorted_gen {α : Type _} {β : Type _} (C : Nat → List (Nat × α))
    (pos : β → Nat) (z : β → α) {a b : Nat} {xs : List β}
    (hC : ∀ p x, x ∈ C p → x.1 = p)
    (hpos : xs.map pos = List.range' a (b - a)) :
    List.Pairwise (· ≤ ·)
        ((xs.flatMap (fun q => C (pos q) ++ [(pos q + 1, z q)]) ++ C b).map Prod.fst) ∧
      (∀ x ∈ xs.flatMap (fun q => C (pos q) ++ [(pos q + 1, z q)]) ++ C b, x.1 ≤ b) ∧
      (a ≤ b → ∀ x ∈ xs.flatMap (fun q => C (pos q) ++ [(pos q + 1, z q)]) ++ C b,
        a ≤ x.1) := by
  have hCb : List.Pairwise (· ≤ ·) ((C b).map Prod.fst) := by
    refine sorted_const_list (c := b) ?_
    intro t ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    exact hC b x hx
  induction xs generalizing a with
  | nil =>
    refine ⟨by simpa using hCb, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ C b := by simpa using hx
      exact Nat.le_of_eq (hC b x hx')
    · intro _ x hx
      have hx' : x ∈ C b := by simpa using hx
      rw [hC b x hx']
      assumption
  | cons q xs ih =>
    have hlen : b - a ≠ 0 := by
      intro h0
      rw [h0] at hpos
      simp at hpos
    have hrange : List.range' a (b - a) = a :: List.range' (a + 1) (b - (a + 1)) := by
      rw [show b - a = (b - (a + 1)) + 1 from by omega, List.range'_succ]
    rw [List.map_cons, hrange] at hpos
    obtain ⟨hq, hxs⟩ := List.cons.inj hpos
    obtain ⟨ihs, ihb, ihl⟩ := ih hxs
    have hab : a + 1 ≤ b := by omega
    have ihl' := ihl hab
    rw [List.flatMap_cons, List.append_assoc]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_append, List.pairwise_append]
      refine ⟨?_, ihs, ?_⟩
      · rw [List.map_append, List.pairwise_append]
        refine ⟨?_, by simp, ?_⟩
        · refine sorted_const_list (c := a) ?_
          intro t ht
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
          rw [← hq]
          exact hC (pos q) x hx
        · intro t ht t' ht'
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
          have ht'' : t' = pos q + 1 := by simpa using ht'
          rw [hC (pos q) x hx, ht'']
          exact Nat.le_succ _
      · intro t ht t' ht'
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht'
        have hy' := ihl' y hy
        rcases List.mem_append.mp hx with hx | hx
        · rw [hC (pos q) x hx, hq]
          omega
        · have hx' : x = (pos q + 1, z q) := by simpa using hx
          rw [hx', hq]
          exact hy'
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · rw [hC (pos q) x hx, hq]
          omega
        · have hx' : x = (pos q + 1, z q) := by simpa using hx
          rw [hx', hq]
          exact hab
      · exact ihb x hx
    · intro _ x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · rw [hC (pos q) x hx, hq]
          exact Nat.le_refl a
        · have hx' : x = (pos q + 1, z q) := by simpa using hx
          rw [hx', hq]
          exact Nat.le_succ a
      · exact Nat.le_trans (Nat.le_succ a) (ihl' x hx)

/-- A list built from blocks, each holding close entries tagged with
its position `p` and then one item tagged `p + 1`, followed by the
close entries tagged `b`, is in tag order, and its tags are at most
`b`. Isabelle: `blocks_sorted`, whose range `[a..<b]` is
`List.range' a (b - a)`. -/
theorem blocks_sorted {α : Type _} (C : Nat → List (Nat × α)) (z : Nat → α)
    (a b : Nat) (hC : ∀ p x, x ∈ C p → x.1 = p) :
    List.Pairwise (· ≤ ·)
        (((List.range' a (b - a)).flatMap (fun p => C p ++ [(p + 1, z p)]) ++ C b).map
          Prod.fst) ∧
      (∀ x ∈ (List.range' a (b - a)).flatMap (fun p => C p ++ [(p + 1, z p)]) ++ C b,
        x.1 ≤ b) := by
  have h := blocks_sorted_gen C (fun p => p) z (a := a) (b := b)
    (xs := List.range' a (b - a)) hC (List.map_id' _)
  exact ⟨h.1, h.2.1⟩

/-- `insert_at h ys S` places `ys` after every item of `S` tagged at
most `h` and before every item tagged later. Isabelle: `insert_at`. -/
def insert_at {α : Type _} (h : Nat) (ys S : List (Nat × α)) : List (Nat × α) :=
  S.filter (fun x => decide (x.1 ≤ h)) ++ (ys ++ S.filter (fun x => decide (h < x.1)))

/-- Inserting at `h` into a list split at `h`. Isabelle:
`insert_at_split`. -/
theorem insert_at_split {α : Type _} {h : Nat} {U V ys : List (Nat × α)}
    (hU : ∀ x ∈ U, x.1 ≤ h) (hV : ∀ x ∈ V, h < x.1) :
    insert_at h ys (U ++ V) = U ++ (ys ++ V) := by
  have U1 : U.filter (fun x => decide (x.1 ≤ h)) = U :=
    List.filter_eq_self.mpr (fun x hx => decide_eq_true (hU x hx))
  have U2 : U.filter (fun x => decide (h < x.1)) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by
      have := hU x hx
      simp only [decide_eq_true_eq]
      omega)
  have V1 : V.filter (fun x => decide (x.1 ≤ h)) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by
      have := hV x hx
      simp only [decide_eq_true_eq]
      omega)
  have V2 : V.filter (fun x => decide (h < x.1)) = V :=
    List.filter_eq_self.mpr (fun x hx => decide_eq_true (hV x hx))
  simp only [insert_at, List.filter_append, U1, U2, V1, V2, List.append_nil,
    List.nil_append]

/-- On a list in tag order, `insert_at h` inserts right after the
items tagged at most `h`. Isabelle: `insert_at_sorted`. -/
theorem insert_at_sorted {α : Type _} {S : List (Nat × α)}
    (hS : List.Pairwise (· ≤ ·) (S.map Prod.fst)) (h : Nat) (ys : List (Nat × α)) :
    insert_at h ys S =
      S.takeWhile (fun x => decide (x.1 ≤ h)) ++
        (ys ++ S.dropWhile (fun x => decide (x.1 ≤ h))) := by
  induction S with
  | nil => simp [insert_at]
  | cons x S ih =>
    rw [List.map_cons, List.pairwise_cons] at hS
    obtain ⟨x_le, sS⟩ := hS
    by_cases hx : x.1 ≤ h
    · have ih' := ih sS
      simp only [insert_at] at ih' ⊢
      rw [List.filter_cons_of_pos (by simpa using hx),
        List.filter_cons_of_neg (by simpa using hx),
        List.takeWhile_cons_of_pos (by simpa using hx),
        List.dropWhile_cons_of_pos (by simpa using hx), List.cons_append, ih',
        List.cons_append]
    · have all_later : ∀ y ∈ x :: S, h < y.1 := by
        intro y hy
        rcases List.mem_cons.mp hy with hy | hy
        · rw [hy]
          omega
        · have := x_le y.1 (List.mem_map_of_mem hy)
          omega
      have e1 : insert_at h ys (x :: S) = ys ++ x :: S := by
        have := insert_at_split (h := h) (ys := ys) (U := []) (V := x :: S)
          (fun _ hy => by cases hy) all_later
        simpa using this
      rw [e1, List.takeWhile_cons_of_neg (by simpa using hx),
        List.dropWhile_cons_of_neg (by simpa using hx), List.nil_append]

/-- Inserting nothing gives the list back. Isabelle: `insert_at_Nil`. -/
theorem insert_at_Nil {α : Type _} {S : List (Nat × α)}
    (hS : List.Pairwise (· ≤ ·) (S.map Prod.fst)) (h : Nat) :
    insert_at h [] S = S := by
  rw [insert_at_sorted hS h [], List.nil_append, List.takeWhile_append_dropWhile]

/-- A prefix tagged at most `h` stays in front of the insertion.
Port-local. -/
theorem insert_at_append_le {α : Type _} {h : Nat} {U T ys : List (Nat × α)}
    (hU : ∀ x ∈ U, x.1 ≤ h) :
    insert_at h ys (U ++ T) = U ++ insert_at h ys T := by
  have U1 : U.filter (fun x => decide (x.1 ≤ h)) = U :=
    List.filter_eq_self.mpr (fun x hx => decide_eq_true (hU x hx))
  have U2 : U.filter (fun x => decide (h < x.1)) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by
      have := hU x hx
      simp only [decide_eq_true_eq]
      omega)
  simp only [insert_at, List.filter_append, U1, U2, List.nil_append, List.append_assoc]

/-- The merge lemma over any list `xs` whose positions, read by `pos`,
are the range from `a` to `b`. The Isabelle range `[a..<b]` is the
instance `xs = List.range' a (b - a)`, and the consumed log segment
traversed by `zipIdx` is another. Port-local. -/
theorem concat_blocks_insert_gen {α : Type _} {β : Type _} (pos : β → Nat)
    {A B : Nat → List (Nat × α)} {E : β → List (Nat × α)}
    {h a b : Nat} {ys : List (Nat × α)} {xs : List β}
    (A_tag : ∀ p x, x ∈ A p → x.1 = p)
    (E_tag : ∀ q x, x ∈ E q → x.1 = pos q + 1)
    (B_at : ∀ p, B p = if p = h then ys else [])
    (ah : a ≤ h) (hb : h ≤ b) (hpos : xs.map pos = List.range' a (b - a)) :
    xs.flatMap (fun q => A (pos q) ++ (B (pos q) ++ E q)) ++ (A b ++ B b) =
      insert_at h ys (xs.flatMap (fun q => A (pos q) ++ E q) ++ A b) := by
  induction xs generalizing a with
  | nil =>
    have hba : b - a = 0 := by
      cases hn : b - a with
      | zero => rfl
      | succ n =>
        rw [hn, List.range'_succ] at hpos
        simp at hpos
    have hbh : b = h := by omega
    subst hbh
    have Bb : B b = ys := by rw [B_at, if_pos rfl]
    have hU : ∀ x ∈ A b, x.1 ≤ b := fun x hx => Nat.le_of_eq (A_tag b x hx)
    have := insert_at_split (ys := ys) (V := []) hU (fun _ hx => by cases hx)
    simp only [List.flatMap_nil, List.nil_append, List.append_nil] at this ⊢
    rw [this, Bb]
  | cons q xs ih =>
    have hlen : b - a ≠ 0 := by
      intro h0
      rw [h0] at hpos
      simp at hpos
    have hrange : List.range' a (b - a) = a :: List.range' (a + 1) (b - (a + 1)) := by
      rw [show b - a = (b - (a + 1)) + 1 from by omega, List.range'_succ]
    rw [List.map_cons, hrange] at hpos
    obtain ⟨hq, hxs⟩ := List.cons.inj hpos
    have pos_gt : ∀ q' ∈ xs, a + 1 ≤ pos q' := by
      intro q' hq'
      have hm : pos q' ∈ xs.map pos := List.mem_map_of_mem hq'
      rw [hxs, List.mem_range'_1] at hm
      exact hm.1
    rw [List.flatMap_cons, List.flatMap_cons]
    by_cases hah : a = h
    · subst hah
      have Ba : B (pos q) = ys := by rw [B_at, hq, if_pos rfl]
      have Bb : B b = [] := by
        rw [B_at, if_neg (by omega)]
      have Brest : xs.flatMap (fun q => A (pos q) ++ (B (pos q) ++ E q)) =
          xs.flatMap (fun q => A (pos q) ++ E q) := by
        refine flatMap_congr (fun q' hq' => ?_)
        rw [B_at, if_neg (by have := pos_gt q' hq'; omega), List.nil_append]
      have hU : ∀ x ∈ A (pos q), x.1 ≤ a := fun x hx => by
        rw [A_tag _ x hx, hq]
        exact Nat.le_refl a
      have hV : ∀ x ∈ E q ++ (xs.flatMap (fun q => A (pos q) ++ E q) ++ A b), a < x.1 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rw [E_tag q x hx, hq]
          exact Nat.lt_succ_self a
        · rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨q', hq', hx'⟩ := List.mem_flatMap.mp hx
            have := pos_gt q' hq'
            rcases List.mem_append.mp hx' with hx' | hx'
            · rw [A_tag _ x hx']
              omega
            · rw [E_tag q' x hx']
              omega
          · rw [A_tag b x hx]
            omega
      have e1 := insert_at_split (ys := ys) hU hV
      rw [Brest, Bb, Ba, List.append_nil]
      simp only [List.append_assoc]
      rw [e1]
    · have Ba : B (pos q) = [] := by rw [B_at, hq, if_neg hah]
      have ih' := ih (a := a + 1) (by omega) hxs
      have hU : ∀ x ∈ A (pos q) ++ E q, x.1 ≤ h := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rw [A_tag _ x hx, hq]
          omega
        · rw [E_tag q x hx, hq]
          omega
      have e2 := insert_at_append_le (ys := ys)
        (T := xs.flatMap (fun q => A (pos q) ++ E q) ++ A b) hU
      simp only [List.append_assoc] at e2
      rw [Ba, List.nil_append]
      simp only [List.append_assoc]
      rw [ih', e2]

/-- The merge lemma. A list built from blocks `A p ++ B p ++ E p`,
where `A p` is tagged `p`, `E p` is tagged `p + 1`, and `B` is empty
except for `B h = ys`, is the same list without `B` with `ys` inserted
at `h`. Isabelle: `concat_blocks_insert`, whose range `[a..<b]` is
`List.range' a (b - a)`. -/
theorem concat_blocks_insert {α : Type _} {A B E : Nat → List (Nat × α)}
    {h a b : Nat} {ys : List (Nat × α)}
    (A_tag : ∀ p x, x ∈ A p → x.1 = p)
    (E_tag : ∀ p x, x ∈ E p → x.1 = p + 1)
    (B_at : ∀ p, B p = if p = h then ys else [])
    (ah : a ≤ h) (hb : h ≤ b) :
    (List.range' a (b - a)).flatMap (fun p => A p ++ (B p ++ E p)) ++ (A b ++ B b) =
      insert_at h ys ((List.range' a (b - a)).flatMap (fun p => A p ++ E p) ++ A b) :=
  concat_blocks_insert_gen (fun p => p) A_tag E_tag B_at ah hb (List.map_id' _)

/-! ## Source values at log positions -/

/-- The source value of a key does not change across positions that
carry no event for it. Isabelle: `take_state_quiet`, whose `L ! p` is
the bounded `L[p]`. The Isabelle assumption also speaks of the
positions at or beyond the length of `L`, where `L ! p` is an
unspecified value and `take` sees nothing, so this is the same claim
read on the log itself. -/
theorem take_state_quiet {L : List (Event K V)} {n m : Nat} {k : K}
    (nm : n ≤ m)
    (quiet : ∀ p, n ≤ p → p < m → ∀ hp : p < L.length, (L[p]'hp).key ≠ k)
    (σ0 : State K V) :
    state_after σ0 (L.take m) k = state_after σ0 (L.take n) k := by
  have split : L.take m = L.take n ++ (L.take m).drop n := by
    have h := List.take_append_drop n (L.take m)
    rw [List.take_take, Nat.min_eq_left nm] at h
    exact h.symm
  have none : evs_for k ((L.take m).drop n) = [] := by
    refine List.filter_eq_nil_iff.mpr (fun x hx => ?_)
    obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
    have hlen : ((L.take m).drop n).length = min m L.length - n := by
      rw [List.length_drop, List.length_take]
    rw [hlen] at hj
    have hnj : n + j < L.length := by omega
    have hx' : x = L[n + j]'hnj := by
      rw [← hxj, List.getElem_drop, List.getElem_take]
    simp only [decide_eq_true_eq]
    rw [hx']
    exact quiet (n + j) (by omega) (by omega) hnj
  rw [split]
  exact state_after_append_no_k none σ0 (L.take n)

/-- A log event carries the source value of its key just after its
position. Isabelle: `event_honest`, whose `L ! p` is the bounded
`L[p]` under the Isabelle assumption `p < length L`. -/
theorem event_honest {L : List (Event K V)} {p : Nat} {k : K}
    (hp : p < L.length) (key : (L[p]'hp).key = k) (σ0 : State K V) :
    (L[p]'hp).img = state_after σ0 (L.take (p + 1)) k := by
  have htake : L.take (p + 1) = L.take p ++ [L[p]'hp] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hp]
    rfl
  rw [htake, state_after_snoc]
  simp only [apply_ev]
  rw [if_pos key.symm]

/-- The key step. A timed list `T` for one key `k`, in tag order, with
every tag between `a` and `b`, every item carrying the source value of
`k` at its own tag, and every log event of `k` from `a` to `b` among
its items, replays from any initial state to the source value at `b`.
Isabelle: `honest_stream_last`, whose `L ! p` in the completeness
assumption is the bounded `L[p]`. The Isabelle assumption also speaks
of the positions at or beyond the length of `L`, which `take` does not
see. -/
theorem honest_stream_last {L : List (Event K V)} {σ0 : State K V} {k : K}
    {a b : Nat} {T : List (Nat × Event K V)}
    (ne : T ≠ [])
    (keyed : ∀ x ∈ T, x.2.key = k)
    (honest : ∀ x ∈ T, x.2.img = state_after σ0 (L.take x.1) k)
    (sorted : List.Pairwise (· ≤ ·) (T.map Prod.fst))
    (low : ∀ x ∈ T, a ≤ x.1)
    (high : ∀ x ∈ T, x.1 ≤ b)
    (complete : ∀ p, a ≤ p → p < b → ∀ hp : p < L.length,
      (L[p]'hp).key = k → (p + 1, L[p]'hp) ∈ T)
    (D : State K V) :
    state_after D (T.map Prod.snd) k = state_after σ0 (L.take b) k := by
  have last_in : T.getLast ne ∈ T := List.getLast_mem ne
  have evs : evs_for k (T.map Prod.snd) = T.map Prod.snd := by
    refine List.filter_eq_self.mpr (fun e he => ?_)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact decide_eq_true (keyed x hx)
  have map_ne : T.map Prod.snd ≠ [] := by
    intro h
    exact ne (List.map_eq_nil_iff.mp h)
  have evs_ne : evs_for k (T.map Prod.snd) ≠ [] := by
    rw [evs]
    exact map_ne
  have max : ∀ x ∈ T, x.1 ≤ (T.getLast ne).1 := by
    intro x hx
    have hmem : x.1 ∈ T.map Prod.fst := List.mem_map_of_mem hx
    have h := sorted_le_last sorted hmem
    rw [List.getLast_map] at h
    exact h
  have tb : (T.getLast ne).1 ≤ b := high _ last_in
  have quiet : ∀ p, (T.getLast ne).1 ≤ p → p < b → ∀ hp : p < L.length,
      (L[p]'hp).key ≠ k := by
    intro p tp pb hp key
    have ap : a ≤ p := Nat.le_trans (low _ last_in) tp
    have hin := complete p ap pb hp key
    have := max _ hin
    simp only at this
    omega
  rw [state_after_last_event evs_ne D, getLast_eq_of_eq evs evs_ne,
    List.getLast_map, honest _ last_in]
  exact (take_state_quiet tb quiet σ0).symm

/-! ## Close entries: their tags, and the value they carry -/

/-- Every close entry due at a position is the entry of an enumerated
key of a unit whose high edge denotes that position. Isabelle:
`closes_at_item`, stated in the `capture_plan` context, which has no
assumption beyond the coordinate space. -/
theorem closes_at_item {S : CoordinateSpace K V C} {units : List (CUnit K V C)}
    {svl : CUnit K V C → List K} {p : Nat} {x : Nat × Event K V}
    (hx : x ∈ closes_at S units svl p) :
    ∃ u ∈ units, ∃ k ∈ svl u,
      x = (S.den u.hi, ⟨k, u.refresh k⟩) ∧ S.den u.hi = p := by
  obtain ⟨⟨u, i⟩, hui, hxu⟩ := List.mem_flatMap.mp hx
  obtain ⟨-, -, hgot⟩ := List.mem_zipIdx hui
  have hu_in : u ∈ units := by
    rw [hgot]
    exact List.getElem_mem _
  by_cases hc : S.den u.hi = p
  · rw [if_pos hc] at hxu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hxu
    exact ⟨u, hu_in, k, hk, rfl, hc⟩
  · rw [if_neg hc] at hxu
    cases hxu

/-- Every close entry due at a position is tagged with that position.
Isabelle: `closes_at_tag`. -/
theorem closes_at_tag {S : CoordinateSpace K V C} {units : List (CUnit K V C)}
    {svl : CUnit K V C → List K} {p : Nat} {x : Nat × Event K V}
    (hx : x ∈ closes_at S units svl p) : x.1 = p := by
  obtain ⟨u, -, k, -, rfl, hp⟩ := closes_at_item hx
  exact hp

/-- The length of the consumed segment up to a coordinate. Port-local. -/
theorem seg_len_den (S : CoordinateSpace K V C) (a : Nat) (f : C) :
    ((S.log.take (S.den f)).drop a).length = S.den f - a :=
  seg_length S (S.den_le_len f)

/-- The positions of the consumed segment, traversed by `zipIdx`, are
the position range. Port-local. -/
theorem seg_zipIdx_pos (S : CoordinateSpace K V C) (a : Nat) (f : C) :
    (((S.log.take (S.den f)).drop a).zipIdx a).map Prod.snd =
      List.range' a (S.den f - a) := by
  rw [List.zipIdx_map_snd, seg_len_den]

/-- The pass's timed emission is in tag order. Isabelle:
`emission_t_sorted`, stated in the `capture_plan` context. -/
theorem emission_t_sorted (S : CoordinateSpace K V C) (units : List (CUnit K V C))
    (f : C) (svl : CUnit K V C → List K) (s0 : C) :
    List.Pairwise (· ≤ ·) ((emission_t S units f svl s0).map Prod.fst) :=
  (blocks_sorted_gen (closes_at S units svl) Prod.snd Prod.fst
    (fun _ _ hx => closes_at_tag hx) (seg_zipIdx_pos S (S.den s0) f)).1

/-- The pass's timed emission for a single key is in tag order.
Isabelle: `titems_emission_sorted`, stated in the `capture_plan`
context. -/
theorem titems_emission_sorted (S : CoordinateSpace K V C)
    (units : List (CUnit K V C)) (f : C) (svl : CUnit K V C → List K) (s0 : C)
    (k : K) :
    List.Pairwise (· ≤ ·) ((titems_for k (emission_t S units f svl s0)).map Prod.fst) :=
  sorted_map_fst_filter (emission_t_sorted S units f svl s0)

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

/-- An enumerated close entry carries the source value at its unit's
close. The key is untouched inside the unit's window, so the value
read at the O2 coordinate is still the source value at the high edge.
Isabelle: `listed_entry_honest`. -/
theorem listed_entry_honest {svl : CUnit K V C → List K}
    (hsvl : svl_ok2 S units svl) {u : CUnit K V C} (hu : u ∈ units) {k : K}
    (listed : k ∈ svl u) :
    u.refresh k = state_after σ0 (S.pfx u.hi) k := by
  have k_dom : u.dom k := svl2_sub_dom hsvl hu listed
  have quiet : evs_for k (S.win u.lo u.hi) = [] := svl2_untouched hsvl hu listed
  obtain ⟨c, c_lo, c_hi, honest⟩ := H.O2_honest u hu k k_dom
  have lo_hi : S.cle u.lo u.hi := H.bracket_lo_hi u hu
  rw [honest, S.win_invariant_state c_lo c_hi quiet σ0,
    S.win_invariant_state lo_hi (S.cle_refl u.hi) quiet σ0]

/-- A key of the scope that the enumeration does not list, and that no
consumed log event mentions, is absent at the frontier. Had it been
read as present, it would be a survivor and therefore listed.
Isabelle: `unlisted_quiet_absent`. -/
theorem unlisted_quiet_absent {svl : CUnit K V C → List K} {s0 : C}
    (hsvl : svl_ok2 S units svl)
    (s0lo : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k)
    (unlisted : k ∉ svl (the_unit units f k))
    (quiet : evs_for k (S.win s0 f) = []) :
    state_after σ0 (S.pfx f) k = none := by
  obtain ⟨u_in, k_dom⟩ := H.the_unit_props hk
  have s0_lo : S.cle s0 (the_unit units f k).lo := s0lo _ u_in
  have lo_hi : S.cle (the_unit units f k).lo (the_unit units f k).hi :=
    H.bracket_lo_hi _ u_in
  have hi_f : S.cle (the_unit units f k).hi f := H.bracket_hi_f _ u_in
  have lo_f : S.cle (the_unit units f k).lo f := S.cle_trans lo_hi hi_f
  have quiet_lo_f : evs_for k (S.win (the_unit units f k).lo f) = [] := by
    have hs := S.evs_for_win_split s0_lo lo_f k
    rw [quiet] at hs
    exact (List.append_eq_nil_iff.mp hs.symm).2
  have quiet_win : evs_for k
      (S.win (the_unit units f k).lo (the_unit units f k).hi) = [] := by
    have hs := S.evs_for_win_split lo_hi hi_f k
    rw [quiet_lo_f] at hs
    exact (List.append_eq_nil_iff.mp hs.symm).1
  have refresh_none : (the_unit units f k).refresh k = none := by
    refine Classical.byContradiction fun hr => unlisted ?_
    exact svl2_surv hsvl u_in ⟨k_dom, hr, quiet_win⟩
  have hsink : sink_at S units f f k = (the_unit units f k).refresh k := by
    simp only [sink_at]
    rw [dif_pos quiet_lo_f]
  rw [← H.contract_cut hk, hsink, refresh_none]

/-- The frontier enters a contract only as the bound on the high
edges, so a contract whose units all close at or before a coordinate
`g` is also a contract with frontier `g`. Isabelle:
`contract_with_frontier`. -/
theorem contract_with_frontier {g : C} (hi_g : ∀ u ∈ units, S.cle u.hi g) :
    CaptureContract S σ0 units scope g :=
  ⟨H.O1_cover, H.O1_disjoint, H.bracket_lo_hi, hi_g, H.O2_honest⟩

end CaptureContract

/-! ## A pass and a request served inside it, over one log -/

/-- Membership in the consumed segment from position `a` to a
coordinate, read as a log position. Port-local. -/
theorem mem_seg_pos {S : CoordinateSpace K V C} {a : Nat} {f : C} {e : Event K V}
    (he : e ∈ (S.log.take (S.den f)).drop a) :
    ∃ p, a ≤ p ∧ ∃ h : p < S.den f,
      e = S.log[p]'(Nat.lt_of_lt_of_le h (S.den_le_len f)) := by
  obtain ⟨j, hj, hej⟩ := List.mem_iff_getElem.mp he
  have hj' : j < S.den f - a := by
    rw [← seg_len_den S a f]
    exact hj
  refine ⟨a + j, Nat.le_add_right a j, by omega, ?_⟩
  rw [← hej, List.getElem_drop, List.getElem_take]

/-- An entry of the consumed segment traversed by `zipIdx` is the log
event at its position. Port-local. -/
theorem mem_seg_zipIdx {S : CoordinateSpace K V C} {a : Nat} {f : C}
    {ep : Event K V × Nat}
    (hep : ep ∈ ((S.log.take (S.den f)).drop a).zipIdx a) :
    a ≤ ep.2 ∧ ∃ h : ep.2 < S.den f,
      ep.1 = S.log[ep.2]'(Nat.lt_of_lt_of_le h (S.den_le_len f)) := by
  obtain ⟨e, i⟩ := ep
  obtain ⟨h1, h2, h3⟩ := List.mem_zipIdx hep
  rw [seg_len_den] at h2
  refine ⟨h1, by simp only; omega, ?_⟩
  simp only
  rw [h3, List.getElem_drop, List.getElem_take]
  congr 1
  omega

/-- Every log event of the consumed segment appears in the segment
traversed by `zipIdx`, at its position. Port-local. -/
theorem seg_zipIdx_mem {S : CoordinateSpace K V C} {a p : Nat} {f : C}
    (h1 : a ≤ p) (h2 : p < S.den f) :
    (S.log[p]'(Nat.lt_of_lt_of_le h2 (S.den_le_len f)), p) ∈
      ((S.log.take (S.den f)).drop a).zipIdx a := by
  rw [List.mem_iff_getElem]
  have hlen : p - a < (((S.log.take (S.den f)).drop a).zipIdx a).length := by
    rw [List.length_zipIdx, seg_len_den]
    omega
  refine ⟨p - a, hlen, ?_⟩
  rw [List.getElem_zipIdx, List.getElem_drop, List.getElem_take]
  have e : a + (p - a) = p := by omega
  simp only [e]

/-- A full pass and a request served inside it, over one coordinate
space and one initial source state. The pass `P` is a contract over
the units `U1`, the scope `sc1` and the frontier `f1`. The request `R`
is a contract over the units `U2` and the scope `sc2` with the same
frontier `f1`, so its units close at or before the pass's frontier.
Isabelle: locale `pass_with_request`, which adds no assumption of its
own to the two contracts. -/
structure PassWithRequest (S : CoordinateSpace K V C) (σ0 : State K V)
    (U1 : List (CUnit K V C)) (sc1 : K → Prop) (f1 : C)
    (U2 : List (CUnit K V C)) (sc2 : K → Prop) : Prop where
  /-- The pass. Isabelle: the locale instance `P`. -/
  P : CaptureContract S σ0 U1 sc1 f1
  /-- The request. Isabelle: the locale instance `R`. -/
  R : CaptureContract S σ0 U2 sc2 f1

/-- The interleaved stream, block by block over the pass's consumed log
positions: the pass's close blocks at the position, then the request's
close blocks at the position, then the log event at the position. Units
whose high edge sits at the frontier close after the last consumed
event, the pass's before the request's. Isabelle: `inter_t`, which maps
over the positions `[den s0..<den f1]` and reads `L ! p`. The port
traverses the consumed segment with `zipIdx`, as the core's
`emission_t` does, which gives the same list. -/
def inter_t (S : CoordinateSpace K V C) (U1 : List (CUnit K V C)) (f1 : C)
    (U2 : List (CUnit K V C)) (svl1 svl2 : CUnit K V C → List K) (s0 : C) :
    List (Nat × Event K V) :=
  (((S.log.take (S.den f1)).drop (S.den s0)).zipIdx (S.den s0)).flatMap
      (fun ep => closes_at S U1 svl1 ep.2 ++
        (closes_at S U2 svl2 ep.2 ++ [(ep.2 + 1, ep.1)]))
    ++ (closes_at S U1 svl1 (S.den f1) ++ closes_at S U2 svl2 (S.den f1))

/-- The interleaved stream with the tags dropped. Isabelle: `inter`. -/
def inter (S : CoordinateSpace K V C) (U1 : List (CUnit K V C)) (f1 : C)
    (U2 : List (CUnit K V C)) (svl1 svl2 : CUnit K V C → List K) (s0 : C) :
    List (Event K V) :=
  (inter_t S U1 f1 U2 svl1 svl2 s0).map Prod.snd

/-- Splitting a flat map whose blocks hold three parts: up to order, it
is the flat map of the outer parts followed by the flat map of the
middle parts. Port-local. -/
theorem flatMap_perm_split {β : Type _} {γ : Type _} (xs : List β)
    (A B E : β → List γ) :
    (xs.flatMap (fun q => A q ++ (B q ++ E q))).Perm
      (xs.flatMap (fun q => A q ++ E q) ++ xs.flatMap B) := by
  induction xs with
  | nil => exact List.Perm.refl []
  | cons q xs ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left (A q) ?_
    refine (List.perm_append_comm_assoc (B q) (E q) _).trans ?_
    refine List.Perm.append_left (E q) ?_
    refine (List.Perm.append_left (B q) ih).trans ?_
    exact List.perm_append_comm_assoc (B q) _ _

namespace PassWithRequest

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {U1 : List (CUnit K V C)} {sc1 : K → Prop} {f1 : C}
  {U2 : List (CUnit K V C)} {sc2 : K → Prop}
  (H : PassWithRequest S σ0 U1 sc1 f1 U2 sc2)

include H

/-! ### The stream is the pass's emission with the request's close blocks merged in -/

omit H in
/-- With an empty enumeration for the request, the stream is the
pass's emission. Isabelle: `inter_t_no_request`. -/
theorem inter_t_no_request (svl1 : CUnit K V C → List K) (s0 : C) :
    inter_t S U1 f1 U2 svl1 (fun _ => []) s0 = emission_t S U1 f1 svl1 s0 := by
  have nil : ∀ p, closes_at S U2 (fun _ => []) p = [] := by
    intro p
    apply flatMap_eq_nil_of_forall
    intro ui _
    by_cases hc : S.den ui.1.hi = p
    · rw [if_pos hc]
      rfl
    · rw [if_neg hc]
  simp only [inter_t, emission_t, nil, List.nil_append, List.append_nil]

omit H in
/-- As a multiset, the stream is the pass's emission plus the
request's close blocks at the positions from `s0` to `f1`. Isabelle:
`inter_t_mset`, whose multiset equality
`mset X = mset Y + mset Z` is the permutation `X.Perm (Y ++ Z)`, and
whose range `[den s0..<den f1]` is
`List.range' (S.den s0) (S.den f1 - S.den s0)`. -/
theorem inter_t_mset (svl1 svl2 : CUnit K V C → List K) (s0 : C) :
    (inter_t S U1 f1 U2 svl1 svl2 s0).Perm
      (emission_t S U1 f1 svl1 s0 ++
        ((List.range' (S.den s0) (S.den f1 - S.den s0)).flatMap (closes_at S U2 svl2)
          ++ closes_at S U2 svl2 (S.den f1))) := by
  rw [← seg_zipIdx_pos S (S.den s0) f1, List.flatMap_map]
  have h1 := flatMap_perm_split
    (((S.log.take (S.den f1)).drop (S.den s0)).zipIdx (S.den s0))
    (fun ep => closes_at S U1 svl1 ep.2) (fun ep => closes_at S U2 svl2 ep.2)
    (fun ep => [(ep.2 + 1, ep.1)])
  simp only [inter_t, emission_t]
  refine (h1.append_right _).trans ?_
  simp only [List.append_assoc]
  exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)

omit H in
/-- The stream is in position order. Isabelle: `inter_t_sorted`. -/
theorem inter_t_sorted (svl1 svl2 : CUnit K V C → List K) (s0 : C) :
    List.Pairwise (· ≤ ·) ((inter_t S U1 f1 U2 svl1 svl2 s0).map Prod.fst) := by
  have hC : ∀ p x, x ∈ closes_at S U1 svl1 p ++ closes_at S U2 svl2 p → x.1 = p := by
    intro p x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact closes_at_tag hx
    · exact closes_at_tag hx
  have h := (blocks_sorted_gen (fun p => closes_at S U1 svl1 p ++ closes_at S U2 svl2 p)
    Prod.snd Prod.fst hC (seg_zipIdx_pos S (S.den s0) f1)).1
  simp only [List.append_assoc] at h
  exact h

/-! ### What an item of the stream is -/

omit H in
/-- An item of the stream is a log event of the consumed segment, or a
close entry of the pass or of the request at a consumed position or at
the frontier. Isabelle: `inter_t_item_cases`, an `obtains` statement,
stated here as the disjunction of its three cases. The log event at
position `p` is the bounded `S.log[p]`, in range because
`p < S.den f1`. -/
theorem inter_t_item_cases {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    {x : Nat × Event K V} (hx : x ∈ inter_t S U1 f1 U2 svl1 svl2 s0) :
    (∃ p, S.den s0 ≤ p ∧ ∃ h2 : p < S.den f1,
        x = (p + 1, S.log[p]'(Nat.lt_of_lt_of_le h2 (S.den_le_len f1)))) ∨
      (∃ p, (S.den s0 ≤ p ∧ p < S.den f1 ∨ p = S.den f1) ∧
        x ∈ closes_at S U1 svl1 p) ∨
      (∃ p, (S.den s0 ≤ p ∧ p < S.den f1 ∨ p = S.den f1) ∧
        x ∈ closes_at S U2 svl2 p) := by
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨ep, hep, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨h1, h2, he⟩ := mem_seg_zipIdx hep
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (Or.inl ⟨ep.2, Or.inl ⟨h1, h2⟩, hx⟩)
    · rcases List.mem_append.mp hx with hx | hx
      · exact Or.inr (Or.inr ⟨ep.2, Or.inl ⟨h1, h2⟩, hx⟩)
      · left
        refine ⟨ep.2, h1, h2, ?_⟩
        rw [List.mem_singleton.mp hx, he]
  · rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (Or.inl ⟨S.den f1, Or.inr rfl, hx⟩)
    · exact Or.inr (Or.inr ⟨S.den f1, Or.inr rfl, hx⟩)

/-- Every item of the stream carries the source value of its own key
at its own tag: a log event by `event_honest`, a close entry of either
read by `listed_entry_honest`. Isabelle: `inter_item_honest`. -/
theorem inter_item_honest {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    {x : Nat × Event K V} (hx : x ∈ inter_t S U1 f1 U2 svl1 svl2 s0) :
    x.2.img = state_after σ0 (S.log.take x.1) x.2.key := by
  rcases inter_t_item_cases hx with ⟨p, -, h2, rfl⟩ | ⟨p, -, hP⟩ | ⟨p, -, hR⟩
  · exact event_honest _ rfl σ0
  · obtain ⟨u, hu, k', hk', rfl, -⟩ := closes_at_item hP
    exact H.P.listed_entry_honest hsvl1 hu hk'
  · obtain ⟨u, hu, k', hk', rfl, -⟩ := closes_at_item hR
    exact H.R.listed_entry_honest hsvl2 hu hk'

omit H in
/-- Every tag of the stream lies between the consumption start and the
frontier. Isabelle: `inter_t_tag_bounds`. -/
theorem inter_t_tag_bounds {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (s0f1 : S.den s0 ≤ S.den f1)
    {x : Nat × Event K V} (hx : x ∈ inter_t S U1 f1 U2 svl1 svl2 s0) :
    S.den s0 ≤ x.1 ∧ x.1 ≤ S.den f1 := by
  rcases inter_t_item_cases hx with ⟨p, h1, h2, rfl⟩ | ⟨p, hp, hP⟩ | ⟨p, hp, hR⟩
  · exact ⟨Nat.le_succ_of_le h1, h2⟩
  · rw [closes_at_tag hP]
    omega
  · rw [closes_at_tag hR]
    omega

omit H in
/-- Every log event of a key from the consumption start to the
frontier is among the stream's items for the key. Isabelle:
`inter_key_complete`, whose `L ! p` is the bounded `S.log[p]`, in
range because `p < S.den f1`. -/
theorem inter_key_complete {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    {p : Nat} {k : K} (h1 : S.den s0 ≤ p) (h2 : p < S.den f1)
    (key : (S.log[p]'(Nat.lt_of_lt_of_le h2 (S.den_le_len f1))).key = k) :
    (p + 1, S.log[p]'(Nat.lt_of_lt_of_le h2 (S.den_le_len f1))) ∈
      titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) := by
  refine List.mem_filter.mpr ⟨?_, decide_eq_true key⟩
  refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, seg_zipIdx_mem h1 h2, ?_⟩)
  simp

/-! ### The per-key characterization -/

/-- Per key, the interleaved stream is the pass's own per-key emission
with the request's entry for the key, if the request lists it,
inserted at the position of the request's close, after anything the
pass emits at that position. Isabelle: `titems_inter`. -/
theorem titems_inter {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (hsvl2 : svl_ok2 S U2 svl2)
    (s0hi2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.hi) (k : K) :
    titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) =
      if sc2 k ∧ k ∈ svl2 (the_unit U2 f1 k)
      then insert_at (S.den (the_unit U2 f1 k).hi)
        [(S.den (the_unit U2 f1 k).hi, ⟨k, (the_unit U2 f1 k).refresh k⟩)]
        (titems_for k (emission_t S U1 f1 svl1 s0))
      else titems_for k (emission_t S U1 f1 svl1 s0) := by
  have inter_dist : titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) =
      (((S.log.take (S.den f1)).drop (S.den s0)).zipIdx (S.den s0)).flatMap
          (fun ep => titems_for k (closes_at S U1 svl1 ep.2) ++
            (titems_for k (closes_at S U2 svl2 ep.2) ++ titems_for k [(ep.2 + 1, ep.1)]))
        ++ (titems_for k (closes_at S U1 svl1 (S.den f1)) ++
          titems_for k (closes_at S U2 svl2 (S.den f1))) := by
    simp only [inter_t, titems_append, titems_flatMap]
  have emis_dist : titems_for k (emission_t S U1 f1 svl1 s0) =
      (((S.log.take (S.den f1)).drop (S.den s0)).zipIdx (S.den s0)).flatMap
          (fun ep => titems_for k (closes_at S U1 svl1 ep.2) ++
            titems_for k [(ep.2 + 1, ep.1)])
        ++ titems_for k (closes_at S U1 svl1 (S.den f1)) := by
    simp only [emission_t, titems_append, titems_flatMap]
  have A_tag : ∀ p x, x ∈ titems_for k (closes_at S U1 svl1 p) → x.1 = p :=
    fun _ _ hx => closes_at_tag (List.mem_filter.mp hx).1
  have E_tag : ∀ (ep : Event K V × Nat) x,
      x ∈ titems_for k [((ep.2 + 1, ep.1) : Nat × Event K V)] → x.1 = ep.2 + 1 := by
    intro ep x hx
    rw [List.mem_singleton.mp (List.mem_filter.mp hx).1]
  by_cases listed : sc2 k ∧ k ∈ svl2 (the_unit U2 f1 k)
  · rw [if_pos listed]
    obtain ⟨k2, hl⟩ := listed
    have u_in := (H.R.the_unit_props k2).1
    have ah : S.den s0 ≤ S.den (the_unit U2 f1 k).hi := s0hi2 _ u_in
    have hb : S.den (the_unit U2 f1 k).hi ≤ S.den f1 := H.R.bracket_hi_f _ u_in
    rw [inter_dist, emis_dist]
    refine concat_blocks_insert_gen Prod.snd
      (A := fun p => titems_for k (closes_at S U1 svl1 p))
      (B := fun p => titems_for k (closes_at S U2 svl2 p))
      (E := fun ep => titems_for k [(ep.2 + 1, ep.1)])
      A_tag E_tag ?_ ah hb (seg_zipIdx_pos S (S.den s0) f1)
    intro p
    show titems_for k (closes_at S U2 svl2 p) = _
    rw [H.R.titems_closes_at2 hsvl2 k2 p]
    by_cases hp : p = S.den (the_unit U2 f1 k).hi
    · rw [if_pos ⟨hp.symm, hl⟩, if_pos hp, hp]
    · rw [if_neg (fun h => hp h.1.symm), if_neg hp]
  · rw [if_neg listed]
    have B_nil : ∀ p, titems_for k (closes_at S U2 svl2 p) = [] := by
      intro p
      by_cases k2 : sc2 k
      · rw [H.R.titems_closes_at2 hsvl2 k2 p, if_neg (fun h => listed ⟨k2, h.2⟩)]
      · exact H.R.titems_closes_at_out hsvl2 k2 p
    rw [inter_dist, emis_dist]
    simp only [B_nil, List.nil_append, List.append_nil]

/-! ### A key that the stream mentions ends at the source state -/

/-- If the interleaved stream carries anything for a key, the key ends
at the source state at the frontier, from any initial sink state.
Isabelle: `inter_key_replay`. -/
theorem inter_key_replay {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0f1 : S.den s0 ≤ S.den f1) {k : K}
    (ne : titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) ≠ []) (D : State K V) :
    state_after D (inter S U1 f1 U2 svl1 svl2 s0) k = state_after σ0 (S.pfx f1) k := by
  have T_item : ∀ x ∈ titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0),
      x ∈ inter_t S U1 f1 U2 svl1 svl2 s0 ∧ x.2.key = k := by
    intro x hx
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hx
    exact ⟨h1, of_decide_eq_true h2⟩
  have keyed : ∀ x ∈ titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0), x.2.key = k :=
    fun x hx => (T_item x hx).2
  have honest : ∀ x ∈ titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0),
      x.2.img = state_after σ0 (S.log.take x.1) k := by
    intro x hx
    have h := H.inter_item_honest hsvl1 hsvl2 (T_item x hx).1
    rw [(T_item x hx).2] at h
    exact h
  have sorted : List.Pairwise (· ≤ ·)
      ((titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0)).map Prod.fst) :=
    sorted_map_fst_filter (inter_t_sorted svl1 svl2 s0)
  have low : ∀ x ∈ titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0), S.den s0 ≤ x.1 :=
    fun x hx => (inter_t_tag_bounds s0f1 (T_item x hx).1).1
  have high : ∀ x ∈ titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0), x.1 ≤ S.den f1 :=
    fun x hx => (inter_t_tag_bounds s0f1 (T_item x hx).1).2
  have complete : ∀ p, S.den s0 ≤ p → p < S.den f1 → ∀ hp : p < S.log.length,
      (S.log[p]'hp).key = k →
        (p + 1, S.log[p]'hp) ∈ titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) :=
    fun _ h1 h2 _ key => inter_key_complete h1 h2 key
  have T_self : titems_for k (titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0)) =
      titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) :=
    List.filter_eq_self.mpr (fun x hx => decide_eq_true (keyed x hx))
  have evs : evs_for k (inter S U1 f1 U2 svl1 svl2 s0) =
      evs_for k ((titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0)).map Prod.snd) := by
    rw [inter, evs_for_map_snd, evs_for_map_snd, T_self]
  rw [replay_per_key evs D]
  exact honest_stream_last ne keyed honest sorted low high complete D

/-! ### Safety and convergence -/

/-- Safety of a pass with a request served inside it. Every key of
either scope ends at the source state at the pass's frontier, or it is
absent there, neither read listed it, no log event from the
consumption start to the frontier mentions it, and the sink keeps its
initial value. Isabelle: `pass_with_request_safe`. -/
theorem pass_with_request_safe {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0lo2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.lo)
    {k : K} (hk : sc1 k ∨ sc2 k) (D0 : State K V) :
    state_after D0 (inter S U1 f1 U2 svl1 svl2 s0) k = state_after σ0 (S.pfx f1) k ∨
      (state_after D0 (inter S U1 f1 U2 svl1 svl2 s0) k = D0 k ∧
        state_after σ0 (S.pfx f1) k = none ∧
        (sc1 k → k ∉ svl1 (the_unit U1 f1 k)) ∧
        (sc2 k → k ∉ svl2 (the_unit U2 f1 k)) ∧
        evs_for k (S.win s0 f1) = []) := by
  have P_s0lo : ∀ u ∈ U1, S.cle s0 u.lo := s0lo
  have R_s0lo : ∀ u ∈ U2, S.cle s0 u.lo := s0lo2
  have s0hi2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.hi :=
    fun u hu => Nat.le_trans (s0lo2 u hu) (H.R.bracket_lo_hi u hu)
  have s0f1 : S.den s0 ≤ S.den f1 := by
    by_cases k1 : sc1 k
    · have u := (H.P.the_unit_props k1).1
      exact S.cle_trans (S.cle_trans (P_s0lo _ u) (H.P.bracket_lo_hi _ u))
        (H.P.bracket_hi_f _ u)
    · have k2 : sc2 k := hk.resolve_left k1
      have u := (H.R.the_unit_props k2).1
      exact S.cle_trans (S.cle_trans (R_s0lo _ u) (H.R.bracket_lo_hi _ u))
        (H.R.bracket_hi_f _ u)
  by_cases silent : titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) = []
  · right
    have kept : state_after D0 (inter S U1 f1 U2 svl1 svl2 s0) k = D0 k := by
      refine state_after_no_events ?_ D0
      rw [inter, evs_for_map_snd, silent]
      rfl
    have char := H.titems_inter (svl1 := svl1) hsvl2 s0hi2 k
    have R_unlisted : ¬ (sc2 k ∧ k ∈ svl2 (the_unit U2 f1 k)) := by
      intro listed
      rw [if_pos listed, silent] at char
      simp [insert_at] at char
    rw [if_neg R_unlisted, silent] at char
    have P_empty : titems_for k (emission_t S U1 f1 svl1 s0) = [] := char.symm
    have quiet : evs_for k (S.win s0 f1) = [] := by
      refine List.filter_eq_nil_iff.mpr (fun e he => ?_)
      obtain ⟨p, h1, h2, rfl⟩ := mem_seg_pos he
      intro key
      have hin := inter_key_complete (U1 := U1) (U2 := U2) (svl1 := svl1) (svl2 := svl2)
        h1 h2 (of_decide_eq_true key)
      rw [silent] at hin
      cases hin
    have P_unlisted : sc1 k → k ∉ svl1 (the_unit U1 f1 k) := by
      intro k1 hl
      have master := H.P.titems_emission_master2 hsvl1 P_s0lo k1
      rw [P_empty, if_pos hl] at master
      simp at master
    have src_none : state_after σ0 (S.pfx f1) k = none := by
      by_cases k1 : sc1 k
      · exact H.P.unlisted_quiet_absent hsvl1 P_s0lo k1 (P_unlisted k1) quiet
      · have k2 : sc2 k := hk.resolve_left k1
        exact H.R.unlisted_quiet_absent hsvl2 R_s0lo k2
          (fun hl => R_unlisted ⟨k2, hl⟩) quiet
    exact ⟨kept, src_none, P_unlisted, fun k2 hl => R_unlisted ⟨k2, hl⟩, quiet⟩
  · left
    exact H.inter_key_replay hsvl1 hsvl2 s0f1 silent D0

/-- Convergence of a pass with a request served inside it: under
coverage of every key that the sink holds, that is absent at the
pass's frontier, and that no log event from the consumption start to
the frontier mentions, the sink ends at the source state on both
scopes. Isabelle: `pass_with_request_converges`. -/
theorem pass_with_request_converges {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0lo2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.lo)
    (cover : ∀ k, (sc1 k ∨ sc2 k) → D0 k ≠ none →
      state_after σ0 (S.pfx f1) k = none → evs_for k (S.win s0 f1) = [] →
      (sc1 k ∧ k ∈ svl1 (the_unit U1 f1 k)) ∨
        (sc2 k ∧ k ∈ svl2 (the_unit U2 f1 k))) :
    ∀ k, (sc1 k ∨ sc2 k) →
      state_after D0 (inter S U1 f1 U2 svl1 svl2 s0) k = state_after σ0 (S.pfx f1) k := by
  intro k hk
  rcases H.pass_with_request_safe hsvl1 hsvl2 s0lo s0lo2 hk D0 with
    h | ⟨hD, hsrc, hn1, hn2, hq⟩
  · exact h
  · by_cases hD0 : D0 k = none
    · rw [hD, hD0, hsrc]
    · rcases cover k hk hD0 hsrc hq with ⟨h1, hl⟩ | ⟨h2, hl⟩
      · exact absurd hl (hn1 h1)
      · exact absurd hl (hn2 h2)

/-! ### A request that lists its absent keys completes the pass -/

/-- A request that lists every key it reads as absent and untouched
completes the pass when every key the pass leaves wrong, with no log
event during the pass, is in the request's scope. Isabelle:
`pass_with_listing_request_converges`. -/
theorem pass_with_listing_request_converges {svl1 svl2 : CUnit K V C → List K}
    {s0 : C} {D0 : State K V}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0lo2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.lo)
    (lists_absent : ∀ u ∈ U2, ∀ k, absent_untouched S u k → k ∈ svl2 u)
    (in_scope : ∀ k, sc1 k → D0 k ≠ none → sink_at S U1 f1 f1 k = none →
      k ∉ svl1 (the_unit U1 f1 k) → evs_for k (S.win s0 f1) = [] → sc2 k) :
    ∀ k, (sc1 k ∨ sc2 k) →
      state_after D0 (inter S U1 f1 U2 svl1 svl2 s0) k = state_after σ0 (S.pfx f1) k := by
  refine H.pass_with_request_converges hsvl1 hsvl2 s0lo s0lo2 ?_
  intro k hk held src_none quiet
  by_cases k2 : sc2 k
  · -- The request reads the key as absent and untouched, so it lists it.
    right
    refine ⟨k2, ?_⟩
    obtain ⟨u_in, k_dom⟩ := H.R.the_unit_props k2
    have lo_hi := H.R.bracket_lo_hi _ u_in
    have hi_f1 := H.R.bracket_hi_f _ u_in
    have s0_lo : S.cle s0 (the_unit U2 f1 k).lo := s0lo2 _ u_in
    have lo_f1 : S.cle (the_unit U2 f1 k).lo f1 := S.cle_trans lo_hi hi_f1
    have lo_f1_q : evs_for k (S.win (the_unit U2 f1 k).lo f1) = [] := by
      have hs := S.evs_for_win_split s0_lo lo_f1 k
      rw [quiet] at hs
      exact (List.append_eq_nil_iff.mp hs.symm).2
    have win_q : evs_for k
        (S.win (the_unit U2 f1 k).lo (the_unit U2 f1 k).hi) = [] := by
      have hs := S.evs_for_win_split lo_hi hi_f1 k
      rw [lo_f1_q] at hs
      exact (List.append_eq_nil_iff.mp hs.symm).1
    obtain ⟨c, c_lo, c_hi, honest⟩ := H.R.O2_honest _ u_in k k_dom
    have c_f1 : S.cle c f1 := S.cle_trans c_hi hi_f1
    have hr : (the_unit U2 f1 k).refresh k = none := by
      rw [honest, S.win_invariant_state c_lo c_f1 lo_f1_q σ0,
        ← S.win_invariant_state lo_f1 (S.cle_refl f1) lo_f1_q σ0]
      exact src_none
    exact lists_absent _ u_in k ⟨k_dom, hr, win_q⟩
  · -- Only the pass owns the key, so the pass lists it.
    left
    have k1 : sc1 k := hk.resolve_right k2
    refine ⟨k1, ?_⟩
    have sink_none : sink_at S U1 f1 f1 k = none :=
      (H.P.contract_cut k1).trans src_none
    exact Classical.byContradiction fun hnl =>
      k2 (in_scope k k1 held sink_none hnl quiet)

/-- The keys a pass leaves wrong are exactly the unlisted keys of its
scope that the sink holds, that are absent at the pass's frontier, and
that no log event during the pass mentions. This is a fact about the
pass alone. Isabelle: `pass_leaves_wrong_iff` of the locale
`pass_with_request`, with the statement and proof of the lemma of the
same name in `Orphan_Absence_Composition`. -/
theorem pass_leaves_wrong_iff {svl1 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    {k : K} (k1 : sc1 k) (D0 : State K V) :
    state_after D0 (emission S U1 f1 svl1 s0) k ≠ sink_at S U1 f1 f1 k ↔
      (D0 k ≠ none ∧ sink_at S U1 f1 f1 k = none ∧
        k ∉ svl1 (the_unit U1 f1 k) ∧ evs_for k (S.win s0 f1) = []) := by
  have P_s0lo : ∀ u ∈ U1, S.cle s0 u.lo := s0lo
  constructor
  · intro wrong
    rcases H.P.absent_replay_safe hsvl1 P_s0lo k1 D0 with
      h | ⟨hD, hsink, -, hnl, hq⟩
    · exact absurd h wrong
    · refine ⟨fun hD0 => wrong ?_, hsink, hnl, hq⟩
      rw [hD, hsink, hD0]
  · rintro ⟨held, hsink, hnl, hq⟩ heq
    rw [H.P.unlisted_quiet_key_kept hsvl1 P_s0lo k1 hnl hq D0, hsink] at heq
    exact held heq

/-- A key-list request served inside the pass completes it. The
request reads each requested key at its own coordinate `rc k` inside
the pass's span (a request that runs in batches reads each batch at
its own coordinate), its scope holds every requested key that is
absent where it reads it, and every key the pass leaves wrong was
requested. Then the sink ends at the source state on both scopes.
Isabelle: `request_in_pass_converges`, whose set of requested keys `K`
is the predicate `req` here, since `K` names the key type in the
port. -/
theorem request_in_pass_converges {svl1 svl2 : CUnit K V C → List K}
    {s0 : C} {D0 : State K V} {req : K → Prop} {rc : K → C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0lo2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.lo)
    (lists_absent : ∀ u ∈ U2, ∀ k, absent_untouched S u k → k ∈ svl2 u)
    (s0_rc : ∀ k, req k → S.den s0 ≤ S.den (rc k))
    (rc_f1 : ∀ k, req k → S.den (rc k) ≤ S.den f1)
    (sc2_abs : ∀ k, req k → state_after σ0 (S.pfx (rc k)) k = none → sc2 k)
    (asked : ∀ k, sc1 k →
      state_after D0 (emission S U1 f1 svl1 s0) k ≠ sink_at S U1 f1 f1 k →
      req k) :
    ∀ k, (sc1 k ∨ sc2 k) →
      state_after D0 (inter S U1 f1 U2 svl1 svl2 s0) k = state_after σ0 (S.pfx f1) k := by
  have P_s0lo : ∀ u ∈ U1, S.cle s0 u.lo := s0lo
  refine H.pass_with_listing_request_converges hsvl1 hsvl2 s0lo s0lo2 lists_absent ?_
  intro k k1 held sink_none nl quiet
  have kept := H.P.unlisted_quiet_key_kept hsvl1 P_s0lo k1 nl quiet D0
  have wrong : state_after D0 (emission S U1 f1 svl1 s0) k ≠
      sink_at S U1 f1 f1 k := by
    rw [kept, sink_none]
    exact held
  have kK : req k := asked k k1 wrong
  have s0rc : S.cle s0 (rc k) := s0_rc k kK
  have rcf1 : S.cle (rc k) f1 := rc_f1 k kK
  have s0_f1 : S.cle s0 f1 := S.cle_trans s0rc rcf1
  have hrc : state_after σ0 (S.pfx (rc k)) k = none := by
    rw [S.win_invariant_state s0rc rcf1 quiet σ0,
      ← S.win_invariant_state s0_f1 (S.cle_refl f1) quiet σ0,
      ← H.P.contract_cut k1]
    exact sink_none
  exact sc2_abs k kK hrc

end PassWithRequest

/-- The interleaved stream with the reverse tie order: at each position
the request's close blocks come before the pass's, and at the frontier
the request's close blocks come before the pass's. Isabelle:
`inter_t_rev`, traversed with `zipIdx` as `inter_t`. -/
def inter_t_rev (S : CoordinateSpace K V C) (U1 : List (CUnit K V C)) (f1 : C)
    (U2 : List (CUnit K V C)) (svl1 svl2 : CUnit K V C → List K) (s0 : C) :
    List (Nat × Event K V) :=
  (((S.log.take (S.den f1)).drop (S.den s0)).zipIdx (S.den s0)).flatMap
      (fun ep => closes_at S U2 svl2 ep.2 ++
        (closes_at S U1 svl1 ep.2 ++ [(ep.2 + 1, ep.1)]))
    ++ (closes_at S U2 svl2 (S.den f1) ++ closes_at S U1 svl1 (S.den f1))

/-- The reverse-order stream with the tags dropped. Isabelle:
`inter_rev`. -/
def inter_rev (S : CoordinateSpace K V C) (U1 : List (CUnit K V C)) (f1 : C)
    (U2 : List (CUnit K V C)) (svl1 svl2 : CUnit K V C → List K) (s0 : C) :
    List (Event K V) :=
  (inter_t_rev S U1 f1 U2 svl1 svl2 s0).map Prod.snd

namespace PassWithRequest

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {U1 : List (CUnit K V C)} {sc1 : K → Prop} {f1 : C}
  {U2 : List (CUnit K V C)} {sc2 : K → Prop}
  (H : PassWithRequest S σ0 U1 sc1 f1 U2 sc2)

include H

/-! ### The reverse tie order at equal positions -/

omit H in
/-- Both tie orders carry the same items. Isabelle: `inter_t_rev_set`,
an equality of sets, stated here pointwise. -/
theorem inter_t_rev_set (svl1 svl2 : CUnit K V C → List K) (s0 : C)
    (x : Nat × Event K V) :
    x ∈ inter_t_rev S U1 f1 U2 svl1 svl2 s0 ↔ x ∈ inter_t S U1 f1 U2 svl1 svl2 s0 := by
  simp only [inter_t_rev, inter_t, List.mem_append, List.mem_flatMap, or_left_comm,
    or_comm]

omit H in
/-- The reverse-order stream is in position order. Isabelle:
`inter_t_rev_sorted`. -/
theorem inter_t_rev_sorted (svl1 svl2 : CUnit K V C → List K) (s0 : C) :
    List.Pairwise (· ≤ ·) ((inter_t_rev S U1 f1 U2 svl1 svl2 s0).map Prod.fst) := by
  have hC : ∀ p x, x ∈ closes_at S U2 svl2 p ++ closes_at S U1 svl1 p → x.1 = p := by
    intro p x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact closes_at_tag hx
    · exact closes_at_tag hx
  have h := (blocks_sorted_gen (fun p => closes_at S U2 svl2 p ++ closes_at S U1 svl1 p)
    Prod.snd Prod.fst hC (seg_zipIdx_pos S (S.den s0) f1)).1
  simp only [List.append_assoc] at h
  exact h

/-- If the reverse-order stream carries anything for a key, the key
ends at the source state at the frontier, from any initial sink state.
Isabelle: `inter_rev_key_replay`. -/
theorem inter_rev_key_replay {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0f1 : S.den s0 ≤ S.den f1) {k : K}
    (ne : titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0) ≠ []) (D : State K V) :
    state_after D (inter_rev S U1 f1 U2 svl1 svl2 s0) k =
      state_after σ0 (S.pfx f1) k := by
  have T_set : ∀ x, x ∈ titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0) ↔
      x ∈ titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) := by
    intro x
    simp only [titems_for, List.mem_filter, inter_t_rev_set]
  have T_item : ∀ x ∈ titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0),
      x ∈ inter_t S U1 f1 U2 svl1 svl2 s0 ∧ x.2.key = k := by
    intro x hx
    obtain ⟨h1, h2⟩ := List.mem_filter.mp ((T_set x).mp hx)
    exact ⟨h1, of_decide_eq_true h2⟩
  have keyed : ∀ x ∈ titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0), x.2.key = k :=
    fun x hx => (T_item x hx).2
  have honest : ∀ x ∈ titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0),
      x.2.img = state_after σ0 (S.log.take x.1) k := by
    intro x hx
    have h := H.inter_item_honest hsvl1 hsvl2 (T_item x hx).1
    rw [(T_item x hx).2] at h
    exact h
  have sorted : List.Pairwise (· ≤ ·)
      ((titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0)).map Prod.fst) :=
    sorted_map_fst_filter (inter_t_rev_sorted svl1 svl2 s0)
  have low : ∀ x ∈ titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0), S.den s0 ≤ x.1 :=
    fun x hx => (inter_t_tag_bounds s0f1 (T_item x hx).1).1
  have high : ∀ x ∈ titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0), x.1 ≤ S.den f1 :=
    fun x hx => (inter_t_tag_bounds s0f1 (T_item x hx).1).2
  have complete : ∀ p, S.den s0 ≤ p → p < S.den f1 → ∀ hp : p < S.log.length,
      (S.log[p]'hp).key = k →
        (p + 1, S.log[p]'hp) ∈ titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0) :=
    fun _ h1 h2 _ key => (T_set _).mpr (inter_key_complete h1 h2 key)
  have T_self : titems_for k (titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0)) =
      titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0) :=
    List.filter_eq_self.mpr (fun x hx => decide_eq_true (keyed x hx))
  have evs : evs_for k (inter_rev S U1 f1 U2 svl1 svl2 s0) =
      evs_for k ((titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0)).map Prod.snd) := by
    rw [inter_rev, evs_for_map_snd, evs_for_map_snd, T_self]
  rw [replay_per_key evs D]
  exact honest_stream_last ne keyed honest sorted low high complete D

/-- Under either tie order, every key replays to the same value.
Isabelle: `inter_rev_same_replay`. -/
theorem inter_rev_same_replay {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0f1 : S.den s0 ≤ S.den f1) (D : State K V) (k : K) :
    state_after D (inter_rev S U1 f1 U2 svl1 svl2 s0) k =
      state_after D (inter S U1 f1 U2 svl1 svl2 s0) k := by
  have sets : ∀ x, x ∈ titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0) ↔
      x ∈ titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) := by
    intro x
    simp only [titems_for, List.mem_filter, inter_t_rev_set]
  by_cases silent : titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) = []
  · have silent' : titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0) = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr (fun x hx => ?_)
      have hx' := (sets x).mp hx
      rw [silent] at hx'
      cases hx'
    have e1 : evs_for k (inter_rev S U1 f1 U2 svl1 svl2 s0) = [] := by
      rw [inter_rev, evs_for_map_snd, silent']
      rfl
    have e2 : evs_for k (inter S U1 f1 U2 svl1 svl2 s0) = [] := by
      rw [inter, evs_for_map_snd, silent]
      rfl
    rw [state_after_no_events e1 D, state_after_no_events e2 D]
  · have ne' : titems_for k (inter_t_rev S U1 f1 U2 svl1 svl2 s0) ≠ [] := by
      intro h
      apply silent
      refine List.eq_nil_iff_forall_not_mem.mpr (fun x hx => ?_)
      have hx' := (sets x).mpr hx
      rw [h] at hx'
      cases hx'
    rw [H.inter_rev_key_replay hsvl1 hsvl2 s0f1 ne' D,
      H.inter_key_replay hsvl1 hsvl2 s0f1 silent D]

/-- A key of either scope puts the consumption start at or before the
frontier. Isabelle: `s0_le_f1_of_key`. -/
theorem s0_le_f1_of_key {s0 : C}
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0lo2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.lo)
    {k : K} (hk : sc1 k ∨ sc2 k) : S.den s0 ≤ S.den f1 := by
  by_cases k1 : sc1 k
  · have u := (H.P.the_unit_props k1).1
    exact Nat.le_trans (s0lo _ u)
      (Nat.le_trans (H.P.bracket_lo_hi _ u) (H.P.bracket_hi_f _ u))
  · have k2 : sc2 k := hk.resolve_left k1
    have u := (H.R.the_unit_props k2).1
    exact Nat.le_trans (s0lo2 _ u)
      (Nat.le_trans (H.R.bracket_lo_hi _ u) (H.R.bracket_hi_f _ u))

/-- Safety under the reverse tie order. Isabelle:
`pass_with_request_safe_rev`. -/
theorem pass_with_request_safe_rev {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0lo2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.lo)
    {k : K} (hk : sc1 k ∨ sc2 k) (D0 : State K V) :
    state_after D0 (inter_rev S U1 f1 U2 svl1 svl2 s0) k = state_after σ0 (S.pfx f1) k ∨
      (state_after D0 (inter_rev S U1 f1 U2 svl1 svl2 s0) k = D0 k ∧
        state_after σ0 (S.pfx f1) k = none ∧
        (sc1 k → k ∉ svl1 (the_unit U1 f1 k)) ∧
        (sc2 k → k ∉ svl2 (the_unit U2 f1 k)) ∧
        evs_for k (S.win s0 f1) = []) := by
  have s0f1 := H.s0_le_f1_of_key s0lo s0lo2 hk
  rw [H.inter_rev_same_replay hsvl1 hsvl2 s0f1 D0 k]
  exact H.pass_with_request_safe hsvl1 hsvl2 s0lo s0lo2 hk D0

/-- Convergence under the reverse tie order. Isabelle:
`pass_with_request_converges_rev`. -/
theorem pass_with_request_converges_rev {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    {D0 : State K V}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0lo2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.lo)
    (cover : ∀ k, (sc1 k ∨ sc2 k) → D0 k ≠ none →
      state_after σ0 (S.pfx f1) k = none → evs_for k (S.win s0 f1) = [] →
      (sc1 k ∧ k ∈ svl1 (the_unit U1 f1 k)) ∨
        (sc2 k ∧ k ∈ svl2 (the_unit U2 f1 k))) :
    ∀ k, (sc1 k ∨ sc2 k) →
      state_after D0 (inter_rev S U1 f1 U2 svl1 svl2 s0) k =
        state_after σ0 (S.pfx f1) k := by
  intro k hk
  have s0f1 := H.s0_le_f1_of_key s0lo s0lo2 hk
  rw [H.inter_rev_same_replay hsvl1 hsvl2 s0f1 D0 k]
  exact H.pass_with_request_converges hsvl1 hsvl2 s0lo s0lo2 cover k hk

/-! ### Any tie order at equal positions -/

/-- Any timed list with the same items as `inter_t` and in position
order replays to the same value as `inter_t` on every key. Isabelle:
`inter_any_same_replay`, whose set equality `set T = set (inter_t ..)`
is stated pointwise. -/
theorem inter_any_same_replay {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    {T : List (Nat × Event K V)}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0f1 : S.den s0 ≤ S.den f1)
    (T_set : ∀ x, x ∈ T ↔ x ∈ inter_t S U1 f1 U2 svl1 svl2 s0)
    (T_sorted : List.Pairwise (· ≤ ·) (T.map Prod.fst)) (D : State K V) (k : K) :
    state_after D (T.map Prod.snd) k = state_after D (inter S U1 f1 U2 svl1 svl2 s0) k := by
  have sets : ∀ x, x ∈ titems_for k T ↔
      x ∈ titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) := by
    intro x
    simp only [titems_for, List.mem_filter, T_set]
  by_cases silent : titems_for k (inter_t S U1 f1 U2 svl1 svl2 s0) = []
  · have silent' : titems_for k T = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr (fun x hx => ?_)
      have hx' := (sets x).mp hx
      rw [silent] at hx'
      cases hx'
    have e1 : evs_for k (T.map Prod.snd) = [] := by
      rw [evs_for_map_snd, silent']
      rfl
    have e2 : evs_for k (inter S U1 f1 U2 svl1 svl2 s0) = [] := by
      rw [inter, evs_for_map_snd, silent]
      rfl
    rw [state_after_no_events e1 D, state_after_no_events e2 D]
  · have Tk_ne : titems_for k T ≠ [] := by
      intro h
      apply silent
      refine List.eq_nil_iff_forall_not_mem.mpr (fun x hx => ?_)
      have hx' := (sets x).mpr hx
      rw [h] at hx'
      cases hx'
    have Tk_item : ∀ x ∈ titems_for k T,
        x ∈ inter_t S U1 f1 U2 svl1 svl2 s0 ∧ x.2.key = k := by
      intro x hx
      obtain ⟨h1, h2⟩ := List.mem_filter.mp ((sets x).mp hx)
      exact ⟨h1, of_decide_eq_true h2⟩
    have keyed : ∀ x ∈ titems_for k T, x.2.key = k := fun x hx => (Tk_item x hx).2
    have honest : ∀ x ∈ titems_for k T, x.2.img = state_after σ0 (S.log.take x.1) k := by
      intro x hx
      have h := H.inter_item_honest hsvl1 hsvl2 (Tk_item x hx).1
      rw [(Tk_item x hx).2] at h
      exact h
    have sorted : List.Pairwise (· ≤ ·) ((titems_for k T).map Prod.fst) :=
      sorted_map_fst_filter T_sorted
    have low : ∀ x ∈ titems_for k T, S.den s0 ≤ x.1 :=
      fun x hx => (inter_t_tag_bounds s0f1 (Tk_item x hx).1).1
    have high : ∀ x ∈ titems_for k T, x.1 ≤ S.den f1 :=
      fun x hx => (inter_t_tag_bounds s0f1 (Tk_item x hx).1).2
    have complete : ∀ p, S.den s0 ≤ p → p < S.den f1 → ∀ hp : p < S.log.length,
        (S.log[p]'hp).key = k → (p + 1, S.log[p]'hp) ∈ titems_for k T :=
      fun _ h1 h2 _ key => (sets _).mpr (inter_key_complete h1 h2 key)
    have T_self : titems_for k (titems_for k T) = titems_for k T :=
      List.filter_eq_self.mpr (fun x hx => decide_eq_true (keyed x hx))
    have evs : evs_for k (T.map Prod.snd) = evs_for k ((titems_for k T).map Prod.snd) := by
      rw [evs_for_map_snd, evs_for_map_snd, T_self]
    rw [replay_per_key evs D, honest_stream_last Tk_ne keyed honest sorted low high complete D,
      H.inter_key_replay hsvl1 hsvl2 s0f1 silent D]
    rfl

/-- Safety for any stream in position order with the same items as
`inter_t`, however it breaks ties at each position. Isabelle:
`pass_with_request_safe_any`. -/
theorem pass_with_request_safe_any {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    {T : List (Nat × Event K V)}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0lo2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.lo)
    (T_set : ∀ x, x ∈ T ↔ x ∈ inter_t S U1 f1 U2 svl1 svl2 s0)
    (T_sorted : List.Pairwise (· ≤ ·) (T.map Prod.fst))
    {k : K} (hk : sc1 k ∨ sc2 k) (D0 : State K V) :
    state_after D0 (T.map Prod.snd) k = state_after σ0 (S.pfx f1) k ∨
      (state_after D0 (T.map Prod.snd) k = D0 k ∧
        state_after σ0 (S.pfx f1) k = none ∧
        (sc1 k → k ∉ svl1 (the_unit U1 f1 k)) ∧
        (sc2 k → k ∉ svl2 (the_unit U2 f1 k)) ∧
        evs_for k (S.win s0 f1) = []) := by
  have s0f1 := H.s0_le_f1_of_key s0lo s0lo2 hk
  rw [H.inter_any_same_replay hsvl1 hsvl2 s0f1 T_set T_sorted D0 k]
  exact H.pass_with_request_safe hsvl1 hsvl2 s0lo s0lo2 hk D0

/-- Convergence for any stream in position order with the same items
as `inter_t`. Isabelle: `pass_with_request_converges_any`. -/
theorem pass_with_request_converges_any {svl1 svl2 : CUnit K V C → List K} {s0 : C}
    {T : List (Nat × Event K V)} {D0 : State K V}
    (hsvl1 : svl_ok2 S U1 svl1) (hsvl2 : svl_ok2 S U2 svl2)
    (s0lo : ∀ u ∈ U1, S.den s0 ≤ S.den u.lo)
    (s0lo2 : ∀ u ∈ U2, S.den s0 ≤ S.den u.lo)
    (T_set : ∀ x, x ∈ T ↔ x ∈ inter_t S U1 f1 U2 svl1 svl2 s0)
    (T_sorted : List.Pairwise (· ≤ ·) (T.map Prod.fst))
    (cover : ∀ k, (sc1 k ∨ sc2 k) → D0 k ≠ none →
      state_after σ0 (S.pfx f1) k = none → evs_for k (S.win s0 f1) = [] →
      (sc1 k ∧ k ∈ svl1 (the_unit U1 f1 k)) ∨
        (sc2 k ∧ k ∈ svl2 (the_unit U2 f1 k))) :
    ∀ k, (sc1 k ∨ sc2 k) →
      state_after D0 (T.map Prod.snd) k = state_after σ0 (S.pfx f1) k := by
  intro k hk
  have s0f1 := H.s0_le_f1_of_key s0lo s0lo2 hk
  rw [H.inter_any_same_replay hsvl1 hsvl2 s0f1 T_set T_sorted D0 k]
  exact H.pass_with_request_converges hsvl1 hsvl2 s0lo s0lo2 cover k hk

end PassWithRequest

end

end DBLogContract
