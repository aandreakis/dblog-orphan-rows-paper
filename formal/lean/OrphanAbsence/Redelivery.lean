import OrphanAbsence.Replay

/-!
# Re-delivery: repeated items and in-order at-least-once delivery

This file ports the general part of `Orphan_Absence_Replay.thy` from
the Isabelle session `Orphan_Absence`. The fixtures of that theory are
ported in `RedeliveryWitnesses.lean`. The module name `Replay` is
taken by the replay results of `Orphan_Absence.thy`, so this port is
called `Redelivery`.

The model applies an emitted stream once, in order. A real pipeline
delivers at least once. A reader that restarts resumes from an earlier
position of the same stream and applies some items again. This can
happen at every hop between the connector and the sink. The results:

* Idempotence: re-applying any suffix of an applied stream, re-applying
  a stream from any earlier prefix, and repeating a block or a single
  event in place leave the replayed state unchanged
  (`replay_suffix_idempotent`, `replay_from_prefix`,
  `repeat_block_noop`, `duplicate_in_place_noop`,
  `repeat_in_place_noop`, `close_block_reapply_noop`).
* A re-emitted absence entry is a no-op when the stream's last event
  for the key is a delete, or when the stream has no event for the key
  and the initial sink state does not hold it (`absence_reemit_noop`).
* An in-order at-least-once reader is modeled by its cursor over the
  stream (`reads_from`, `at_least_once`). A finite chain of such
  readers is a redelivery (`redelivered`). Whatever such a chain
  delivers replays to the same state as the stream itself
  (`at_least_once_replay`, `redelivered_replay`).
* Transfer: the safety and convergence theorems hold for every
  redelivery of the emission, and in a per-key form for every stream
  whose events for a key form a redelivery of the emission's events
  for that key. A keyed topic with several partitions yields such
  streams (`partitioned_delivery_per_key`).

Transport, recorded with the conventions of `VERIFICATION.md`:

* The theory names its delivered stream `S`. Here it is `Sq`, since
  `S` names the coordinate space.
* `suffix zs xs` and `prefix ys xs` are the core relations
  `zs <:+ xs` and `ys <+: xs`. Both state the same existential as the
  library definitions of HOL.
* HOL's `rtranclp` has no counterpart in the core library of Lean. It
  is defined here as `rtranclp`, with the same two rules.
* `filter P` takes `P : α → Bool`, the type of Lean's `List.filter`.
* HOL's `last`, `hd` and `xs ! 0` are total. Here they are `getLast`,
  `head` and bounded `getElem` with their nonemptiness proofs.
-/

namespace DBLogContract

universe u v w x y

attribute [local instance] Classical.propDecidable

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-! ## Re-applying a suffix, or restarting after an applied prefix, changes nothing -/

/-- Port-local. A stream with an event for a key decides that key,
whatever state it is applied to. -/
private theorem state_after_indep {k : K} {Q : List (Event K V)}
    (h : evs_for k Q ≠ []) (σ σ' : State K V) :
    state_after σ Q k = state_after σ' Q k := by
  rw [state_after_last_event h σ, state_after_last_event h σ']

/-- A consumer that has applied a stream and then receives any suffix
of it again, in order, ends in the state it was in. Isabelle:
`replay_suffix_idempotent`. -/
theorem replay_suffix_idempotent {zs xs : List (Event K V)}
    (h : zs <:+ xs) (D : State K V) :
    state_after (state_after D xs) zs = state_after D xs := by
  obtain ⟨ys, rfl⟩ := h
  funext k
  by_cases hz : evs_for k zs = []
  · exact state_after_no_events hz _
  · rw [state_after_indep hz (state_after D (ys ++ zs)) (state_after D ys),
      ← state_after_append]

/-- A block applied twice in a row ends in the state of one
application. Isabelle: `replay_block_twice`. -/
theorem replay_block_twice (D : State K V) (bs : List (Event K V)) :
    state_after (state_after D bs) bs = state_after D bs :=
  replay_suffix_idempotent (List.suffix_refl bs) D

/-- A consumer that has applied a prefix of the stream, restarts from
the beginning and applies the whole stream ends in the state of a
single application. Isabelle: `replay_from_prefix`. -/
theorem replay_from_prefix {ys xs : List (Event K V)}
    (h : ys <+: xs) (D : State K V) :
    state_after (state_after D ys) xs = state_after D xs := by
  obtain ⟨ws, rfl⟩ := h
  rw [state_after_append, replay_block_twice, ← state_after_append]

/-! ## Repetitions in place change nothing -/

/-- A block delivered twice in a row, anywhere in the stream, changes
nothing. Isabelle: `repeat_block_noop`. -/
theorem repeat_block_noop (D : State K V) (xs bs zs : List (Event K V)) :
    state_after D (xs ++ (bs ++ (bs ++ zs))) =
      state_after D (xs ++ (bs ++ zs)) := by
  simp only [state_after_append, replay_block_twice]

/-- A single event delivered twice in a row changes nothing.
Isabelle: `duplicate_in_place_noop`. -/
theorem duplicate_in_place_noop (D : State K V) (xs : List (Event K V))
    (e : Event K V) (zs : List (Event K V)) :
    state_after D (xs ++ e :: e :: zs) = state_after D (xs ++ e :: zs) :=
  repeat_block_noop D xs [e] zs

/-- A single event delivered any positive number of times in a row
changes nothing. Isabelle: `repeat_in_place_noop`. -/
theorem repeat_in_place_noop (D : State K V) (xs : List (Event K V))
    (n : Nat) (e : Event K V) (zs : List (Event K V)) :
    state_after D (xs ++ (List.replicate (n + 1) e ++ zs)) =
      state_after D (xs ++ e :: zs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc state_after D (xs ++ (List.replicate (n + 1 + 1) e ++ zs))
        = state_after D (xs ++ e :: e :: (List.replicate n e ++ zs)) := rfl
      _ = state_after D (xs ++ e :: (List.replicate n e ++ zs)) :=
          duplicate_in_place_noop D xs e _
      _ = state_after D (xs ++ (List.replicate (n + 1) e ++ zs)) := rfl
      _ = state_after D (xs ++ e :: zs) := ih

/-- A unit's close block re-applied right after itself, anywhere in a
stream, changes nothing. It needs neither an admissible enumeration
nor distinct keys. Isabelle: `close_block_reapply_noop`, stated in the
context `capture_plan`, whose denotation is the space `S`. -/
theorem close_block_reapply_noop (S : CoordinateSpace K V C)
    (svl : CUnit K V C → List K) (u : CUnit K V C) (D : State K V)
    (xs zs : List (Event K V)) :
    state_after D (xs ++ ((close_block S svl u).map Prod.snd ++
      ((close_block S svl u).map Prod.snd ++ zs))) =
      state_after D (xs ++ ((close_block S svl u).map Prod.snd ++ zs)) :=
  repeat_block_noop D xs _ zs

/-! ## A re-emitted absence entry is a no-op -/

/-- A delete for a key the sink does not hold leaves the sink as it
is. Isabelle: `delete_absent_noop`. -/
theorem delete_absent_noop {D : State K V} {k : K} (h : D k = none) :
    state_after D [(⟨k, none⟩ : Event K V)] = D := by
  funext k'
  show apply_ev D ⟨k, none⟩ k' = D k'
  simp only [apply_ev]
  by_cases hk : k' = k
  · rw [if_pos hk, hk, h]
  · rw [if_neg hk]

/-- A delete for a key the sink does not hold at that point of a
stream leaves the rest of the replay as it is. Isabelle:
`delete_absent_in_stream_noop`. -/
theorem delete_absent_in_stream_noop {D : State K V}
    {xs : List (Event K V)} {k : K}
    (absent : state_after D xs k = none) (zs : List (Event K V)) :
    state_after D (xs ++ (⟨k, none⟩ : Event K V) :: zs) =
      state_after D (xs ++ zs) := by
  calc state_after D (xs ++ (⟨k, none⟩ : Event K V) :: zs)
      = state_after (state_after (state_after D xs)
          [(⟨k, none⟩ : Event K V)]) zs := by
        rw [state_after_append]
        rfl
    _ = state_after (state_after D xs) zs := by
        rw [delete_absent_noop absent]
    _ = state_after D (xs ++ zs) := (state_after_append D xs zs).symm

/-- Appending an absence entry for `k` changes nothing when the
stream's last event for `k` is a delete, or when the stream has no
event for `k` and the initial sink state does not hold `k`. The first
alternative carries the nonemptiness proof that `getLast` needs.
Isabelle: `absence_reemit_noop`. -/
theorem absence_reemit_noop {k : K} {Sq : List (Event K V)}
    {D0 : State K V}
    (h : (∃ hne : evs_for k Sq ≠ [], ((evs_for k Sq).getLast hne).img = none) ∨
      (evs_for k Sq = [] ∧ D0 k = none)) :
    state_after D0 (Sq ++ [(⟨k, none⟩ : Event K V)]) = state_after D0 Sq := by
  have absent : state_after D0 Sq k = none := by
    rcases h with ⟨hne, himg⟩ | ⟨hnil, hD⟩
    · rw [state_after_last_event hne D0]
      exact himg
    · rw [state_after_no_events hnil D0]
      exact hD
  have h2 := delete_absent_in_stream_noop absent []
  rw [List.append_nil] at h2
  exact h2

/-! ## In-order at-least-once delivery -/

/-- A reader of the stream `xs` whose cursor is at a position delivers
a list of items until it stops. Isabelle: inductive `reads_from`, with
the stream as its fixed parameter. -/
inductive reads_from {α : Type x} (xs : List α) : Nat → List α → Prop where
  /-- At the end of the stream the reader stops and delivers nothing.
  Isabelle: rule `finish`. -/
  | finish : reads_from xs xs.length []
  /-- The reader reads the item at the cursor and advances. Isabelle:
  rule `advance`. -/
  | advance {c : Nat} {ys : List α} (hc : c < xs.length) :
      reads_from xs (c + 1) ys → reads_from xs c (xs[c] :: ys)
  /-- The reader rewinds the cursor to an earlier position, or to the
  cursor itself. Isabelle: rule `rewind`. -/
  | rewind {c' c : Nat} {ys : List α} :
      c' ≤ c → reads_from xs c' ys → reads_from xs c ys

/-- An at-least-once delivery of `xs`: what a reader delivers from
position 0. Isabelle: `at_least_once`. -/
def at_least_once {α : Type x} (xs ys : List α) : Prop :=
  reads_from xs 0 ys

/-- The reflexive transitive closure of a relation, with the two rules
of HOL's `rtranclp`. Port-local. The core library of Lean has no such
closure. The first argument is a fixed parameter, as in HOL's
induction rule `rtranclp_induct`. -/
inductive rtranclp {α : Type x} (r : α → α → Prop) (a : α) : α → Prop where
  /-- Isabelle: rule `rtrancl_refl` of `rtranclp`. -/
  | rtrancl_refl : rtranclp r a a
  /-- Isabelle: rule `rtrancl_into_rtrancl` of `rtranclp`. -/
  | rtrancl_into_rtrancl {b c : α} : rtranclp r a b → r b c → rtranclp r a c

/-- Multi-hop delivery: the end of any finite chain of at-least-once
hops, the empty chain included. Isabelle: `redelivered`, defined there
as `at_least_once⇧*⇧*`. -/
def redelivered {α : Type x} : List α → List α → Prop :=
  rtranclp at_least_once

/-! ### The delivery class contains the expected streams -/

/-- Reading straight ahead from `i` to `j` delivers the segment between
them, in order. Isabelle: `reads_from_forward`. -/
theorem reads_from_forward {α : Type x} {xs : List α} {j : Nat}
    {ys : List α} (rd : reads_from xs j ys) {i : Nat} (ij : i ≤ j)
    (jn : j ≤ xs.length) :
    reads_from xs i (List.take (j - i) (List.drop i xs) ++ ys) := by
  obtain ⟨d, hd⟩ : ∃ d, j - i = d := ⟨_, rfl⟩
  induction d generalizing i with
  | zero =>
    have hij : i = j := by omega
    subst hij
    rw [Nat.sub_self, List.take_zero, List.nil_append]
    exact rd
  | succ d ih =>
    have i_lt : i < xs.length := by omega
    have h1 := ih (i := i + 1) (by omega) (by omega)
    have h2 := reads_from.advance i_lt h1
    have hd' : j - (i + 1) = d := by omega
    rw [hd'] at h2
    rw [List.drop_eq_getElem_cons i_lt, hd, List.take_succ_cons,
      List.cons_append]
    exact h2

/-- Reading straight ahead from `i` to the end delivers the rest of the
stream. Isabelle: `reads_from_drop`. -/
theorem reads_from_drop {α : Type x} {xs : List α} {i : Nat}
    (h : i ≤ xs.length) : reads_from xs i (List.drop i xs) := by
  have h1 := reads_from_forward (reads_from.finish (xs := xs)) h (Nat.le_refl _)
  rw [List.append_nil, List.take_of_length_le (by simp)] at h1
  exact h1

/-- The stream itself is an at-least-once delivery of it. Isabelle:
`at_least_once_refl`. -/
theorem at_least_once_refl {α : Type x} (xs : List α) :
    at_least_once xs xs := by
  have h1 := reads_from_drop (xs := xs) (Nat.zero_le _)
  rw [List.drop_zero] at h1
  exact h1

/-- The basic restart: the reader has applied the first `j` items,
rewinds to an earlier position `i` and reads from there to the end.
Isabelle: `at_least_once_rewind_once`. -/
theorem at_least_once_rewind_once {α : Type x} {xs : List α} {i j : Nat}
    (ij : i ≤ j) (jn : j ≤ xs.length) :
    at_least_once xs (List.take j xs ++ List.drop i xs) := by
  have h1 : reads_from xs i (List.drop i xs) := reads_from_drop (by omega)
  have h2 : reads_from xs j (List.drop i xs) := reads_from.rewind ij h1
  have h3 := reads_from_forward h2 (Nat.zero_le j) jn
  rw [Nat.sub_zero, List.drop_zero] at h3
  exact h3

/-- A consumer that applied a prefix `ws` and restarts from any
position inside it. Isabelle: `at_least_once_restart`. -/
theorem at_least_once_restart {α : Type x} {ws xs : List α} {i : Nat}
    (pre : ws <+: xs) (hi : i ≤ ws.length) :
    at_least_once xs (ws ++ List.drop i xs) := by
  have hws : List.take ws.length xs = ws :=
    (List.prefix_iff_eq_take.mp pre).symm
  have h1 := at_least_once_rewind_once hi pre.length_le
  rw [hws] at h1
  exact h1

/-- A re-delivery of a suffix at the end. Isabelle:
`at_least_once_suffix`. -/
theorem at_least_once_suffix {α : Type x} (xs : List α) (i : Nat) :
    at_least_once xs (xs ++ List.drop i xs) := by
  by_cases h : i ≤ xs.length
  · have h1 := at_least_once_rewind_once h (Nat.le_refl _)
    rw [List.take_length] at h1
    exact h1
  · rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
    exact at_least_once_refl xs

/-- A block delivered twice in a row. Isabelle:
`at_least_once_block_dup`. -/
theorem at_least_once_block_dup {α : Type x} (xs bs zs : List α) :
    at_least_once (xs ++ (bs ++ zs)) (xs ++ (bs ++ (bs ++ zs))) := by
  have h1 := at_least_once_rewind_once (xs := xs ++ (bs ++ zs))
    (i := xs.length) (j := xs.length + bs.length) (by omega) (by simp)
  have ht : List.take (xs.length + bs.length) (xs ++ (bs ++ zs)) = xs ++ bs := by
    rw [List.take_add, List.take_left, List.drop_left, List.take_left]
  rw [ht, List.drop_left, List.append_assoc] at h1
  exact h1

/-- A single event delivered twice in a row. Isabelle:
`at_least_once_dup_in_place`. -/
theorem at_least_once_dup_in_place {α : Type x} (xs : List α) (e : α)
    (zs : List α) :
    at_least_once (xs ++ e :: zs) (xs ++ e :: e :: zs) :=
  at_least_once_block_dup xs [e] zs

/-- The empty chain of hops. Isabelle: `redelivered_refl`. -/
theorem redelivered_refl {α : Type x} (xs : List α) : redelivered xs xs :=
  rtranclp.rtrancl_refl

/-- One more hop. Isabelle: `redelivered_hop`. -/
theorem redelivered_hop {α : Type x} {xs ys zs : List α}
    (h1 : redelivered xs ys) (h2 : at_least_once ys zs) :
    redelivered xs zs :=
  rtranclp.rtrancl_into_rtrancl h1 h2

/-- A further hop may deliver a block twice in a row. Isabelle:
`redelivered_block_dup`. -/
theorem redelivered_block_dup {α : Type x} {xs ys bs zs : List α}
    (h : redelivered xs (ys ++ (bs ++ zs))) :
    redelivered xs (ys ++ (bs ++ (bs ++ zs))) :=
  redelivered_hop h (at_least_once_block_dup ys bs zs)

/-- A further hop may deliver an event twice in a row. Isabelle:
`redelivered_dup_in_place`. -/
theorem redelivered_dup_in_place {α : Type x} {xs ys : List α} {e : α}
    {zs : List α} (h : redelivered xs (ys ++ e :: zs)) :
    redelivered xs (ys ++ e :: e :: zs) :=
  redelivered_hop h (at_least_once_dup_in_place ys e zs)

/-- A further hop may deliver a suffix again at the end. Isabelle:
`redelivered_suffix`. -/
theorem redelivered_suffix {α : Type x} {xs ys : List α}
    (h : redelivered xs ys) (i : Nat) :
    redelivered xs (ys ++ List.drop i ys) :=
  redelivered_hop h (at_least_once_suffix ys i)

/-! ### Every delivery replays to the same state -/

/-- The invariant of a reader at cursor `c` whose sink is in state
`σ`: every key either holds the value that the first `c` items give
it, replayed from `D`, or the stream still has an event for the key at
or after the cursor. Isabelle: `settled`. -/
def settled (D : State K V) (xs : List (Event K V)) (c : Nat)
    (σ : State K V) : Prop :=
  ∀ k, σ k = state_after D (List.take c xs) k ∨
    evs_for k (List.drop c xs) ≠ []

/-- Isabelle: `state_after_Cons`. The core port states the same fact as
`state_after_cons`. -/
theorem state_after_Cons (σ : State K V) (e : Event K V)
    (P : List (Event K V)) :
    state_after σ (e :: P) = state_after (apply_ev σ e) P :=
  rfl

/-- The invariant holds at the start. Isabelle: `settled_start`. -/
theorem settled_start (D : State K V) (xs : List (Event K V)) :
    settled D xs 0 D :=
  fun _ => Or.inl rfl

/-- At the end of the stream the invariant gives the replay of the
whole stream. Isabelle: `settled_finish`. -/
theorem settled_finish {D : State K V} {xs : List (Event K V)}
    {σ : State K V} (h : settled D xs xs.length σ) :
    σ = state_after D xs := by
  funext k
  rcases h k with h1 | h1
  · rw [List.take_length] at h1
    exact h1
  · rw [List.drop_length, evs_for_nil] at h1
    exact absurd rfl h1

/-- Reading ahead keeps the invariant. Isabelle: `settled_advance`. -/
theorem settled_advance {D : State K V} {xs : List (Event K V)} {c : Nat}
    {σ : State K V} (hc : c < xs.length) (st : settled D xs c σ) :
    settled D xs (c + 1) (apply_ev σ xs[c]) := by
  intro k
  have tk : List.take (c + 1) xs = List.take c xs ++ [xs[c]] :=
    List.take_succ_eq_append_getElem hc
  have dr : List.drop c xs = xs[c] :: List.drop (c + 1) xs :=
    List.drop_eq_getElem_cons hc
  by_cases hk : xs[c].key = k
  · left
    rw [tk, state_after_snoc]
    simp only [apply_ev]
    rw [if_pos hk.symm, if_pos hk.symm]
  · have same : apply_ev σ xs[c] k = σ k := by
      simp only [apply_ev]
      rw [if_neg (Ne.symm hk)]
    have src : state_after D (List.take (c + 1) xs) k =
        state_after D (List.take c xs) k := by
      rw [tk, state_after_snoc]
      simp only [apply_ev]
      rw [if_neg (Ne.symm hk)]
    have log : evs_for k (List.drop (c + 1) xs) = evs_for k (List.drop c xs) := by
      rw [dr, evs_for_cons, if_neg hk]
    rw [same, src, log]
    exact st k

/-- Rewinding keeps the invariant. Isabelle: `settled_rewind`. -/
theorem settled_rewind {D : State K V} {xs : List (Event K V)}
    {c' c : Nat} {σ : State K V} (le : c' ≤ c) (st : settled D xs c σ) :
    settled D xs c' σ := by
  intro k
  have tk : List.take c xs =
      List.take c' xs ++ List.take (c - c') (List.drop c' xs) := by
    have h1 := List.take_add (l := xs) (i := c') (j := c - c')
    rw [Nat.add_sub_cancel' le] at h1
    exact h1
  have dr : List.drop c' xs =
      List.take (c - c') (List.drop c' xs) ++ List.drop c xs := by
    have shift : List.drop c xs = List.drop (c - c') (List.drop c' xs) := by
      rw [List.drop_drop, Nat.add_sub_cancel' le]
    rw [shift, List.take_append_drop]
  by_cases hq : evs_for k (List.drop c' xs) = []
  · rw [dr, evs_for_append] at hq
    obtain ⟨quiet_W, quiet_rest⟩ := List.append_eq_nil_iff.mp hq
    left
    rcases st k with h | h
    · rw [h, tk, state_after_append_no_k quiet_W]
    · exact absurd quiet_rest h
  · exact Or.inr hq

/-- Whatever a reader delivers from a settled state replays to the
state of the whole stream. Isabelle: `reads_from_replay`. -/
theorem reads_from_replay {D : State K V} {xs : List (Event K V)} {c : Nat}
    {ys : List (Event K V)} {σ : State K V} (h : reads_from xs c ys)
    (st : settled D xs c σ) :
    state_after σ ys = state_after D xs := by
  induction h generalizing σ with
  | finish =>
    rw [state_after_nil]
    exact settled_finish st
  | advance hc _ ih =>
    rw [state_after_Cons]
    exact ih (settled_advance hc st)
  | rewind hle _ ih =>
    exact ih (settled_rewind hle st)

/-- Every at-least-once delivery replays to the same state as the
stream, from every initial state. Isabelle: `at_least_once_replay`. -/
theorem at_least_once_replay {xs ys : List (Event K V)}
    (h : at_least_once xs ys) (D : State K V) :
    state_after D ys = state_after D xs :=
  reads_from_replay h (settled_start D xs)

/-- Every redelivery replays to the same state as the stream, from
every initial state. Isabelle: `redelivered_replay`. -/
theorem redelivered_replay {xs ys : List (Event K V)}
    (h : redelivered xs ys) (D : State K V) :
    state_after D ys = state_after D xs := by
  change rtranclp at_least_once xs ys at h
  induction h with
  | rtrancl_refl => rfl
  | rtrancl_into_rtrancl _ hstep ih =>
    rw [at_least_once_replay hstep D, ih]

/-! ## Transfer of the safety and convergence results -/

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

/-- Safety for every redelivery of the emission: each scoped key ends
at the canonical replay value or is a surviving orphan. Isabelle:
`absent_replay_safe_at_least_once`. -/
theorem absent_replay_safe_at_least_once {svl : CUnit K V C → List K}
    {s0 : C} {Sq : List (Event K V)}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k)
    (red : redelivered (emission S units f svl s0) Sq) (D0 : State K V) :
    state_after D0 Sq k = sink_at S units f f k ∨
      (state_after D0 Sq k = D0 k ∧
        sink_at S units f f k = none ∧
        absent_untouched S (the_unit units f k) k ∧
        k ∉ svl (the_unit units f k) ∧
        evs_for k (S.win s0 f) = []) := by
  rw [redelivered_replay red D0]
  exact H.absent_replay_safe hsvl hs0 hk D0

/-- Convergence for every redelivery of the emission: under coverage
every scoped key ends at the source state at the frontier. Isabelle:
`self_stabilization_at_least_once`. -/
theorem self_stabilization_at_least_once {svl : CUnit K V C → List K}
    {s0 : C} {D0 : State K V} {Sq : List (Event K V)}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    (cov : covers S units f svl D0 s0)
    (red : redelivered (emission S units f svl s0) Sq) :
    ∀ k, scope k → state_after D0 Sq k = state_after σ0 (S.pfx f) k := by
  rw [redelivered_replay red D0]
  exact H.self_stabilization hsvl hs0 cov

end CaptureContract

/-! ## Per-key delivery -/

/-- Selecting a key's events twice selects them once. Isabelle:
`evs_for_idem`. -/
theorem evs_for_idem (k : K) (P : List (Event K V)) :
    evs_for k (evs_for k P) = evs_for k P := by
  simp [evs_for, List.filter_filter]

/-- A stream whose events for a key form a redelivery of another
stream's events for that key replays to the same value at that key.
Isabelle: `redelivered_key_replay`. -/
theorem redelivered_key_replay {k : K} {E Sq : List (Event K V)}
    (h : redelivered (evs_for k E) (evs_for k Sq)) (D : State K V) :
    state_after D Sq k = state_after D E k :=
  calc state_after D Sq k = state_after D (evs_for k Sq) k :=
        replay_per_key (evs_for_idem k Sq).symm D
    _ = state_after D (evs_for k E) k := congrFun (redelivered_replay h D) k
    _ = state_after D E k := replay_per_key (evs_for_idem k E) D

/-- The per-key hypothesis for every key gives the same replay.
Isabelle: `redelivered_per_key_replay`. -/
theorem redelivered_per_key_replay {E Sq : List (Event K V)}
    (per_key : ∀ k, redelivered (evs_for k E) (evs_for k Sq))
    (D : State K V) :
    state_after D Sq = state_after D E :=
  funext fun k => redelivered_key_replay (per_key k) D

/-! ### Filtering a delivery, and partitioned topics -/

/-- The number of kept items before the cursor grows with the cursor.
Isabelle: `length_filter_take_mono`. -/
theorem length_filter_take_mono {α : Type x} (P : α → Bool) (xs : List α)
    {c' c : Nat} (h : c' ≤ c) :
    (List.filter P (List.take c' xs)).length ≤
      (List.filter P (List.take c xs)).length := by
  have htk : List.take c xs =
      List.take c' xs ++ List.take (c - c') (List.drop c' xs) := by
    have h1 := List.take_add (l := xs) (i := c') (j := c - c')
    rw [Nat.add_sub_cancel' h] at h1
    exact h1
  rw [htk, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

/-- Filtering a delivery by a predicate on items gives a delivery of the
filtered stream, from the number of kept items before the cursor.
Isabelle: `reads_from_filter`. -/
theorem reads_from_filter {α : Type x} (P : α → Bool) {xs : List α}
    {c : Nat} {ys : List α} (h : reads_from xs c ys) :
    reads_from (List.filter P xs) (List.filter P (List.take c xs)).length
      (List.filter P ys) := by
  induction h with
  | finish =>
    rw [List.take_length, List.filter_nil]
    exact reads_from.finish
  | @advance c ys hc _ ih =>
    rw [List.take_succ_eq_append_getElem hc, List.filter_append] at ih
    by_cases hP : P xs[c] = true
    · rw [List.filter_cons_of_pos hP, List.filter_nil, List.length_append,
        List.length_singleton] at ih
      have split : List.filter P xs = List.filter P (List.take c xs) ++
          xs[c] :: List.filter P (List.drop (c + 1) xs) := by
        conv => lhs; rw [← List.take_append_drop c xs, List.drop_eq_getElem_cons hc]
        rw [List.filter_append, List.filter_cons_of_pos hP]
      have m_lt : (List.filter P (List.take c xs)).length <
          (List.filter P xs).length := by
        rw [split, List.length_append, List.length_cons]
        omega
      have nth : (List.filter P xs)[(List.filter P (List.take c xs)).length]'m_lt
          = xs[c] := by
        have key : ∀ (L l1 l2 : List α) (a : α), L = l1 ++ a :: l2 →
            ∀ (hl : l1.length < L.length), L[l1.length]'hl = a := by
          intro L l1 l2 a hL hl
          subst hL
          simp
        exact key _ _ _ _ split m_lt
      have h2 := reads_from.advance m_lt ih
      rw [nth] at h2
      rw [List.filter_cons_of_pos hP]
      exact h2
    · rw [List.filter_cons_of_neg hP, List.filter_nil, List.append_nil] at ih
      rw [List.filter_cons_of_neg hP]
      exact ih
  | rewind hle _ ih =>
    exact reads_from.rewind (length_filter_take_mono P xs hle) ih

/-- Filtering an at-least-once delivery gives an at-least-once delivery
of the filtered stream. Isabelle: `at_least_once_filter`. -/
theorem at_least_once_filter {α : Type x} (P : α → Bool) {xs ys : List α}
    (h : at_least_once xs ys) :
    at_least_once (List.filter P xs) (List.filter P ys) := by
  have h1 := reads_from_filter P h
  rw [List.take_zero, List.filter_nil, List.length_nil] at h1
  exact h1

/-- Filtering a redelivery gives a redelivery of the filtered stream.
Isabelle: `redelivered_filter`. -/
theorem redelivered_filter {α : Type x} (P : α → Bool) {xs ys : List α}
    (h : redelivered xs ys) :
    redelivered (List.filter P xs) (List.filter P ys) := by
  change rtranclp at_least_once xs ys at h
  induction h with
  | rtrancl_refl => exact redelivered_refl _
  | rtrancl_into_rtrancl _ hstep ih =>
    exact redelivered_hop ih (at_least_once_filter P hstep)

/-- A key's events of a redelivery form a redelivery of the key's
events of the stream. Isabelle: `redelivered_evs_for`. -/
theorem redelivered_evs_for {xs ys : List (Event K V)} (k : K)
    (h : redelivered xs ys) :
    redelivered (evs_for k xs) (evs_for k ys) :=
  redelivered_filter (fun e : Event K V => decide (e.key = k)) h

/-- A partitioned topic yields the per-key hypothesis. The map `part`
assigns every key its partition, partition `p` carries the stream's
events for its keys, and `T p` is a redelivery of it. When the sink's
events for every key are that key's events in its own partition's
delivery, every key's events form a redelivery of the stream's events
for that key. Isabelle: `partitioned_delivery_per_key`. -/
theorem partitioned_delivery_per_key {ι : Type y} {part : K → ι}
    {E Sq : List (Event K V)} {T : ι → List (Event K V)}
    (parts : ∀ p, redelivered (List.filter (fun e => decide (part e.key = p)) E) (T p))
    (interleave : ∀ k', evs_for k' Sq = evs_for k' (T (part k'))) (k : K) :
    redelivered (evs_for k E) (evs_for k Sq) := by
  have own : evs_for k (List.filter (fun e => decide (part e.key = part k)) E) =
      evs_for k E := by
    simp only [evs_for, List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases he : e.key = k
    · simp [he]
    · simp [he]
  have h := redelivered_evs_for k (parts (part k))
  rw [own, ← interleave k] at h
  exact h

/-- A reader that delivers nothing is at or beyond the end of the
stream. Isabelle: `reads_from_empty_end`. -/
theorem reads_from_empty_end {α : Type x} {xs : List α} {c : Nat}
    {ys : List α} : reads_from xs c ys → ys = [] → xs.length ≤ c := by
  intro h
  induction h with
  | finish => intro _; exact Nat.le_refl _
  | advance _ _ _ => intro h; exact absurd h (List.cons_ne_nil _ _)
  | rewind hle _ ih => intro h; exact Nat.le_trans (ih h) hle

/-- Port-local. A reader that delivers something reads a nonempty
stream. It supplies the nonemptiness proofs in the statements of
`reads_from_last` and `reads_from_hd`. Isabelle: the same fact is
`reads_from_nonempty`, stated after them. -/
theorem reads_from_ne {α : Type x} {xs : List α} {c : Nat}
    {ys : List α} : reads_from xs c ys → ys ≠ [] → xs ≠ [] := by
  intro h
  induction h with
  | finish => intro hne; exact absurd rfl hne
  | advance hc _ _ =>
    intro _ hx
    subst hx
    exact absurd hc (Nat.not_lt_zero _)
  | rewind _ _ ih => exact ih

/-- A reader that delivers something ends with the stream's last item.
Isabelle: `reads_from_last`, with HOL's total `last` of the stream as
`getLast` with its nonemptiness proof. -/
theorem reads_from_last {α : Type x} {xs : List α} {c : Nat}
    {ys : List α} :
    ∀ (h : reads_from xs c ys) (hne : ys ≠ []),
      ys.getLast hne = xs.getLast (reads_from_ne h hne) := by
  intro h
  induction h with
  | finish => intro hne; exact absurd rfl hne
  | @advance c ys hc hrd ih =>
    intro hne
    by_cases hys : ys = []
    · subst hys
      have hle := reads_from_empty_end hrd rfl
      have hc' : c = xs.length - 1 := by omega
      rw [List.getLast_singleton, List.getLast_eq_getElem]
      subst hc'
      rfl
    · rw [List.getLast_cons hys]
      exact ih hys
  | rewind _ _ ih => intro hne; exact ih hne

/-- A reader that starts at position 0 and delivers something starts
with the stream's first item. Isabelle: `reads_from_hd`, with HOL's
total `xs ! 0` as bounded `getElem` with its bound proof. -/
theorem reads_from_hd {α : Type x} {xs : List α} {c : Nat}
    {ys : List α} :
    ∀ (h : reads_from xs c ys), c = 0 → ∀ (hne : ys ≠ []),
      ys.head hne = xs[0]'(List.length_pos_iff.mpr (reads_from_ne h hne)) := by
  intro h
  induction h with
  | finish => intro _ hne; exact absurd rfl hne
  | @advance c ys hc _ _ =>
    intro hc0 _
    subst hc0
    rfl
  | rewind hle _ ih =>
    intro hc0 hne
    exact ih (by omega) hne

/-- A reader that delivers something reads a nonempty stream.
Isabelle: `reads_from_nonempty`. -/
theorem reads_from_nonempty {α : Type x} {xs : List α} {c : Nat}
    {ys : List α} : reads_from xs c ys → ys ≠ [] → xs ≠ [] :=
  reads_from_ne

/-- Every nonempty redelivery of a stream starts with the stream's first
item and ends with its last. The nonemptiness of the stream is the
first conjunct, and the other two use its proof. Isabelle:
`redelivered_hd_last`. -/
theorem redelivered_hd_last {α : Type x} {xs ys : List α}
    (h : redelivered xs ys) (hne : ys ≠ []) :
    ∃ hxs : xs ≠ [], ys.head hne = xs.head hxs ∧
      ys.getLast hne = xs.getLast hxs := by
  change rtranclp at_least_once xs ys at h
  revert hne
  induction h with
  | rtrancl_refl => intro hne; exact ⟨hne, rfl, rfl⟩
  | @rtrancl_into_rtrancl ys zs _ hstep ih =>
    intro hne
    have rd : reads_from ys 0 zs := hstep
    have ys_ne : ys ≠ [] := reads_from_nonempty rd hne
    obtain ⟨hxs, hhd, hlast⟩ := ih ys_ne
    refine ⟨hxs, ?_, ?_⟩
    · exact (reads_from_hd rd rfl hne).trans
        ((List.head_eq_getElem ys_ne).symm.trans hhd)
    · exact (reads_from_last rd hne).trans hlast

namespace CaptureContract

variable {S : CoordinateSpace K V C} {σ0 : State K V}
  {units : List (CUnit K V C)} {scope : K → Prop} {f : C}
  (H : CaptureContract S σ0 units scope f)

include H

/-- Safety in the per-key form: the key's events of the applied stream
form a redelivery of the emission's events for the key. Isabelle:
`absent_replay_safe_at_least_once_per_key`. -/
theorem absent_replay_safe_at_least_once_per_key
    {svl : CUnit K V C → List K} {s0 : C} {Sq : List (Event K V)}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    {k : K} (hk : scope k)
    (per_key : redelivered (evs_for k (emission S units f svl s0)) (evs_for k Sq))
    (D0 : State K V) :
    state_after D0 Sq k = sink_at S units f f k ∨
      (state_after D0 Sq k = D0 k ∧
        sink_at S units f f k = none ∧
        absent_untouched S (the_unit units f k) k ∧
        k ∉ svl (the_unit units f k) ∧
        evs_for k (S.win s0 f) = []) := by
  rw [redelivered_key_replay per_key D0]
  exact H.absent_replay_safe hsvl hs0 hk D0

/-- Convergence in the per-key form: under coverage, and with the
per-key hypothesis for every scoped key, every scoped key ends at the
source state at the frontier. Isabelle:
`self_stabilization_at_least_once_per_key`. -/
theorem self_stabilization_at_least_once_per_key
    {svl : CUnit K V C → List K} {s0 : C} {D0 : State K V}
    {Sq : List (Event K V)}
    (hsvl : svl_ok2 S units svl)
    (hs0 : ∀ u ∈ units, S.cle s0 u.lo)
    (cov : covers S units f svl D0 s0)
    (per_key : ∀ k, scope k →
      redelivered (evs_for k (emission S units f svl s0)) (evs_for k Sq)) :
    ∀ k, scope k → state_after D0 Sq k = state_after σ0 (S.pfx f) k := by
  intro k hk
  rw [redelivered_key_replay (per_key k hk) D0]
  exact H.self_stabilization hsvl hs0 cov k hk

end CaptureContract

end

end DBLogContract
