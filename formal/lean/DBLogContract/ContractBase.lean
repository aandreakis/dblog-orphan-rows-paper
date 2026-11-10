/-!
# Contract base: events, source states, coordinates, and windows

This file is a port of `Contract_Base.thy` from the Isabelle
development that accompanies the paper. The port re-proves the same
statements over the same representation; it does not reinterpret
them.

The objects, in paper terms (Sections 2 and 3 of the paper):

* An event carries a key and the full post-image of that key, with
  `none` recording a delete. Events denote post-commit occurrences:
  the log has no pending, uncommitted, or aborted-transaction state.
  A transaction-aware instance contributes a complete transaction
  block only after commit. An event-level prefix inside such a block
  is merely an intermediate replay prefix of already-committed
  events, not a database state during the commit.
* A source state is the per-key partial map from keys to values.
* `state_after` folds a log prefix over an initial state. This is
  the per-key replay fold of Section 2, and `state_after_key` proves
  its per-key characterization: the last event for a key decides,
  and absent any event the initial state persists.
* A coordinate space assigns each coordinate the log prefix it
  denotes, represented by prefix length. Nestedness of denoted
  prefixes is proved as a theorem of this representation
  (`den_nested`), and the derived relation `cle` agrees with prefix
  inclusion of denotations (`cle_iff_prefix`). This is the paper's
  Definition 2.1.
* The window of two ordered coordinates is the half-open log
  segment between their denoted prefixes, low edge excluded, high
  edge included. This is the paper's Definition 2.2, and
  `oracle_set_reading` proves the membership-oracle set reading.
* `win_invariant_state` is the paper's Lemma 4.1 (window invariance):
  if no event for a key falls in a window, the source state on that
  key is the same at every coordinate of the window.

The port is classical. Definitions take decidability from
`Classical.propDecidable`, which mirrors the classical logic of the
Isabelle/HOL source, so no decidability hypotheses appear in any
statement. The development is a proof artifact and nothing in it is
meant to execute.
-/

namespace DBLogContract

universe u v w

attribute [local instance] Classical.propDecidable

/-- One committed change: a key together with the full post-image of
that key. `none` records a delete. Isabelle: datatype `event` with
projections `ev_key` and `ev_img`. -/
structure Event (K : Type u) (V : Type v) where
  key : K
  img : Option V

/-- A source state: the per-key partial map. `none` means the key is
absent. Isabelle: type synonym `state`; an `abbrev` is the
corresponding transparent definition. -/
abbrev State (K : Type u) (V : Type v) : Type (max u v) := K → Option V

variable {K : Type u} {V : Type v} {C : Type w}

noncomputable section

/-- Apply one event to a state: the event's key takes the event's
image, every other key is unchanged. Isabelle: `apply_ev`. -/
def apply_ev (σ : State K V) (e : Event K V) : State K V :=
  fun k => if k = e.key then e.img else σ k

/-- The row-event replay state after the committed-log prefix `P`, over
the initial state `σ0`: the left fold of `apply_ev`. In a
transaction-aware instance this is also a committed database state when
`P` ends at a transaction boundary. This is the contract's σ_P, the
per-key replay fold of Section 2 of the paper. Isabelle: `state_after`. -/
def state_after (σ0 : State K V) (P : List (Event K V)) : State K V :=
  P.foldl apply_ev σ0

/-- The events of `P` that carry key `k`, in log order. Isabelle:
`evs_for`. -/
def evs_for (k : K) (P : List (Event K V)) : List (Event K V) :=
  P.filter (fun e => decide (e.key = k))

@[simp] theorem evs_for_nil (k : K) : evs_for k ([] : List (Event K V)) = [] := rfl

theorem evs_for_cons (k : K) (e : Event K V) (P : List (Event K V)) :
    evs_for k (e :: P) =
      if e.key = k then e :: evs_for k P else evs_for k P := by
  simp only [evs_for, List.filter_cons, decide_eq_true_eq]

@[simp] theorem evs_for_append (k : K) (P Q : List (Event K V)) :
    evs_for k (P ++ Q) = evs_for k P ++ evs_for k Q := by
  simp [evs_for, List.filter_append]

@[simp] theorem state_after_nil (σ0 : State K V) : state_after σ0 [] = σ0 := rfl

theorem state_after_cons (σ0 : State K V) (e : Event K V) (P : List (Event K V)) :
    state_after σ0 (e :: P) = state_after (apply_ev σ0 e) P := rfl

theorem state_after_append (σ0 : State K V) (P Q : List (Event K V)) :
    state_after σ0 (P ++ Q) = state_after (state_after σ0 P) Q := by
  simp [state_after, List.foldl_append]

theorem state_after_snoc (σ0 : State K V) (P : List (Event K V)) (e : Event K V) :
    state_after σ0 (P ++ [e]) = apply_ev (state_after σ0 P) e := by
  rw [state_after_append]; rfl

/-- The per-key characterization of the source state: the last event
for the key decides, and absent any event the initial state
persists. This is the shape every argument below reduces to.
Isabelle: `state_after_key` (stated there with the total `last`;
stated here with the proof-carrying `getLast`, which is the same
claim in Lean's total style). -/
theorem state_after_key (σ0 : State K V) (P : List (Event K V)) (k : K) :
    state_after σ0 P k =
      if h : evs_for k P = [] then σ0 k else ((evs_for k P).getLast h).img := by
  induction P generalizing σ0 with
  | nil => simp
  | cons e P ih =>
    rw [state_after_cons, ih, evs_for_cons]
    by_cases he : e.key = k
    · rw [if_pos he]
      by_cases hP : evs_for k P = []
      · rw [dif_pos hP]
        rw [dif_neg (List.cons_ne_nil e _)]
        have : apply_ev σ0 e k = e.img := by
          simp only [apply_ev]
          rw [if_pos he.symm]
        rw [this, hP, List.getLast_singleton]
      · rw [dif_neg hP, dif_neg (List.cons_ne_nil e _), List.getLast_cons hP]
    · rw [if_neg he]
      have : apply_ev σ0 e k = σ0 k := by
        simp only [apply_ev]
        rw [if_neg (Ne.symm he)]
      rw [this]

theorem state_after_no_events {k : K} {P : List (Event K V)}
    (h : evs_for k P = []) (σ0 : State K V) :
    state_after σ0 P k = σ0 k := by
  rw [state_after_key, dif_pos h]

theorem state_after_last_event {k : K} {P : List (Event K V)}
    (h : evs_for k P ≠ []) (σ0 : State K V) :
    state_after σ0 P k = ((evs_for k P).getLast h).img := by
  rw [state_after_key, dif_neg h]

theorem state_after_append_no_k {k : K} {Q : List (Event K V)}
    (h : evs_for k Q = []) (σ0 : State K V) (P : List (Event K V)) :
    state_after σ0 (P ++ Q) k = state_after σ0 P k := by
  rw [state_after_append, state_after_no_events h]

/-- Helper: a shorter take is a prefix of a longer take of the same
list. Isabelle: `take_prefix_take`. -/
theorem take_prefix_take {α : Type u} {m n : Nat} (h : m ≤ n) (xs : List α) :
    xs.take m <+: xs.take n := by
  have heq : xs.take m = (xs.take n).take m := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [heq]
  exact List.take_prefix m (xs.take n)

/-- A coordinate space over a log: an arbitrary coordinate type `C`
with a denotation `den` giving, for each coordinate, the length of
the log prefix it denotes. Prefixes of one list biject with prefix
lengths, so this representation is exactly "coordinates denote
prefixes of the log" (paper Definition 2.1); the bound `den_le_len`
says a coordinate never denotes beyond the committed history under
discussion. Isabelle: locale `coordinate_space`, with `L` for the
log. -/
structure CoordinateSpace (K : Type u) (V : Type v) (C : Type w) where
  log : List (Event K V)
  den : C → Nat
  den_le_len : ∀ c, den c ≤ log.length

namespace CoordinateSpace

variable (S : CoordinateSpace K V C)

/-- The log prefix a coordinate denotes. Isabelle: `pfx`. -/
def pfx (c : C) : List (Event K V) := S.log.take (S.den c)

/-- The derived coordinate relation, written ⊑ in the Isabelle
source and ≼ in the paper: `cle c c'` holds when the prefix `c`
denotes is included in the prefix `c'` denotes. It is a preorder,
not a total order on `C`, and distinct coordinates may denote the
same prefix. Isabelle: `cle`. -/
def cle (c c' : C) : Prop := S.den c ≤ S.den c'

@[simp] theorem cle_refl (c : C) : S.cle c c := Nat.le_refl _

theorem cle_trans {c c' c'' : C} (h : S.cle c c') (h' : S.cle c' c'') :
    S.cle c c'' := Nat.le_trans h h'

@[simp] theorem pfx_length (c : C) : (S.pfx c).length = S.den c := by
  simp [pfx, List.length_take, Nat.min_eq_left (S.den_le_len c)]

/-- `cle` agrees with prefix inclusion of the denotations: the
representation is faithful to the contract's reading of ⊑ as
denotation inclusion. Isabelle: `cle_iff_prefix`. -/
theorem cle_iff_prefix {c c' : C} : S.cle c c' ↔ S.pfx c <+: S.pfx c' := by
  constructor
  · intro h
    exact take_prefix_take h S.log
  · intro h
    have hl := h.length_le
    rw [pfx_length, pfx_length] at hl
    exact hl

/-- MD1's nestedness clause is a theorem of the representation: any
two denoted prefixes are nested. Isabelle: `den_nested`. -/
theorem den_nested (c c' : C) :
    S.pfx c <+: S.pfx c' ∨ S.pfx c' <+: S.pfx c := by
  rcases Nat.le_total (S.den c) (S.den c') with h | h
  · exact Or.inl (S.cle_iff_prefix.mp h)
  · exact Or.inr (S.cle_iff_prefix.mp h)

/-- The half-open window `(lo, hi]` as a log segment: the list
difference of the two denoted prefixes, kept in commit order (paper
Definition 2.2). Low edge excluded, high edge included. Isabelle:
`win`. -/
def win (lo hi : C) : List (Event K V) :=
  (S.log.take (S.den hi)).drop (S.den lo)

/-- The prefix of the high edge splits as the prefix of the low edge
followed by the window. Isabelle: `pfx_split`. -/
theorem pfx_split {lo hi : C} (h : S.cle lo hi) :
    S.pfx hi = S.pfx lo ++ S.win lo hi := by
  have h1 : S.pfx lo = (S.log.take (S.den hi)).take (S.den lo) := by
    simp only [pfx]
    rw [List.take_take, Nat.min_eq_left h]
  rw [h1]
  simp only [win, pfx]
  rw [List.take_append_drop]

theorem win_length {lo hi : C} (_h : S.cle lo hi) :
    (S.win lo hi).length = S.den hi - S.den lo := by
  simp [win, List.length_drop, List.length_take,
        Nat.min_eq_left (S.den_le_len hi)]

theorem win_empty_iff {lo hi : C} (h : S.cle lo hi) :
    S.win lo hi = [] ↔ S.den lo = S.den hi := by
  rw [← List.length_eq_zero_iff, S.win_length h]
  have : S.cle lo hi := h
  simp only [cle] at this
  omega

theorem win_split {lo mid hi : C} (h1 : S.cle lo mid) (h2 : S.cle mid hi) :
    S.win lo hi = S.win lo mid ++ S.win mid hi := by
  have hlh : S.cle lo hi := S.cle_trans h1 h2
  apply List.append_cancel_left (as := S.pfx lo)
  calc S.pfx lo ++ S.win lo hi
      = S.pfx hi := (S.pfx_split hlh).symm
    _ = S.pfx mid ++ S.win mid hi := S.pfx_split h2
    _ = (S.pfx lo ++ S.win lo mid) ++ S.win mid hi := by
          rw [← S.pfx_split h1]
    _ = S.pfx lo ++ (S.win lo mid ++ S.win mid hi) := by
          rw [List.append_assoc]

/-- Window entries are log entries at their shifted positions:
occurrence (position) identity is preserved. Isabelle: `win_nth`. -/
theorem win_nth {lo hi : C} (h : S.cle lo hi) {p : Nat}
    (hp : p < S.den hi - S.den lo) :
    (S.win lo hi)[p]'(by rw [S.win_length h]; exact hp) =
      S.log[S.den lo + p]'(by have := S.den_le_len hi; omega) := by
  simp only [win, List.getElem_drop, List.getElem_take]

/-- The membership oracle's set reading: under distinct occurrences
the window is exactly the difference of the denoted prefixes, the
paper's `e ∈ ⟦hi⟧ \ ⟦lo⟧` reading of Definition 2.2. The development
itself reasons at position level, where no distinctness is needed;
this lemma ties the representation to the paper-level set phrasing.
Isabelle: `oracle_set_reading` (stated there as an equality of
finite sets; stated here as the pointwise membership equivalence,
which is the same claim). -/
theorem oracle_set_reading (hd : S.log.Nodup) {lo hi : C}
    (h : S.cle lo hi) (e : Event K V) :
    e ∈ S.win lo hi ↔ e ∈ S.pfx hi ∧ e ∉ S.pfx lo := by
  have split := S.pfx_split h
  have hnd : (S.pfx hi).Nodup :=
    List.Nodup.sublist (List.take_prefix _ _).sublist hd
  rw [split] at hnd
  rcases List.nodup_append.mp hnd with ⟨-, -, hdisj⟩
  constructor
  · intro hw
    refine ⟨by rw [split]; exact List.mem_append.mpr (Or.inr hw), ?_⟩
    intro hlo
    exact hdisj e hlo e hw rfl
  · rintro ⟨hhi, hlo⟩
    rw [split] at hhi
    rcases List.mem_append.mp hhi with hL | hR
    · exact absurd hL hlo
    · exact hR

theorem evs_for_pfx_split {lo hi : C} (h : S.cle lo hi) (k : K) :
    evs_for k (S.pfx hi) = evs_for k (S.pfx lo) ++ evs_for k (S.win lo hi) := by
  rw [S.pfx_split h, evs_for_append]

theorem evs_for_win_split {lo mid hi : C} (h1 : S.cle lo mid)
    (h2 : S.cle mid hi) (k : K) :
    evs_for k (S.win lo hi) =
      evs_for k (S.win lo mid) ++ evs_for k (S.win mid hi) := by
  rw [S.win_split h1 h2, evs_for_append]

/-- Window invariance (paper Lemma 4.1): if no event for a key falls
in a window, the source state on that key is the same at every
coordinate of the window. This is the fact that lets a
bracket-locally honest refresh value propagate to any other
coordinate of its bracket. Isabelle: `win_invariant_state`. -/
theorem win_invariant_state {k : K} {lo c hi : C}
    (lo_c : S.cle lo c) (c_hi : S.cle c hi)
    (quiet : evs_for k (S.win lo hi) = []) (σ0 : State K V) :
    state_after σ0 (S.pfx c) k = state_after σ0 (S.pfx lo) k := by
  have hsplit := S.evs_for_win_split lo_c c_hi k
  rw [quiet] at hsplit
  have h1 : evs_for k (S.win lo c) = [] :=
    (List.append_eq_nil_iff.mp hsplit.symm).1
  rw [S.pfx_split lo_c]
  exact state_after_append_no_k h1 σ0 (S.pfx lo)

theorem win_invariant_state2 {k : K} {lo c c' hi : C}
    (h1 : S.cle lo c) (h2 : S.cle c hi) (h3 : S.cle lo c') (h4 : S.cle c' hi)
    (quiet : evs_for k (S.win lo hi) = []) (σ0 : State K V) :
    state_after σ0 (S.pfx c) k = state_after σ0 (S.pfx c') k := by
  rw [S.win_invariant_state h1 h2 quiet σ0,
      S.win_invariant_state h3 h4 quiet σ0]

end CoordinateSpace

end

end DBLogContract
