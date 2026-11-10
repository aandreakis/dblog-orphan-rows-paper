import DBLogContract.CutTheorem

/-!
# The chunk ranges of one snapshot pass tile the key space

This file ports the general part of `Orphan_Absence_Tiling.thy` from the
Isabelle session `Orphan_Absence`, up to the subsection "Bridge". The
concrete examples of that theory are ported in `TilingWitnesses.lean`,
and the bridge to the contract core in `TilingBridge.lean`.

The model. Keys are of any linearly ordered type. The source state at a
read's cut is the set of keys present there, a predicate on keys. A pass
consumes a list of such sets, one per read. A page is the `n` smallest
present keys strictly above the previous chunk's last returned key. A
bounded page also stays at or below the maximum key `M` recorded at the
start of the pass. A short page ends the range open above, except in the
bounded main loop, where it ends the range at `M` and hands over to the
tail reads above `M`.

The results, for every chunk limit `n > 0`:

* The emitted ranges are pairwise disjoint, the first is open below, and
  each next range starts exactly where the previous one ends.
* A completed pass covers every key. A pass stopped by the tail-read limit
  covers exactly the keys at or below its frontier.
* On a finite source state every range is exact for its own read.
* A full page reads the same on a source with a higher key added, so
  closing a full page open above would certify a present key absent.

## Transport

* Isabelle's sort `linorder` is the port-local class `Linorder`. It
  carries `≤` and `<` and exactly the five axioms of HOL's `linorder`.
* Sets of keys are predicates `K → Prop`, and set equalities and
  inclusions are stated pointwise. HOL's `finite`, `sorted_list_of_set`,
  `card` and `insort` are port-local definitions with HOL's values,
  `[]` and `0` on an infinite set included.
* HOL's `last` is total. On the empty list it is an unspecified element
  of the type, and every HOL type has one. The scans apply `last` to a
  page that is empty when the chunk limit is 0, so they use the
  port-local total `last`, and the scans and the theorems about them
  take `[Nonempty K]`. Where an assumption before it gives the
  nonemptiness directly, the port uses `getLast` with that proof. The
  other statements use the total `last`.
* `xs ! i` is bounded `getElem`. Where the bound is not an assumption,
  it is derived from the assumptions before it.
-/

namespace DBLogContract

namespace Tiling

universe u v w

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Linear orders, finite sets and sorted lists -/

/-- Isabelle's type class `linorder`: the operations `≤` and `<`, with a
reflexive, transitive, antisymmetric and total `≤`, and a `<` that is
`≤` without `≥`. The axioms carry HOL's names. Port-local. -/
class Linorder (K : Type u) extends LE K, LT K where
  order_refl : ∀ a : K, a ≤ a
  order_trans : ∀ a b c : K, a ≤ b → b ≤ c → a ≤ c
  antisym : ∀ a b : K, a ≤ b → b ≤ a → a = b
  linear : ∀ a b : K, a ≤ b ∨ b ≤ a
  less_le_not_le : ∀ a b : K, a < b ↔ a ≤ b ∧ ¬ b ≤ a

/-- The natural numbers with their usual order are a `Linorder`, as
`nat` is a `linorder` in HOL. Port-local. -/
instance : Linorder Nat where
  order_refl := Nat.le_refl
  order_trans := fun _ _ _ => Nat.le_trans
  antisym := fun _ _ => Nat.le_antisymm
  linear := Nat.le_total
  less_le_not_le := fun _ _ => Nat.lt_iff_le_and_not_ge

/-- HOL's `finite`, read as a listing: a set is finite when it is the
set of some list (convention 2 of `VERIFICATION.md`). Port-local. -/
def finite {α : Type u} (A : α → Prop) : Prop :=
  ∃ xs : List α, ∀ k, k ∈ xs ↔ A k

/-- HOL's `card`: the number of elements of a finite set, the length of
any duplicate-free listing of it, and 0 for an infinite set. Port-local. -/
def card {α : Type u} (A : α → Prop) : Nat :=
  if h : ∃ xs : List α, xs.Nodup ∧ ∀ k, k ∈ xs ↔ A k then (Classical.choose h).length
  else 0

/-- HOL's total `last`. On a nonempty list it is the last entry. On the
empty list it is a fixed unspecified element of the type, as HOL's
`last []` is. Port-local. -/
def last {α : Type u} [Nonempty α] (xs : List α) : α :=
  match xs.getLast? with
  | some x => x
  | none => Classical.choice inferInstance

/-- On a nonempty list the total `last` is `getLast`. Port-local. -/
theorem last_eq_getLast {α : Type u} [Nonempty α] {xs : List α} (h : xs ≠ []) :
    last xs = xs.getLast h := by
  simp [last, List.getLast?_eq_some_getLast h]

section Order

variable {K : Type u} [Linorder K]

/-- HOL's `order_refl`. Port-local. -/
private theorem ord_le_refl (a : K) : a ≤ a := Linorder.order_refl a

/-- HOL's `order_trans`. Port-local. -/
private theorem ord_le_trans {a b c : K} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  Linorder.order_trans a b c h1 h2

/-- HOL's `less_imp_le`. Port-local. -/
private theorem ord_le_of_lt {a b : K} (h : a < b) : a ≤ b :=
  ((Linorder.less_le_not_le a b).mp h).1

/-- HOL's `leD`. Port-local. -/
private theorem ord_not_le_of_lt {a b : K} (h : a < b) : ¬ b ≤ a :=
  ((Linorder.less_le_not_le a b).mp h).2

/-- HOL's `less_irrefl`. Port-local. -/
private theorem ord_lt_irrefl (a : K) : ¬ a < a :=
  fun h => ord_not_le_of_lt h (ord_le_refl a)

/-- HOL's `not_le_imp_less`. Port-local. -/
private theorem ord_lt_of_not_le {a b : K} (h : ¬ a ≤ b) : b < a :=
  (Linorder.less_le_not_le b a).mpr ⟨(Linorder.linear a b).resolve_left h, h⟩

/-- HOL's `not_less`. Port-local. -/
private theorem ord_not_lt {a b : K} : ¬ a < b ↔ b ≤ a := by
  constructor
  · intro h
    exact Classical.byContradiction fun hba => h (ord_lt_of_not_le hba)
  · intro h hab
    exact ord_not_le_of_lt hab h

/-- HOL's `not_le`. Port-local. -/
private theorem ord_not_le {a b : K} : ¬ a ≤ b ↔ b < a := by
  constructor
  · exact ord_lt_of_not_le
  · intro h hab
    exact ord_not_le_of_lt h hab

/-- HOL's `le_less_trans`. Port-local. -/
private theorem ord_lt_of_le_of_lt {a b c : K} (h1 : a ≤ b) (h2 : b < c) : a < c :=
  (Linorder.less_le_not_le a c).mpr
    ⟨ord_le_trans h1 (ord_le_of_lt h2), fun hca => ord_not_le_of_lt h2 (ord_le_trans hca h1)⟩

/-- HOL's `less_le_trans`. Port-local. -/
private theorem ord_lt_of_lt_of_le {a b c : K} (h1 : a < b) (h2 : b ≤ c) : a < c :=
  (Linorder.less_le_not_le a c).mpr
    ⟨ord_le_trans (ord_le_of_lt h1) h2, fun hca => ord_not_le_of_lt h1 (ord_le_trans h2 hca)⟩

/-- HOL's `less_trans`. Port-local. -/
private theorem ord_lt_trans {a b c : K} (h1 : a < b) (h2 : b < c) : a < c :=
  ord_lt_of_lt_of_le h1 (ord_le_of_lt h2)

/-- HOL's `less_imp_neq`. Port-local. -/
private theorem ord_ne_of_lt {a b : K} (h : a < b) : a ≠ b := by
  intro hab
  subst hab
  exact ord_lt_irrefl a h

/-- HOL's `le_less_linear`, with the disjuncts swapped. Port-local. -/
private theorem ord_lt_or_le (a b : K) : a < b ∨ b ≤ a := by
  by_cases h : b ≤ a
  · exact Or.inr h
  · exact Or.inl (ord_lt_of_not_le h)

/-- HOL's `le_neq_trans`. Port-local. -/
private theorem ord_lt_of_le_of_ne {a b : K} (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by
  rcases ord_lt_or_le a b with h | h
  · exact h
  · exact absurd (Linorder.antisym a b h1 h) h2

/-- HOL's `insort`, the library function `insort_key (λx. x)`: insert a
key before the first entry it is at most. Port-local. -/
def insort (x : K) : List K → List K
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insort x ys

/-- HOL's `set_insort_key`, pointwise. Port-local. -/
private theorem mem_insort (x k : K) (l : List K) : k ∈ insort x l ↔ k = x ∨ k ∈ l := by
  induction l with
  | nil => simp [insort]
  | cons y ys ih =>
    simp only [insort]
    by_cases h : x ≤ y
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      simp only [List.mem_cons, ih]
      constructor
      · rintro (h1 | h1 | h1)
        · exact Or.inr (Or.inl h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inr (Or.inl h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)

/-- HOL's `length_insort`. Port-local. -/
private theorem length_insort (x : K) (l : List K) : (insort x l).length = l.length + 1 := by
  induction l with
  | nil => simp [insort]
  | cons y ys ih =>
    simp only [insort]
    by_cases h : x ≤ y
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      simp [ih]

/-- Inserting a new key keeps a list strictly sorted. Port-local. -/
private theorem pairwise_insort {x : K} {l : List K} (hl : List.Pairwise (· < ·) l)
    (hx : x ∉ l) : List.Pairwise (· < ·) (insort x l) := by
  induction l with
  | nil => simp [insort]
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxys : x ∉ ys := fun h => hx (List.mem_cons_of_mem y h)
    simp only [insort]
    by_cases h : x ≤ y
    · rw [if_pos h]
      have hlt : x < y := ord_lt_of_le_of_ne h hxy
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr hl⟩
      intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · exact hz ▸ hlt
      · exact ord_lt_trans hlt (hl.1 z hz)
    · rw [if_neg h, List.pairwise_cons]
      refine ⟨?_, ih hl.2 hxys⟩
      intro z hz
      rcases (mem_insort x z ys).mp hz with hz | hz
      · exact hz ▸ ord_lt_of_not_le h
      · exact hl.1 z hz

/-- Insertion sort with `insort`. Port-local, used only in proofs. -/
private def isort : List K → List K
  | [] => []
  | y :: ys => insort y (isort ys)

/-- Insertion sort keeps the members. Port-local. -/
private theorem mem_isort (k : K) (l : List K) : k ∈ isort l ↔ k ∈ l := by
  induction l with
  | nil => simp [isort]
  | cons y ys ih => simp [isort, mem_insort, ih]

/-- Insertion sort keeps the length. Port-local. -/
private theorem length_isort (l : List K) : (isort l).length = l.length := by
  induction l with
  | nil => simp [isort]
  | cons y ys ih => simp [isort, length_insort, ih]

/-- Insertion sort of a duplicate-free list is strictly sorted. Port-local. -/
private theorem pairwise_isort {l : List K} (hl : l.Nodup) :
    List.Pairwise (· < ·) (isort l) := by
  induction l with
  | nil => simp [isort]
  | cons y ys ih =>
    rw [List.nodup_cons] at hl
    exact pairwise_insort (ih hl.2) (fun h => hl.1 ((mem_isort y ys).mp h))

/-- Every listing has a strictly sorted listing of the same members.
Port-local. -/
private theorem exists_sorted_listing (xs : List K) :
    ∃ ys : List K, List.Pairwise (· < ·) ys ∧ ∀ k, k ∈ ys ↔ k ∈ xs := by
  induction xs with
  | nil => exact ⟨[], List.Pairwise.nil, fun k => by simp⟩
  | cons x xs ih =>
    obtain ⟨ys, hs, hm⟩ := ih
    by_cases hx : x ∈ ys
    · refine ⟨ys, hs, fun k => ?_⟩
      rw [List.mem_cons, ← hm]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · exact h ▸ hx
        · exact h
    · refine ⟨insort x ys, pairwise_insort hs hx, fun k => ?_⟩
      rw [mem_insort, List.mem_cons, hm]

/-- Two strictly sorted lists with the same members are equal. Port-local. -/
private theorem sorted_listing_unique {xs ys : List K} (hx : List.Pairwise (· < ·) xs)
    (hy : List.Pairwise (· < ·) ys) (hm : ∀ k, k ∈ xs ↔ k ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => exact absurd ((hm y).mpr List.mem_cons_self) (List.not_mem_nil)
  | cons x xs ih =>
    cases ys with
    | nil => exact absurd ((hm x).mp List.mem_cons_self) (List.not_mem_nil)
    | cons y ys =>
      rw [List.pairwise_cons] at hx hy
      have hxy : x = y := by
        refine Classical.byContradiction fun hne => ?_
        have h1 : y < x := by
          rcases List.mem_cons.mp ((hm x).mp List.mem_cons_self) with h | h
          · exact absurd h hne
          · exact hy.1 x h
        have h2 : x < y := by
          rcases List.mem_cons.mp ((hm y).mpr List.mem_cons_self) with h | h
          · exact absurd h.symm hne
          · exact hx.1 y h
        exact ord_lt_irrefl x (ord_lt_trans h2 h1)
      subst hxy
      have tails : ∀ k, k ∈ xs ↔ k ∈ ys := by
        intro k
        constructor
        · intro hk
          rcases List.mem_cons.mp ((hm k).mp (List.mem_cons_of_mem x hk)) with h | h
          · exact absurd h (ord_ne_of_lt (hx.1 k hk)).symm
          · exact h
        · intro hk
          rcases List.mem_cons.mp ((hm k).mpr (List.mem_cons_of_mem x hk)) with h | h
          · exact absurd h (ord_ne_of_lt (hy.1 k hk)).symm
          · exact h
      rw [ih hx.2 hy.2 tails]

/-- HOL's `sorted_list_of_set`: for a finite set, the strictly sorted list
of its members, which is unique, and `[]` for an infinite set, as in HOL.
Port-local. -/
def sorted_list_of_set (A : K → Prop) : List K :=
  if h : ∃ xs : List K, List.Pairwise (· < ·) xs ∧ ∀ k, k ∈ xs ↔ A k then Classical.choose h
  else []

/-- A strictly sorted listing of a set is its `sorted_list_of_set`.
Port-local. -/
theorem sorted_list_of_set_eq {A : K → Prop} {xs : List K}
    (hs : List.Pairwise (· < ·) xs) (hm : ∀ k, k ∈ xs ↔ A k) :
    sorted_list_of_set A = xs := by
  have hex : ∃ xs : List K, List.Pairwise (· < ·) xs ∧ ∀ k, k ∈ xs ↔ A k := ⟨xs, hs, hm⟩
  simp only [sorted_list_of_set]
  rw [dif_pos hex]
  obtain ⟨hs', hm'⟩ := Classical.choose_spec hex
  exact sorted_listing_unique hs' hs (fun k => (hm' k).trans (hm k).symm)

/-- A finite set has a strictly sorted listing. Port-local. -/
private theorem finite_exists_sorted {A : K → Prop} (fin : finite A) :
    ∃ xs : List K, List.Pairwise (· < ·) xs ∧ ∀ k, k ∈ xs ↔ A k := by
  obtain ⟨xs, hxs⟩ := fin
  obtain ⟨ys, hs, hm⟩ := exists_sorted_listing xs
  exact ⟨ys, hs, fun k => (hm k).trans (hxs k)⟩

/-- `sorted_list_of_set` is strictly sorted, on every set. Port-local. -/
theorem sorted_list_of_set_sorted (A : K → Prop) :
    List.Pairwise (· < ·) (sorted_list_of_set A) := by
  simp only [sorted_list_of_set]
  split
  · next h => exact (Classical.choose_spec h).1
  · exact List.Pairwise.nil

/-- On a finite set, the members of `sorted_list_of_set` are the members
of the set. Port-local. -/
theorem mem_sorted_list_of_set {A : K → Prop} (fin : finite A) (k : K) :
    k ∈ sorted_list_of_set A ↔ A k := by
  obtain ⟨xs, hs, hm⟩ := finite_exists_sorted fin
  rw [sorted_list_of_set_eq hs hm]
  exact hm k

/-- Every member of `sorted_list_of_set A` is a member of `A`, on every
set. Port-local. -/
theorem mem_sorted_list_of_set_imp {A : K → Prop} {k : K}
    (h : k ∈ sorted_list_of_set A) : A k := by
  by_cases fin : finite A
  · exact (mem_sorted_list_of_set fin k).mp h
  · have hnil : sorted_list_of_set A = [] := by
      simp only [sorted_list_of_set]
      rw [dif_neg]
      rintro ⟨xs, -, hm⟩
      exact fin ⟨xs, hm⟩
    rw [hnil] at h
    exact absurd h List.not_mem_nil

/-- The length of `sorted_list_of_set A` is `card A`, on every set, as in
HOL. Port-local. -/
theorem length_sorted_list_of_set (A : K → Prop) :
    (sorted_list_of_set A).length = card A := by
  by_cases fin : finite A
  · obtain ⟨xs, hs, hm⟩ := finite_exists_sorted fin
    rw [sorted_list_of_set_eq hs hm]
    have hnd : xs.Nodup := hs.imp (fun h => ord_ne_of_lt h)
    have hex : ∃ ys : List K, ys.Nodup ∧ ∀ k, k ∈ ys ↔ A k := ⟨xs, hnd, hm⟩
    simp only [card]
    rw [dif_pos hex]
    obtain ⟨hnd', hm'⟩ := Classical.choose_spec hex
    have heq : isort (Classical.choose hex) = xs :=
      sorted_listing_unique (pairwise_isort hnd') hs
        (fun k => ((mem_isort k _).trans (hm' k)).trans (hm k).symm)
    rw [← heq, length_isort]
  · have hnil : sorted_list_of_set A = [] := by
      simp only [sorted_list_of_set]
      rw [dif_neg]
      rintro ⟨xs, -, hm⟩
      exact fin ⟨xs, hm⟩
    have hc : card A = 0 := by
      simp only [card]
      rw [dif_neg]
      rintro ⟨xs, -, hm⟩
      exact fin ⟨xs, hm⟩
    rw [hnil, hc]
    rfl

/-- HOL's `sorted_list_of_set_insert`: inserting a new key into a finite
set inserts it into the sorted list. Port-local. -/
theorem sorted_list_of_set_insert {A : K → Prop} {x : K} (fin : finite A) (hx : ¬ A x) :
    sorted_list_of_set (fun y => y = x ∨ A y) = insort x (sorted_list_of_set A) := by
  apply sorted_list_of_set_eq
  · exact pairwise_insort (sorted_list_of_set_sorted A)
      (fun h => hx ((mem_sorted_list_of_set fin x).mp h))
  · intro k
    rw [mem_insort, mem_sorted_list_of_set fin]

omit [Linorder K] in
/-- A finite set stays finite when a condition is added. Port-local. -/
private theorem finite_and {S : K → Prop} (fin : finite S) (P : K → Prop) :
    finite (fun k => S k ∧ P k) := by
  obtain ⟨xs, hxs⟩ := fin
  refine ⟨xs.filter (fun k => decide (P k)), fun k => ?_⟩
  rw [List.mem_filter, hxs, decide_eq_true_eq]

/-! ## Bounds, ranges and chunks -/

/-- A lower bound is exclusive, and `none` is open below: `above_lo lo k`
holds when `k` lies above the lower bound `lo`. Isabelle: `above_lo`. -/
def above_lo (lo : Option K) (k : K) : Prop :=
  match lo with
  | none => True
  | some a => a < k

/-- An upper bound is inclusive, and `none` is open above: `upto_hi hi k`
holds when `k` lies at or below the upper bound `hi`. Isabelle:
`upto_hi`. -/
def upto_hi (hi : Option K) (k : K) : Prop :=
  match hi with
  | none => True
  | some b => k ≤ b

/-- Isabelle: `above_lo_None`. -/
@[simp] theorem above_lo_None (k : K) : above_lo none k := trivial

/-- Isabelle: `above_lo_Some`. -/
@[simp] theorem above_lo_Some (a k : K) : above_lo (some a) k ↔ a < k := Iff.rfl

/-- Isabelle: `upto_hi_None`. -/
@[simp] theorem upto_hi_None (k : K) : upto_hi none k := trivial

/-- Isabelle: `upto_hi_Some`. -/
@[simp] theorem upto_hi_Some (b k : K) : upto_hi (some b) k ↔ k ≤ b := Iff.rfl

end Order

/-- A chunk as the connector records it: the two range bounds and the raw
keys the chunk query returned, in key order. Isabelle: record `chunk`
with fields `c_lo`, `c_hi`, `c_rows`. -/
structure Chunk (K : Type u) where
  c_lo : Option K
  c_hi : Option K
  c_rows : List K

/-- The type of chunks has an element, so the total `last` applies to
lists of chunks, as HOL's `last` does. Port-local. -/
instance {K : Type u} : Nonempty (Chunk K) := ⟨{ c_lo := none, c_hi := none, c_rows := [] }⟩

section Chunks

variable {K : Type u} [Linorder K]

/-- The keys of a chunk are the keys inside its range. Isabelle:
`chunk_keys`. -/
def chunk_keys (c : Chunk K) : K → Prop :=
  fun k => above_lo c.c_lo k ∧ upto_hi c.c_hi k

/-- The keys a list of chunks covers, the union of their ranges.
Isabelle: `covered`. -/
def covered (cs : List (Chunk K)) : K → Prop :=
  fun k => ∃ c ∈ cs, chunk_keys c k

/-- A chunk is exact for a source state `S` when the keys it returned are
exactly the keys of its range present in `S`. The Isabelle set equality
`set (c_rows c) = chunk_keys c ∩ S` is stated pointwise. Isabelle:
`chunk_exact`. -/
def chunk_exact (S : K → Prop) (c : Chunk K) : Prop :=
  ∀ k, k ∈ c.c_rows ↔ (chunk_keys c k ∧ S k)

/-- An exact chunk returns every present key of its range. Isabelle:
`exact_sound`. -/
theorem exact_sound {S : K → Prop} {c : Chunk K} {k : K} (hex : chunk_exact S c)
    (hk : chunk_keys c k) (hS : S k) : k ∈ c.c_rows :=
  (hex k).mpr ⟨hk, hS⟩

/-- A key of an exact chunk's range that the chunk did not return was
absent. Isabelle: `exact_absent`. -/
theorem exact_absent {S : K → Prop} {c : Chunk K} {k : K} (hex : chunk_exact S c)
    (hk : chunk_keys c k) (hn : k ∉ c.c_rows) : ¬ S k :=
  fun hS => hn ((hex k).mpr ⟨hk, hS⟩)

/-! ## Pages: the `n` smallest keys of a set -/

/-- The `n` smallest keys of a set, in key order. Isabelle: `smallest`. -/
def smallest (n : Nat) (A : K → Prop) : List K :=
  (sorted_list_of_set A).take n

/-- The page of a plain chunk query, `SELECT ... WHERE k > lo ORDER BY k
LIMIT n`. Isabelle: `page`. -/
def page (S : K → Prop) (lo : Option K) (n : Nat) : List K :=
  smallest n (fun k => S k ∧ above_lo lo k)

/-- The page of a bounded chunk query, which adds `k ≤ M`. Isabelle:
`bpage`. -/
def bpage (S : K → Prop) (lo : Option K) (M : K) (n : Nat) : List K :=
  smallest n (fun k => S k ∧ above_lo lo k ∧ k ≤ M)

/-- Every entry of a strictly sorted list is at most its last entry.
Isabelle: `sorted_le_last`, whose `last xs` is `getLast` with the
nonemptiness proof that `x ∈ xs` gives. -/
theorem sorted_le_last {xs : List K} {x : K} (hs : List.Pairwise (· < ·) xs) (hx : x ∈ xs) :
    x ≤ xs.getLast (List.ne_nil_of_mem hx) := by
  have hne : xs ≠ [] := List.ne_nil_of_mem hx
  have split := List.dropLast_concat_getLast hne
  have hs' := split ▸ hs
  rw [List.pairwise_append] at hs'
  have hx' : x ∈ xs.dropLast ++ [xs.getLast hne] := split.symm ▸ hx
  rcases List.mem_append.mp hx' with h | h
  · exact ord_le_of_lt (hs'.2.2 x h _ List.mem_cons_self)
  · have hxl : x = xs.getLast hne := List.mem_singleton.mp h
    calc x = xs.getLast hne := hxl
      _ ≤ xs.getLast hne := ord_le_refl _

/-- A strictly sorted list's prefix holds every entry at most its last
entry. Isabelle: `sorted_take_no_skip`. -/
theorem sorted_take_no_skip {xs : List K} {x : K} {m : Nat}
    (hs : List.Pairwise (· < ·) xs) (hx : x ∈ xs)
    (hne : xs.take m ≠ []) (hle : x ≤ (xs.take m).getLast hne) : x ∈ xs.take m := by
  have split := List.take_append_drop m xs
  have hs' := split.symm ▸ hs
  rw [List.pairwise_append] at hs'
  have hx' : x ∈ xs.take m ++ xs.drop m := split.symm ▸ hx
  rcases List.mem_append.mp hx' with h | h
  · exact h
  · have hlt : (xs.take m).getLast hne < x := hs'.2.2 _ (List.getLast_mem hne) x h
    exact absurd hle (ord_not_le_of_lt hlt)

/-- The `n` smallest keys of a set are keys of the set. The Isabelle
inclusion is stated pointwise. Isabelle: `smallest_subset`. -/
theorem smallest_subset {n : Nat} {A : K → Prop} :
    ∀ k, k ∈ smallest n A → A k :=
  fun _ hk => mem_sorted_list_of_set_imp (List.mem_of_mem_take hk)

/-- Isabelle: `smallest_sorted`. -/
theorem smallest_sorted {n : Nat} {A : K → Prop} :
    List.Pairwise (· < ·) (smallest n A) :=
  (sorted_list_of_set_sorted A).sublist (List.take_sublist n _)

/-- Isabelle: `smallest_length`. -/
theorem smallest_length {n : Nat} {A : K → Prop} :
    (smallest n A).length = min n (card A) := by
  simp only [smallest, List.length_take, length_sorted_list_of_set]

/-- On a finite set, the `n` smallest keys are exactly the keys of the set
at or below the last of them. The set equality is stated pointwise, and
`last` is `getLast` with the assumption `ne`. Isabelle:
`smallest_upto_last`. -/
theorem smallest_upto_last {n : Nat} {A : K → Prop} (fin : finite A)
    (ne : smallest n A ≠ []) :
    ∀ k, k ∈ smallest n A ↔ (A k ∧ k ≤ (smallest n A).getLast ne) := by
  intro k
  constructor
  · intro hk
    exact ⟨smallest_subset k hk, sorted_le_last smallest_sorted hk⟩
  · rintro ⟨hA, hle⟩
    have in_list : k ∈ sorted_list_of_set A := (mem_sorted_list_of_set fin k).mpr hA
    exact sorted_take_no_skip (sorted_list_of_set_sorted A) in_list ne hle

/-- On a finite set, a short result holds every key of the set. The set
equality is stated pointwise. Isabelle: `smallest_short`. -/
theorem smallest_short {n : Nat} {A : K → Prop} (fin : finite A)
    (short : (smallest n A).length < n) :
    ∀ k, k ∈ smallest n A ↔ A k := by
  have hlen : (sorted_list_of_set A).length ≤ n := by
    simp only [smallest, List.length_take] at short
    omega
  have heq : smallest n A = sorted_list_of_set A := List.take_of_length_le hlen
  intro k
  rw [heq]
  exact mem_sorted_list_of_set fin k

/-- On a finite set, `smallest` never skips a key below one it returned.
Isabelle: `smallest_no_skip`. -/
theorem smallest_no_skip {n : Nat} {A : K → Prop} {x y : K} (fin : finite A) (hx : A x)
    (nx : x ∉ smallest n A) (hy : y ∈ smallest n A) : y < x := by
  refine Classical.byContradiction fun hyx => ?_
  have xy : x ≤ y := ord_not_lt.mp hyx
  have ne : smallest n A ≠ [] := List.ne_nil_of_mem hy
  have yl : y ≤ (smallest n A).getLast ne := sorted_le_last smallest_sorted hy
  exact nx ((smallest_upto_last fin ne x).mpr ⟨hx, ord_le_trans xy yl⟩)

/-- On a finite set given as a strictly sorted list, the `n` smallest keys
are the first `n` entries of the list. The Isabelle set equality
`set xs = A` is stated pointwise. Isabelle: `smallest_eqI`. -/
theorem smallest_eqI {n : Nat} {A : K → Prop} {xs ys : List K}
    (sorted : List.Pairwise (· < ·) xs) (set_xs : ∀ k, k ∈ xs ↔ A k)
    (take_n : xs.take n = ys) : smallest n A = ys := by
  simp only [smallest]
  rw [sorted_list_of_set_eq sorted set_xs]
  exact take_n

/-- The page returns present keys above its lower bound. The inclusion is
stated pointwise. Isabelle: `page_sub`. -/
theorem page_sub {S : K → Prop} {lo : Option K} {n : Nat} :
    ∀ k, k ∈ page S lo n → S k ∧ above_lo lo k :=
  smallest_subset

/-- The bounded page returns present keys above its lower bound and at
or below `M`. The inclusion is stated pointwise. Isabelle: `bpage_sub`. -/
theorem bpage_sub {S : K → Prop} {lo : Option K} {M : K} {n : Nat} :
    ∀ k, k ∈ bpage S lo M n → S k ∧ above_lo lo k ∧ k ≤ M :=
  smallest_subset

/-! ## Each of the four chunk kinds is exact for its read -/

/-- A full plain page closed at its last key is exact. Isabelle's
`last (page S lo n)` is `getLast` with the assumption `ne`. Isabelle:
`exact_closed`. -/
theorem exact_closed {S : K → Prop} {lo : Option K} {n : Nat} (fin : finite S)
    (ne : page S lo n ≠ []) :
    chunk_exact S { c_lo := lo, c_hi := some ((page S lo n).getLast ne),
                    c_rows := page S lo n } := by
  have eq : ∀ k, k ∈ page S lo n ↔ ((S k ∧ above_lo lo k) ∧ k ≤ (page S lo n).getLast ne) :=
    smallest_upto_last (finite_and fin (above_lo lo)) ne
  intro k
  show k ∈ page S lo n ↔ (above_lo lo k ∧ k ≤ (page S lo n).getLast ne) ∧ S k
  rw [eq k]
  constructor
  · rintro ⟨⟨hS, ha⟩, hl⟩
    exact ⟨⟨ha, hl⟩, hS⟩
  · rintro ⟨⟨ha, hl⟩, hS⟩
    exact ⟨⟨hS, ha⟩, hl⟩

/-- A short plain page left open above is exact. Isabelle:
`exact_open_above`. -/
theorem exact_open_above {S : K → Prop} {lo : Option K} {n : Nat} (fin : finite S)
    (short : (page S lo n).length < n) :
    chunk_exact S { c_lo := lo, c_hi := none, c_rows := page S lo n } := by
  have eq : ∀ k, k ∈ page S lo n ↔ (S k ∧ above_lo lo k) :=
    smallest_short (finite_and fin (above_lo lo)) short
  intro k
  show k ∈ page S lo n ↔ (above_lo lo k ∧ True) ∧ S k
  rw [eq k, and_true]
  exact And.comm

/-- A full bounded page closed at its last key is exact. Isabelle's
`last (bpage S lo M n)` is `getLast` with the assumption `ne`.
Isabelle: `exact_bounded_closed`. -/
theorem exact_bounded_closed {S : K → Prop} {lo : Option K} {M : K} {n : Nat}
    (fin : finite S) (ne : bpage S lo M n ≠ []) :
    chunk_exact S { c_lo := lo, c_hi := some ((bpage S lo M n).getLast ne),
                    c_rows := bpage S lo M n } := by
  have eq : ∀ k, k ∈ bpage S lo M n ↔
      ((S k ∧ above_lo lo k ∧ k ≤ M) ∧ k ≤ (bpage S lo M n).getLast ne) :=
    smallest_upto_last (finite_and fin (fun k => above_lo lo k ∧ k ≤ M)) ne
  have last_M : (bpage S lo M n).getLast ne ≤ M :=
    (bpage_sub _ (List.getLast_mem ne)).2.2
  intro k
  show k ∈ bpage S lo M n ↔ (above_lo lo k ∧ k ≤ (bpage S lo M n).getLast ne) ∧ S k
  rw [eq k]
  constructor
  · rintro ⟨⟨hS, ha, -⟩, hl⟩
    exact ⟨⟨ha, hl⟩, hS⟩
  · rintro ⟨⟨ha, hl⟩, hS⟩
    exact ⟨⟨hS, ha, ord_le_trans hl last_M⟩, hl⟩

/-- A short bounded page closed at the recorded maximum is exact.
Isabelle: `exact_closed_at_max`. -/
theorem exact_closed_at_max {S : K → Prop} {lo : Option K} {M : K} {n : Nat}
    (fin : finite S) (short : (bpage S lo M n).length < n) :
    chunk_exact S { c_lo := lo, c_hi := some M, c_rows := bpage S lo M n } := by
  have eq : ∀ k, k ∈ bpage S lo M n ↔ (S k ∧ above_lo lo k ∧ k ≤ M) :=
    smallest_short (finite_and fin (fun k => above_lo lo k ∧ k ≤ M)) short
  intro k
  show k ∈ bpage S lo M n ↔ (above_lo lo k ∧ k ≤ M) ∧ S k
  rw [eq k]
  constructor
  · rintro ⟨hS, ha, hM⟩
    exact ⟨⟨ha, hM⟩, hS⟩
  · rintro ⟨⟨ha, hM⟩, hS⟩
    exact ⟨hS, ha, hM⟩

end Chunks

/-! ## Chains of ranges tile their span -/

section Chains

variable {K : Type u} [Linorder K]

/-- `lower_le lo b` holds when the lower bound `lo` is at most `b`, and
always for the open bound `none`. Isabelle: `lower_le`. -/
def lower_le (lo : Option K) (b : K) : Prop :=
  match lo with
  | none => True
  | some a => a ≤ b

/-- Isabelle: `lower_le_None`. -/
@[simp] theorem lower_le_None (b : K) : lower_le none b := trivial

/-- Isabelle: `lower_le_Some`. -/
@[simp] theorem lower_le_Some (a b : K) : lower_le (some a) b ↔ a ≤ b := Iff.rfl

/-- Isabelle: `above_lower_le`. -/
theorem above_lower_le {lo : Option K} {b : K} (h : above_lo lo b) : lower_le lo b := by
  cases lo with
  | none => trivial
  | some a => exact ord_le_of_lt h

/-- Isabelle: `lower_le_above`. -/
theorem lower_le_above {lo : Option K} {b k : K} (h1 : lower_le lo b) (h2 : b < k) :
    above_lo lo k := by
  cases lo with
  | none => trivial
  | some a => exact ord_lt_of_le_of_lt h1 h2

/-- A list of chunks is a chain from the lower bound `lo` when the first
range starts at `lo`, each next range starts at the previous range's
upper bound, only the last range may be open above, and no upper bound
lies below the range's own lower bound. Isabelle: `ranges_chain`. -/
def ranges_chain : Option K → List (Chunk K) → Prop
  | _, [] => True
  | lo, c :: cs =>
    c.c_lo = lo ∧
      (match c.c_hi with
       | none => cs = []
       | some b => lower_le lo b ∧ ranges_chain (some b) cs)

/-- The part of the key space above `lo` that a chain leaves to later
reads: everything above its last upper bound, or nothing when the last
range is open above. Isabelle: `chain_rest`. -/
def chain_rest : Option K → List (Chunk K) → K → Prop
  | lo, [] => fun k => above_lo lo k
  | _, c :: cs =>
    match c.c_hi with
    | none => fun _ => False
    | some b => chain_rest (some b) cs

/-- The empty list of chunks covers no key. Port-local. -/
private theorem covered_nil (k : K) : ¬ covered ([] : List (Chunk K)) k := by
  rintro ⟨c, hc, -⟩
  exact List.not_mem_nil hc

/-- The keys a list of chunks covers, one chunk at a time. Port-local. -/
private theorem covered_cons (c : Chunk K) (cs : List (Chunk K)) (k : K) :
    covered (c :: cs) k ↔ (chunk_keys c k ∨ covered cs k) := by
  constructor
  · rintro ⟨d, hd, hk⟩
    rcases List.mem_cons.mp hd with h | h
    · exact Or.inl (h ▸ hk)
    · exact Or.inr ⟨d, h, hk⟩
  · rintro (h | ⟨d, hd, hk⟩)
    · exact ⟨c, List.mem_cons_self, h⟩
    · exact ⟨d, List.mem_cons_of_mem c hd, hk⟩

/-- Every key of a chain's ranges lies above the chain's lower bound.
Isabelle: `chain_above`. -/
theorem chain_above {lo : Option K} {cs : List (Chunk K)} {c : Chunk K} {k : K}
    (hch : ranges_chain lo cs) (hc : c ∈ cs) (hk : chunk_keys c k) : above_lo lo k := by
  induction cs generalizing lo with
  | nil => exact absurd hc List.not_mem_nil
  | cons d ds ih =>
    simp only [ranges_chain] at hch
    obtain ⟨d_lo, hrest⟩ := hch
    rcases List.mem_cons.mp hc with h | h
    · subst h
      rw [← d_lo]
      exact hk.1
    · cases hb : d.c_hi with
      | none =>
        simp only [hb] at hrest
        subst hrest
        exact absurd h List.not_mem_nil
      | some b =>
        simp only [hb] at hrest
        exact lower_le_above hrest.1 (ih hrest.2 h)

/-- The rest of a chain lies above the chain's lower bound. Isabelle:
`chain_rest_above`. -/
theorem chain_rest_above {lo : Option K} {cs : List (Chunk K)} {k : K}
    (hch : ranges_chain lo cs) (hk : chain_rest lo cs k) : above_lo lo k := by
  induction cs generalizing lo with
  | nil => exact hk
  | cons c cs ih =>
    simp only [ranges_chain] at hch
    cases hb : c.c_hi with
    | none =>
      simp only [chain_rest, hb] at hk
    | some b =>
      simp only [hb] at hch
      simp only [chain_rest, hb] at hk
      exact lower_le_above hch.2.1 (ih hch.2.2 hk)

/-- A chain covers exactly the keys above its lower bound that it does
not leave to later reads. The Isabelle set equality
`covered cs = {k. above_lo lo k} - chain_rest lo cs` is stated pointwise.
Isabelle: `chain_covered`. -/
theorem chain_covered {lo : Option K} {cs : List (Chunk K)} (hch : ranges_chain lo cs) :
    ∀ k, covered cs k ↔ (above_lo lo k ∧ ¬ chain_rest lo cs k) := by
  induction cs generalizing lo with
  | nil =>
    intro k
    simp only [chain_rest]
    constructor
    · intro h
      exact absurd h (covered_nil k)
    · rintro ⟨h1, h2⟩
      exact absurd h1 h2
  | cons c cs ih =>
    simp only [ranges_chain] at hch
    obtain ⟨c_lo, hrest⟩ := hch
    intro k
    rw [covered_cons]
    cases hb : c.c_hi with
    | none =>
      simp only [hb] at hrest
      subst hrest
      simp only [chain_rest, hb, chunk_keys, upto_hi_None, and_true, c_lo, not_false_eq_true]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h (covered_nil k)
      · exact Or.inl
    | some b =>
      simp only [hb] at hrest
      obtain ⟨le, ch⟩ := hrest
      have ih' := ih ch
      have rest_b : ∀ k, chain_rest (some b) cs k → b < k :=
        fun k hk => chain_rest_above ch hk
      have hrest_eq : chain_rest lo (c :: cs) k ↔ chain_rest (some b) cs k := by
        simp only [chain_rest, hb]
      rw [hrest_eq]
      have hck : chunk_keys c k ↔ (above_lo lo k ∧ k ≤ b) := by
        simp only [chunk_keys, hb, upto_hi_Some, c_lo]
      rw [hck]
      rcases ord_lt_or_le b k with high | low
      · have ha : above_lo lo k := lower_le_above le high
        rw [ih' k]
        constructor
        · rintro (⟨_, hkb⟩ | ⟨_, hn⟩)
          · exact absurd hkb (ord_not_le_of_lt high)
          · exact ⟨ha, hn⟩
        · rintro ⟨_, hn⟩
          exact Or.inr ⟨high, hn⟩
      · have hnr : ¬ chain_rest (some b) cs k :=
          fun h => ord_not_le_of_lt (rest_b k h) low
        have hnc : ¬ covered cs k :=
          fun h => ord_not_le_of_lt ((ih' k).mp h).1 low
        constructor
        · rintro (⟨ha, _⟩ | h)
          · exact ⟨ha, hnr⟩
          · exact absurd h hnc
        · rintro ⟨ha, _⟩
          exact Or.inl ⟨ha, low⟩

/-- The ranges of a chain are pairwise disjoint along the list. The
Isabelle relation `chunk_keys c ∩ chunk_keys d = {}` is stated pointwise.
Isabelle: `chain_disjoint`, whose `sorted_wrt` is `List.Pairwise`. -/
theorem chain_disjoint {lo : Option K} {cs : List (Chunk K)} (hch : ranges_chain lo cs) :
    List.Pairwise (fun c d => ∀ k, chunk_keys c k → chunk_keys d k → False) cs := by
  induction cs generalizing lo with
  | nil => exact List.Pairwise.nil
  | cons c cs ih =>
    simp only [ranges_chain] at hch
    obtain ⟨_, hrest⟩ := hch
    cases hb : c.c_hi with
    | none =>
      simp only [hb] at hrest
      subst hrest
      exact List.pairwise_singleton _ _
    | some b =>
      simp only [hb] at hrest
      rw [List.pairwise_cons]
      refine ⟨?_, ih hrest.2⟩
      intro d hd k hkc hkd
      have h1 : b < k := chain_above hrest.2 hd hkd
      have h2 : upto_hi c.c_hi k := hkc.2
      rw [hb] at h2
      exact ord_not_le_of_lt h1 h2

/-- In a chain, each next range starts where the previous one ends.
Isabelle: `chain_consecutive`. -/
theorem chain_consecutive {lo : Option K} {cs : List (Chunk K)} {i : Nat}
    (hch : ranges_chain lo cs) (hi : i + 1 < cs.length) :
    ∃ b, (cs[i]'(Nat.lt_of_succ_lt hi)).c_hi = some b ∧ (cs[i + 1]'hi).c_lo = some b := by
  induction cs generalizing lo i with
  | nil => simp at hi
  | cons c cs ih =>
    have ne : cs ≠ [] := by
      intro h
      subst h
      simp at hi
    simp only [ranges_chain] at hch
    obtain ⟨_, hrest⟩ := hch
    cases hb : c.c_hi with
    | none =>
      simp only [hb] at hrest
      exact absurd hrest ne
    | some b =>
      simp only [hb] at hrest
      cases i with
      | zero =>
        cases cs with
        | nil => exact absurd rfl ne
        | cons d ds =>
          simp only [ranges_chain] at hrest
          exact ⟨b, hb, hrest.2.1⟩
      | succ j =>
        have hj : j + 1 < cs.length := by
          simp only [List.length_cons] at hi
          omega
        obtain ⟨b', h1, h2⟩ := ih hrest.2 hj
        exact ⟨b', h1, h2⟩

/-- A nonempty chain from `lo` starts at `lo`. Isabelle: `chain_first`. -/
theorem chain_first {lo : Option K} {cs : List (Chunk K)} (hch : ranges_chain lo cs)
    (ne : cs ≠ []) : (cs[0]'(List.length_pos_iff.mpr ne)).c_lo = lo := by
  cases cs with
  | nil => exact absurd rfl ne
  | cons c cs =>
    simp only [ranges_chain] at hch
    exact hch.1

end Chains

/-! ## The pass: the bounded main loop, the tail reads, the classic loop -/

/-- The outcome of a pass. `Completed`: a short page was observed in an
unbounded read, so the last range is open above. `Tail_Limit f`: the
tail-read limit stopped the pass, and every key above `f` is uncovered.
`Running f`: the list of reads ran out before the pass ended. The
frontier `f` is an option, and `none` means that no key is covered.
Isabelle: datatype `pass_status`. -/
inductive PassStatus (K : Type u) where
  | Completed : PassStatus K
  | Tail_Limit : Option K → PassStatus K
  | Running : Option K → PassStatus K

section Pass

variable {K : Type u} [Linorder K]

/-- The keys a pass leaves uncovered. Isabelle: `uncovered`. -/
def uncovered : PassStatus K → K → Prop
  | .Completed => fun _ => False
  | .Tail_Limit f => fun k => above_lo f k
  | .Running f => fun k => above_lo f k

/-- The tail reads: plain pages above the current lower bound, at most
`t` of them. A short page ends the pass with a range open above. A full
page closes its range at its last key, and the next read starts there.
HOL's `apfst f` is `Prod.map f id`. Isabelle: `tail_scan`. -/
def tail_scan [Nonempty K] (n : Nat) :
    Nat → Option K → List (K → Prop) → List (Chunk K) × PassStatus K
  | 0, lo, _ => ([], .Tail_Limit lo)
  | _ + 1, lo, [] => ([], .Running lo)
  | t + 1, lo, S :: Ss =>
    if (page S lo n).length < n then
      ([{ c_lo := lo, c_hi := none, c_rows := page S lo n }], .Completed)
    else
      Prod.map (List.cons { c_lo := lo, c_hi := some (last (page S lo n)),
                            c_rows := page S lo n }) id
        (tail_scan n t (some (last (page S lo n))) Ss)

/-- The bounded main loop: bounded pages at or below the recorded maximum
`M`. A short page closes its range at `M`, and the tail reads above `M`
follow, at most `T` of them. Isabelle: `bounded_scan`. -/
def bounded_scan [Nonempty K] (n T : Nat) (M : K) :
    Option K → List (K → Prop) → List (Chunk K) × PassStatus K
  | lo, [] => ([], .Running lo)
  | lo, S :: Ss =>
    if (bpage S lo M n).length < n then
      Prod.map (List.cons { c_lo := lo, c_hi := some M, c_rows := bpage S lo M n }) id
        (tail_scan n T (some M) Ss)
    else
      Prod.map (List.cons { c_lo := lo, c_hi := some (last (bpage S lo M n)),
                            c_rows := bpage S lo M n }) id
        (bounded_scan n T M (some (last (bpage S lo M n))) Ss)

/-- A bounded pass starts open below. The recorded maximum `none` stands
for a table that was empty when the pass started, and the pass goes
straight to the tail reads. Isabelle: `bounded_pass`. -/
def bounded_pass [Nonempty K] (n T : Nat) (Mo : Option K) (Ss : List (K → Prop)) :
    List (Chunk K) × PassStatus K :=
  match Mo with
  | none => tail_scan n T none Ss
  | some M => bounded_scan n T M none Ss

/-- The classic DBLog loop: plain pages until a short page, with no
recorded maximum and no limit on the number of reads. Isabelle:
`classic_scan`. -/
def classic_scan [Nonempty K] (n : Nat) :
    Option K → List (K → Prop) → List (Chunk K) × PassStatus K
  | lo, [] => ([], .Running lo)
  | lo, S :: Ss =>
    if (page S lo n).length < n then
      ([{ c_lo := lo, c_hi := none, c_rows := page S lo n }], .Completed)
    else
      Prod.map (List.cons { c_lo := lo, c_hi := some (last (page S lo n)),
                            c_rows := page S lo n }) id
        (classic_scan n (some (last (page S lo n))) Ss)

/-- The classic pass starts open below. Isabelle: `classic_pass`. -/
def classic_pass [Nonempty K] (n : Nat) (Ss : List (K → Prop)) :
    List (Chunk K) × PassStatus K :=
  classic_scan n none Ss

/-! ## The tail reads emit an exact chain -/

/-- Isabelle: `tail_scan_pos_Nil`. -/
theorem tail_scan_pos_Nil [Nonempty K] {n t : Nat} {lo : Option K} (ht : 0 < t) :
    tail_scan n t lo [] = ([], .Running lo) := by
  cases t with
  | zero => exact absurd ht (Nat.lt_irrefl 0)
  | succ t => rfl

/-- Isabelle: `tail_scan_pos_Cons`. -/
theorem tail_scan_pos_Cons [Nonempty K] {n t : Nat} {lo : Option K} {S : K → Prop}
    {Ss : List (K → Prop)} (ht : 0 < t) :
    tail_scan n t lo (S :: Ss) =
      (if (page S lo n).length < n then
        ([{ c_lo := lo, c_hi := none, c_rows := page S lo n }], .Completed)
      else
        Prod.map (List.cons { c_lo := lo, c_hi := some (last (page S lo n)),
                              c_rows := page S lo n }) id
          (tail_scan n (t - 1) (some (last (page S lo n))) Ss)) := by
  cases t with
  | zero => exact absurd ht (Nat.lt_irrefl 0)
  | succ t => rfl

/-- Isabelle: `page_full_ne`. -/
theorem page_full_ne {S : K → Prop} {lo : Option K} {n : Nat} (hn : 0 < n)
    (full : ¬ (page S lo n).length < n) : page S lo n ≠ [] := by
  intro h
  rw [h] at full
  exact full hn

/-- Isabelle: `bpage_full_ne`. -/
theorem bpage_full_ne {S : K → Prop} {lo : Option K} {M : K} {n : Nat} (hn : 0 < n)
    (full : ¬ (bpage S lo M n).length < n) : bpage S lo M n ≠ [] := by
  intro h
  rw [h] at full
  exact full hn

/-- Isabelle: `page_last_above`, with `last` as `getLast` and the
assumption `h`. -/
theorem page_last_above {S : K → Prop} {lo : Option K} {n : Nat} (h : page S lo n ≠ []) :
    above_lo lo ((page S lo n).getLast h) :=
  (page_sub _ (List.getLast_mem h)).2

/-- Isabelle: `bpage_last_above`, with `last` as `getLast` and the
assumption `h`. -/
theorem bpage_last_above {S : K → Prop} {lo : Option K} {M : K} {n : Nat}
    (h : bpage S lo M n ≠ []) : above_lo lo ((bpage S lo M n).getLast h) :=
  (bpage_sub _ (List.getLast_mem h)).2.1

/-- Isabelle: `bpage_last_le`, with `last` as `getLast` and the
assumption `h`. -/
theorem bpage_last_le {S : K → Prop} {lo : Option K} {M : K} {n : Nat}
    (h : bpage S lo M n ≠ []) : (bpage S lo M n).getLast h ≤ M :=
  (bpage_sub _ (List.getLast_mem h)).2.2

/-- Isabelle: `page_length_le`. -/
theorem page_length_le {S : K → Prop} {lo : Option K} {n : Nat} :
    (page S lo n).length ≤ n := by
  simp only [page, smallest_length]
  exact Nat.min_le_left _ _

/-- Isabelle: `bpage_length_le`. -/
theorem bpage_length_le {S : K → Prop} {lo : Option K} {M : K} {n : Nat} :
    (bpage S lo M n).length ≤ n := by
  simp only [bpage, smallest_length]
  exact Nat.min_le_left _ _

/-! Unfolding the scans one read at a time. Port-local. -/

/-- The tail reads end on a short page. Port-local. -/
private theorem tail_scan_short [Nonempty K] {n t : Nat} {lo : Option K} {S : K → Prop}
    {Ss : List (K → Prop)} (h : (page S lo n).length < n) :
    tail_scan n (t + 1) lo (S :: Ss) =
      ([{ c_lo := lo, c_hi := none, c_rows := page S lo n }], .Completed) := by
  simp only [tail_scan, if_pos h]

/-- The tail reads continue after a full page. Port-local. -/
private theorem tail_scan_full [Nonempty K] {n t : Nat} {lo : Option K} {S : K → Prop}
    {Ss : List (K → Prop)} (h : ¬ (page S lo n).length < n) :
    tail_scan n (t + 1) lo (S :: Ss) =
      ({ c_lo := lo, c_hi := some (last (page S lo n)), c_rows := page S lo n } ::
          (tail_scan n t (some (last (page S lo n))) Ss).1,
        (tail_scan n t (some (last (page S lo n))) Ss).2) := by
  simp only [tail_scan, if_neg h]
  rfl

/-- The bounded scan hands over to the tail reads on a short page. Port-local. -/
private theorem bounded_scan_short [Nonempty K] {n T : Nat} {M : K} {lo : Option K}
    {S : K → Prop} {Ss : List (K → Prop)} (h : (bpage S lo M n).length < n) :
    bounded_scan n T M lo (S :: Ss) =
      ({ c_lo := lo, c_hi := some M, c_rows := bpage S lo M n } ::
          (tail_scan n T (some M) Ss).1, (tail_scan n T (some M) Ss).2) := by
  simp only [bounded_scan, if_pos h]
  rfl

/-- The bounded scan continues after a full page. Port-local. -/
private theorem bounded_scan_full [Nonempty K] {n T : Nat} {M : K} {lo : Option K}
    {S : K → Prop} {Ss : List (K → Prop)} (h : ¬ (bpage S lo M n).length < n) :
    bounded_scan n T M lo (S :: Ss) =
      ({ c_lo := lo, c_hi := some (last (bpage S lo M n)), c_rows := bpage S lo M n } ::
          (bounded_scan n T M (some (last (bpage S lo M n))) Ss).1,
        (bounded_scan n T M (some (last (bpage S lo M n))) Ss).2) := by
  simp only [bounded_scan, if_neg h]
  rfl

/-- The classic scan ends on a short page. Port-local. -/
private theorem classic_scan_short [Nonempty K] {n : Nat} {lo : Option K} {S : K → Prop}
    {Ss : List (K → Prop)} (h : (page S lo n).length < n) :
    classic_scan n lo (S :: Ss) =
      ([{ c_lo := lo, c_hi := none, c_rows := page S lo n }], .Completed) := by
  simp only [classic_scan, if_pos h]

/-- The classic scan continues after a full page. Port-local. -/
private theorem classic_scan_full [Nonempty K] {n : Nat} {lo : Option K} {S : K → Prop}
    {Ss : List (K → Prop)} (h : ¬ (page S lo n).length < n) :
    classic_scan n lo (S :: Ss) =
      ({ c_lo := lo, c_hi := some (last (page S lo n)), c_rows := page S lo n } ::
          (classic_scan n (some (last (page S lo n))) Ss).1,
        (classic_scan n (some (last (page S lo n))) Ss).2) := by
  simp only [classic_scan, if_neg h]
  rfl

/-- HOL's `last_ConsR`, for the total `last`. Port-local. -/
private theorem last_cons_ne {α : Type w} [Nonempty α] {a : α} {l : List α} (h : l ≠ []) :
    last (a :: l) = last l := by
  rw [last_eq_getLast (List.cons_ne_nil a l), last_eq_getLast h, List.getLast_cons h]

/-- HOL's `last.simps` on a singleton, for the total `last`. Port-local. -/
private theorem last_singleton {α : Type w} [Nonempty α] (a : α) : last [a] = a := by
  rw [last_eq_getLast (List.cons_ne_nil a []), List.getLast_singleton]

/-- The tail reads emit a chain. Isabelle: `tail_scan_chain`. -/
theorem tail_scan_chain [Nonempty K] {n t : Nat} {lo : Option K} {Ss : List (K → Prop)}
    (hn : 0 < n) : ranges_chain lo (tail_scan n t lo Ss).1 := by
  induction t generalizing lo Ss with
  | zero => simp [tail_scan, ranges_chain]
  | succ t ih =>
    cases Ss with
    | nil => simp [tail_scan, ranges_chain]
    | cons S Ss =>
      by_cases full : (page S lo n).length < n
      · rw [tail_scan_short full]
        simp [ranges_chain]
      · rw [tail_scan_full full]
        have ne := page_full_ne hn full
        simp only [ranges_chain, true_and]
        refine ⟨?_, ih⟩
        rw [last_eq_getLast ne]
        exact above_lower_le (page_last_above ne)

/-- What the tail reads leave to later reads is what the outcome leaves
uncovered. The set equality is stated pointwise. Isabelle:
`tail_scan_rest`. -/
theorem tail_scan_rest [Nonempty K] {n t : Nat} {lo : Option K} {Ss : List (K → Prop)} :
    ∀ k, chain_rest lo (tail_scan n t lo Ss).1 k ↔ uncovered (tail_scan n t lo Ss).2 k := by
  induction t generalizing lo Ss with
  | zero => intro k; simp [tail_scan, chain_rest, uncovered]
  | succ t ih =>
    cases Ss with
    | nil => intro k; simp [tail_scan, chain_rest, uncovered]
    | cons S Ss =>
      intro k
      by_cases full : (page S lo n).length < n
      · rw [tail_scan_short full]
        simp [chain_rest, uncovered]
      · rw [tail_scan_full full]
        simp only [chain_rest]
        exact ih k

/-- Isabelle: `tail_scan_length`. -/
theorem tail_scan_length [Nonempty K] {n t : Nat} {lo : Option K} {Ss : List (K → Prop)} :
    (tail_scan n t lo Ss).1.length ≤ Ss.length := by
  induction t generalizing lo Ss with
  | zero => simp [tail_scan]
  | succ t ih =>
    cases Ss with
    | nil => simp [tail_scan]
    | cons S Ss =>
      by_cases full : (page S lo n).length < n
      · rw [tail_scan_short full]
        simp
      · rw [tail_scan_full full]
        simp only [List.length_cons]
        exact Nat.succ_le_succ ih

/-- The `i`-th read of the tail reads exists for each chunk they emit.
Port-local, the bound under Isabelle's `Ss ! i`. -/
theorem tail_read_bound [Nonempty K] {n t i : Nat} {lo : Option K} {Ss : List (K → Prop)}
    (hi : i < (tail_scan n t lo Ss).1.length) : i < Ss.length :=
  Nat.lt_of_lt_of_le hi tail_scan_length

/-- Each chunk of the tail reads is exact for its own read, on a finite
source state. Isabelle: `tail_scan_exact`. -/
theorem tail_scan_exact [Nonempty K] {n t i : Nat} {lo : Option K} {Ss : List (K → Prop)}
    (hn : 0 < n) (hi : i < (tail_scan n t lo Ss).1.length)
    (fin : finite (Ss[i]'(tail_read_bound hi))) :
    chunk_exact (Ss[i]'(tail_read_bound hi)) ((tail_scan n t lo Ss).1[i]'hi) := by
  induction t generalizing lo Ss i with
  | zero => simp [tail_scan] at hi
  | succ t ih =>
    cases Ss with
    | nil => simp [tail_scan] at hi
    | cons S Ss =>
      by_cases full : (page S lo n).length < n
      · have hi' := hi
        simp only [tail_scan_short full, List.length_cons, List.length_nil] at hi'
        have i0 : i = 0 := by omega
        subst i0
        simp only [tail_scan_short full]
        exact exact_open_above fin full
      · have ne := page_full_ne hn full
        cases i with
        | zero =>
          simp only [tail_scan_full full]
          show chunk_exact S
            { c_lo := lo, c_hi := some (last (page S lo n)), c_rows := page S lo n }
          rw [last_eq_getLast ne]
          exact exact_closed fin ne
        | succ j =>
          have hj : j < (tail_scan n t (some (last (page S lo n))) Ss).1.length := by
            have hi' := hi
            simp only [tail_scan_full full, List.length_cons] at hi'
            omega
          have h := ih hj fin
          simp only [tail_scan_full full]
          exact h

/-- A pass stopped by the tail-read limit ends with the last key its last
read returned. Isabelle: `tail_scan_limit_last`. -/
theorem tail_scan_limit_last [Nonempty K] {n t : Nat} {lo f : Option K}
    {Ss : List (K → Prop)} (hn : 0 < n) (ht : 0 < t)
    (stop : (tail_scan n t lo Ss).2 = .Tail_Limit f) :
    (tail_scan n t lo Ss).1 ≠ [] ∧ (last (tail_scan n t lo Ss).1).c_rows ≠ [] ∧
      f = some (last (last (tail_scan n t lo Ss).1).c_rows) := by
  induction t generalizing lo Ss with
  | zero => exact absurd ht (Nat.lt_irrefl 0)
  | succ t ih =>
    cases Ss with
    | nil => simp [tail_scan] at stop
    | cons S Ss =>
      by_cases full : (page S lo n).length < n
      · rw [tail_scan_short full] at stop
        cases stop
      · have ne := page_full_ne hn full
        rw [tail_scan_full full] at stop ⊢
        cases t with
        | zero =>
          simp only [tail_scan] at stop ⊢
          injection stop with hf
          rw [last_singleton]
          exact ⟨List.cons_ne_nil _ _, ne, hf.symm⟩
        | succ t' =>
          obtain ⟨h1, h2, h3⟩ := ih (Nat.succ_pos t') stop
          rw [last_cons_ne h1]
          exact ⟨List.cons_ne_nil _ _, h2, h3⟩

/-- Each chunk of the tail reads is the page of its own read, from its
own lower bound. Isabelle: `tail_scan_reads`. -/
theorem tail_scan_reads [Nonempty K] {n t i : Nat} {lo : Option K} {Ss : List (K → Prop)}
    (hi : i < (tail_scan n t lo Ss).1.length) :
    ((tail_scan n t lo Ss).1[i]'hi).c_rows =
      page (Ss[i]'(tail_read_bound hi)) ((tail_scan n t lo Ss).1[i]'hi).c_lo n := by
  induction t generalizing lo Ss i with
  | zero => simp [tail_scan] at hi
  | succ t ih =>
    cases Ss with
    | nil => simp [tail_scan] at hi
    | cons S Ss =>
      by_cases full : (page S lo n).length < n
      · have hi' := hi
        simp only [tail_scan_short full, List.length_cons, List.length_nil] at hi'
        have i0 : i = 0 := by omega
        subst i0
        simp only [tail_scan_short full]
        rfl
      · cases i with
        | zero =>
          simp only [tail_scan_full full]
          rfl
        | succ j =>
          have hj : j < (tail_scan n t (some (last (page S lo n))) Ss).1.length := by
            have hi' := hi
            simp only [tail_scan_full full, List.length_cons] at hi'
            omega
          have h := ih hj
          simp only [tail_scan_full full]
          exact h

/-- The range rule of the tail reads: a full page closes at its last key,
a short page is open above. Isabelle's `last (c_rows c)` is the total
`last`, since the rows are empty when the chunk limit is 0. Isabelle:
`tail_scan_rule`. -/
theorem tail_scan_rule [Nonempty K] {n t : Nat} {lo : Option K} {Ss : List (K → Prop)}
    {c : Chunk K} (hc : c ∈ (tail_scan n t lo Ss).1) :
    (c.c_rows.length = n ∧ c.c_hi = some (last c.c_rows)) ∨
      (c.c_rows.length < n ∧ c.c_hi = none) := by
  induction t generalizing lo Ss with
  | zero => simp [tail_scan] at hc
  | succ t ih =>
    cases Ss with
    | nil => simp [tail_scan] at hc
    | cons S Ss =>
      by_cases full : (page S lo n).length < n
      · rw [tail_scan_short full, List.mem_singleton] at hc
        subst hc
        exact Or.inr ⟨full, rfl⟩
      · rw [tail_scan_full full] at hc
        rcases List.mem_cons.mp hc with h | h
        · subst h
          have len : (page S lo n).length = n :=
            Nat.le_antisymm page_length_le (Nat.le_of_not_lt full)
          exact Or.inl ⟨len, rfl⟩
        · exact ih h

/-- A completed tail scan ends with a short range open above. Isabelle:
`tail_scan_completed`. -/
theorem tail_scan_completed [Nonempty K] {n t : Nat} {lo : Option K} {Ss : List (K → Prop)}
    (h : (tail_scan n t lo Ss).2 = .Completed) :
    (tail_scan n t lo Ss).1 ≠ [] ∧ (last (tail_scan n t lo Ss).1).c_hi = none ∧
      (last (tail_scan n t lo Ss).1).c_rows.length < n := by
  induction t generalizing lo Ss with
  | zero => simp [tail_scan] at h
  | succ t ih =>
    cases Ss with
    | nil => simp [tail_scan] at h
    | cons S Ss =>
      by_cases full : (page S lo n).length < n
      · rw [tail_scan_short full]
        rw [last_singleton]
        exact ⟨List.cons_ne_nil _ _, rfl, full⟩
      · rw [tail_scan_full full] at h ⊢
        obtain ⟨h1, h2, h3⟩ := ih h
        rw [last_cons_ne h1]
        exact ⟨List.cons_ne_nil _ _, h2, h3⟩

/-! ## The bounded main loop emits an exact chain -/

/-- Isabelle: `bounded_scan_chain`. -/
theorem bounded_scan_chain [Nonempty K] {n T : Nat} {M : K} {lo : Option K}
    {Ss : List (K → Prop)} (hn : 0 < n) (hle : lower_le lo M) :
    ranges_chain lo (bounded_scan n T M lo Ss).1 := by
  induction Ss generalizing lo with
  | nil => simp [bounded_scan, ranges_chain]
  | cons S Ss ih =>
    by_cases full : (bpage S lo M n).length < n
    · rw [bounded_scan_short full]
      simp only [ranges_chain, true_and]
      exact ⟨hle, tail_scan_chain hn⟩
    · rw [bounded_scan_full full]
      have ne := bpage_full_ne hn full
      simp only [ranges_chain, true_and]
      rw [last_eq_getLast ne]
      refine ⟨above_lower_le (bpage_last_above ne), ?_⟩
      have h := ih (lo := some ((bpage S lo M n).getLast ne)) (bpage_last_le ne)
      rw [← last_eq_getLast ne] at h ⊢
      exact h

/-- What the bounded scan leaves to later reads is what the outcome
leaves uncovered. The set equality is stated pointwise. Isabelle:
`bounded_scan_rest`. -/
theorem bounded_scan_rest [Nonempty K] {n T : Nat} {M : K} {lo : Option K}
    {Ss : List (K → Prop)} :
    ∀ k, chain_rest lo (bounded_scan n T M lo Ss).1 k ↔
      uncovered (bounded_scan n T M lo Ss).2 k := by
  induction Ss generalizing lo with
  | nil => intro k; simp [bounded_scan, chain_rest, uncovered]
  | cons S Ss ih =>
    intro k
    by_cases full : (bpage S lo M n).length < n
    · rw [bounded_scan_short full]
      simp only [chain_rest]
      exact tail_scan_rest k
    · rw [bounded_scan_full full]
      simp only [chain_rest]
      exact ih k

/-- Isabelle: `bounded_scan_length`. -/
theorem bounded_scan_length [Nonempty K] {n T : Nat} {M : K} {lo : Option K}
    {Ss : List (K → Prop)} : (bounded_scan n T M lo Ss).1.length ≤ Ss.length := by
  induction Ss generalizing lo with
  | nil => simp [bounded_scan]
  | cons S Ss ih =>
    by_cases full : (bpage S lo M n).length < n
    · rw [bounded_scan_short full]
      simp only [List.length_cons]
      exact Nat.succ_le_succ tail_scan_length
    · rw [bounded_scan_full full]
      simp only [List.length_cons]
      exact Nat.succ_le_succ ih

/-- The `i`-th read of the bounded scan exists for each chunk it emits.
Port-local, the bound under Isabelle's `Ss ! i`. -/
theorem bounded_read_bound [Nonempty K] {n T i : Nat} {M : K} {lo : Option K}
    {Ss : List (K → Prop)} (hi : i < (bounded_scan n T M lo Ss).1.length) :
    i < Ss.length :=
  Nat.lt_of_lt_of_le hi bounded_scan_length

/-- Isabelle: `bounded_scan_exact`. -/
theorem bounded_scan_exact [Nonempty K] {n T i : Nat} {M : K} {lo : Option K}
    {Ss : List (K → Prop)} (hn : 0 < n) (hi : i < (bounded_scan n T M lo Ss).1.length)
    (fin : finite (Ss[i]'(bounded_read_bound hi))) :
    chunk_exact (Ss[i]'(bounded_read_bound hi)) ((bounded_scan n T M lo Ss).1[i]'hi) := by
  induction Ss generalizing lo i with
  | nil => simp [bounded_scan] at hi
  | cons S Ss ih =>
    cases i with
    | zero =>
      by_cases full : (bpage S lo M n).length < n
      · simp only [bounded_scan_short full]
        exact exact_closed_at_max fin full
      · have ne := bpage_full_ne hn full
        simp only [bounded_scan_full full]
        show chunk_exact S
          { c_lo := lo, c_hi := some (last (bpage S lo M n)), c_rows := bpage S lo M n }
        rw [last_eq_getLast ne]
        exact exact_bounded_closed fin ne
    | succ j =>
      by_cases full : (bpage S lo M n).length < n
      · have hj : j < (tail_scan n T (some M) Ss).1.length := by
          have hi' := hi
          simp only [bounded_scan_short full, List.length_cons] at hi'
          omega
        have h := tail_scan_exact hn hj fin
        simp only [bounded_scan_short full]
        exact h
      · have hj : j < (bounded_scan n T M (some (last (bpage S lo M n))) Ss).1.length := by
          have hi' := hi
          simp only [bounded_scan_full full, List.length_cons] at hi'
          omega
        have h := ih hj fin
        simp only [bounded_scan_full full]
        exact h

/-- Isabelle: `bounded_scan_limit_last`. -/
theorem bounded_scan_limit_last [Nonempty K] {n T : Nat} {M : K} {lo f : Option K}
    {Ss : List (K → Prop)} (hn : 0 < n) (hT : 0 < T)
    (stop : (bounded_scan n T M lo Ss).2 = .Tail_Limit f) :
    (bounded_scan n T M lo Ss).1 ≠ [] ∧ (last (bounded_scan n T M lo Ss).1).c_rows ≠ [] ∧
      f = some (last (last (bounded_scan n T M lo Ss).1).c_rows) := by
  induction Ss generalizing lo with
  | nil => simp [bounded_scan] at stop
  | cons S Ss ih =>
    by_cases full : (bpage S lo M n).length < n
    · rw [bounded_scan_short full] at stop ⊢
      obtain ⟨h1, h2, h3⟩ := tail_scan_limit_last hn hT stop
      rw [last_cons_ne h1]
      exact ⟨List.cons_ne_nil _ _, h2, h3⟩
    · rw [bounded_scan_full full] at stop ⊢
      obtain ⟨h1, h2, h3⟩ := ih stop
      rw [last_cons_ne h1]
      exact ⟨List.cons_ne_nil _ _, h2, h3⟩

/-- With no tail reads configured, a stopped bounded scan stops at the
recorded maximum. Isabelle: `bounded_scan_no_tail_reads`. -/
theorem bounded_scan_no_tail_reads [Nonempty K] {n : Nat} {M : K} {lo f : Option K}
    {Ss : List (K → Prop)} (h : (bounded_scan n 0 M lo Ss).2 = .Tail_Limit f) :
    f = some M := by
  induction Ss generalizing lo with
  | nil => simp [bounded_scan] at h
  | cons S Ss ih =>
    by_cases full : (bpage S lo M n).length < n
    · rw [bounded_scan_short full] at h
      simp only [tail_scan] at h
      injection h with hf
      exact hf.symm
    · rw [bounded_scan_full full] at h
      exact ih h

/-- Each chunk of the bounded scan is the plain or the bounded page of its
own read. Isabelle: `bounded_scan_reads`. -/
theorem bounded_scan_reads [Nonempty K] {n T i : Nat} {M : K} {lo : Option K}
    {Ss : List (K → Prop)} (hi : i < (bounded_scan n T M lo Ss).1.length) :
    ((bounded_scan n T M lo Ss).1[i]'hi).c_rows =
        page (Ss[i]'(bounded_read_bound hi)) ((bounded_scan n T M lo Ss).1[i]'hi).c_lo n ∨
      ((bounded_scan n T M lo Ss).1[i]'hi).c_rows =
        bpage (Ss[i]'(bounded_read_bound hi)) ((bounded_scan n T M lo Ss).1[i]'hi).c_lo M n := by
  induction Ss generalizing lo i with
  | nil => simp [bounded_scan] at hi
  | cons S Ss ih =>
    cases i with
    | zero =>
      right
      by_cases full : (bpage S lo M n).length < n
      · simp only [bounded_scan_short full]
        rfl
      · simp only [bounded_scan_full full]
        rfl
    | succ j =>
      by_cases full : (bpage S lo M n).length < n
      · have hj : j < (tail_scan n T (some M) Ss).1.length := by
          have hi' := hi
          simp only [bounded_scan_short full, List.length_cons] at hi'
          omega
        have h := tail_scan_reads hj
        left
        simp only [bounded_scan_short full]
        exact h
      · have hj : j < (bounded_scan n T M (some (last (bpage S lo M n))) Ss).1.length := by
          have hi' := hi
          simp only [bounded_scan_full full, List.length_cons] at hi'
          omega
        have h := ih hj
        simp only [bounded_scan_full full]
        exact h

/-- The range rule of the bounded scan. Isabelle's `last (c_rows c)` is
the total `last`. Isabelle: `bounded_scan_rule`. -/
theorem bounded_scan_rule [Nonempty K] {n T : Nat} {M : K} {lo : Option K}
    {Ss : List (K → Prop)} {c : Chunk K} (hc : c ∈ (bounded_scan n T M lo Ss).1) :
    (c.c_rows.length = n ∧ c.c_hi = some (last c.c_rows)) ∨
      (c.c_rows.length < n ∧ c.c_hi = none) ∨
      (c.c_rows.length < n ∧ c.c_hi = some M) := by
  induction Ss generalizing lo with
  | nil => simp [bounded_scan] at hc
  | cons S Ss ih =>
    by_cases full : (bpage S lo M n).length < n
    · rw [bounded_scan_short full] at hc
      rcases List.mem_cons.mp hc with h | h
      · subst h
        exact Or.inr (Or.inr ⟨full, rfl⟩)
      · rcases tail_scan_rule h with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
    · rw [bounded_scan_full full] at hc
      rcases List.mem_cons.mp hc with h | h
      · subst h
        have len : (bpage S lo M n).length = n :=
          Nat.le_antisymm bpage_length_le (Nat.le_of_not_lt full)
        exact Or.inl ⟨len, rfl⟩
      · exact ih h

/-- Isabelle: `bounded_scan_completed`. -/
theorem bounded_scan_completed [Nonempty K] {n T : Nat} {M : K} {lo : Option K}
    {Ss : List (K → Prop)} (h : (bounded_scan n T M lo Ss).2 = .Completed) :
    (bounded_scan n T M lo Ss).1 ≠ [] ∧ (last (bounded_scan n T M lo Ss).1).c_hi = none ∧
      (last (bounded_scan n T M lo Ss).1).c_rows.length < n := by
  induction Ss generalizing lo with
  | nil => simp [bounded_scan] at h
  | cons S Ss ih =>
    by_cases full : (bpage S lo M n).length < n
    · rw [bounded_scan_short full] at h ⊢
      obtain ⟨h1, h2, h3⟩ := tail_scan_completed h
      rw [last_cons_ne h1]
      exact ⟨List.cons_ne_nil _ _, h2, h3⟩
    · rw [bounded_scan_full full] at h ⊢
      obtain ⟨h1, h2, h3⟩ := ih h
      rw [last_cons_ne h1]
      exact ⟨List.cons_ne_nil _ _, h2, h3⟩

/-! ## Pass-level facts -/

/-- Isabelle: `pass_chain`. -/
theorem pass_chain [Nonempty K] {n T : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    (hn : 0 < n) : ranges_chain none (bounded_pass n T Mo Ss).1 := by
  cases Mo with
  | none => exact tail_scan_chain hn
  | some M => exact bounded_scan_chain hn trivial

/-- The set equality is stated pointwise. Isabelle: `pass_rest`. -/
theorem pass_rest [Nonempty K] {n T : Nat} {Mo : Option K} {Ss : List (K → Prop)} :
    ∀ k, chain_rest none (bounded_pass n T Mo Ss).1 k ↔
      uncovered (bounded_pass n T Mo Ss).2 k := by
  cases Mo with
  | none => exact tail_scan_rest
  | some M => exact bounded_scan_rest

/-- A pass covers exactly the keys its outcome does not leave uncovered.
The Isabelle set equality `covered (...) = - uncovered (...)` is stated
pointwise. Isabelle: `pass_covered`. -/
theorem pass_covered [Nonempty K] {n T : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    (hn : 0 < n) :
    ∀ k, covered (bounded_pass n T Mo Ss).1 k ↔ ¬ uncovered (bounded_pass n T Mo Ss).2 k := by
  intro k
  rw [chain_covered (pass_chain hn) k, pass_rest k]
  simp only [above_lo_None, true_and]

/-- The `i`-th read of a pass exists for each chunk the pass emits.
Port-local, the bound under Isabelle's `Ss ! i`. -/
theorem pass_read_bound [Nonempty K] {n T i : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} (hcs : cs = (bounded_pass n T Mo Ss).1) (hi : i < cs.length) :
    i < Ss.length := by
  subst hcs
  cases Mo with
  | none => exact tail_read_bound hi
  | some M => exact bounded_read_bound hi

/-- Isabelle: `pass_exact`. -/
theorem pass_exact [Nonempty K] {n T i : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    (hn : 0 < n) (hi : i < (bounded_pass n T Mo Ss).1.length)
    (fin : finite (Ss[i]'(pass_read_bound rfl hi))) :
    chunk_exact (Ss[i]'(pass_read_bound rfl hi)) ((bounded_pass n T Mo Ss).1[i]'hi) := by
  cases Mo with
  | none => exact tail_scan_exact hn hi fin
  | some M => exact bounded_scan_exact hn hi fin

/-! ## Main results for the bounded pass

Throughout, `n` is the chunk limit, `T` the tail-read limit, `Mo` the
maximum key recorded at the start (or `none` for a table that was empty
then), and `Ss` the source states at the cuts of the successive reads.
The `i`-th chunk is the result of the `i`-th read. -/

/-- Isabelle: `chunks_le_reads`. -/
theorem chunks_le_reads [Nonempty K] {n T : Nat} {Mo : Option K} {Ss : List (K → Prop)} :
    (bounded_pass n T Mo Ss).1.length ≤ Ss.length := by
  cases Mo with
  | none => exact tail_scan_length
  | some M => exact bounded_scan_length

/-- Each chunk is the result of its own read: its rows are the page of
the source state at the `i`-th cut, queried from the chunk's own lower
bound, either plain or bounded at the recorded maximum. Isabelle:
`chunk_is_read`. -/
theorem chunk_is_read [Nonempty K] {n T i : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} (hcs : cs = (bounded_pass n T Mo Ss).1) (hi : i < cs.length) :
    (cs[i]'hi).c_rows = page (Ss[i]'(pass_read_bound hcs hi)) (cs[i]'hi).c_lo n ∨
      (∃ M, Mo = some M ∧
        (cs[i]'hi).c_rows = bpage (Ss[i]'(pass_read_bound hcs hi)) (cs[i]'hi).c_lo M n) := by
  subst hcs
  cases Mo with
  | none => exact Or.inl (tail_scan_reads hi)
  | some M =>
    rcases bounded_scan_reads hi with h | h
    · exact Or.inl h
    · exact Or.inr ⟨M, rfl, h⟩

/-- The range rule, as a property of the output. A chunk with a full page
closes at its last returned key. A chunk with a short page is open above,
or closes at the recorded maximum. Isabelle's `last (c_rows c)` is the
total `last`. Isabelle: `range_rule`. -/
theorem range_rule [Nonempty K] {n T : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} {c : Chunk K} (hcs : cs = (bounded_pass n T Mo Ss).1)
    (hc : c ∈ cs) :
    (c.c_rows.length = n ∧ c.c_hi = some (last c.c_rows)) ∨
      (c.c_rows.length < n ∧ c.c_hi = none) ∨
      (c.c_rows.length < n ∧ c.c_hi = Mo) := by
  subst hcs
  cases Mo with
  | none =>
    rcases tail_scan_rule hc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | some M => exact bounded_scan_rule hc

/-- A pass completes only on a short page of an unbounded read: its last
range is open above and its last page is short. Isabelle:
`completed_last_open_above`. -/
theorem completed_last_open_above [Nonempty K] {n T : Nat} {Mo : Option K}
    {Ss : List (K → Prop)} {cs : List (Chunk K)}
    (complete : (bounded_pass n T Mo Ss).2 = .Completed)
    (hcs : cs = (bounded_pass n T Mo Ss).1) :
    cs ≠ [] ∧ (last cs).c_hi = none ∧ (last cs).c_rows.length < n := by
  subst hcs
  cases Mo with
  | none => exact tail_scan_completed complete
  | some M => exact bounded_scan_completed complete

/-- With at least one tail read configured, an empty source table produces
a single chunk with both bounds open and no rows. The empty set `{}` is
the predicate `fun _ => False`. Isabelle: `empty_table_single_range`. -/
theorem empty_table_single_range [Nonempty K] {n T : Nat} {Ss : List (K → Prop)}
    (hn : 0 < n) (hT : 0 < T) :
    bounded_pass n T none ((fun _ => False) :: Ss) =
      ([{ c_lo := none, c_hi := none, c_rows := [] }], .Completed) := by
  have hp : page (fun _ : K => False) none n = [] := by
    simp only [page]
    exact smallest_eqI List.Pairwise.nil (fun k => by simp) (List.take_nil)
  show tail_scan n T none ((fun _ => False) :: Ss) = _
  rw [tail_scan_pos_Cons hT, hp]
  simp only [List.length_nil, if_pos hn]

/-- The emitted ranges are pairwise disjoint. The Isabelle set equality
`chunk_keys (cs ! i) ∩ chunk_keys (cs ! j) = {}` is stated pointwise.
Isabelle: `ranges_disjoint`. -/
theorem ranges_disjoint [Nonempty K] {n T i j : Nat} {Mo : Option K}
    {Ss : List (K → Prop)} {cs : List (Chunk K)} (hn : 0 < n)
    (hcs : cs = (bounded_pass n T Mo Ss).1) (hi : i < cs.length) (hj : j < cs.length)
    (hij : i ≠ j) :
    ∀ k, chunk_keys (cs[i]'hi) k → chunk_keys (cs[j]'hj) k → False := by
  have sw := chain_disjoint (hcs ▸ pass_chain (T := T) (Mo := Mo) (Ss := Ss) hn)
  rw [List.pairwise_iff_getElem] at sw
  intro k hki hkj
  rcases Nat.lt_or_gt_of_ne hij with lt | gt
  · exact sw i j hi hj lt k hki hkj
  · exact sw j i hj hi gt k hkj hki

/-- The first range is open below. Isabelle: `ranges_first_open_below`. -/
theorem ranges_first_open_below [Nonempty K] {n T : Nat} {Mo : Option K}
    {Ss : List (K → Prop)} {cs : List (Chunk K)} (hn : 0 < n)
    (hcs : cs = (bounded_pass n T Mo Ss).1) (ne : cs ≠ []) :
    (cs[0]'(List.length_pos_iff.mpr ne)).c_lo = none :=
  chain_first (hcs ▸ pass_chain (T := T) (Mo := Mo) (Ss := Ss) hn) ne

/-- Each next range starts exactly where the previous one ends. Isabelle:
`ranges_consecutive`. -/
theorem ranges_consecutive [Nonempty K] {n T i : Nat} {Mo : Option K}
    {Ss : List (K → Prop)} {cs : List (Chunk K)} (hn : 0 < n)
    (hcs : cs = (bounded_pass n T Mo Ss).1) (hi : i + 1 < cs.length) :
    ∃ b, (cs[i]'(Nat.lt_of_succ_lt hi)).c_hi = some b ∧ (cs[i + 1]'hi).c_lo = some b :=
  chain_consecutive (hcs ▸ pass_chain (T := T) (Mo := Mo) (Ss := Ss) hn) hi

/-- Consecutive ranges `(a, b]` and `(b, c]` leave no gap. The Isabelle
union is stated as a disjunction. Isabelle: `ranges_no_gap`. -/
theorem ranges_no_gap [Nonempty K] {n T i : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} {k : K} (hn : 0 < n) (hcs : cs = (bounded_pass n T Mo Ss).1)
    (hi : i + 1 < cs.length)
    (lo : above_lo (cs[i]'(Nat.lt_of_succ_lt hi)).c_lo k)
    (hi' : upto_hi (cs[i + 1]'hi).c_hi k) :
    chunk_keys (cs[i]'(Nat.lt_of_succ_lt hi)) k ∨ chunk_keys (cs[i + 1]'hi) k := by
  obtain ⟨b, hb1, hb2⟩ := ranges_consecutive hn hcs hi
  rcases ord_lt_or_le b k with high | low
  · right
    refine ⟨?_, hi'⟩
    rw [hb2]
    exact high
  · left
    refine ⟨lo, ?_⟩
    rw [hb1]
    exact low

/-- A completed pass covers every key. The Isabelle set equality
`covered (...) = UNIV` is stated pointwise. Isabelle:
`union_on_completion`. -/
theorem union_on_completion [Nonempty K] {n T : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    (hn : 0 < n) (complete : (bounded_pass n T Mo Ss).2 = .Completed) :
    ∀ k, covered (bounded_pass n T Mo Ss).1 k := by
  intro k
  rw [pass_covered hn k, complete]
  exact id

/-- A pass stopped by the tail-read limit covers exactly the keys at or
below its frontier. The set equality is stated pointwise. Isabelle:
`union_on_limit`. -/
theorem union_on_limit [Nonempty K] {n T : Nat} {Mo f : Option K} {Ss : List (K → Prop)}
    (hn : 0 < n) (stop : (bounded_pass n T Mo Ss).2 = .Tail_Limit f) :
    ∀ k, covered (bounded_pass n T Mo Ss).1 k ↔ ¬ above_lo f k := by
  intro k
  rw [pass_covered hn k, stop]
  rfl

/-- The set equality `- covered (...) = {k. above_lo f k}` is stated
pointwise. Isabelle: `uncovered_on_limit`. -/
theorem uncovered_on_limit [Nonempty K] {n T : Nat} {Mo f : Option K} {Ss : List (K → Prop)}
    (hn : 0 < n) (stop : (bounded_pass n T Mo Ss).2 = .Tail_Limit f) :
    ∀ k, ¬ covered (bounded_pass n T Mo Ss).1 k ↔ above_lo f k := by
  intro k
  rw [union_on_limit hn stop k]
  exact Classical.not_not

/-- The frontier of a pass stopped by the tail-read limit, with at least
one tail read allowed: the last key that the last read returned. Isabelle:
`limit_frontier_last_returned`. -/
theorem limit_frontier_last_returned [Nonempty K] {n T : Nat} {Mo f : Option K}
    {Ss : List (K → Prop)} {cs : List (Chunk K)} (hn : 0 < n) (hT : 0 < T)
    (stop : (bounded_pass n T Mo Ss).2 = .Tail_Limit f)
    (hcs : cs = (bounded_pass n T Mo Ss).1) :
    cs ≠ [] ∧ (last cs).c_rows ≠ [] ∧ f = some (last (last cs).c_rows) := by
  subst hcs
  cases Mo with
  | none => exact tail_scan_limit_last hn hT stop
  | some M => exact bounded_scan_limit_last hn hT stop

/-- With no tail reads allowed, the frontier of a stopped pass is the
recorded maximum. Isabelle: `limit_frontier_no_tail_reads`. -/
theorem limit_frontier_no_tail_reads [Nonempty K] {n : Nat} {Mo f : Option K}
    {Ss : List (K → Prop)} (stop : (bounded_pass n 0 Mo Ss).2 = .Tail_Limit f) :
    f = Mo := by
  cases Mo with
  | none =>
    simp only [bounded_pass, tail_scan] at stop
    injection stop with hf
    exact hf.symm
  | some M => exact bounded_scan_no_tail_reads stop

/-- With at least one tail read configured, a stopped pass covers exactly
the keys at or below the last key its last read returned. Isabelle's
`last (c_rows (last cs))` is the total `last`, and the set equality is
stated pointwise. Isabelle: `union_on_limit_last_returned`. -/
theorem union_on_limit_last_returned [Nonempty K] {n T : Nat} {Mo f : Option K}
    {Ss : List (K → Prop)} {cs : List (Chunk K)} {b : K} (hn : 0 < n) (hT : 0 < T)
    (stop : (bounded_pass n T Mo Ss).2 = .Tail_Limit f)
    (hcs : cs = (bounded_pass n T Mo Ss).1) (hb : b = last (last cs).c_rows) :
    ∀ k, covered cs k ↔ k ≤ b := by
  have hf : f = some b := by
    rw [hb]
    exact (limit_frontier_last_returned hn hT stop hcs).2.2
  intro k
  rw [hcs, union_on_limit hn stop k, hf, above_lo_Some]
  exact ord_not_lt

/-- The set equality `- covered cs = {k. b < k}` is stated pointwise.
Isabelle: `uncovered_on_limit_last_returned`. -/
theorem uncovered_on_limit_last_returned [Nonempty K] {n T : Nat} {Mo f : Option K}
    {Ss : List (K → Prop)} {cs : List (Chunk K)} {b : K} (hn : 0 < n) (hT : 0 < T)
    (stop : (bounded_pass n T Mo Ss).2 = .Tail_Limit f)
    (hcs : cs = (bounded_pass n T Mo Ss).1) (hb : b = last (last cs).c_rows) :
    ∀ k, ¬ covered cs k ↔ b < k := by
  have hf : f = some b := by
    rw [hb]
    exact (limit_frontier_last_returned hn hT stop hcs).2.2
  intro k
  rw [hcs, uncovered_on_limit hn stop k, hf, above_lo_Some]

/-- While the pass is still running, the ranges emitted so far tile
exactly the keys at or below the frontier. The set equality is stated
pointwise. Isabelle: `union_in_progress`. -/
theorem union_in_progress [Nonempty K] {n T : Nat} {Mo f : Option K} {Ss : List (K → Prop)}
    (hn : 0 < n) (run : (bounded_pass n T Mo Ss).2 = .Running f) :
    ∀ k, covered (bounded_pass n T Mo Ss).1 k ↔ ¬ above_lo f k := by
  intro k
  rw [pass_covered hn k, run]
  rfl

/-- Soundness of every range for its own read, on a finite source state.
The set equality is stated pointwise. Isabelle: `range_exact`. -/
theorem range_exact [Nonempty K] {n T i : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} (hn : 0 < n) (hcs : cs = (bounded_pass n T Mo Ss).1)
    (hi : i < cs.length) (fin : finite (Ss[i]'(pass_read_bound hcs hi))) :
    ∀ k, k ∈ (cs[i]'hi).c_rows ↔
      (chunk_keys (cs[i]'hi) k ∧ (Ss[i]'(pass_read_bound hcs hi)) k) := by
  subst hcs
  exact pass_exact hn hi fin

/-- Isabelle: `range_sound`. -/
theorem range_sound [Nonempty K] {n T i : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} {k : K} (hn : 0 < n) (hcs : cs = (bounded_pass n T Mo Ss).1)
    (hi : i < cs.length) (fin : finite (Ss[i]'(pass_read_bound hcs hi)))
    (hk : chunk_keys (cs[i]'hi) k) (present : (Ss[i]'(pass_read_bound hcs hi)) k) :
    k ∈ (cs[i]'hi).c_rows :=
  (range_exact hn hcs hi fin k).mpr ⟨hk, present⟩

/-- A key of a range that its read did not return was absent at that
read's cut. Isabelle: `range_absent`. -/
theorem range_absent [Nonempty K] {n T i : Nat} {Mo : Option K} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} {k : K} (hn : 0 < n) (hcs : cs = (bounded_pass n T Mo Ss).1)
    (hi : i < cs.length) (fin : finite (Ss[i]'(pass_read_bound hcs hi)))
    (hk : chunk_keys (cs[i]'hi) k) (not_selected : k ∉ (cs[i]'hi).c_rows) :
    ¬ (Ss[i]'(pass_read_bound hcs hi)) k :=
  fun present => not_selected (range_sound hn hcs hi fin hk present)

/-! ## The classic loop as a special case -/

/-- With more tail reads allowed than there are reads, the tail reads are
the classic loop. Isabelle: `tail_scan_unlimited`. -/
theorem tail_scan_unlimited [Nonempty K] {n t : Nat} {lo : Option K} {Ss : List (K → Prop)}
    (h : Ss.length < t) : tail_scan n t lo Ss = classic_scan n lo Ss := by
  induction Ss generalizing t lo with
  | nil =>
    cases t with
    | zero => exact absurd h (Nat.lt_irrefl 0)
    | succ t => rfl
  | cons S Ss ih =>
    cases t with
    | zero => exact absurd h (Nat.not_lt_zero _)
    | succ t =>
      have lt : Ss.length < t := by
        simp only [List.length_cons] at h
        omega
      by_cases full : (page S lo n).length < n
      · rw [tail_scan_short full, classic_scan_short full]
      · rw [tail_scan_full full, classic_scan_full full, ih lt]

/-- Isabelle: `classic_is_special_case`. -/
theorem classic_is_special_case [Nonempty K] {n T : Nat} {Ss : List (K → Prop)}
    (h : Ss.length < T) : bounded_pass n T none Ss = classic_pass n Ss :=
  tail_scan_unlimited h

/-- HOL's `Suc (length Ss)` is `Ss.length + 1`. Isabelle: `classic_special`. -/
theorem classic_special [Nonempty K] {n : Nat} {Ss : List (K → Prop)} :
    classic_pass n Ss = bounded_pass n (Ss.length + 1) none Ss :=
  (classic_is_special_case (Nat.lt_succ_self _)).symm

/-- Isabelle: `classic_scan_not_limited`. -/
theorem classic_scan_not_limited [Nonempty K] {n : Nat} {lo f : Option K}
    {Ss : List (K → Prop)} : (classic_scan n lo Ss).2 ≠ .Tail_Limit f := by
  induction Ss generalizing lo with
  | nil => simp [classic_scan]
  | cons S Ss ih =>
    by_cases full : (page S lo n).length < n
    · rw [classic_scan_short full]
      simp
    · rw [classic_scan_full full]
      exact ih

/-- Isabelle: `classic_not_limited`. -/
theorem classic_not_limited [Nonempty K] {n : Nat} {f : Option K} {Ss : List (K → Prop)} :
    (classic_pass n Ss).2 ≠ .Tail_Limit f :=
  classic_scan_not_limited

/-- Isabelle: `classic_chunks`. -/
theorem classic_chunks [Nonempty K] {n : Nat} {Ss : List (K → Prop)} {cs : List (Chunk K)}
    (hcs : cs = (classic_pass n Ss).1) : cs = (bounded_pass n (Ss.length + 1) none Ss).1 := by
  rw [hcs, classic_special]

/-- The `i`-th read of a classic pass exists for each chunk the pass
emits. Port-local, the bound under Isabelle's `Ss ! i`. -/
theorem classic_read_bound [Nonempty K] {n i : Nat} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} (hcs : cs = (classic_pass n Ss).1) (hi : i < cs.length) :
    i < Ss.length :=
  pass_read_bound (classic_chunks hcs) hi

/-- Isabelle: `classic_ranges_disjoint`. -/
theorem classic_ranges_disjoint [Nonempty K] {n i j : Nat} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} (hn : 0 < n) (hcs : cs = (classic_pass n Ss).1)
    (hi : i < cs.length) (hj : j < cs.length) (hij : i ≠ j) :
    ∀ k, chunk_keys (cs[i]'hi) k → chunk_keys (cs[j]'hj) k → False :=
  ranges_disjoint hn (classic_chunks hcs) hi hj hij

/-- Isabelle: `classic_ranges_first_open_below`. -/
theorem classic_ranges_first_open_below [Nonempty K] {n : Nat} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} (hn : 0 < n) (hcs : cs = (classic_pass n Ss).1) (ne : cs ≠ []) :
    (cs[0]'(List.length_pos_iff.mpr ne)).c_lo = none :=
  ranges_first_open_below hn (classic_chunks hcs) ne

/-- Isabelle: `classic_ranges_consecutive`. -/
theorem classic_ranges_consecutive [Nonempty K] {n i : Nat} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} (hn : 0 < n) (hcs : cs = (classic_pass n Ss).1)
    (hi : i + 1 < cs.length) :
    ∃ b, (cs[i]'(Nat.lt_of_succ_lt hi)).c_hi = some b ∧ (cs[i + 1]'hi).c_lo = some b :=
  ranges_consecutive hn (classic_chunks hcs) hi

/-- A completed classic pass covers every key. The set equality
`covered (...) = UNIV` is stated pointwise. Isabelle:
`classic_union_on_completion`. -/
theorem classic_union_on_completion [Nonempty K] {n : Nat} {Ss : List (K → Prop)}
    (hn : 0 < n) (complete : (classic_pass n Ss).2 = .Completed) :
    ∀ k, covered (classic_pass n Ss).1 k := by
  rw [classic_special] at complete ⊢
  exact union_on_completion hn complete

/-- The set equality is stated pointwise. Isabelle:
`classic_union_in_progress`. -/
theorem classic_union_in_progress [Nonempty K] {n : Nat} {f : Option K}
    {Ss : List (K → Prop)} (hn : 0 < n) (run : (classic_pass n Ss).2 = .Running f) :
    ∀ k, covered (classic_pass n Ss).1 k ↔ ¬ above_lo f k := by
  rw [classic_special] at run ⊢
  exact union_in_progress hn run

/-- Isabelle: `classic_range_sound`. -/
theorem classic_range_sound [Nonempty K] {n i : Nat} {Ss : List (K → Prop)}
    {cs : List (Chunk K)} {k : K} (hn : 0 < n) (hcs : cs = (classic_pass n Ss).1)
    (hi : i < cs.length) (fin : finite (Ss[i]'(classic_read_bound hcs hi)))
    (hk : chunk_keys (cs[i]'hi) k) (present : (Ss[i]'(classic_read_bound hcs hi)) k) :
    k ∈ (cs[i]'hi).c_rows :=
  range_sound hn (classic_chunks hcs) hi fin hk present

/-- On an empty source table the classic pass emits a single chunk with
both bounds open and no rows. Isabelle:
`classic_empty_table_single_range`. -/
theorem classic_empty_table_single_range [Nonempty K] {n : Nat} {Ss : List (K → Prop)}
    (hn : 0 < n) :
    classic_pass n ((fun _ => False) :: Ss) =
      ([{ c_lo := none, c_hi := none, c_rows := [] }], .Completed) := by
  have hp : page (fun _ : K => False) none n = [] := by
    simp only [page]
    exact smallest_eqI List.Pairwise.nil (fun k => by simp) (List.take_nil)
  show classic_scan n none ((fun _ => False) :: Ss) = _
  have hshort : (page (fun _ : K => False) none n).length < n := by
    rw [hp]
    exact hn
  rw [classic_scan_short hshort, hp]

/-! ## The terminal rule is necessary -/

/-- Inserting a key above the first `n` entries of a list leaves those
entries unchanged. Isabelle: `take_insort_above`. -/
theorem take_insort_above {n : Nat} {xs : List K} {k : K} (h1 : n ≤ xs.length)
    (h2 : ∀ x ∈ xs.take n, x < k) : (insort k xs).take n = xs.take n := by
  induction xs generalizing n with
  | nil =>
    have hn : n = 0 := Nat.le_zero.mp h1
    subst hn
    rfl
  | cons y ys ih =>
    cases n with
    | zero => rfl
    | succ m =>
      have yk : ¬ k ≤ y :=
        ord_not_le.mpr (h2 y (by rw [List.take_succ_cons]; exact List.mem_cons_self))
      have hm : m ≤ ys.length := by
        simp only [List.length_cons] at h1
        omega
      have hbelow : ∀ x ∈ ys.take m, x < k := by
        intro x hx
        exact h2 x (by rw [List.take_succ_cons]; exact List.mem_cons_of_mem y hx)
      simp only [insort, if_neg yk, List.take_succ_cons, ih hm hbelow]

/-- A full page cannot tell whether more keys exist above its last key:
adding any key above it leaves the page unchanged. HOL's `insert k S` is
the predicate `fun x => x = k ∨ S x`. Isabelle's `last (page S lo n)` is
`getLast`, with the nonemptiness proof that `0 < n` and `full` give.
Isabelle: `full_page_hides_higher_keys`. -/
theorem full_page_hides_higher_keys {S : K → Prop} {lo : Option K} {n : Nat} {k : K}
    (fin : finite S) (hn : 0 < n) (full : (page S lo n).length = n)
    (above : (page S lo n).getLast (List.ne_nil_of_length_pos (Nat.lt_of_lt_of_eq hn full.symm)) < k) :
    page (fun x => x = k ∨ S x) lo n = page S lo n := by
  by_cases hk : S k
  · have heq : (fun x => x = k ∨ S x) = S := by
      funext x
      apply propext
      constructor
      · rintro (h | h)
        · exact h ▸ hk
        · exact h
      · exact Or.inr
    rw [heq]
  · have ne : page S lo n ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_lt_of_eq hn full.symm)
    have k_above : above_lo lo k :=
      lower_le_above (above_lower_le (page_last_above ne)) above
    have ins : (fun x => (x = k ∨ S x) ∧ above_lo lo x) =
        (fun x => x = k ∨ (S x ∧ above_lo lo x)) := by
      funext x
      apply propext
      constructor
      · rintro ⟨h | h, ha⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, ha⟩
      · rintro (h | ⟨h, ha⟩)
        · exact ⟨Or.inl h, h ▸ k_above⟩
        · exact ⟨Or.inr h, ha⟩
    have finA : finite (fun x => S x ∧ above_lo lo x) := finite_and fin (above_lo lo)
    have kA : ¬ (S k ∧ above_lo lo k) := fun h => hk h.1
    have sl := sorted_list_of_set_insert finA kA
    have len : n ≤ (sorted_list_of_set (fun x => S x ∧ above_lo lo x)).length := by
      have h := full
      simp only [page, smallest, List.length_take] at h
      omega
    have below : ∀ x ∈ (sorted_list_of_set (fun x => S x ∧ above_lo lo x)).take n, x < k := by
      intro x hx
      have hxp : x ∈ page S lo n := hx
      exact ord_lt_of_le_of_lt (sorted_le_last smallest_sorted hxp) above
    show (sorted_list_of_set (fun x => (x = k ∨ S x) ∧ above_lo lo x)).take n =
      (sorted_list_of_set (fun x => S x ∧ above_lo lo x)).take n
    rw [ins, sl]
    exact take_insort_above len below

/-- Closing a full page open above would be wrong on the source with a
higher key added. Isabelle: `open_above_after_full_page_unsound`. -/
theorem open_above_after_full_page_unsound {S : K → Prop} {lo : Option K} {n : Nat} {k : K}
    (fin : finite S) (hn : 0 < n) (full : (page S lo n).length = n)
    (above : (page S lo n).getLast (List.ne_nil_of_length_pos (Nat.lt_of_lt_of_eq hn full.symm)) < k) :
    ¬ chunk_exact (fun x => x = k ∨ S x)
        { c_lo := lo, c_hi := none, c_rows := page (fun x => x = k ∨ S x) lo n } := by
  intro ex
  have same := full_page_hides_higher_keys fin hn full above
  have ne : page S lo n ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_lt_of_eq hn full.symm)
  have k_above : above_lo lo k :=
    lower_le_above (above_lower_le (page_last_above ne)) above
  have hk : k ∈ page (fun x => x = k ∨ S x) lo n :=
    (ex k).mpr ⟨⟨k_above, trivial⟩, Or.inl rfl⟩
  rw [same] at hk
  exact ord_not_le_of_lt above (sorted_le_last smallest_sorted hk)

end Pass

end

end Tiling

end DBLogContract
