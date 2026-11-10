# Verification record: Lean port of Orphan_Absence

Port of six of the seven theories of the Isabelle/HOL session
`Orphan_Absence`, `Orphan_Absence.thy`, `Orphan_Absence_Composition.thy`,
`Orphan_Absence_Interleaved.thy`, `Orphan_Absence_Replay.thy`,
`Orphan_Absence_Tiling.thy` and `Orphan_Absence_Restart.thy`, to Lean 4,
on top of an unchanged copy of the Lean port of the Generalized DBLog
contract core. Toolchain
`leanprover/lean4:v4.32.2`, zero dependencies (core toolchain library
only). The build below ran from a clean build directory
(`rm -rf .lake && lake build`) with network access denied. Axiom bar for
every theorem: at most `propext`, `Classical.choice` and `Quot.sound`,
the three standard axioms of the Lean 4 core logic. Hashes are full
`shasum -a 256` digests.

## Source of truth

The Isabelle theories this port follows, and the four core theories they
use. Paths are relative to the deposit folder
`DBLog_Orphan_Absence_artifact-1.0/`.

| SHA-256 | File | Lines |
| --- | --- | ---: |
| `4ba055af52a1100538f9a92a33ea0fbd67a5e3e7a5ce86461647c3e265c5fcf3` | `orphan_absence/Orphan_Absence.thy` | 1,228 |
| `037ca5ffbabe3a4c1296ef48054914a20e81c33faae1e4b5a8cc262967e52a18` | `orphan_absence/Orphan_Absence_Composition.thy` | 608 |
| `fd47e419a3ba81309c564ba1faac4dc792c6be451fb54ed70e0bd2f2bf874385` | `orphan_absence/Orphan_Absence_Interleaved.thy` | 1,625 |
| `15640f8795c62fb35a62b963834881e7d40d033192b654690afc18f7d37679ce` | `orphan_absence/Orphan_Absence_Replay.thy` | 1,090 |
| `aab93c7e30928bb3cefa280b85e5680039464b2bf063dca2374c7acf4394ab6f` | `orphan_absence/Orphan_Absence_Tiling.thy` | 2,054 |
| `b90507fe3a857fb667f947f06e9ec214c6d1020c8b6dfdc222bb359eaed81b59` | `orphan_absence/Orphan_Absence_Restart.thy` | 1,396 |
| `2a36ee47f03f6ca8c9fc06b40ead4edfecfcb3724c8c2322700f2bc4d36773c2` | `dblog_framework/framework_core/Contract_Base.thy` | 297 |
| `c7f439a78b0a99bc4d40284f15945da42d6963c8414cfc0ff315f037ad36fed2` | `dblog_framework/framework_core/Cut_Theorem.thy` | 610 |
| `5ea6273af9bfe27f31d50252c723902d82861ac432b24e32e50748de7f3fde4f` | `dblog_framework/framework_core/Merge_Disciplines.thy` | 704 |
| `e5017b4210d3a006325e37833b0fc4232c01c1518f58ad5e5ad1610d1e403c3c` | `dblog_framework/framework_core/Contract_Witnesses.thy` | 612 |

The hashes of the six session theories equal their entries in the
deposit's `SHA256SUMS`. The session's remaining theory,
`Orphan_Absence_Range_Merge.thy`, is not ported, as the README explains.

## The core copy

`DBLogContract.lean`, the five files `DBLogContract/*.lean`, `LICENSE`
and `lean-toolchain` are byte-identical (checked with `cmp`) to the
corresponding files of the Lean development in the Generalized DBLog
artifact, version 1.0: the folder `dblog_framework/lean/` inside
`Generalized_DBLog_artifact-1.0.zip` with SHA-256
`a0c1e01b7e06abd4057a6b5327f06184915a0b7e1e7b2da7d7b358866bf660c0`, the
hash that the release notes of that artifact record for the public ZIP
of DOI 10.5281/zenodo.22643866. They are also byte-identical to the
working copy of that development from which this one was taken. The
core's own `README.md` and `VERIFICATION.md` are not copied. They
describe the core port and stay with that artifact. The copy builds
unchanged under the pinned toolchain and prints its own audit of 87
commands.

## Transport conventions

The port follows the global transport conventions of the core port
(classical logic through `Classical.propDecidable` as a local instance,
sets of keys as predicates, locales as structures or explicit
arguments, Isabelle names kept verbatim). The statements below are the
ones whose shape differs from the Isabelle text. Each says the same as
its Isabelle counterpart, or drops an assumption the Isabelle proof
does not use.

1. Sets as predicates, read pointwise. `absent_untouched`,
   `except_keys` and `record_enum` are predicates `K → Prop`. The two
   inclusions of `svl_ok2` become two implications. The inclusions of
   `absent_untouched_sub_dom` and `svl2_sub_dom` become implications.
   The set equalities `dom_minus_except`,
   `set (svl u) = record_enum u E D0` (in `record_enum_ok2`,
   `record_enum_covers`, `chunk_record_converges`,
   `except_overapprox_safe`), `orph_survivors`,
   `orph_absent_untouched`, `rah_survivors`, `rah_absent_untouched` and
   `rq_absent_untouched` become pointwise equivalences.
   `except_keys u ⊆ E u` and `R.absent_untouched u ⊆ set (svl2 u)` (in
   `pass_then_request_converges` and `request_after_pass_converges`)
   become implications. `rq.survivors rq_unit = {}` becomes
   `¬ survivors sc rq_unit k` for every `k`. `k ∈ sc1 ∪ sc2` becomes
   `sc1 k ∨ sc2 k`.
2. Finiteness as a listing. HOL's `finite A` holds exactly when `A` is
   the set of some list. The assumptions `finite (survivors u)` and
   `finite {k. D0 k ≠ None}` of `svl2_exists_covering` and
   `range_record_converges` are stated as
   `∃ xs : List K, ∀ k, k ∈ xs ↔ survivors S u k` and
   `∃ ys : List K, ∀ k, k ∈ ys ↔ D0 k ≠ none`. The core port states the
   finiteness assumption of `svl_exists` with a duplicate-free listing.
   This port uses a plain listing, which is the weaker assumption of the
   two, and removes duplicates in the proof (`exists_nodup_listing`).
3. Locale parameters as explicit arguments. Isabelle `emission svl s0`,
   `sink_at f k`, `the_unit k`, `win lo hi` and `pfx c` are
   `emission S units f svl s0`, `sink_at S units f f k`,
   `the_unit units f k`, `S.win lo hi` and `S.pfx c`, where
   `S : CoordinateSpace K V C` bundles the log and the denotation. In
   the composition theory, `P.emission svl1 s0` is
   `emission S U1 f1 svl1 s0`, `R.emission svl2 f1` is
   `emission S U2 f2 svl2 f1`, `P.sink_at f1 k` is
   `sink_at S U1 f1 f1 k`, `P.the_unit k` and `R.the_unit k` are
   `the_unit U1 f1 k` and `the_unit U2 f2 k`, `P.win` and `P.pfx` are
   `S.win` and `S.pfx`, and `composed svl1 svl2 s0` is
   `composed S U1 f1 U2 f2 svl1 svl2 s0`. A free state that appears only
   in a conclusion is an explicit argument: `D0` of
   `absent_replay_safe`, `unlisted_quiet_key_kept`,
   `pass_then_read_safe`, `pass_leaves_wrong_iff`,
   `absent_replay_safe_at_least_once`,
   `absent_replay_safe_at_least_once_per_key`, `pass_with_request_safe`
   with its `_rev` and `_any` forms and `PassWithRequest.pass_leaves_wrong_iff`,
   `D` of `emission_out_of_scope_replay`, `inter_key_replay`,
   `inter_rev_key_replay`, `inter_rev_same_replay`,
   `inter_any_same_replay` and `honest_stream_last`, `X` of
   `win_last_src`, `σ0` of `take_state_quiet` and `event_honest`, `D0`
   of `restart_safe`, and `D` of `resumed_key_replay` and
   `cut_key_replay`.
4. The contract as an argument. Theorems that use the assumptions of the
   Isabelle `capture_contract` locale take `H : CaptureContract S σ0
   units scope f`. The lemmas that the Isabelle session states inside
   that locale without using its assumptions are stated without `H`:
   `svl_ok_imp_ok2`, `absent_untouched_sub_dom`, `svl2_distinct`,
   `svl2_sub_dom`, `svl2_untouched`, `svl2_surv`,
   `titems_close_block2`, `svl2_exists_covering`, `sink_read_covers`,
   `dom_minus_except`, `record_enum_ok2` and `record_enum_covers`. This
   drops an unused assumption and changes nothing else. The core port
   does the same for `svl_exists` and `titems_close_block`. In the same
   way, `win_last_src` uses none of the assumptions of the locale
   `pass_then_read` and is stated without the `PassThenRead` argument,
   and `close_block_reapply_noop`, stated in the Isabelle `capture_plan`
   context, takes only the coordinate space it uses. The locale
   `pass_with_request` has no assumptions of its own beyond its two
   contracts, and its lemmas `inter_t_no_request`, `inter_t_mset`,
   `inter_t_sorted`, `inter_t_item_cases`, `inter_t_tag_bounds`,
   `inter_key_complete`, `inter_t_rev_set` and `inter_t_rev_sorted` use
   neither, so they are stated without the `PassWithRequest` argument.
   Its `capture_plan` lemmas `closes_at_item`, `closes_at_tag`,
   `emission_t_sorted` and `titems_emission_sorted` are top-level. The
   lemmas `restart_stream_timed`, `restart_cut_prefix`,
   `restart_at_frontier`, `cut_item`, `cut_tag_le`, `cut_sorted`,
   `resumed_item_cases` and `resumed_complete` of the locale
   `pass_restart` use none of its assumptions and are stated without the
   `PassRestart` argument, and the `capture_plan` lemmas of
   `Orphan_Absence_Restart.thy` are top-level.
5. The position-list normal form. `titems_emission_master2` and
   `titems_emission_out` state the per-key items of the consumed segment
   as `titems_for k (tagged_seg S a b)` where the Isabelle statements
   have `map (λp. (Suc p, L ! p)) (kposs k a b)`. This is the transport
   of the core port's `titems_emission_master`: `tagged_seg` pairs each
   event of the segment with its tag `p + 1` by `zipIdx`, without the
   junk-total `!`, and the two lists are the same entry for entry.
6. Record updates written out. `late_absence_split` writes the two
   halves that the Isabelle statement introduces with `defines` as the
   record updates `{ u with dom := fun k => u.dom k ∧ u.refresh k ≠ none }`
   and `{ u with dom := fun k => u.dom k ∧ u.refresh k = none, hi := q }`.
   The unit `[⦇u_dom = T, u_lo = lo, u_hi = hi, u_refresh = λ_. None⦈]`
   of `absence_assertion_contract` is the structure instance
   `{ dom := T, lo := lo, hi := hi, refresh := fun _ => none }`.
7. Interpretations as theorems. The Isabelle interpretations `orph` and
   `rah` of `capture_contract` are the theorems `wit_orph_contract` and
   `wit_rah_contract`, as the core port does for its fixtures. The
   lemma `rq_contract` and the interpretation `rq` that it justifies
   state one fact, which is the theorem `rq_contract`. The
   interpretation `pr` of `pass_then_read` is the theorem
   `wit_pr_instance`. In the same way, the lemmas `rqb_contract` and
   `rqo_contract` with the interpretations `rqb` and `rqo` are the
   theorems `rqb_contract` and `rqo_contract`, and the interpretations
   `pwb`, `pwa` and `pwo` of `pass_with_request` are the theorems
   `wit_pwb_instance`, `wit_pwa_instance` and `wit_pwo_instance`. For
   `Orphan_Absence_Restart.thy`, the lemma `ri_contract` with the
   interpretation `ri` is the theorem `ri_contract`, the interpretations
   `rx`, `rj`, `tr1` and `tr2` of `capture_contract` are
   `wit_rx_contract`, `wit_rj_contract`, `wit_tr1_contract` and
   `wit_tr2_contract`, the interpretations `rs`, `rs0`, `rt` and `rtr` of
   `pass_restart` are `wit_rs_instance`, `wit_rs0_instance`,
   `wit_rt_instance` and `wit_rtr_instance`, and the interpretation `tc`
   of `coordinate_space` is a definition of a coordinate space, as the
   core port defines `sc`. The interpreted constants (`orph.emission`,
   `rq.survivors`, `pr.composed`, `pwb.inter`, `rs.restart_stream` and
   the like) are the general constants applied to the fixture's space and
   unit families.
8. The two-reads locale as a structure. The locale `pass_then_read`
   imports two instances `P` and `R` of `capture_contract` over the same
   log, denotation and initial state, and adds two assumptions. It is
   the `Prop`-valued structure `PassThenRead S σ0 U1 sc1 f1 U2 sc2 f2`
   with the fields `P`, `R`, `f1_le_f2` and `f1_le_lo2`, the assumptions
   stated with `S.den` exactly as the Isabelle locale states them with
   `den`. The theorems of the locale take `H : PassThenRead S σ0 U1 sc1
   f1 U2 sc2 f2`, as the core port does for `capture_contract`. The
   locale `pass_with_request` imports the contracts `P` and `R` over the
   same log with the same frontier `f1` and adds nothing. It is the
   structure `PassWithRequest S σ0 U1 sc1 f1 U2 sc2` with the fields `P`
   and `R`, so `R.the_unit k` is `the_unit U2 f1 k`. The locale
   `pass_restart` imports the contracts `P1` and `P2`, fixes `cmt` and
   `crash` and adds five assumptions. It is the structure
   `PassRestart S σ0 U1 sc1 f1 U2 sc2 f2 cmt crash` with the fields `P1`,
   `P2`, `cmt_le_crash`, `crash_le_f1`, `crash_le_f2`, `crash_le_lo2` and
   `reexec`, the last with its strict `<` and its inclusion read
   pointwise.
9. Renamed variables. The set `K` of requested keys of
   `request_after_pass_converges` is the predicate `req`, since `K` names
   the key type in the port. In `replay_per_key` the two streams are
   named `Sq'` and `Sq`, since `S` names the coordinate space.
10. An assumption kept unused. `emission_out_of_scope` keeps the
    Isabelle assumption `s0 ⊑ f` as `_hs0f`. The Isabelle proof needs it
    to turn the window into a position list. The Lean proof does not,
    since the window is the log segment by definition. The statement is
    kept as the source states it.
11. List relations, closures and partial list functions
    (`Orphan_Absence_Replay.thy`). `suffix zs xs` and `prefix ys xs` are
    `zs <:+ xs` and `ys <+: xs`, the same existentials as HOL's
    definitions. `redelivered` is the reflexive transitive closure of
    `at_least_once`, through the port-local inductive `rtranclp` with
    HOL's two rules. A filter predicate `P :: 'a ⇒ bool` is
    `P : α → Bool`. The filter of `partitioned_delivery_per_key` decides
    its equality with the classical instance, which gives the same list.
    HOL's total `last`, `hd` and `xs ! 0` are `getLast`, `head` and
    bounded `getElem` with their nonemptiness proofs. In
    `reads_from_last` and `reads_from_hd` the proofs come from the
    statement's own assumptions through `reads_from_ne`. In
    `redelivered_hd_last` and `absence_reemit_noop` the nonemptiness is
    the witness of a dependent conjunction `∃ h : xs ≠ [], …`, which is
    equivalent to the Isabelle conjunction. The stream variable `S` of
    eight statements is named `Sq`, as in convention 9.
12. Multisets, orders and positions (`Orphan_Absence_Interleaved.thy`).
    Lean's core library has no multisets, so the multiset equality of
    `inter_t_mset` is the permutation
    `(inter_t …).Perm (emission_t … ++ (Z ++ W))`, the same claim since
    `mset (xs @ ys) = mset xs + mset ys`. The sort `linorder` of
    `sorted_const_list`, `sorted_map_fst_filter` and `sorted_le_last` is
    `[LE α] [Std.IsLinearOrder α]`, the core library's reflexive,
    transitive, antisymmetric and total `≤`, which is all these
    statements use. A position range `[a..<b]` is `List.range' a (b - a)`,
    `concat (map f xs)` is `xs.flatMap f`, and `Suc p` is `p + 1`. The
    definitions `inter_t` and `inter_t_rev` traverse the consumed log
    segment with `zipIdx`, as the core's `emission_t` does, so that they
    denote the same lists entry for entry. HOL's `L ! p` is the bounded
    `S.log[p]`. In `event_honest`, `inter_t_item_cases` and
    `inter_key_complete` the bound comes from the statement's own
    assumptions. In the assumptions of `take_state_quiet` and
    `honest_stream_last` the quantifier ranges over the positions inside
    the log only, where HOL also constrains its unspecified values beyond
    the log, so these two Lean statements are stronger. The `obtains` of
    `inter_t_item_cases` is the disjunction of its three cases. The set
    equalities `inter_t_rev_set` and `T_set` (in `inter_any_same_replay`
    and the `_any` theorems) are pointwise equivalences.
13. The standalone tiling model (`Orphan_Absence_Tiling.thy`). Every
    declaration lives in the namespace `DBLogContract.Tiling`, the role
    that Isabelle's qualification by theory name plays, since the theory
    shares the name `sorted_le_last` with `Orphan_Absence_Interleaved.thy`.
    The sort `linorder` is the port-local class `Tiling.Linorder`, which
    extends `LE` and `LT` with exactly HOL's five axioms, because these
    statements use `<` as well as `≤`. HOL's `finite` is a listing, and
    `card`, `sorted_list_of_set`, `last` and `insort` are port-local
    definitions with HOL's values on every input: `sorted_list_of_set`
    is the unique strictly sorted listing of a finite set and `[]` on an
    infinite one, `card` its length and `0` on an infinite set, and
    `last []` a fixed unspecified element. That last value needs an
    element of the key type. The scans and every theorem about them
    therefore take the instance `[Nonempty K]`. Every HOL type is
    nonempty, so these theorems cover exactly the key types the Isabelle
    theorems cover. This instance is the one assumption of the port that
    the Isabelle text does not show. Where the Isabelle statement assumes
    a list nonempty, `last xs` is `xs.getLast h` with that proof, the
    same value. Elsewhere the statements use the total `last`, as the
    Isabelle writes them. `xs ! i` is bounded `getElem`, with the bounds
    of `Ss ! i` derived from `i < length` of the emitted chunks by the
    port-local `tail_read_bound`, `bounded_read_bound`, `pass_read_bound`
    and `classic_read_bound`. Set equalities, inclusions, `UNIV`, `{}`,
    `insert`, complements and disjointness are read pointwise, and a
    concrete set such as `{11, 12, 13}` is membership in a list. The
    record `chunk` is the structure `Tiling.Chunk`, the datatype
    `pass_status` the inductive type `Tiling.PassStatus`, each `fun` a
    definition by structural recursion with the same equations, `apfst f`
    is `Prod.map f id`, and `Suc n` is `n + 1`. The locale
    `ordered_key_space` adds only the order on keys to a coordinate
    space, so its theorems take `S : CoordinateSpace K V C` and
    `[Linorder K]`. Its `pass_units` traverses `cs.zipIdx`, the same list
    entry for entry as the map over `[0..<length cs]` with `cs ! i`, and
    its interpretation `wit_space` is the definition `Tiling.wit_space`.
14. The restart stream (`Orphan_Absence_Restart.thy`). The re-delivered
    segment `map (λq. L ! q) [den cmt..<den crash]` of `restart_stream`
    is `(S.log.take (S.den crash)).drop (S.den cmt)`, and its timed form
    `map (λq. (Suc q, L ! q)) [den cmt..<den crash]` in `resumed_t` is
    `tagged_seg S (S.den cmt) (S.den crash)`, the same lists entry for
    entry because `den crash ≤ length L`, and both empty when `den cmt`
    exceeds `den crash`. The right side of `cut_blocks` walks the
    consumed segment with `zipIdx`, as `emission_t` does. The `obtains`
    of `emission_t_item_cases` and `resumed_item_cases` is the
    disjunction of its cases, the case `q < den X ∧ x = (Suc q, L ! q)`
    as the dependent conjunction `∃ h : q < S.den X, x = (q + 1, S.log[q])`,
    and in `cut_complete`, `resumed_complete`, `evs_for_win_quiet` and
    `emission_t_event_in` the bound of `S.log[q]` comes from the
    statement's own `q < den _`. The sort `linorder` of
    `filter_tag_le_sorted` is `[LE α] [Std.IsLinearOrder α]`, as in
    convention 12. On `Nat` the tag filters decide `≤` with `Nat.decLe`
    where the generic lemma uses the classical instance, which gives the
    same list, and the proof of `restart_cut_prefix` bridges the two.

One proof differs in structure from the Isabelle proof. The Isabelle
proof of `late_absence_split` maps family positions through
`split_index_subset`, `split_index_ne` and `split_index_bound`. The Lean
proof reads the positional disjointness field `O1_disjoint` as pairwise
disjointness along the list (`O1_disjoint_iff_pairwise`) and decomposes
it over the append. The three index lemmas are therefore not ported. The
statement of `late_absence_split` is unchanged. The proofs of the
composition theory follow the Isabelle proofs case by case. The Isabelle
proof of `unlisted_quiet_absent_at` uses the core's `contract_cut_unit`,
which the Lean core copy does not carry, so the Lean proof makes the same
per-unit argument inline, and the statement is unchanged.

Port-local helpers, each marked in its docstring: `survivors_sub_dom`
(an Isabelle core lemma of `Merge_Disciplines.thy` that the Lean core
does not carry), `evs_emission_master2` (the plain-stream reading of
`titems_emission_master2`, which the Isabelle proofs perform inline as
the fact `master`), `exists_nodup_listing` (in place of HOL's
`finite_distinct_list`), `O1_disjoint_iff_pairwise`, the inductive
`rtranclp` (HOL's reflexive transitive closure), `reads_from_ne` (the
content of `reads_from_nonempty`, proved before the two statements that
use it), and for `Orphan_Absence_Interleaved.thy` the general block
lemmas `blocks_sorted_gen`, `insert_at_append_le` and
`concat_blocks_insert_gen`, the segment lemmas `seg_len_den`,
`seg_zipIdx_pos`, `mem_seg_pos`, `mem_seg_zipIdx` and `seg_zipIdx_mem`,
and `flatMap_perm_split` (the multiset split that the Isabelle proof of
`inter_t_mset` states inline), and for `Orphan_Absence_Tiling.thy` the
class `Tiling.Linorder` with its instance for `Nat`, the definitions
`Tiling.finite`, `Tiling.card`, `Tiling.sorted_list_of_set`,
`Tiling.last` and `Tiling.insort`, the instance `Nonempty (Chunk K)`
(audited as `Tiling.instNonemptyChunk`), the facts
`Tiling.last_eq_getLast`, `Tiling.sorted_list_of_set_eq`,
`Tiling.sorted_list_of_set_sorted`, `Tiling.mem_sorted_list_of_set`,
`Tiling.mem_sorted_list_of_set_imp`, `Tiling.length_sorted_list_of_set`
and `Tiling.sorted_list_of_set_insert`, and the four bound lemmas named
in convention 13.

## Coverage

`Orphan_Absence.thy` has 59 declarations: 8 definitions, 49 lemmas and
theorems, and 2 interpretations. The port carries 56 of them under their
Isabelle names, with the interpretations `orph` and `rah` as the
theorems `wit_orph_contract` and `wit_rah_contract`. The 3 that it does
not carry are the index lemmas `split_index_subset`, `split_index_ne`
and `split_index_bound`, described above.

`Orphan_Absence_Composition.thy` has 23 declarations: 1 locale, 2
definitions, 18 lemmas, theorems and corollaries, and 2
interpretations. The port carries all of them. The locale is the
structure `PassThenRead`, the interpretation `pr` is the theorem
`wit_pr_instance`, and the lemma `rq_contract` and the interpretation
`rq` are the one theorem `rq_contract`.

`Orphan_Absence_Interleaved.thy` has 70 declarations: 1 locale, 7
definitions, 57 lemmas, theorems and corollaries, and 5
interpretations. The port carries all of them, in `Interleaved.lean`
and `InterleavedWitnesses.lean`. The locale is the structure
`PassWithRequest`, the interpretations `pwb`, `pwa` and `pwo` are the
theorems `wit_pwb_instance`, `wit_pwa_instance` and `wit_pwo_instance`,
and the lemmas `rqb_contract` and `rqo_contract` with the
interpretations `rqb` and `rqo` are the theorems `rqb_contract` and
`rqo_contract`.

`Orphan_Absence_Replay.thy` has 70 declarations: 1 inductive, 7
definitions and 62 lemmas and theorems. The port carries all of them
under their Isabelle names, in `Redelivery.lean` and
`RedeliveryWitnesses.lean`.

`Orphan_Absence_Tiling.thy` has 145 declarations: 18 definitions, 6
recursive functions, 1 datatype, 1 record, 1 locale, 1 interpretation
and 117 lemmas, theorems and corollaries. The port carries all of them,
in `Tiling.lean`, `TilingWitnesses.lean` and `TilingBridge.lean`. The
record is the structure `Tiling.Chunk`, the datatype the inductive type
`Tiling.PassStatus`, and the interpretation `wit_space` a definition.
The locale `ordered_key_space` has no declaration of its own, since it
adds only the order on keys, which the bridge theorems take as the class
`Tiling.Linorder` beside the coordinate space.

`Orphan_Absence_Restart.thy` has 69 declarations: 1 locale, 10
definitions, 48 lemmas and theorems, and 10 interpretations. The port
carries all of them, in `Restart.lean` and `RestartWitnesses.lean`. The
locale is the structure `PassRestart`, the interpretations of
`capture_contract` and `pass_restart` are theorems, the lemma
`ri_contract` and the interpretation `ri` are the one theorem
`ri_contract`, and the interpretation `tc` of `coordinate_space` is the
definition `tc`.

With the port-local helpers the port has 388 public theorems (52 for
the first theory, 19 for the composition theory, 69 for the interleaved
theory, 63 for the delivery theory, 129 for the tiling theory and 56 for
the restart theory, the counts of the third to fifth including their
port-local helpers), 65 definitions, the inductives `reads_from`,
`rtranclp` and `Tiling.PassStatus`, the structures `PassThenRead`,
`PassWithRequest`, `PassRestart` and `Tiling.Chunk`, and the class
`Tiling.Linorder`, plus 56 private lemmas (concrete evaluations, order
facts and proof steps).

## Build record (2026-11-07)

Environment: macOS 27.2 (build 26B123) on Apple Silicon (arm64), elan
4.2.4.

    $ lean --version
    Lean (version 4.32.2, arm64-apple-darwin24.6.0, commit f3b06c705e6c85f5314019d5d3baab0fec5b580c, Release)
    $ lake --version
    Lake version 5.0.0-src+f3b06c7 (Lean version 4.32.2)

Command, from this directory:

    rm -rf .lake
    sandbox-exec -p '(version 1)(allow default)(deny network*)' lake build

The sandbox profile denies all network access, which shows that the
build downloads nothing. A plain `lake build` runs the same build.

Result: `Build completed successfully (27 jobs).`, exit status 0, about
5 seconds of wall time (19:10:12 to 19:10:16 UTC on 2026-11-06, which is
2026-11-07 in Singapore). The log has no warning and no error line.
Every module of the core copy and of the port was elaborated, including
both audit modules. This build supersedes the earlier ones (16 jobs for
the first theory and 18 with the composition theory on 2026-11-04, 20
with the delivery theory, 22 with the interleaved theory and 25 with the
tiling theory on 2026-11-07).

The same command on a copy of this directory outside the workspace,
made without `.lake/`, gave the same result and the same audit output,
line for line. The directory builds on its own.

## Axiom audit

`OrphanAbsence/AxiomAudit.lean` runs `#print axioms` on all 388 public
theorems of the port. Its list was compared mechanically with the
public theorems that the compiled modules declare, read from the Lean
environment with structure projections and generated lemmas left out,
and the two lists are equal. The comparison caught one omission before
this record was written, the instance `Nonempty (Chunk K)`, which is a
theorem because its class is a proposition, and its audit line was
added. The footprints:

- 316 theorems: `[propext, Classical.choice, Quot.sound]`
- 43 theorems: `[propext, Quot.sound]`
- 1 theorem: `[propext, Classical.choice]` (`Tiling.last_eq_getLast`)
- 8 theorems: `[propext]` (`seg_len_den`, `seg_zipIdx_pos`,
  `flatMap_perm_split`, `PassWithRequest.inter_t_mset`, `orph_s0lo_den`,
  `Tiling.chain_above`, `PassRestart.cut_item`, `PassRestart.cut_tag_le`)
- 20 theorems without any axiom

The build log prints the footprint of every theorem.

The core audit `DBLogContract/AxiomAudit.lean` prints its 87 lines as
before: 61 at `[propext, Classical.choice, Quot.sound]`, 10 at
`[propext, Quot.sound]`, 13 at `[propext]` and 3 without any axiom.

Lean wraps a long message onto a second line, so the check joins each
footprint with its continuation lines before reading the axiom list.
Filtering all 475 footprints of the build log against the three allowed
axioms leaves nothing, and no `sorryAx` appears. The 10 private lemmas
(`state_sc_pfx1_3`, `state_sc_pfx1_4`, `state_sc_pfx2_3` and
`state_sc_pfx2_4` in `Witnesses.lean`, `rq_state_pfx2_4` in
`CompositionWitnesses.lean`, `state_after_indep` in `Redelivery.lean`,
and `rd_state_pfx2_4`, `rd_state_pfx2_3`, `rd_doubled_redelivered` and
`reorder_evs_eq` in `RedeliveryWitnesses.lean`) cannot be named from
another module. The footprints of the theorems that use them include
theirs.

## Source checks

After removing line comments and block comments, docstrings included,
no Lean file of this directory contains the token `sorry`, the token
`admit` or an `axiom` declaration (24 files scanned, 0 hits). The words
occur only in prose: two audit docstrings name `sorry`, and one core
docstring uses "admit" as an English verb.

## Statement-fidelity reviews

Each port was checked by blind reviewers (Claude Opus 5.5, read-only),
one for each of the first two theories and a pair at medium and at
extra-high reasoning effort for each later one. A reviewer had the
Isabelle theory, the definitions it rests on in both developments and
the new Lean modules, and it printed the elaborated Lean statements with
`lake env lean --stdin`. It had the transport conventions but not the
porter's own conclusions, and it reported only breakages, each with a
witness.

- `Orphan_Absence.thy`: no mismatch found. Every one of the 56 ported
  declarations was rated the same as its Isabelle counterpart, 12 of
  them with the unused contract assumption dropped (convention 4). The
  reviewer named the same 3 Isabelle declarations without a Lean
  counterpart. The review ran before a wording pass on the docstrings,
  which changed no statement.
- `Orphan_Absence_Composition.thy`: no mismatch found. Every one of the
  23 declarations was rated the same as its Isabelle counterpart, except
  `win_last_src`, which was rated stronger because it is stated without
  the `PassThenRead` argument (convention 4). The reviewer found no
  declaration without a Lean counterpart. It also checked on the fixture
  that `tagged_seg sc 0 2` reduces to the list that the Isabelle normal
  form `map (λp. (Suc p, L_s ! p)) [0..<2]` denotes. The review ran on
  the final sources.
- `Orphan_Absence_Interleaved.thy`: no mismatch found by either
  reviewer. One rated 68 of the 70 declarations the same and
  `take_state_quiet` and `honest_stream_last` stronger (convention 12).
  The other rated 60 the same and 10 stronger: those two and the eight
  locale lemmas stated without the `PassWithRequest` argument
  (convention 4). Both checked that `inter_t` and `inter_t_rev` denote the
  Isabelle lists entry for entry, the empty range included, and found no
  `sorry`, `admit`, `native_decide`, `axiom` or outside import.
- `Orphan_Absence_Replay.thy`: no mismatch found by either reviewer.
  Both rated 69 of the 70 declarations the same as their Isabelle
  counterparts and `close_block_reapply_noop` stronger, since it takes
  only the coordinate space (convention 4). Both accepted the encodings
  of convention 11 and found no `sorry`, `admit`, `native_decide`,
  `axiom` or outside import. After the review the helper `reads_from_ne`
  was made public, so that the statements of `reads_from_last` and
  `reads_from_hd` name it. Nothing else changed.
- `Orphan_Absence_Tiling.thy`: no mismatch found by either reviewer. One
  listed verdicts for 31 declarations, the other for all 145, every one
  the same as its Isabelle counterpart. Both checked the encodings of
  convention 13 on their merits: the five axioms of `Tiling.Linorder`,
  HOL's values of `card` and `sorted_list_of_set` on infinite sets, the
  total `last` used alike in the scans and in the statements, the
  instance `[Nonempty K]`, which holds for every HOL type, the derived
  index bounds, and `pass_units` entry for entry. Neither found a
  `sorry`, `admit`, `native_decide`, `axiom` or outside import. After the
  review the instance `Nonempty (Chunk K)` was added to the audit, and
  nothing else changed.
- `Orphan_Absence_Restart.thy`: no mismatch found by either reviewer.
  One rated 66 declarations the same and `restart_at_frontier` and
  `resumed_complete` stronger, the other 61 the same and 8 stronger, all
  of them locale lemmas stated without the `PassRestart` argument
  (convention 4). Both checked `restart_stream`, `cut_t` and `resumed_t`
  entry for entry, the five locale assumptions, both theorems conjunct
  for conjunct, and the fixture constants and computed streams, and
  neither found a `sorry`, `admit`, `native_decide`, `axiom` or outside
  import.

## Line counts

Lines are physical lines, docstrings included. Definitions counts the
`def` declarations. `Composition.lean`, `Interleaved.lean`, `Restart.lean` and `Tiling.lean` also declare the structures `PassThenRead`, `PassWithRequest`, `PassRestart` and `Tiling.Chunk`, `Redelivery.lean` and `Tiling.lean` declare the inductives `reads_from`, `rtranclp` and `Tiling.PassStatus`, and `Tiling.lean` declares the class `Tiling.Linorder` and the instance `Nonempty (Chunk K)`, a theorem that the audit covers and this table does not count.

| File | Lines | Public theorems | Private theorems | Definitions | Audit commands |
| --- | ---: | ---: | ---: | ---: | ---: |
| `OrphanAbsence.lean` | 17 | 0 | 0 | 0 | 0 |
| `OrphanAbsence/Emission.lean` | 414 | 12 | 0 | 2 | 0 |
| `OrphanAbsence/Replay.lean` | 458 | 11 | 0 | 1 | 0 |
| `OrphanAbsence/ChunkRecord.lean` | 151 | 5 | 0 | 2 | 0 |
| `OrphanAbsence/ContractUnits.lean` | 239 | 3 | 0 | 0 | 0 |
| `OrphanAbsence/Witnesses.lean` | 351 | 21 | 4 | 3 | 0 |
| `OrphanAbsence/Composition.lean` | 441 | 11 | 0 | 1 | 0 |
| `OrphanAbsence/CompositionWitnesses.lean` | 180 | 8 | 1 | 1 | 0 |
| `OrphanAbsence/Interleaved.lean` | 1463 | 51 | 0 | 5 | 0 |
| `OrphanAbsence/InterleavedWitnesses.lean` | 319 | 18 | 0 | 2 | 0 |
| `OrphanAbsence/Redelivery.lean` | 795 | 50 | 1 | 3 | 0 |
| `OrphanAbsence/RedeliveryWitnesses.lean` | 290 | 13 | 4 | 4 | 0 |
| `OrphanAbsence/Restart.lean` | 818 | 30 | 0 | 3 | 0 |
| `OrphanAbsence/RestartWitnesses.lean` | 600 | 26 | 3 | 8 | 0 |
| `OrphanAbsence/Tiling.lean` | 2079 | 108 | 34 | 22 | 0 |
| `OrphanAbsence/TilingWitnesses.lean` | 226 | 14 | 3 | 5 | 0 |
| `OrphanAbsence/TilingBridge.lean` | 299 | 6 | 6 | 3 | 0 |
| `OrphanAbsence/AxiomAudit.lean` | 488 | 0 | 0 | 0 | 388 |
| Port total | 9628 | 387 | 56 | 65 | 388 |
| Core copy total (`DBLogContract.lean`, `DBLogContract/`) | 2292 | | | | 87 |

## File hashes

Every file of this directory except this record and the build
directory `.lake/`.

| SHA-256 | File |
| --- | --- |
| `5375c2c5e323f40c0031aa8c82f66bb9197214001039e6a8c9ff2a5eb3aa24a9` | `.gitignore` |
| `fb16145bf525e409a2f60703bffaf77932e193949b493bb529302ad4db886ea4` | `DBLogContract.lean` |
| `69d227773b741743d24f5ebb4ccd5a127d135d0a7dd3d148da041c562efa3800` | `LICENSE` |
| `ca6cc8f4d148b434a1fc110dd8c14708d2d636a21293a091f54117fd9b1e4482` | `OrphanAbsence.lean` |
| `fbf1fa231d6610c2cdfa2a14c2419c9d2fa362e36838a8458bb0ba09358cbc76` | `README.md` |
| `9a89aaf6b703f9cfc59c245f36edaf7012882c7bb99b3f909180f55b8822e73c` | `lake-manifest.json` |
| `6748d4efe9d39961db78074e8646a6c0136606b2b7c0f5767fe0256b594301fb` | `lakefile.toml` |
| `2bdc48adfa58d0017e538a0ad117c5d73d35deec879978f909406a80c8037273` | `lean-toolchain` |
| `bb2cf6dcd2a88a4faa60db1014266f280063c9ccc144c596075d08809ca1e4d7` | `DBLogContract/AxiomAudit.lean` |
| `5a48af56ae4f04b0f76cd2227d4852ae6519cd6012c08cbca832842a5f4d3d44` | `DBLogContract/ContractBase.lean` |
| `18358f6c5e65eb6ee6f077a2ab39caa943c56d21b99365b3ac52ae251bfc2009` | `DBLogContract/ContractWitnesses.lean` |
| `6c81f28c4d5a5227a266637d4834bbe17bff2c3d80feef77065d3295610295ae` | `DBLogContract/CutTheorem.lean` |
| `ea116cfc41b4826b1562f4200ab26602adbef36e0ed6f1c4ba892767a412cd88` | `DBLogContract/MergeDisciplines.lean` |
| `9800d6eb30a84c2579da44f471ccbe902d66a80d311cd09e5d3a7618f5d2fa1e` | `OrphanAbsence/AxiomAudit.lean` |
| `cc266bbd6a892cd0cef898be20f1d3f4e3d50b71ba0ed7e7fe95e7e07c255fec` | `OrphanAbsence/ChunkRecord.lean` |
| `6aef19af32403086a23a20dfbf827865eb35795e02a2814fbbd27ce4a35d1615` | `OrphanAbsence/Composition.lean` |
| `d3fb8d3ef9b29347a405c82b4f4fac9b18132f2ed8a7b664cf9fed5f60c871f7` | `OrphanAbsence/CompositionWitnesses.lean` |
| `14d1656ec5d81049c44aadcc8b66352fd1485bf1011406e9a29ee4e2f9b3e896` | `OrphanAbsence/ContractUnits.lean` |
| `f4a4a09ddee14d0272472bd1d9c252350744f5f75d4cab4b864b651ef7503c8b` | `OrphanAbsence/Emission.lean` |
| `56bab429e05068838634cf8e6eb6b84c48b13f75e10523be09dcc2b212781f38` | `OrphanAbsence/Interleaved.lean` |
| `d0205189d13edd1d1c32616b9f04b9258c224008b1a8d74903552c663a9801de` | `OrphanAbsence/InterleavedWitnesses.lean` |
| `0b94256752ffd48ec1ec290343a2363a9898034e6b73692bd054f117a7b1d540` | `OrphanAbsence/Redelivery.lean` |
| `c79f4eaf49612a631e20b70559488fb7006e7a3aa90a64f908126c733811e79f` | `OrphanAbsence/RedeliveryWitnesses.lean` |
| `bb149e58d5c6a92b78e7ebdd1514b007be762ca553390c4c96af8ed2a29d9a54` | `OrphanAbsence/Replay.lean` |
| `2483e6ca8e59b0a8473cd1bbf624c5316f7cacf8d547c737500887dccf26b985` | `OrphanAbsence/Restart.lean` |
| `b0639530f939a32b56cbf5da8878afd67a770e3bcc74891667ebf05225dd157d` | `OrphanAbsence/RestartWitnesses.lean` |
| `876201135613bfce1bfdd4a90415d3227a26248ce05d5cd1c97a309a07e30bdf` | `OrphanAbsence/Tiling.lean` |
| `8d5e3f1a60d923fc7df996643654887fa2f29c3abae069b3812d6d8db317d9c3` | `OrphanAbsence/TilingBridge.lean` |
| `58d8825a4e1c05c8e80ce50f608d25d66c4cd065f88def1778044e3590594567` | `OrphanAbsence/TilingWitnesses.lean` |
| `87bcdd12edd68e3f344602d901017f2dc1749ab6278b21937b9743e911b03fd1` | `OrphanAbsence/Witnesses.lean` |

## Revision of 2026-11-05

An outside review found two wording slips that the Isabelle theory and this
port share, and no statement changed. The chunk-record docstring of
`ChunkRecord.lean` now says the sink upserts the surviving returned rows,
as `record_enum` does. The existence docstrings of `Replay.lean` and the
README name finitely many survivors per unit beside the finite sink, the
assumption both developments already state. `Orphan_Absence.thy` changed
in the same two comments, so its hash in the source table above is new and
its line count is unchanged. A clean offline rebuild completed in 18 jobs
with exit 0 and the same 158 audit lines within the three standard axioms.

## Second revision of 2026-11-05

The paper split the chunk record's single key list into two, the
selected keys and the changed keys, whose union is this port's
`except_keys`. The module docstring of `ChunkRecord.lean` and the README
say so now, and no statement changed. `Orphan_Absence.thy` changed in the
same text block, so its hash in the source table above is new and its
line count grew from 1224 to 1226, as `ChunkRecord.lean` grew from 150 to
151 lines (its other docstrings now say "except set" for the same union).
An offline rebuild from the deposit ZIP then passed with the same audit. Later that evening the paper dropped
over-approximation from its mechanism (its two lists are exact), so the same
two comments and the READMEs now call `except_overapprox_safe` a robustness
result the paper does not rely on. Hashes updated, line counts unchanged. The paper then renamed the construct to the chunk info record, and the same two comments say so (hashes updated again, line counts unchanged). The port total in the line-count table above was corrected from 2363 to 2364 after a recheck, and the READMEs now say chunk info record throughout.

## Revision of 2026-11-07

A final outside review found two comments that said more than their
lemmas. The text before `sink_read_covers` in `Orphan_Absence.thy` now
says that the premise reads the log-only state, which is the sink's state
for an unlisted key, and that a listed key needs no coverage argument. The
heading "Re-applying a suffix, or restarting after an applied prefix,
changes nothing" replaces a broader one in `Orphan_Absence_Replay.thy` and
in `Redelivery.lean`. No statement changed. The source table above carries
the new hashes of the two theories, and `Orphan_Absence.thy` grew from 1,226
to 1,228 lines. The offline rebuild from the deposit ZIP completed in 27
jobs with the same 475 audit lines within the three standard axioms.
