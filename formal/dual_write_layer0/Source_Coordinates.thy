(*  Title:   Source_Coordinates.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Source_Coordinates
  imports Source_History
begin

section \<open>Named concrete source coordinates\<close>

text \<open>
  Shared concrete source coordinates for the witness and fixture
  theories.

  The witness and fixture theories use named concrete
  source coordinates (\<open>ec1..ec4\<close>, \<open>ct1\<close>, \<open>c1_w\<close>/\<open>c2_w\<close>, the fixture
  coordinates, ...), each sitting on a strict
  @{const src_lt} chain @{text "c0 < ec1 < ec2 < \<dots>"} with derived
  @{const src_le} / distinctness / transitivity facts. This theory
  provides them all through a single \<^emph>\<open>order
  embedding\<close> of @{typ nat} into @{typ src_coord},

    @{text "coord_of_nat n = Abs_src_coord n"},

  together with generic @{attribute simp} order facts. Each named
  coordinate is defined as a @{text coord_of_nat} of a concrete index
  --- e.g. \<open>ec1 \<equiv> coord_of_nat 1\<close> ---
  and every order relationship is a lemma
  discharging by @{method simp} from nat
  arithmetic.

  @{type src_coord} is a @{command typedef} copy of @{typ nat}
  (@{thm [source] type_definition_src_coord}), so @{text coord_of_nat}
  is a bijection and the order is reflected exactly.
\<close>

definition coord_of_nat :: "nat \<Rightarrow> src_coord" where
  "coord_of_nat n = Abs_src_coord n"

lemma Rep_coord_of_nat [simp]: "Rep_src_coord (coord_of_nat n) = n"
  by (simp add: coord_of_nat_def Abs_src_coord_inverse[OF UNIV_I])

lemma coord_of_nat_Rep [simp]: "coord_of_nat (Rep_src_coord c) = c"
  by (simp add: coord_of_nat_def Rep_src_coord_inverse)

lemma coord_of_nat_inject [simp]:
  "(coord_of_nat m = coord_of_nat n) = (m = n)"
  by (simp add: coord_of_nat_def Abs_src_coord_inject[OF UNIV_I UNIV_I])

text \<open>The base coordinate is the image of \<open>0\<close>.\<close>

lemma c0_eq_coord_of_nat_0: "c0 = coord_of_nat 0"
  by (simp add: c0_def coord_of_nat_def)

lemma coord_of_nat_eq_c0_iff [simp]: "(coord_of_nat n = c0) = (n = 0)"
  by (simp add: c0_eq_coord_of_nat_0)

lemma c0_eq_coord_of_nat_iff [simp]: "(c0 = coord_of_nat n) = (n = 0)"
  by (simp add: c0_eq_coord_of_nat_0)

text \<open>
  The order is reflected by @{const coord_of_nat}, in both the primitive
  (@{const src_le} / @{const src_lt}) and the typeclass (@{text "(\<le>)"} /
  @{text "(<)"}) forms.
\<close>

lemma src_le_coord_of_nat [simp]:
  "src_le (coord_of_nat m) (coord_of_nat n) = (m \<le> n)"
  by (simp add: src_le_def)

lemma src_lt_coord_of_nat [simp]:
  "src_lt (coord_of_nat m) (coord_of_nat n) = (m < n)"
  by (simp add: src_lt_def less_le)

lemma less_eq_coord_of_nat [simp]:
  "(coord_of_nat m \<le> coord_of_nat n) = (m \<le> n)"
  by (simp add: less_eq_src_coord_def)

lemma less_coord_of_nat [simp]:
  "(coord_of_nat m < coord_of_nat n) = (m < n)"
  by (simp add: less_src_coord_def)

text \<open>
  Convenience facts for the base coordinate, which the witness / fixture
  chains state as @{term "src_lt c0 (coord_of_nat n)"}. (The non-strict
  @{term "src_le c0 c"} is already @{thm [source] c0_least} for every
  @{text c}.)
\<close>

lemma src_lt_c0_coord_of_nat [simp]:
  "src_lt c0 (coord_of_nat n) = (0 < n)"
  by (simp add: c0_eq_coord_of_nat_0)

lemma less_c0_coord_of_nat [simp]:
  "(c0 < coord_of_nat n) = (0 < n)"
  by (simp add: less_src_coord_def)

lemma src_le_c0_coord_of_nat [simp]:
  "src_le c0 (coord_of_nat n)"
  by (simp add: c0_eq_coord_of_nat_0)

text \<open>
  Illustration (the shape the named coordinates below reproduce): a
  strict chain over @{const coord_of_nat} and every derived
  @{const src_le} / distinctness fact discharge by @{method simp} alone.
\<close>

lemma coord_of_nat_chain_example:
  "src_lt c0 (coord_of_nat 1)"
  "src_lt (coord_of_nat 1) (coord_of_nat 2)"
  "src_le (coord_of_nat 1) (coord_of_nat 2)"
  "coord_of_nat 1 \<noteq> coord_of_nat 2"
  "src_le c0 (coord_of_nat 3)"
  by simp_all

subsection \<open>Positive-witness coordinates\<close>

text \<open>
  The positive-witness coordinates: each sits on a
  strict @{const src_lt} chain above @{const c0}, with the
  @{const src_le} / distinctness facts derived. All are
  @{const coord_of_nat} definitions --- one shared theory, distinct
  indices so no two named coordinates collide --- with the order /
  distinctness consequences proved as named lemmas, every
  one discharging by @{method simp} from the generic facts above. The
  witness theories import this theory and cite these lemmas by name.

  Index map: @{text "ec1..ec4 = 1..4"} (running example, the
  @{text Layer01_Virtual_Cut_Example_Core} family); @{text "ct1 = 5"} (Topic 1,
  the @{text Layer01_Witness_Topics_Core} family); @{text "c1_w = 6"},
  @{text "c2_w = 7"}
  (minimum-viable wellformed-run witness, the @{text Layer01_Witnesses_Core}
  family). The
  lemmas are deliberately not @{attribute simp} rules; the witness
  proofs cite them by name.
\<close>

text \<open>Running-example coordinates \<open>ec1 < ec2 < ec3 < ec4\<close> above \<open>c0\<close>.\<close>

definition ec1 :: src_coord where "ec1 = coord_of_nat 1"
definition ec2 :: src_coord where "ec2 = coord_of_nat 2"
definition ec3 :: src_coord where "ec3 = coord_of_nat 3"
definition ec4 :: src_coord where "ec4 = coord_of_nat 4"

lemmas ec_defs = ec1_def ec2_def ec3_def ec4_def

lemma c0_lt_ec1: "src_lt c0 ec1" by (simp add: ec_defs)
lemma ec1_lt_ec2: "src_lt ec1 ec2" by (simp add: ec_defs)
lemma ec2_lt_ec3: "src_lt ec2 ec3" by (simp add: ec_defs)
lemma ec3_lt_ec4: "src_lt ec3 ec4" by (simp add: ec_defs)

lemma c0_le_ec1: "src_le c0 ec1" by (simp add: ec_defs)
lemma ec1_le_ec2: "src_le ec1 ec2" by (simp add: ec_defs)
lemma ec2_le_ec3: "src_le ec2 ec3" by (simp add: ec_defs)
lemma ec3_le_ec4: "src_le ec3 ec4" by (simp add: ec_defs)
lemma c0_le_ec2: "src_le c0 ec2" by (simp add: ec_defs)
lemma c0_le_ec3: "src_le c0 ec3" by (simp add: ec_defs)
lemma c0_le_ec4: "src_le c0 ec4" by (simp add: ec_defs)
lemma ec1_le_ec3: "src_le ec1 ec3" by (simp add: ec_defs)
lemma ec1_le_ec4: "src_le ec1 ec4" by (simp add: ec_defs)
lemma ec2_le_ec4: "src_le ec2 ec4" by (simp add: ec_defs)

lemma ec1_neq_ec2: "ec1 \<noteq> ec2" by (simp add: ec_defs)
lemma ec2_neq_ec3: "ec2 \<noteq> ec3" by (simp add: ec_defs)
lemma ec3_neq_ec4: "ec3 \<noteq> ec4" by (simp add: ec_defs)
lemma ec1_neq_ec3: "ec1 \<noteq> ec3" by (simp add: ec_defs)
lemma c0_neq_ec1: "c0 \<noteq> ec1" by (simp add: ec_defs)
lemma c0_neq_ec2: "c0 \<noteq> ec2" by (simp add: ec_defs)
lemma c0_neq_ec3: "c0 \<noteq> ec3" by (simp add: ec_defs)
lemma c0_neq_ec4: "c0 \<noteq> ec4" by (simp add: ec_defs)

text \<open>Topic 1 coordinate \<open>ct1\<close> above \<open>c0\<close>.\<close>

definition ct1 :: src_coord where "ct1 = coord_of_nat 5"

lemma c0_lt_ct1: "src_lt c0 ct1" by (simp add: ct1_def)
lemma c0_le_ct1: "src_le c0 ct1" by (simp add: ct1_def)
lemma c0_neq_ct1: "c0 \<noteq> ct1" by (simp add: ct1_def)
lemma not_src_le_ct1_c0: "\<not> src_le ct1 c0"
  by (simp add: ct1_def c0_eq_coord_of_nat_0)
lemma src_le_ct1_ct1: "src_le ct1 ct1" by (rule src_le_refl)

text \<open>Wellformed-run witness coordinates \<open>c1_w < c2_w\<close> above \<open>c0\<close>.\<close>

definition c1_w :: src_coord where "c1_w = coord_of_nat 6"
definition c2_w :: src_coord where "c2_w = coord_of_nat 7"

lemma c0_lt_c1_w: "src_lt c0 c1_w" by (simp add: c1_w_def)
lemma c1_w_lt_c2_w: "src_lt c1_w c2_w" by (simp add: c1_w_def c2_w_def)
lemma c0_neq_c1_w: "c0 \<noteq> c1_w" by (simp add: c1_w_def)
lemma c0_le_c1_w: "src_le c0 c1_w" by (simp add: c1_w_def)
lemma c1_w_neq_c2_w: "c1_w \<noteq> c2_w" by (simp add: c1_w_def c2_w_def)
lemma c0_neq_c2_w: "c0 \<noteq> c2_w" by (simp add: c2_w_def)

subsection \<open>Fixture coordinates\<close>

text \<open>
  The negative-fixture coordinates: distinct indices \<open>8..18\<close> continue
  the witness range \<open>1..7\<close>; order facts discharge by @{method simp}.

  Layer 0/1 fixtures (the @{text Layer01_Fixtures_Core} family): single
  coordinates above
  \<open>c0\<close> --- \<open>caf_c1 = 8\<close>, \<open>sc_c1 = 9\<close>, \<open>ec_c1 = 10\<close>, \<open>md_c1 = 11\<close>,
  \<open>dm_c1 = 12\<close>, \<open>do_c1 = 13\<close>. Layer 2 fixtures (the
  @{text Layer2_Fixtures_Core} family):
  \<open>l2_cp_c1 = 14\<close>, \<open>l2_future_c1 = 15\<close>, and the off-by-one chain
  \<open>l2_fo_before = 16 < l2_fo_frontier = 17 < l2_fo_after = 18\<close>.
\<close>

definition caf_c1 :: src_coord where "caf_c1 = coord_of_nat 8"
lemma caf_c0_lt_c1: "src_lt c0 caf_c1" by (simp add: caf_c1_def)
lemma caf_not_src_le_c1_c0: "\<not> src_le caf_c1 c0"
  by (simp add: caf_c1_def c0_eq_coord_of_nat_0)

definition sc_c1 :: src_coord where "sc_c1 = coord_of_nat 9"
lemma sc_c0_lt_c1: "src_lt c0 sc_c1" by (simp add: sc_c1_def)
lemma sc_c1_le_c1: "src_le sc_c1 sc_c1" by (rule src_le_refl)

definition ec_c1 :: src_coord where "ec_c1 = coord_of_nat 10"
lemma ec_c0_lt_c1: "src_lt c0 ec_c1" by (simp add: ec_c1_def)
lemma ec_c1_le_c1: "src_le ec_c1 ec_c1" by (rule src_le_refl)

definition md_c1 :: src_coord where "md_c1 = coord_of_nat 11"
lemma md_c0_lt_c1: "src_lt c0 md_c1" by (simp add: md_c1_def)
lemma md_c0_le_c1: "src_le c0 md_c1" by (simp add: md_c1_def)
lemma md_c1_le_c1: "src_le md_c1 md_c1" by (rule src_le_refl)

definition dm_c1 :: src_coord where "dm_c1 = coord_of_nat 12"
lemma dm_c0_lt_c1: "src_lt c0 dm_c1" by (simp add: dm_c1_def)
lemma dm_c1_le_c1: "src_le dm_c1 dm_c1" by (rule src_le_refl)

definition do_c1 :: src_coord where "do_c1 = coord_of_nat 13"
lemma do_c0_lt_c1: "src_lt c0 do_c1" by (simp add: do_c1_def)
lemma do_c1_le_c1: "src_le do_c1 do_c1" by (rule src_le_refl)

definition l2_cp_c1 :: src_coord where "l2_cp_c1 = coord_of_nat 14"
lemma l2_cp_c0_lt_c1: "src_lt c0 l2_cp_c1" by (simp add: l2_cp_c1_def)
lemma l2_cp_not_le_c0: "\<not> l2_cp_c1 \<le> c0"
  by (simp add: l2_cp_c1_def c0_eq_coord_of_nat_0)

definition l2_future_c1 :: src_coord where "l2_future_c1 = coord_of_nat 15"
lemma l2_future_c0_lt_c1: "src_lt c0 l2_future_c1" by (simp add: l2_future_c1_def)
lemma l2_future_not_le_c0: "\<not> l2_future_c1 \<le> c0"
  by (simp add: l2_future_c1_def c0_eq_coord_of_nat_0)

definition l2_fo_before :: src_coord where "l2_fo_before = coord_of_nat 16"
definition l2_fo_frontier :: src_coord where "l2_fo_frontier = coord_of_nat 17"
definition l2_fo_after :: src_coord where "l2_fo_after = coord_of_nat 18"

lemma l2_fo_before_lt_frontier: "src_lt l2_fo_before l2_fo_frontier"
  by (simp add: l2_fo_before_def l2_fo_frontier_def)
lemma l2_fo_frontier_lt_after: "src_lt l2_fo_frontier l2_fo_after"
  by (simp add: l2_fo_frontier_def l2_fo_after_def)
lemma l2_fo_before_le_frontier: "l2_fo_before \<le> l2_fo_frontier"
  by (simp add: l2_fo_before_def l2_fo_frontier_def)
lemma l2_fo_after_not_le_frontier: "\<not> l2_fo_after \<le> l2_fo_frontier"
  by (simp add: l2_fo_after_def l2_fo_frontier_def)

end
