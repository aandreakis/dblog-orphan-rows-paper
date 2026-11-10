(*  Title:   Layer4_Witnesses_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer4_Witnesses_Core
  imports Layer01_Virtual_Cut_Example_Core Virtual_Cut_Core
begin

section \<open>Layer 3/4 witness anchor data (carrier-independent)\<close>

text \<open>
  Carrier- and certificate-independent core of the Layer 4 positive
  whole-table witness.

  Holds the anchor-boundary data that the constructed Layer 3 / Layer 4
  witness interpretation (@{text Layer3_Witnesses_Inst}), the Layer 4 fixture
  theories, and @{text Public_Checker_Witness} reuse: the anchor boundary
  @{text l4_anchor}, the @{const Src} / @{const latest_src_event} facts at the
  anchor on the running-example history, the anchor-domain computation
  @{text l4_anchor_domain}, the post-anchor touched-key set
  @{text touched_H_ex_anchor_ec4}, and the derived strict / non-strict
  coordinate orderings. None of this mentions a run, chunk, or certificate
  carrier, so the theory imports only
  @{text Layer01_Virtual_Cut_Example_Core} (for
  @{const b0_ex} / @{const H_ex}) and
  @{text Virtual_Cut_Core} (home of the Layer-4 set
  operators, @{const anchor_domain} in particular).
\<close>

subsection \<open>Anchor boundary\<close>

definition l4_anchor :: frontier where
  "l4_anchor = ec1"

subsection \<open>Anchor and post-anchor source facts (independent of certificates)\<close>

lemma latest_src_event_H_ex_ec1_other:
  assumes "k \<noteq> (100::nat)" and "k \<noteq> 200"
  shows "latest_src_event H_ex ec1 k = None"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec1
                \<and> key_of (hist_event (H_ex ! i)) = k"
  have "filter ?P [0, 1, 2, 3] = []"
    using assms src_le_refl[where c=ec1] not_src_le_ec2_ec1
          not_src_le_ec3_ec1 not_src_le_ec4_ec1
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma Src_b0_ex_H_ex_ec1:
  "Src b0_ex H_ex ec1 =
     (\<lambda>k. if k = (100::nat) then Some (3000::nat)
          else if k = 200 then Some 10000
          else None)"
proof
  fix k :: nat
  show "Src b0_ex H_ex ec1 k =
        (if k = (100::nat) then Some (3000::nat)
         else if k = 200 then Some 10000
         else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis using Src_b0_ex_H_ex_ec1_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis using Src_b0_ex_H_ex_ec1_200 by simp
    next
      case not200: False
      hence latest_none: "latest_src_event H_ex ec1 k = None"
        using not100 latest_src_event_H_ex_ec1_other by blast
      show ?thesis
        unfolding Src_def b0_ex_def
        using not100 not200 latest_none by simp
    qed
  qed
qed

lemma l4_anchor_domain:
  "anchor_domain b0_ex H_ex l4_anchor = {100, 200}"
  unfolding anchor_domain_def l4_anchor_def Src_b0_ex_H_ex_ec1
  by auto

lemma ec1_lt_ec3: "src_lt ec1 ec3"
  using ec1_le_ec3 ec1_neq_ec3 by (simp add: src_lt_def)

lemma ec1_lt_ec4: "src_lt ec1 ec4"
  using ec1_le_ec4 ec1_neq_ec4 by (simp add: src_lt_def)

lemma ec1_less_ec2: "ec1 < ec2"
  using ec1_lt_ec2 by (simp add: less_src_coord_def)

lemma ec1_less_ec3: "ec1 < ec3"
  using ec1_lt_ec3 by (simp add: less_src_coord_def)

lemma ec1_less_ec4: "ec1 < ec4"
  using ec1_lt_ec4 by (simp add: less_src_coord_def)

lemma ec2_less_eq_ec4: "ec2 \<le> ec4"
  using ec2_le_ec4 by (simp add: less_eq_src_coord_def)

lemma ec3_less_eq_ec4: "ec3 \<le> ec4"
  using ec3_le_ec4 by (simp add: less_eq_src_coord_def)

text \<open>The @{text H_ex} post-anchor touched set over the explicit frontier
  @{term ec4}: between the anchor and the frontier exactly the keys 200
  (updated at @{term ec3}) and 300 (inserted at @{term ec2}) are touched.
  Shared by the Layer 3/4 witness interpretation
  (@{text Layer3_Witnesses_Inst}) and the constructed Layer 4 fixtures
  (@{text Layer4_Fixtures_Inst}).\<close>

lemma touched_H_ex_anchor_ec4:
  "touched_between H_ex l4_anchor ec4 = {200, 300}"
proof (rule subset_antisym)
  show "touched_between H_ex l4_anchor ec4 \<subseteq> {200, 300}"
    unfolding touched_between_def l4_anchor_def H_ex_def
    by auto
next
  show "{200, 300} \<subseteq> touched_between H_ex l4_anchor ec4"
  proof
    fix k :: nat
    assume "k \<in> {200, 300}"
    hence "k = 200 \<or> k = 300" by simp
    thus "k \<in> touched_between H_ex l4_anchor ec4"
    proof
      assume k200: "k = 200"
      have in_H: "(ec3, Update 200 12000) \<in> set H_ex"
        by (simp add: H_ex_def)
      have witness:
        "\<exists>c e. (c, e) \<in> set H_ex \<and> ec1 < c \<and> c \<le> ec4 \<and> key_of e = k"
        using in_H k200 ec1_less_ec3 ec3_less_eq_ec4
        by (intro exI[where x=ec3]
                  exI[where x="Update (200::nat) (12000::nat)"]) auto
      show ?thesis
        unfolding touched_between_def l4_anchor_def using witness by blast
    next
      assume k300: "k = 300"
      have in_H: "(ec2, Insert 300 2500) \<in> set H_ex"
        by (simp add: H_ex_def)
      have witness:
        "\<exists>c e. (c, e) \<in> set H_ex \<and> ec1 < c \<and> c \<le> ec4 \<and> key_of e = k"
        using in_H k300 ec1_less_ec2 ec2_less_eq_ec4
        by (intro exI[where x=ec2]
                  exI[where x="Insert (300::nat) (2500::nat)"]) auto
      show ?thesis
        unfolding touched_between_def l4_anchor_def using witness by blast
    qed
  qed
qed

text \<open>The running-example history has no event for the out-of-table key 999 ---
  used by the constructed Layer 4 fixtures in @{text Layer4_Fixtures_Inst}.\<close>

lemma latest_src_event_H_ex_ec4_999:
  "latest_src_event H_ex ec4 (999::nat) = None"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec4
                \<and> key_of (hist_event (H_ex ! i)) = (999::nat)"
  have "filter ?P [0, 1, 2, 3] = []"
    using H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3 by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

end
