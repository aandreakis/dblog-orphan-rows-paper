(*  Title:   DBLog_Cert_Substrate_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory DBLog_Cert_Substrate_Inst
  imports DBLog_Cert_Substrate Continuation
begin

section \<open>Certificate substrate: continuation corollaries and a canonical
  concrete interpretation\<close>

text \<open>
  Two pieces over the certificate-substrate locales of
  @{text DBLog_Cert_Substrate}.

    \<^item> \<^bold>\<open>Continuation corollaries, locale side.\<close> The continuation
        extension @{text Continuation} states its two
        cert-bound corollaries --- @{thm [source] virtual_cut_restrict_to_subscope}
        and the @{locale layer3_checker_substrate} corollary
        @{text accepted_certificate_continuation_sound}
        --- over the \<^emph>\<open>global\<close> certificate carriers and the global
        @{locale layer3_checker_substrate}. Their heavy content lives entirely
        in the carrier-independent pure core (@{thm [source] virtual_cut_state_continuation},
        @{thm [source] virtual_cut_state_restrict_scope}, @{const cdc_segment_between}),
        which is global. Here we restate just the
        two thin corollaries inside @{locale dblog_cert_substrate} /
        @{locale dblog_checker_substrate}, reusing the global pure-core theorems
        verbatim, so the continuation proof API is available at every
        interpretation of the substrate locales.

    \<^item> \<^bold>\<open>Canonical concrete interpretation.\<close> The certificate-side analogue of
        the @{text canonical} run interpretation of
        @{text DBLog_Run_Substrate}. We instantiate
        @{locale dblog_cert_substrate} at the concrete run carrier
        @{typ "('k, 'v) run"} (through its selector functions) and
        a one-point certificate / evidence / observation carrier (@{typ unit}).
        @{locale dblog_cert_substrate} assumes nothing beyond the two
        @{const chunks_list} obligations it inherits from
        @{locale dblog_run_substrate}, so the interpretation discharges its
        proof obligations with @{method simp} alone, introducing no axiom. Its
        success certifies that the abstract certificate interface is inhabited
        end-to-end on the full certificate accessor set.

  The canonical certificate interpretation's verifier rejects everything, so it
  inhabits the interface without accepting any certificate. The \<^emph>\<open>accepting\<close>
  interpretation of @{locale dblog_checker_substrate} --- discharging the four
  primitive checker obligations over a wellformed materialized run --- is
  constructed in @{text Layer3_Witnesses_Inst}.
\<close>

subsection \<open>Continuation corollaries over the abstract cert carriers\<close>

context dblog_cert_substrate
begin

text \<open>Sub-scope restriction over a certificate, cert-substrate side: the locale
  instance of the global @{thm [source] virtual_cut_restrict_to_subscope},
  reducing to the global pure-core @{thm [source] virtual_cut_state_restrict_scope}.\<close>

theorem virtual_cut_restrict_to_subscope:
  assumes vc:  "virtual_cut b0 C H"
      and sub: "K' \<subseteq> scope C"
  shows "virtual_cut_state b0 (clean_prefix C) K' (frontier C) H"
proof -
  have "virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"
    using vc by (simp add: virtual_cut_def virtual_cut_state_def virtual_cut_state_def)
  thus ?thesis
    using sub by (rule virtual_cut_state_restrict_scope)
qed

end

context dblog_checker_substrate
begin

text \<open>Continuation over an accepted certificate, checker-substrate side: the
  locale instance of the global
  @{thm [source] layer3_checker_substrate.accepted_certificate_continuation_sound},
  composing the inherited @{thm [source] accepted_virtual_cut_sound} with the
  global pure-core @{thm [source] virtual_cut_state_continuation}.\<close>

theorem accepted_certificate_continuation_sound:
  assumes accept:   "verify C E = accept_value"
      and faithful: "faithful_source_observation E b0 H Raw"
      and wfH:      "wellformed_src_history H"
      and seg:      "cdc_segment_between H (scope C) (frontier C) f' \<delta>"
  shows "virtual_cut_state b0 (clean_prefix C @ \<delta>) (scope C) f' H"
proof -
  have "virtual_cut b0 C H"
    by (rule accepted_virtual_cut_sound[OF accept faithful])
  hence "virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"
    unfolding virtual_cut_def virtual_cut_state_def virtual_cut_state_def .
  from virtual_cut_state_continuation[OF wfH this seg]
  show ?thesis .
qed

end


subsection \<open>Canonical certificate-substrate interpretation\<close>

text \<open>
  The run side reuses the concrete @{type run} carrier through its selector
  functions (chunks modeled as @{typ nat}, the chunk enumeration
  @{term "remdups \<circ> rr_chunks_list"}). The certificate, evidence, and
  observation carriers are the one-point type @{typ unit}; their accessors are
  arbitrary total functions (the locale constrains none of them), so the only
  proof obligations are the two inherited @{const chunks_list} facts, which hold
  definitionally for every carrier value.
\<close>

global_interpretation canonical_cert: dblog_cert_substrate
  rr_scope
  rr_frontier
  "\<lambda>r. set (rr_chunks_list r)"
  rr_src_history
  rr_rresult
  rr_cdc
  "\<lambda>r. remdups (rr_chunks_list r)"
  rr_dom
  rr_resp
  rr_lwm
  rr_uwm
  rr_rcoord
  "\<lambda>_::unit. {}"
  "\<lambda>_::unit. c0"
  "\<lambda>_::unit. []"
  "\<lambda>(_::unit) (_::unit). Reject"
  Accept
  "\<lambda>(_::unit) _ _ (_::unit). False"
  "\<lambda>(_::unit) (_::unit) _. False"
  "\<lambda>(_::unit) (_::unit). False"
  "\<lambda>(_::unit) (_::unit). False"
  by unfold_locales simp_all

end
