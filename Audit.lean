import TraceSqrt

/-!
# Axiom audit

Run from the package root after `lake build`:

    lake env lean Audit.lean

Each `#print axioms` line below reports the axioms that the declaration depends on. For every
declaration the output is exactly Lean's three standard axioms `propext`, `Classical.choice`, and
`Quot.sound`; in particular, `sorryAx` never appears. The list covers every node of the dependency
graph in `README.md` together with the four randomized-context theorems.

This file is not part of the `TraceSqrt` library, so `lake build` does not compile it.
-/

open TraceSqrt

-- Section 1 & Appendix B
#print axioms lem_envelope
#print axioms lem_gap_function
#print axioms quad_potential_variational
#print axioms lem_directional_sd_decrease
#print axioms lem_directional_sd_decrease_binary

-- Section 2, Appendix C & Appendix E
#print axioms thm_bayesian_contextual_search
#print axioms thm_bayesian_contextual_search_rand_ctx
#print axioms lem_deviation_contraction
#print axioms rem_pd
#print axioms thm_adversarial_contextual_search
#print axioms thm_adversarial_contextual_search_rand_ctx
#print axioms lem_drift
#print axioms lem_scalar_potential
#print axioms prop_search_lower_bound
#print axioms prop_search_lower_bound_potential

-- Section 3, Appendix D & Appendix E
#print axioms lem_toi
#print axioms thm_bayesian_bilateral_trade
#print axioms thm_bayesian_bilateral_trade_rand_ctx
#print axioms lem_initial_potential_jitter_and_lip
#print axioms lem_trade_lottery
#print axioms thm_adversarial_bilateral_trade
#print axioms cor_adversarial_bilateral_trade_regret
#print axioms thm_adversarial_bilateral_trade_rand_ctx
#print axioms claim_D_nonneg
#print axioms claim_gain_decomposition
#print axioms claim_trade_displacement
#print axioms claim_trade_profile
#print axioms lem_trade_small_gain
#print axioms claim_trade_minimax
#print axioms thm_sion_minimax
#print axioms cor_sion_affine
#print axioms prop_trade_lower_bound
#print axioms prop_trade_lower_bound_potential
#print axioms cor_trade_lower_bound_potential
