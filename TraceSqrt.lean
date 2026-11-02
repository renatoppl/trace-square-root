import TraceSqrt.Defs

-- Section 1 & Appendix B: Trace-Square-Root & Quadratic Potentials
import TraceSqrt.Potential.GapEnvelope
import TraceSqrt.Potential.PotentialDecrease

-- Section 2, Appendix C, & Appendix E: Contextual Search
import TraceSqrt.Search.DeviationContraction
import TraceSqrt.Search.BayesianSearch
import TraceSqrt.Search.ScalarPotential
import TraceSqrt.Search.AdversarialDrift
import TraceSqrt.Search.AdversarialSearch
import TraceSqrt.Search.LowerBound

-- Section 3, Appendix D, & Appendix E: Contextual Bilateral Trade
import TraceSqrt.Trade.Displacement
import TraceSqrt.Trade.TradeProfile
import TraceSqrt.Trade.SmallGain
import TraceSqrt.Trade.TradeOrInformation
import TraceSqrt.Trade.BayesianTrade
import TraceSqrt.Trade.SionMinimax
import TraceSqrt.Trade.MinimaxLottery
import TraceSqrt.Trade.TradeLottery
import TraceSqrt.Trade.AdversarialTrade
import TraceSqrt.Trade.LowerBound

/-!
# Contextual Search and Bilateral Trade with a Trace-Square-Root Potential

Complete Lean 4 (`v4.27.0` + Mathlib `v4.27.0`) formalization of all 22 numbered mathematical
statements (lemmas, theorems, remarks, claims, corollaries, and propositions), key variational
and small-gain identities, and all 4 online algorithms in:

*Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
by Romain Cosson, Federico Fusco, Anupam Gupta, Stefano Leonardi, Renato Paes Leme, and Matteo Russo.

Importing `TraceSqrt` brings all shared definitions (`TraceSqrt.Defs`) and all 18 proof modules
into scope under the `TraceSqrt` namespace.
-/
