import Mathlib

/-!
# Shared Definitions for Contextual Search and Bilateral Trade

Core mathematical definitions, potential functions, and online protocols for
*Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Cosson, Fusco, Gupta, Leonardi, Paes Leme, and Russo).

## Organization
1. **Conventions & Moments** (Section 1.4 & Appendix A): `paperSign`, `vecL2Norm`,
   `rademacherExpect`, `rvStdDev`, `condMean`, `condStdDev`, `rvMeanVec`, `rvCovMat`,
   `prob_expectation_le_of_pointwise`.
2. **Trace-Square-Root & Gap Potentials** (Section 1.2.2 & Appendix B): `traceSqrtPotential`,
   `psdTraceSqrt`, `gapPotential`, `envelopeSlope`, `envelopeObjective`.
3. **Bayesian Contextual Search** (Section 2.1, Algorithm 1): `searchBranchEvent`,
   `expectedPosteriorStdDev`, `SearchObs`, `alg1ExpectedLoss`.
4. **Adversarial Contextual Search** (Section 2.2 & Appendix C, Algorithm 2): `scalarPotential`,
   `scalarPostedPrice`, `scalarFeedback`, `scalarUpdatedCenter`, `scalarUpdatedScale`,
   `quadPotential`, `alg2PostedPrice`, `alg2NextCenter`, `alg2NextScale`, `alg2RunExpected`,
   `alg2InitScale`.
5. **Contextual Search Lower Bound** (Appendix E, Proposition E.1): `SearchLearner`,
   `searchTrajectory`, `searchCumulativeLoss`, `hypercubeTarget`, `unifBoolPrior`.
6. **Scalar Trade-or-Information & Bayesian Bilateral Trade** (Section 3.1 & Appendix D.1,
   Algorithm 3): `posteriorDeltaSq`, `posteriorDelta`, `posteriorVarrho`, `tradeEvent`,
   `tradeProfile`, `agentInfoDrop`, `totalInfoDrop`, `supInfoDrop`, `availableGain`,
   `expectedLostGain`, `tradeProfileEnvelope`, `tradeBayesPotential`, `alg3SelectPrice`,
   `BayesTradeObs`, `alg3ExpectedRegret`.
7. **Adversarial Bilateral Trade & Minimax** (Section 3.2 & Appendix D.2, Algorithm 4):
   `agentQuadPotential`, `tradeQuadPotential`, `TradePlan`, `planRoundCost`,
   `IsValidTradeLottery`, `alg4SelectLottery`, `AdvTradeObs`, `alg4RunExpected`, `alg4InitScale`,
   `UnitBallPair`, `PDTradeState`, `RealTradePlan`, `realPlanRoundCost`, `realPlanExcessCost`,
   `lotteryExpectedExcessCost`, `tradeBayesianValue`, `tradeWorstCaseLotteryValue`.
8. **Bilateral Trade Lower Bound** (Appendix E, Proposition E.2): `tradeFeedbackBit`,
   `tradeRoundLoss`, `BudgetBalancedBroker`, `tradeTrajectory`, `tradeCumulativeRegret`,
   `priorSellerVec`, `priorBuyerVec`.
-/

namespace TraceSqrt

/-! ## 1. Conventions and Basic Probability / Linear-Algebra Primitives -/

/-- Paper sign convention `sign(0) = 1`: returns `1` for `0 ≤ u` and `-1` for `u < 0`. -/
noncomputable def paperSign (u : ℝ) : ℝ :=
  if 0 ≤ u then 1 else -1

/-- Euclidean L2 norm on `Fin d → ℝ`: `‖v‖₂ = √(∑ i, v_i^2)`. -/
noncomputable def vecL2Norm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, (v i) ^ 2)

/-- Uniform expectation `(f(-1) + f(1)) / 2` over a Rademacher coin `ε ∈ {-1, 1}`. -/
noncomputable def rademacherExpect (f : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (f (-1) + f 1)

/-- Standard deviation `sd(Z) = √(Var(Z))` under a measure `ν`. -/
noncomputable def rvStdDev {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℝ) (ν : MeasureTheory.Measure Ω) : ℝ :=
  Real.sqrt (ProbabilityTheory.variance Z ν)

/-- Conditional mean `E[Z | E]` under `ProbabilityTheory.cond μ E`. -/
noncomputable def condMean {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (E : Set Ω) : ℝ :=
  ∫ ω, Z ω ∂(ProbabilityTheory.cond μ E)

/-- Conditional standard deviation `sd(Z | E)` under `ProbabilityTheory.cond μ E`. -/
noncomputable def condStdDev {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (E : Set Ω) : ℝ :=
  rvStdDev Z (ProbabilityTheory.cond μ E)

/-- Mean vector `E_ν[Z]` of a random vector `Z : Ω → (Fin d → ℝ)`. -/
noncomputable def rvMeanVec {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → (Fin d → ℝ)) (ν : MeasureTheory.Measure Ω) : Fin d → ℝ :=
  fun i => ∫ ω, Z ω i ∂ν

/-- Covariance matrix `Cov_ν(Z)_{ij} = E_ν[(Z_i - μ_i)(Z_j - μ_j)]`. -/
noncomputable def rvCovMat {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → (Fin d → ℝ)) (ν : MeasureTheory.Measure Ω) : Matrix (Fin d) (Fin d) ℝ :=
  let mu := rvMeanVec Z ν
  Matrix.of fun i j => ∫ ω, (Z ω i - mu i) * (Z ω j - mu j) ∂ν

/-- Expectation bound on a probability space `(Ξ, ν)` for a pointwise nonnegative, bounded
quantity `L : Ξ → ℝ`: gives the extended Lebesgue bound unconditionally and integrability plus
the Bochner integral bound under `AEStronglyMeasurable`. -/
lemma prob_expectation_le_of_pointwise {Ξ : Type*} [MeasurableSpace Ξ]
    (ν : MeasureTheory.Measure Ξ) [MeasureTheory.IsProbabilityMeasure ν]
    (L : Ξ → ℝ) (B : ℝ) (hL : ∀ ξ, 0 ≤ L ξ ∧ L ξ ≤ B) :
    (∫⁻ ξ, ENNReal.ofReal (L ξ) ∂ν ≤ ENNReal.ofReal B) ∧
    (MeasureTheory.AEStronglyMeasurable L ν →
      MeasureTheory.Integrable L ν ∧ 0 ≤ (∫ ξ, L ξ ∂ν) ∧ (∫ ξ, L ξ ∂ν) ≤ B) := by
  refine ⟨?_, fun hmeas => ?_⟩
  · calc ∫⁻ ξ, ENNReal.ofReal (L ξ) ∂ν
        ≤ ∫⁻ _ξ, ENNReal.ofReal B ∂ν :=
          MeasureTheory.lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hL ξ).2
      _ = ENNReal.ofReal B := by simp
  · have h_int : MeasureTheory.Integrable L ν :=
      MeasureTheory.Integrable.of_bound hmeas B
        (Filter.Eventually.of_forall fun ξ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hL ξ).1]
          exact (hL ξ).2)
    refine ⟨h_int, MeasureTheory.integral_nonneg (fun ξ => (hL ξ).1), ?_⟩
    calc ∫ ξ, L ξ ∂ν
        ≤ ∫ _ξ, B ∂ν :=
          MeasureTheory.integral_mono h_int (MeasureTheory.integrable_const B) (fun ξ => (hL ξ).2)
      _ = B := by simp

/-! ## 2. Trace-Square-Root and Variational Gap Potentials (Section 1.2.2 & Appendix B) -/

/-- Trace-square-root potential `Ψ(Σ) = Tr(Σ^{1/2})` for a positive-semidefinite matrix `Σ`
(Section 1.2.2, Eq. (1)). -/
noncomputable def traceSqrtPotential {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) : ℝ :=
  Matrix.trace hS.sqrt

/-- Total function version of the trace-square-root potential `Ψ(Σ) = Tr(Σ^{1/2})` when `Σ ⪰ 0`
(and `0` otherwise). -/
noncomputable def psdTraceSqrt {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  letI := Classical.propDecidable
  if hS : S.PosSemidef then Matrix.trace hS.sqrt else 0

/-- Residual / gap potential `g_x(Σ) = Tr(Σ^{1/2}) - √(xᵀ Σ x)` for `Σ ⪰ 0`
(Section 1.2.2, Lemma 1.1 & Appendix B, Lemma B.1, Eq. (23)). -/
noncomputable def gapPotential {d : ℕ} (x : Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) : ℝ :=
  Matrix.trace hS.sqrt - Real.sqrt (dotProduct x (S.mulVec x))

/-- Affine slope matrix `H_R(x) = R⁻¹ - (x xᵀ) / ‖R x‖₂` (defined as `R⁻¹` when `x = 0`). -/
noncomputable def envelopeSlope {d : ℕ} (x : Fin d → ℝ)
    (R : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  if x = 0 then R⁻¹ else R⁻¹ - (vecL2Norm (R.mulVec x))⁻¹ • Matrix.vecMulVec x x

/-- Variational objective `Tr(R) - ‖R x‖₂ + Tr(H_R(x) Σ)` inside the infimum of Eq. (4)
and Lemma B.1, Eq. (24). -/
noncomputable def envelopeObjective {d : ℕ} (x : Fin d → ℝ)
    (R S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Matrix.trace R - vecL2Norm (R.mulVec x) + Matrix.trace (envelopeSlope x R * S)

/-! ## 3. Bayesian Contextual Search (Section 2.1, Algorithm 1) -/

/-- Branch event `{ω | (0 ≤ Z(ω) - P) = b}` for posted price `P = μ_Z + (σ_Z / 2) ε` under
`sign(0) = 1`. -/
def searchBranchEvent {Ω : Type*}
    (Z : Ω → ℝ) (muZ sigmaZ eps : ℝ) (b : Bool) : Set Ω :=
  {ω | decide (0 ≤ Z ω - (muZ + (sigmaZ / 2) * eps)) = b}

/-- Expected posterior standard deviation `E[sd(Z | P, Y)]` when `P = μ_Z + (σ_Z / 2) ε`
for independent uniform `ε ∈ {-1, 1}` and `Y = sign(Z - P)` (Lemma 2.2). -/
noncomputable def expectedPosteriorStdDev {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℝ) (μ : MeasureTheory.Measure Ω) : ℝ :=
  let muZ := ∫ ω, Z ω ∂μ
  let sigmaZ := rvStdDev Z μ
  (1 / 2 : ℝ) *
    ((∑ b : Bool,
        μ.real (searchBranchEvent Z muZ sigmaZ (-1) b) *
          condStdDev Z μ (searchBranchEvent Z muZ sigmaZ (-1) b)) +
     (∑ b : Bool,
        μ.real (searchBranchEvent Z muZ sigmaZ 1 b) *
          condStdDev Z μ (searchBranchEvent Z muZ sigmaZ 1 b)))

/-- Complete single-round observation `(x_s, ε_s, P_s, Y_s)` recorded in `𝓕_{t-1}` for contextual
search (Section 1.4, Algorithms 1 and 2): context `ctx`, learner Rademacher coin `coin ∈ {-1, 1}`,
posted price `price`, and comparison feedback `feedback ∈ {-1, 1}`. -/
structure SearchObs (d : ℕ) where
  ctx : Fin d → ℝ
  coin : ℝ
  price : ℝ
  feedback : ℝ

/-- Recursive `N`-round expected cumulative loss of Algorithm 1 (Bayesian Contextual Search)
starting from current posterior `ν` and observed full history `hist` (`𝓕_{t-1}`, containing past
contexts, learner coins, posted prices, and feedback bits) against an adaptive context strategy
`ctxPolicy` (Theorem 2.1). -/
noncomputable def alg1ExpectedLoss {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → (Fin d → ℝ))
    (ctxPolicy : List (SearchObs d) → (Fin d → ℝ)) :
    ℕ → MeasureTheory.Measure Ω → List (SearchObs d) → ℝ
  | 0, _, _ => 0
  | n + 1, ν, hist =>
      let x := ctxPolicy hist
      let muVec := rvMeanVec Z ν
      let S := rvCovMat Z ν
      let muProj := dotProduct x muVec
      let sigProj := Real.sqrt (dotProduct x (S.mulVec x))
      let stepForCoin (eps : ℝ) : ℝ :=
        let P := muProj + (sigProj / 2) * eps
        let curLoss := ∫ ω, |dotProduct x (Z ω) - P| ∂ν
        let E_pos : Set Ω := {ω | 0 ≤ dotProduct x (Z ω) - P}
        let E_neg : Set Ω := E_posᶜ
        let p_pos := ν.real E_pos
        let p_neg := ν.real E_neg
        let rem_pos :=
          if ν E_pos = 0 then 0
          else p_pos * alg1ExpectedLoss Z ctxPolicy n (ProbabilityTheory.cond ν E_pos)
            (hist ++ [⟨x, eps, P, 1⟩])
        let rem_neg :=
          if ν E_neg = 0 then 0
          else p_neg * alg1ExpectedLoss Z ctxPolicy n (ProbabilityTheory.cond ν E_neg)
            (hist ++ [⟨x, eps, P, -1⟩])
        curLoss + rem_pos + rem_neg
      (1 / 2 : ℝ) * (stepForCoin (-1) + stepForCoin 1)

/-! ## 4. Adversarial Contextual Search (Section 2.2 & Appendix C, Algorithm 2) -/

/-- Scalar quadratic potential `φ(m, r, z) = r + (m - z)^2 / r` (Appendix C.1, Lemma C.1). -/
noncomputable def scalarPotential (m r z : ℝ) : ℝ :=
  r + (m - z) ^ 2 / r

/-- Scalar randomized price `P(ε) = m + (r / 2) ε` for `ε ∈ {-1, 1}` (Lemma C.1). -/
noncomputable def scalarPostedPrice (m r eps : ℝ) : ℝ :=
  m + (r / 2) * eps

/-- Binary comparison feedback `Y(ε) = sign(z - P(ε))` under `sign(0) = 1` (Lemma C.1). -/
noncomputable def scalarFeedback (m r z eps : ℝ) : ℝ :=
  paperSign (z - scalarPostedPrice m r eps)

/-- Updated scalar center `m⁺(ε) = m + r Y / (3 - ε Y)` (Lemma C.1). -/
noncomputable def scalarUpdatedCenter (m r z eps : ℝ) : ℝ :=
  let Y := scalarFeedback m r z eps
  m + r * Y / (3 - eps * Y)

/-- Updated scalar scale `r⁺(ε) = 3 r / (3 - ε Y)` (Lemma C.1). -/
noncomputable def scalarUpdatedScale (m r z eps : ℝ) : ℝ :=
  let Y := scalarFeedback m r z eps
  3 * r / (3 - eps * Y)

/-- Quadratic matrix potential `Φ(m, R, z) = Tr(R) + (z - m)ᵀ R⁻¹ (z - m)`
(Section 1.2.2 Eq. (6) & Section 2.2 Eq. (12)). -/
noncomputable def quadPotential {d : ℕ}
    (mVec : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ) (zVec : Fin d → ℝ) : ℝ :=
  Matrix.trace R + dotProduct (zVec - mVec) (R⁻¹.mulVec (zVec - mVec))

/-- Price posted by Algorithm 2 at state `(mVec, R)`, context `xVec`, and coin `eps ∈ {-1, 1}`. -/
noncomputable def alg2PostedPrice {d : ℕ}
    (mVec : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    (xVec : Fin d → ℝ) (eps : ℝ) : ℝ :=
  if xVec = 0 then 0
  else dotProduct xVec mVec + (vecL2Norm (R.mulVec xVec) / 2) * eps

/-- Updated center `m_{t+1}` of Algorithm 2. -/
noncomputable def alg2NextCenter {d : ℕ}
    (mVec : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    (zVec xVec : Fin d → ℝ) (eps : ℝ) : Fin d → ℝ :=
  if xVec = 0 then mVec
  else
    let u := R.mulVec xVec
    let a := dotProduct xVec u
    let r := vecL2Norm u
    let P := alg2PostedPrice mVec R xVec eps
    let Y := paperSign (dotProduct xVec zVec - P)
    mVec + (Y * r / (a * (3 - eps * Y))) • u

/-- Updated scale matrix `R_{t+1}` of Algorithm 2. -/
noncomputable def alg2NextScale {d : ℕ}
    (mVec : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
    (zVec xVec : Fin d → ℝ) (eps : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  if xVec = 0 then R
  else
    let u := R.mulVec xVec
    let a := dotProduct xVec u
    let P := alg2PostedPrice mVec R xVec eps
    let Y := paperSign (dotProduct xVec zVec - P)
    R + (eps * Y / (a * (3 - eps * Y))) • Matrix.vecMulVec u u

/-- Recursive `N`-round execution of Algorithm 2 against a full-history adaptive context policy
`ctxPolicy` (`𝓕_{t-1}`), returning `(E[∑ ℓ_t], E[Φ_{T+1}])`. -/
noncomputable def alg2RunExpected {d : ℕ}
    (zVec : Fin d → ℝ)
    (ctxPolicy : List (SearchObs d) → (Fin d → ℝ)) :
    ℕ → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ → List (SearchObs d) → ℝ × ℝ
  | 0, mVec, R, _ => (0, quadPotential mVec R zVec)
  | n + 1, mVec, R, hist =>
      let xVec := ctxPolicy hist
      let branch (eps : ℝ) : ℝ × ℝ :=
        let P := alg2PostedPrice mVec R xVec eps
        let Y := paperSign (dotProduct xVec zVec - P)
        let ell := |dotProduct xVec zVec - P|
        let mNext := alg2NextCenter mVec R zVec xVec eps
        let RNext := alg2NextScale mVec R zVec xVec eps
        let sub := alg2RunExpected zVec ctxPolicy n mNext RNext (hist ++ [⟨xVec, eps, P, Y⟩])
        (ell + sub.1, sub.2)
      let bNeg := branch (-1)
      let bPos := branch 1
      ((1 / 2 : ℝ) * (bNeg.1 + bPos.1), (1 / 2 : ℝ) * (bNeg.2 + bPos.2))

/-- Initial scale matrix `R₁ = (1 / √d) I_d` of Algorithm 2. -/
noncomputable def alg2InitScale (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (Real.sqrt d)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)

/-! ## 5. Contextual Search Lower Bound (Appendix E, Proposition E.1) -/

/-- A possibly randomized contextual-search learner driven by a random seed `ω : Ω`.
At each round, given `ω`, the list of prior `(context, feedback_bit)` observations,
and the current context `x_t`, it outputs a price `P_t ∈ ℝ` measurably in `ω`. -/
structure SearchLearner (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  postPrice : Ω → List ((Fin d → ℝ) × ℝ) → (Fin d → ℝ) → ℝ
  measurable_postPrice :
    ∀ (hist : List ((Fin d → ℝ) × ℝ)) (x : Fin d → ℝ),
      Measurable (fun ω => postPrice ω hist x)

/-- Left-fold execution of `T` rounds of contextual search from round `0` to `T - 1`. -/
noncomputable def searchTrajectory {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (learner : SearchLearner d Ω) (z : Fin d → ℝ) (ω : Ω)
    (T : ℕ) (ctxs : Fin T → (Fin d → ℝ)) : ℝ × List ((Fin d → ℝ) × ℝ) :=
  (List.finRange T).foldl
    (fun (acc : ℝ × List ((Fin d → ℝ) × ℝ)) (t : Fin T) =>
      let lossSoFar := acc.1
      let hist := acc.2
      let xt := ctxs t
      let pt := learner.postPrice ω hist xt
      let yt := paperSign (dotProduct xt z - pt)
      let ell := |dotProduct xt z - pt|
      (lossSoFar + ell, hist ++ [(xt, yt)]))
    (0, [])

/-- Total cumulative loss `∑_{t=1}^T |x_tᵀ z - P_t|` over `T` rounds. -/
noncomputable def searchCumulativeLoss {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (learner : SearchLearner d Ω) (z : Fin d → ℝ)
    (T : ℕ) (ctxs : Fin T → (Fin d → ℝ)) (ω : Ω) : ℝ :=
  (searchTrajectory learner z ω T ctxs).1

/-- Coordinate-hypercube corner `z_σ ∈ {-1/√d, +1/√d}^d` used in Proposition E.1. -/
noncomputable def hypercubeTarget {d : ℕ} (signs : Fin d → Bool) : Fin d → ℝ :=
  fun j => if signs j then 1 / Real.sqrt d else -1 / Real.sqrt d

/-- Uniform probability measure on `Fin d → Bool`, assigning weight `2^{-d}` to each Boolean
coordinate vector in the coordinate-wise constructions of Propositions E.1 and E.2. -/
noncomputable def unifBoolPrior (d : ℕ) : MeasureTheory.Measure (Fin d → Bool) :=
  ((2 ^ d : ENNReal)⁻¹) • ∑ c : Fin d → Bool, MeasureTheory.Measure.dirac c

instance instIsProbabilityMeasureUnifBoolPrior (d : ℕ) :
    MeasureTheory.IsProbabilityMeasure (unifBoolPrior d) := by
  constructor
  change (((2 ^ d : ENNReal)⁻¹) • ∑ c : Fin d → Bool, MeasureTheory.Measure.dirac c) Set.univ = 1
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.finset_sum_apply]
  have h_dirac : ∀ c : Fin d → Bool, (MeasureTheory.Measure.dirac c) Set.univ = 1 := fun c => by
    rw [MeasureTheory.Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply]
  simp_rw [h_dirac]
  have h_card : Fintype.card (Fin d → Bool) = 2 ^ d := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [Finset.sum_const, Finset.card_univ, h_card, nsmul_eq_mul, mul_one,
    Nat.cast_pow, Nat.cast_ofNat, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (pow_ne_zero d two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)

/-! ## 6. Scalar Trade-or-Information & Bayesian Bilateral Trade (Section 3.1 & Appendix D.1) -/

/-- Squared posterior displacement `δ_{Z|E}^2 = (E[Z|E] - μ_Z)^2 + (sd(Z|E) - σ_Z)^2`
(Appendix D.1, Claim D.3). -/
noncomputable def posteriorDeltaSq {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (E : Set Ω) : ℝ :=
  (condMean Z μ E - ∫ ω, Z ω ∂μ) ^ 2 + (condStdDev Z μ E - rvStdDev Z μ) ^ 2

/-- Posterior displacement `δ_{Z|E} = √(δ_{Z|E}^2)` (Appendix D.1, Claim D.3). -/
noncomputable def posteriorDelta {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (E : Set Ω) : ℝ :=
  Real.sqrt (posteriorDeltaSq Z μ E)

/-- Conditional root-mean-square deviation from the prior mean:
`ϱ_{Z|E} = √(E[(Z - μ_Z)^2 | E])` (Appendix D.1, Claim D.3). -/
noncomputable def posteriorVarrho {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (E : Set Ω) : ℝ :=
  Real.sqrt (∫ ω, (Z ω - ∫ ω', Z ω' ∂μ) ^ 2 ∂(ProbabilityTheory.cond μ E))

/-- Trade event `E(p) = {ω | S(ω) ≤ p ∧ p ≤ B(ω)}` at common price `p`. -/
def tradeEvent {Ω : Type*} (S B : Ω → ℝ) (p : ℝ) : Set Ω :=
  {ω | S ω ≤ p ∧ p ≤ B ω}

/-- Trade profile `α(p) = P(S ≤ p ≤ B)` as a real probability in `[0, 1]`
(Section 3.1 & Appendix D.1, Claims D.2 and D.4). -/
noncomputable def tradeProfile {Ω : Type*} [MeasurableSpace Ω]
    (S B : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (p : ℝ) : ℝ :=
  μ.real (tradeEvent S B p)

/-- Per-agent standard-deviation drop `D_Z(p) = sd(Z) - E[sd(Z | Y_p)]` at common price `p`. -/
noncomputable def agentInfoDrop {Ω : Type*} [MeasurableSpace Ω]
    (Z S B : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (p : ℝ) : ℝ :=
  let E := tradeEvent S B p
  rvStdDev Z μ - (μ.real E * condStdDev Z μ E + μ.real Eᶜ * condStdDev Z μ Eᶜ)

/-- Combined scalar information drop `D(p) = D_S(p) + D_B(p)` at common price `p`
(Section 3.1 Eq. (16) & Appendix D.1, Claim D.1). -/
noncomputable def totalInfoDrop {Ω : Type*} [MeasurableSpace Ω]
    (S B : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (p : ℝ) : ℝ :=
  agentInfoDrop S S B μ p + agentInfoDrop B S B μ p

/-- Uniform information ceiling `D̄ = sup_{p ∈ ℝ} D(p)` (Appendix D.1, Claim D.4). -/
noncomputable def supInfoDrop {Ω : Type*} [MeasurableSpace Ω]
    (S B : Ω → ℝ) (μ : MeasureTheory.Measure Ω) : ℝ :=
  sSup (Set.range (totalInfoDrop S B μ))

/-- Expected available gain from trade `G = E[(B - S)_+]` (Appendix D.1, Claim D.2). -/
noncomputable def availableGain {Ω : Type*} [MeasurableSpace Ω]
    (S B : Ω → ℝ) (μ : MeasureTheory.Measure Ω) : ℝ :=
  ∫ ω, max (B ω - S ω) 0 ∂μ

/-- Expected lost gain `L(p) = E[(B - S)_+ (1 - Y_p)]` at common price `p`
(Section 3.1 Eq. (15) & Lemma 3.1). -/
noncomputable def expectedLostGain {Ω : Type*} [MeasurableSpace Ω]
    (S B : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (p : ℝ) : ℝ :=
  ∫ ω, max (B ω - S ω) 0 * (if S ω ≤ p ∧ p ≤ B ω then 0 else 1) ∂μ

/-- Five-piece trade-profile upper-bound envelope `H(p)` from Appendix D.1, Claim D.4.
When `σ_S > 0` and `σ_B > 0` (the overlapping regime after deterministic corner cases), the five
pieces coincide verbatim with the display before Claim D.4; if a standard deviation vanishes,
its degenerate zero-length central singleton `{μ_Z}` takes value `1` rather than Lean's `0 / 0 = 0`,
preserving `α(p) ≤ H(p)` everywhere without altering the Lebesgue integral of `H`. -/
noncomputable def tradeProfileEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (S B : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (p : ℝ) : ℝ :=
  let muS := ∫ ω, S ω ∂μ
  let muB := ∫ ω, B ω ∂μ
  let sigS := rvStdDev S μ
  let sigB := rvStdDev B μ
  let Dbar := supInfoDrop S B μ
  if p < muS - sigS / 3 then
    (2 * sigS * Dbar) / (muS - p) ^ 2
  else if p ≤ muS + sigS / 3 then
    if sigS = 0 then 1 else (225 * Dbar) / (2 * sigS)
  else if p < muB - sigB / 3 then
    1
  else if p ≤ muB + sigB / 3 then
    if sigB = 0 then 1 else (225 * Dbar) / (2 * sigB)
  else
    (2 * sigB * Dbar) / (p - muB) ^ 2

/-- Bilateral-trade Bayesian potential `Ψ_tr(ν) = Tr(√Cov_ν(W_S)) + Tr(√Cov_ν(W_B))`
(Section 3.1 Eq. (14), Algorithm 3). -/
noncomputable def tradeBayesPotential {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (WS WB : Ω → (Fin d → ℝ)) (ν : MeasureTheory.Measure Ω) : ℝ :=
  psdTraceSqrt (rvCovMat WS ν) + psdTraceSqrt (rvCovMat WB ν)

/-- Common-price selection rule of Algorithm 3 (selects a price satisfying `L(p) ≤ 2^{11} D(p)`
whenever one exists, as guaranteed by Lemma 3.1, and `0` otherwise). -/
noncomputable def alg3SelectPrice {Ω : Type*} [MeasurableSpace Ω]
    (S B : Ω → ℝ) (ν : MeasureTheory.Measure Ω) : ℝ :=
  letI := Classical.propDecidable
  if h : ∃ p : ℝ, expectedLostGain S B ν p ≤ (2 ^ 11 : ℝ) * totalInfoDrop S B ν p then
    Classical.choose h
  else 0

/-- Complete single-round observation `(x_s, p_s, Y_s)` recorded in `𝓕_{t-1}` for Bayesian
bilateral trade (Section 1.4, Algorithm 3): context `ctx`, posted common price `price`, and
realized trade indicator `feedback ∈ {0, 1}` (Algorithm 3 uses no fresh learner randomization). -/
structure BayesTradeObs (d : ℕ) where
  ctx : Fin d → ℝ
  price : ℝ
  feedback : ℝ

/-- Recursive `N`-round expected cumulative regret of Algorithm 3 (Bayesian Bilateral Trade,
Theorem 3.2) against a full-history adaptive context strategy `ctxPolicy` (`𝓕_{t-1}`). -/
noncomputable def alg3ExpectedRegret {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (WS WB : Ω → (Fin d → ℝ))
    (ctxPolicy : List (BayesTradeObs d) → (Fin d → ℝ)) :
    ℕ → MeasureTheory.Measure Ω → List (BayesTradeObs d) → ℝ
  | 0, _, _ => 0
  | n + 1, ν, hist =>
      let x := ctxPolicy hist
      let S : Ω → ℝ := fun ω => dotProduct x (WS ω)
      let B : Ω → ℝ := fun ω => dotProduct x (WB ω)
      let p := alg3SelectPrice S B ν
      let curLoss := expectedLostGain S B ν p
      let E_tr : Set Ω := {ω | S ω ≤ p ∧ p ≤ B ω}
      let E_no : Set Ω := E_trᶜ
      let rem_tr :=
        if ν E_tr = 0 then 0
        else ν.real E_tr * alg3ExpectedRegret WS WB ctxPolicy n (ProbabilityTheory.cond ν E_tr)
          (hist ++ [⟨x, p, 1⟩])
      let rem_no :=
        if ν E_no = 0 then 0
        else ν.real E_no * alg3ExpectedRegret WS WB ctxPolicy n (ProbabilityTheory.cond ν E_no)
          (hist ++ [⟨x, p, 0⟩])
      curLoss + rem_tr + rem_no

/-! ## 7. Adversarial Bilateral Trade & Minimax (Section 3.2 & Appendix D.2, Algorithm 4) -/

/-- Per-agent quadratic potential `Φ_d(m, R, z) = Tr(R) + (z - m)ᵀ R⁻¹ (z - m)`. -/
noncomputable def agentQuadPotential {d : ℕ}
    (mVec : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ) (zVec : Fin d → ℝ) : ℝ :=
  Matrix.trace R + dotProduct (zVec - mVec) (R⁻¹.mulVec (zVec - mVec))

/-- Block-diagonal bilateral-trade quadratic potential
`Φ((m_S, m_B), diag(R_S, R_B), (s, b)) = Φ_d(m_S, R_S, s) + Φ_d(m_B, R_B, b)`
(Section 3.2 Eq. (20)). -/
noncomputable def tradeQuadPotential {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (s b : Fin d → ℝ) : ℝ :=
  agentQuadPotential mS RS s + agentQuadPotential mB RB b

/-- Deterministic bilateral-trade plan with common rational offer `p = q` and
positive-definite block-diagonal successor states for `Y = 0` and `Y = 1` (Lemma 3.3). -/
structure TradePlan (d : ℕ) where
  price : ℚ
  mS0 : Fin d → ℝ
  mB0 : Fin d → ℝ
  RS0 : Matrix (Fin d) (Fin d) ℝ
  RB0 : Matrix (Fin d) (Fin d) ℝ
  mS1 : Fin d → ℝ
  mB1 : Fin d → ℝ
  RS1 : Matrix (Fin d) (Fin d) ℝ
  RB1 : Matrix (Fin d) (Fin d) ℝ
  posDef_RS0 : RS0.PosDef
  posDef_RB0 : RB0.PosDef
  posDef_RS1 : RS1.PosDef
  posDef_RB1 : RB1.PosDef

/-- Forgone gain + scaled successor potential `ℓ(w) + 2^{10} Φ(m⁺, R⁺, w)` of a plan at `(s, b)`. -/
noncomputable def planRoundCost {d : ℕ}
    (x : Fin d → ℝ) (plan : TradePlan d) (s b : Fin d → ℝ) : ℝ :=
  let S := dotProduct x s
  let B := dotProduct x b
  let p : ℝ := plan.price
  if S ≤ p ∧ p ≤ B then
    (2 ^ 10 : ℝ) * tradeQuadPotential plan.mS1 plan.mB1 plan.RS1 plan.RB1 s b
  else
    max (B - S) 0 + (2 ^ 10 : ℝ) * tradeQuadPotential plan.mS0 plan.mB0 plan.RS0 plan.RB0 s b

/-- Validity predicate for a finite lottery of plans with slack `γ` (Lemma 3.3 & Algorithm 4). -/
def IsValidTradeLottery {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (γ : ℝ) (lottery : List (ℝ × TradePlan d)) : Prop :=
  (∀ wp ∈ lottery, 0 ≤ wp.1) ∧
  (lottery.map Prod.fst).sum = 1 ∧
  (∀ s b : Fin d → ℝ, vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 →
    (lottery.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum ≤
      (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB s b + γ)

/-- Algorithm 4's per-round lottery selector at round index `roundIdx` (`t = roundIdx + 1`),
using `γ_t = 1 / (t (t + 1))`. -/
noncomputable def alg4SelectLottery {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (roundIdx : ℕ) : List (ℝ × TradePlan d) :=
  letI := Classical.propDecidable
  let t : ℝ := (roundIdx : ℝ) + 1
  let γ : ℝ := 1 / (t * (t + 1))
  if h : ∃ lottery : List (ℝ × TradePlan d), IsValidTradeLottery mS mB RS RB x γ lottery then
    Classical.choose h
  else
    []

/-- Complete single-round observation `(x_s, idx_s, plan_s, p_s, Y_s)` recorded in `𝓕_{t-1}` for
adversarial bilateral trade (Section 1.4, Algorithm 4): context `ctx`, sampled lottery-atom index
`atomIdx`, sampled `plan : TradePlan d` (including its price and both successor states), posted
common price `price`, and realized trade indicator `feedback ∈ {0, 1}`. -/
structure AdvTradeObs (d : ℕ) where
  ctx : Fin d → ℝ
  atomIdx : ℕ
  plan : TradePlan d
  price : ℝ
  feedback : ℝ

/-- Recursive `N`-round execution of Algorithm 4 starting from round index `roundIdx` against a
full-history adaptive context strategy `ctxPolicy` (`𝓕_{t-1}`), returning
`(E[Reg_rem], E[Φ_{T+1}])` (Theorem 3.4). -/
noncomputable def alg4RunExpected {d : ℕ}
    (s b : Fin d → ℝ)
    (ctxPolicy : List (AdvTradeObs d) → (Fin d → ℝ)) :
    ℕ → ℕ → (Fin d → ℝ) → (Fin d → ℝ) →
    Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ →
    List (AdvTradeObs d) → ℝ × ℝ
  | 0, _, mS, mB, RS, RB, _ =>
      (0, tradeQuadPotential mS mB RS RB s b)
  | n + 1, roundIdx, mS, mB, RS, RB, hist =>
      let x := ctxPolicy hist
      let lottery := alg4SelectLottery mS mB RS RB x roundIdx
      let evalAtom (entry : (ℝ × TradePlan d) × ℕ) : ℝ × ℝ :=
        let w := entry.1.1
        let plan := entry.1.2
        let idx := entry.2
        let p : ℝ := plan.price
        let S := dotProduct x s
        let B := dotProduct x b
        if S ≤ p ∧ p ≤ B then
          let sub := alg4RunExpected s b ctxPolicy n (roundIdx + 1)
            plan.mS1 plan.mB1 plan.RS1 plan.RB1 (hist ++ [⟨x, idx, plan, p, 1⟩])
          (w * sub.1, w * sub.2)
        else
          let ell := max (B - S) 0
          let sub := alg4RunExpected s b ctxPolicy n (roundIdx + 1)
            plan.mS0 plan.mB0 plan.RS0 plan.RB0 (hist ++ [⟨x, idx, plan, p, 0⟩])
          (w * (ell + sub.1), w * sub.2)
      let terms := lottery.zipIdx.map evalAtom
      ((terms.map Prod.fst).sum, (terms.map Prod.snd).sum)

/-- Initial per-agent scale matrix `(1 / √d) I_d` of Algorithm 4 (`R₁ = I_{2d} / √d`). -/
noncomputable def alg4InitScale (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (Real.sqrt d)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- Euclidean space `ℝ^d` for compact metric-space formulations in Appendix D.2. -/
abbrev EucVec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Joint Euclidean space `ℝ^d ×₂ ℝ^d ≅ ℝ^{2d}` endowed with the Euclidean L2 metric. -/
abbrev EucPair (d : ℕ) := WithLp 2 (EucVec d × EucVec d)

/-- Admissible hidden-pair subset `{ (s, b) ∈ ℝ^{2d} | ‖s‖₂ ≤ 1 ∧ ‖b‖₂ ≤ 1 }` (`K = B_2^d × B_2^d`). -/
def UnitBallPairSet (d : ℕ) : Set (EucPair d) :=
  {w | ‖WithLp.fst w‖ ≤ 1 ∧ ‖WithLp.snd w‖ ≤ 1}

/-- Compact metric space `K = B_2^d × B_2^d ⊂ ℝ^{2d}` of admissible hidden valuation pairs
(Appendix D.2, Claim D.5 & Corollary D.7). -/
abbrev UnitBallPair (d : ℕ) := Subtype (UnitBallPairSet d)

/-- Seller parameter `s : Fin d → ℝ` of `w ∈ K`. -/
def UnitBallPair.seller {d : ℕ} (w : UnitBallPair d) : Fin d → ℝ :=
  (WithLp.fst w.1).ofLp

/-- Buyer parameter `b : Fin d → ℝ` of `w ∈ K`. -/
def UnitBallPair.buyer {d : ℕ} (w : UnitBallPair d) : Fin d → ℝ :=
  (WithLp.snd w.1).ofLp

lemma isCompact_unitBallPairSet (d : ℕ) : IsCompact (UnitBallPairSet d) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le (continuous_norm.comp (WithLp.continuous_fst 2 (EucVec d) (EucVec d)))
        continuous_const).inter
      (isClosed_le (continuous_norm.comp (WithLp.continuous_snd 2 (EucVec d) (EucVec d)))
        continuous_const)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨2, fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, WithLp.prod_norm_eq_add (by norm_num)]
    have h1 : ‖WithLp.fst w‖ ^ (2 : ℝ) ≤ 1 := by
      rw [Real.rpow_two]; nlinarith [hw.1, norm_nonneg (WithLp.fst w)]
    have h2 : ‖WithLp.snd w‖ ^ (2 : ℝ) ≤ 1 := by
      rw [Real.rpow_two]; nlinarith [hw.2, norm_nonneg (WithLp.snd w)]
    have hsum : ‖WithLp.fst w‖ ^ (2 : ℝ) + ‖WithLp.snd w‖ ^ (2 : ℝ) ≤ 4 := by linarith
    calc (‖WithLp.fst w‖ ^ (2 : ℝ) + ‖WithLp.snd w‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
        ≤ (4 : ℝ) ^ (1 / (2 : ℝ)) := Real.rpow_le_rpow (by positivity) hsum (by positivity)
      _ = 2 := by norm_num

instance instCompactSpaceUnitBallPair (d : ℕ) : CompactSpace (UnitBallPair d) :=
  isCompact_iff_compactSpace.mp (isCompact_unitBallPairSet d)

instance instNonemptyUnitBallPair (d : ℕ) : Nonempty (UnitBallPair d) :=
  ⟨⟨0, ⟨by simp, by simp⟩⟩⟩

/-- Raw ambient coordinates `(m_S, m_B, R_S, R_B)` of a block-diagonal bilateral-trade state. -/
abbrev RawTradeState (d : ℕ) :=
  (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)

/-- Subset of positive-definite block-diagonal bilateral-trade states (`R_S ≻ 0` and `R_B ≻ 0`). -/
def PDTradeStateSet (d : ℕ) : Set (RawTradeState d) :=
  {st | (Matrix.of st.2.2.1).PosDef ∧ (Matrix.of st.2.2.2).PosDef}

/-- Topological and Borel space of positive-definite block-diagonal bilateral-trade states
`((m_S, m_B), diag(R_S, R_B))` with `R_S ≻ 0` and `R_B ≻ 0`. -/
abbrev PDTradeState (d : ℕ) := Subtype (PDTradeStateSet d)

/-- Seller center `m_S` of a positive-definite block-diagonal state. -/
def PDTradeState.mS {d : ℕ} (st : PDTradeState d) : Fin d → ℝ := st.1.1

/-- Buyer center `m_B` of a positive-definite block-diagonal state. -/
def PDTradeState.mB {d : ℕ} (st : PDTradeState d) : Fin d → ℝ := st.1.2.1

/-- Seller scale matrix `R_S` of a positive-definite block-diagonal state. -/
def PDTradeState.RS {d : ℕ} (st : PDTradeState d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of st.1.2.2.1

/-- Buyer scale matrix `R_B` of a positive-definite block-diagonal state. -/
def PDTradeState.RB {d : ℕ} (st : PDTradeState d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of st.1.2.2.2

lemma PDTradeState.posDef_RS {d : ℕ} (st : PDTradeState d) : st.RS.PosDef := st.2.1

lemma PDTradeState.posDef_RB {d : ℕ} (st : PDTradeState d) : st.RB.PosDef := st.2.2

/-- Construct a `PDTradeState d` from `(mS, mB, RS, RB)` and positivity proofs. -/
def PDTradeState.mk' {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (hRS : RS.PosDef) (hRB : RB.PosDef) : PDTradeState d :=
  ⟨(mS, mB, RS, RB), ⟨hRS, hRB⟩⟩

/-- Space `A` of deterministic bilateral-trade plans with arbitrary real common price `p_a ∈ ℝ`
and positive-definite block-diagonal successor states for `Y = 0` and `Y = 1`
(Appendix D.2, Claim D.5). -/
abbrev RealTradePlan (d : ℕ) := ℝ × PDTradeState d × PDTradeState d

/-- Common price `p_a ∈ ℝ` of a plan `a ∈ A`. -/
def RealTradePlan.price {d : ℕ} (a : RealTradePlan d) : ℝ := a.1

/-- Rejection (`Y = 0`) successor state `(m_a^{(0)}, R_a^{(0)})` of `a ∈ A`. -/
def RealTradePlan.succ0 {d : ℕ} (a : RealTradePlan d) : PDTradeState d := a.2.1

/-- Trade (`Y = 1`) successor state `(m_a^{(1)}, R_a^{(1)})` of `a ∈ A`. -/
def RealTradePlan.succ1 {d : ℕ} (a : RealTradePlan d) : PDTradeState d := a.2.2

/-- Nonnegative round cost `ℓ_a(w) + 2^{10} Φ_a⁺(w)` of a real-priced plan `a ∈ A` at `(s, b)`. -/
noncomputable def realPlanRoundCost {d : ℕ}
    (x : Fin d → ℝ) (a : RealTradePlan d) (s b : Fin d → ℝ) : ℝ :=
  let S := dotProduct x s
  let B := dotProduct x b
  let p := a.price
  if S ≤ p ∧ p ≤ B then
    (2 ^ 10 : ℝ) * tradeQuadPotential a.succ1.mS a.succ1.mB a.succ1.RS a.succ1.RB s b
  else
    max (B - S) 0 + (2 ^ 10 : ℝ) * tradeQuadPotential a.succ0.mS a.succ0.mB a.succ0.RS a.succ0.RB s b

/-- Excess cost `f_a(w) = ℓ_a(w) + 2^{10} Φ_a⁺(w) - 2^{10} Φ_0(w)` of plan `a ∈ A` at `w ∈ K`
(Appendix D.2, Eq. before Claim D.5). -/
noncomputable def realPlanExcessCost {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (a : RealTradePlan d) (w : UnitBallPair d) : ℝ :=
  realPlanRoundCost x a w.seller w.buyer -
    (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer

/-- Exact `EReal`-valued expected excess cost `E_{a ~ Q}[f_a(w)] ∈ (-∞, +∞]` under an arbitrary
probability lottery `Q` on `A` (defined via the nonnegative Lebesgue integral of
`ℓ_a(w) + 2^{10} Φ_a⁺(w)` minus the deterministic current potential `2^{10} Φ_0(w)`, avoiding
any junk-value convention for lotteries with infinite expected successor potential). -/
noncomputable def lotteryExpectedExcessCost {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (Q : MeasureTheory.ProbabilityMeasure (RealTradePlan d))
    (w : UnitBallPair d) : EReal :=
  (∫⁻ a, ENNReal.ofReal (realPlanRoundCost x a w.seller w.buyer)
      ∂(Q : MeasureTheory.Measure (RealTradePlan d))).toEReal -
    (((2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer : ℝ) : EReal)

/-- Bayesian value `V_B = sup_{ρ ∈ P(K)} inf_{a ∈ A} E_ρ[f_a(W)]` (Appendix D.2, Claim D.5). -/
noncomputable def tradeBayesianValue {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : EReal :=
  ⨆ ρ : MeasureTheory.ProbabilityMeasure (UnitBallPair d),
    ⨅ a : RealTradePlan d,
      ((∫ w, realPlanExcessCost mS mB RS RB x a w
          ∂(ρ : MeasureTheory.Measure (UnitBallPair d)) : ℝ) : EReal)

/-- Worst-case lottery value `V_W = inf_Q sup_{w ∈ K} E_{a ~ Q}[f_a(w)]` over all Borel
probability lotteries `Q` on `A` (Appendix D.2, Claim D.5). -/
noncomputable def tradeWorstCaseLotteryValue {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : EReal :=
  ⨅ Q : MeasureTheory.ProbabilityMeasure (RealTradePlan d),
    ⨆ w : UnitBallPair d, lotteryExpectedExcessCost mS mB RS RB x Q w

/-! ## 8. Bilateral Trade Lower Bound (Appendix E, Proposition E.2) -/

/-- One-bit trade indicator `1{xᵀ s ≤ p ∧ q ≤ xᵀ b}`. -/
noncomputable def tradeFeedbackBit {d : ℕ}
    (s b x : Fin d → ℝ) (p q : ℝ) : ℝ :=
  if dotProduct x s ≤ p ∧ q ≤ dotProduct x b then 1 else 0

/-- Single-round bilateral-trade regret `(xᵀ (b - s))_+ (1 - Y)`. -/
noncomputable def tradeRoundLoss {d : ℕ}
    (s b x : Fin d → ℝ) (p q : ℝ) : ℝ :=
  max (dotProduct x b - dotProduct x s) 0 * (1 - tradeFeedbackBit s b x p q)

/-- A possibly randomized per-round budget-balanced (`p_t ≤ q_t`) bilateral-trade broker. -/
structure BudgetBalancedBroker (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  postOffer : Ω → List ((Fin d → ℝ) × ℝ) → (Fin d → ℝ) → ℝ × ℝ
  budget_balanced :
    ∀ (ω : Ω) (hist : List ((Fin d → ℝ) × ℝ)) (x : Fin d → ℝ),
      (postOffer ω hist x).1 ≤ (postOffer ω hist x).2
  measurable_postOffer :
    ∀ (hist : List ((Fin d → ℝ) × ℝ)) (x : Fin d → ℝ),
      Measurable (fun ω => postOffer ω hist x)

/-- Left-fold execution of `T` rounds of contextual bilateral trade from round `0` to `T - 1`. -/
noncomputable def tradeTrajectory {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (broker : BudgetBalancedBroker d Ω) (s b : Fin d → ℝ) (ω : Ω)
    (T : ℕ) (ctxs : Fin T → (Fin d → ℝ)) : ℝ × List ((Fin d → ℝ) × ℝ) :=
  (List.finRange T).foldl
    (fun (acc : ℝ × List ((Fin d → ℝ) × ℝ)) (t : Fin T) =>
      let regSoFar := acc.1
      let hist := acc.2
      let xt := ctxs t
      let offer := broker.postOffer ω hist xt
      let yt := tradeFeedbackBit s b xt offer.1 offer.2
      let ell := tradeRoundLoss s b xt offer.1 offer.2
      (regSoFar + ell, hist ++ [(xt, yt)]))
    (0, [])

/-- Cumulative bilateral-trade regret `Reg_T = ∑_{t=1}^T (x_tᵀ (b - s))_+ (1 - Y_t)`. -/
noncomputable def tradeCumulativeRegret {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (broker : BudgetBalancedBroker d Ω) (s b : Fin d → ℝ)
    (T : ℕ) (ctxs : Fin T → (Fin d → ℝ)) (ω : Ω) : ℝ :=
  (tradeTrajectory broker s b ω T ctxs).1

/-- Seller coordinate vector under the two-interval prior of Proposition E.2:
`s_j = 0` or `2 / (3 √d)`. -/
noncomputable def priorSellerVec {d : ℕ} (choice : Fin d → Bool) : Fin d → ℝ :=
  fun j => if choice j then 2 / (3 * Real.sqrt d) else 0

/-- Buyer coordinate vector under the two-interval prior of Proposition E.2:
`b_j = 1 / (3 √d)` or `1 / √d`. -/
noncomputable def priorBuyerVec {d : ℕ} (choice : Fin d → Bool) : Fin d → ℝ :=
  fun j => if choice j then 1 / Real.sqrt d else 1 / (3 * Real.sqrt d)

end TraceSqrt
