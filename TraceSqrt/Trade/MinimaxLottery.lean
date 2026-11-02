import TraceSqrt.Defs
import TraceSqrt.Potential.PotentialDecrease
import TraceSqrt.Trade.TradeOrInformation
import TraceSqrt.Trade.SionMinimax
import TraceSqrt.Trade.TradeLottery

set_option maxHeartbeats 4000000

/-!
# Claim D.5: Minimax Duality and Regular Near-Optimal Lotteries (`cl:trade-minimax`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Appendix D.2, Claim D.5 `cl:trade-minimax`).

Proves:
1. Finiteness and nonpositivity of the Bayesian value `V_B = sup_ρ inf_a E_ρ[f_a(W)] ≤ 0`,
2. Minimax equality `V_B = V_W = inf_Q sup_{w ∈ K} E_{a ~ Q}[f_a(w)]` over all Borel probability
   lotteries `Q` on `RealTradePlan d` via uniform price-perturbation smoothing and Sion's minimax
   corollary (`cor_sion_affine`, Corollary D.7),
3. Existence for every `η > 0` of a regular near-optimal lottery `Q` (`sup_K E_Q[f_a] < V_W + η`)
   whose price marginal has bounded Lebesgue density with compact support and whose successor
   states lie almost surely in a compact subset of positive-definite block-diagonal states.
-/

namespace TraceSqrt

open MeasureTheory

instance instBorelSpacePDTradeState (d : ℕ) : BorelSpace (PDTradeState d) :=
  Subtype.borelSpace _

instance instBorelSpaceRealTradePlan (d : ℕ) : BorelSpace (RealTradePlan d) :=
  Prod.borelSpace

/-! ## Basic Continuity, Nonnegativity, and Measurability Helpers -/

private lemma continuous_unitBallPair_seller (d : ℕ) :
    Continuous (UnitBallPair.seller (d := d)) :=
  continuous_pi fun i =>
    (PiLp.continuous_apply 2 _ i).comp
      ((WithLp.continuous_fst 2 (EucVec d) (EucVec d)).comp continuous_subtype_val)

private lemma continuous_unitBallPair_buyer (d : ℕ) :
    Continuous (UnitBallPair.buyer (d := d)) :=
  continuous_pi fun i =>
    (PiLp.continuous_apply 2 _ i).comp
      ((WithLp.continuous_snd 2 (EucVec d) (EucVec d)).comp continuous_subtype_val)

private lemma vecL2Norm_eq_eucNorm {d : ℕ} (z : Fin d → ℝ) :
    vecL2Norm z = ‖(WithLp.toLp 2 z : EucVec d)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [vecL2Norm, Real.norm_eq_abs, sq_abs]

private lemma vecL2Norm_unitBallPair_seller {d : ℕ} (w : UnitBallPair d) :
    vecL2Norm w.seller ≤ 1 := by
  rw [vecL2Norm_eq_eucNorm]
  simpa [UnitBallPair.seller] using w.2.1

private lemma vecL2Norm_unitBallPair_buyer {d : ℕ} (w : UnitBallPair d) :
    vecL2Norm w.buyer ≤ 1 := by
  rw [vecL2Norm_eq_eucNorm]
  simpa [UnitBallPair.buyer] using w.2.2

private lemma continuous_pdTradeState_mS (d : ℕ) :
    Continuous (PDTradeState.mS (d := d)) :=
  continuous_fst.comp continuous_subtype_val

private lemma continuous_pdTradeState_mB (d : ℕ) :
    Continuous (PDTradeState.mB (d := d)) :=
  continuous_fst.comp (continuous_snd.comp continuous_subtype_val)

private lemma continuous_pdTradeState_RS (d : ℕ) :
    Continuous (PDTradeState.RS (d := d)) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))))

private lemma continuous_pdTradeState_RB (d : ℕ) :
    Continuous (PDTradeState.RB (d := d)) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))))

private lemma continuous_pdTradeState_RS_inv (d : ℕ) :
    Continuous (fun st : PDTradeState d => st.RS⁻¹) := by
  have h_RS := continuous_pdTradeState_RS d
  have h_ne : ∀ st : PDTradeState d, st.RS.det ≠ 0 := fun st =>
    ((Matrix.isUnit_iff_isUnit_det st.RS).mp st.posDef_RS.isUnit).ne_zero
  have h_eq : (fun st : PDTradeState d => st.RS⁻¹) =
      fun st => (st.RS.det)⁻¹ • st.RS.adjugate := by
    ext st i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h_eq]
  exact (h_RS.matrix_det.inv₀ h_ne).smul h_RS.matrix_adjugate

private lemma continuous_pdTradeState_RB_inv (d : ℕ) :
    Continuous (fun st : PDTradeState d => st.RB⁻¹) := by
  have h_RB := continuous_pdTradeState_RB d
  have h_ne : ∀ st : PDTradeState d, st.RB.det ≠ 0 := fun st =>
    ((Matrix.isUnit_iff_isUnit_det st.RB).mp st.posDef_RB.isUnit).ne_zero
  have h_eq : (fun st : PDTradeState d => st.RB⁻¹) =
      fun st => (st.RB.det)⁻¹ • st.RB.adjugate := by
    ext st i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h_eq]
  exact (h_RB.matrix_det.inv₀ h_ne).smul h_RB.matrix_adjugate

private lemma continuous_agentQuadPotential_of_inv {d : ℕ} {X : Type*} [TopologicalSpace X]
    (m_fn z_fn : X → (Fin d → ℝ))
    (R_fn Rinv_fn : X → Matrix (Fin d) (Fin d) ℝ)
    (hm : Continuous m_fn) (hz : Continuous z_fn)
    (hR : Continuous R_fn) (hRinv : Continuous Rinv_fn)
    (h_inv_eq : ∀ x : X, (R_fn x)⁻¹ = Rinv_fn x) :
    Continuous (fun x : X => agentQuadPotential (m_fn x) (R_fn x) (z_fn x)) := by
  have h_eq : (fun x : X => agentQuadPotential (m_fn x) (R_fn x) (z_fn x)) =
      fun x : X => (∑ i : Fin d, R_fn x i i) +
        ∑ i : Fin d, (z_fn x i - m_fn x i) *
          (∑ j : Fin d, Rinv_fn x i j * (z_fn x j - m_fn x j)) := by
    ext x
    simp [agentQuadPotential, Matrix.trace, dotProduct, Matrix.mulVec, h_inv_eq x]
  rw [h_eq]
  refine (continuous_finset_sum Finset.univ fun i _ =>
      (continuous_apply i).comp ((continuous_apply i).comp hR)).add ?_
  refine continuous_finset_sum Finset.univ fun i _ => ?_
  refine (((continuous_apply i).comp hz).sub ((continuous_apply i).comp hm)).mul ?_
  refine continuous_finset_sum Finset.univ fun j _ => ?_
  exact (((continuous_apply j).comp ((continuous_apply i).comp hRinv))).mul
    (((continuous_apply j).comp hz).sub ((continuous_apply j).comp hm))

private lemma continuous_tradeQuadPotential_pd (d : ℕ) :
    Continuous (fun p : PDTradeState d × UnitBallPair d =>
      tradeQuadPotential p.1.mS p.1.mB p.1.RS p.1.RB p.2.seller p.2.buyer) := by
  have hS := continuous_agentQuadPotential_of_inv
    (fun p : PDTradeState d × UnitBallPair d => p.1.mS)
    (fun p => p.2.seller)
    (fun p => p.1.RS)
    (fun p => p.1.RS⁻¹)
    ((continuous_pdTradeState_mS d).comp continuous_fst)
    ((continuous_unitBallPair_seller d).comp continuous_snd)
    ((continuous_pdTradeState_RS d).comp continuous_fst)
    ((continuous_pdTradeState_RS_inv d).comp continuous_fst)
    (fun _ => rfl)
  have hB := continuous_agentQuadPotential_of_inv
    (fun p : PDTradeState d × UnitBallPair d => p.1.mB)
    (fun p => p.2.buyer)
    (fun p => p.1.RB)
    (fun p => p.1.RB⁻¹)
    ((continuous_pdTradeState_mB d).comp continuous_fst)
    ((continuous_unitBallPair_buyer d).comp continuous_snd)
    ((continuous_pdTradeState_RB d).comp continuous_fst)
    ((continuous_pdTradeState_RB_inv d).comp continuous_fst)
    (fun _ => rfl)
  exact hS.add hB

private lemma continuous_tradeQuadPotential_fixed {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun w : UnitBallPair d =>
      tradeQuadPotential mS mB RS RB w.seller w.buyer) := by
  have hS := continuous_agentQuadPotential_of_inv
    (fun _ : UnitBallPair d => mS) (UnitBallPair.seller)
    (fun _ => RS) (fun _ => RS⁻¹)
    continuous_const (continuous_unitBallPair_seller d)
    continuous_const continuous_const (fun _ => rfl)
  have hB := continuous_agentQuadPotential_of_inv
    (fun _ : UnitBallPair d => mB) (UnitBallPair.buyer)
    (fun _ => RB) (fun _ => RB⁻¹)
    continuous_const (continuous_unitBallPair_buyer d)
    continuous_const continuous_const (fun _ => rfl)
  exact hS.add hB

private lemma agentQuadPotential_nonneg {d : ℕ}
    {m z : Fin d → ℝ} {R : Matrix (Fin d) (Fin d) ℝ} (hR : R.PosDef) :
    0 ≤ agentQuadPotential m R z := by
  have h1 : 0 ≤ Matrix.trace R := hR.posSemidef.trace_nonneg
  have h2 : 0 ≤ dotProduct (z - m) (R⁻¹.mulVec (z - m)) := by
    simpa using hR.inv.posSemidef.dotProduct_mulVec_nonneg (z - m)
  dsimp [agentQuadPotential]
  linarith

private lemma tradeQuadPotential_nonneg {d : ℕ}
    {mS mB s b : Fin d → ℝ} {RS RB : Matrix (Fin d) (Fin d) ℝ}
    (hRS : RS.PosDef) (hRB : RB.PosDef) :
    0 ≤ tradeQuadPotential mS mB RS RB s b :=
  add_nonneg (agentQuadPotential_nonneg hRS) (agentQuadPotential_nonneg hRB)

private lemma realPlanRoundCost_nonneg {d : ℕ}
    (x : Fin d → ℝ) (a : RealTradePlan d) (s b : Fin d → ℝ) :
    0 ≤ realPlanRoundCost x a s b := by
  unfold realPlanRoundCost
  dsimp only
  split_ifs
  · exact mul_nonneg (by positivity)
      (tradeQuadPotential_nonneg a.succ1.posDef_RS a.succ1.posDef_RB)
  · exact add_nonneg (le_max_right _ _)
      (mul_nonneg (by positivity)
        (tradeQuadPotential_nonneg a.succ0.posDef_RS a.succ0.posDef_RB))

private lemma continuous_dotProduct_seller {d : ℕ} (x : Fin d → ℝ) :
    Continuous (fun w : UnitBallPair d => dotProduct x w.seller) := by
  simp only [dotProduct]
  exact continuous_finset_sum Finset.univ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp (continuous_unitBallPair_seller d))

private lemma continuous_dotProduct_buyer {d : ℕ} (x : Fin d → ℝ) :
    Continuous (fun w : UnitBallPair d => dotProduct x w.buyer) := by
  simp only [dotProduct]
  exact continuous_finset_sum Finset.univ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp (continuous_unitBallPair_buyer d))

private lemma measurable_realPlanRoundCost_joint {d : ℕ} (x : Fin d → ℝ) :
    Measurable (fun aw : RealTradePlan d × UnitBallPair d =>
      realPlanRoundCost x aw.1 aw.2.seller aw.2.buyer) := by
  have hS : Continuous (fun aw : RealTradePlan d × UnitBallPair d => dotProduct x aw.2.seller) :=
    (continuous_dotProduct_seller x).comp continuous_snd
  have hB : Continuous (fun aw : RealTradePlan d × UnitBallPair d => dotProduct x aw.2.buyer) :=
    (continuous_dotProduct_buyer x).comp continuous_snd
  have hp : Continuous (fun aw : RealTradePlan d × UnitBallPair d => aw.1.price) :=
    continuous_fst.comp continuous_fst
  have hE : MeasurableSet {aw : RealTradePlan d × UnitBallPair d |
      dotProduct x aw.2.seller ≤ aw.1.price ∧ aw.1.price ≤ dotProduct x aw.2.buyer} :=
    ((isClosed_le hS hp).inter (isClosed_le hp hB)).measurableSet
  have h_br1 : Continuous (fun aw : RealTradePlan d × UnitBallPair d =>
      (2 ^ 10 : ℝ) * tradeQuadPotential aw.1.succ1.mS aw.1.succ1.mB
        aw.1.succ1.RS aw.1.succ1.RB aw.2.seller aw.2.buyer) :=
    continuous_const.mul ((continuous_tradeQuadPotential_pd d).comp
      ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd))
  have h_br0 : Continuous (fun aw : RealTradePlan d × UnitBallPair d =>
      max (dotProduct x aw.2.buyer - dotProduct x aw.2.seller) 0 +
        (2 ^ 10 : ℝ) * tradeQuadPotential aw.1.succ0.mS aw.1.succ0.mB
          aw.1.succ0.RS aw.1.succ0.RB aw.2.seller aw.2.buyer) :=
    ((hB.sub hS).max continuous_const).add
      (continuous_const.mul ((continuous_tradeQuadPotential_pd d).comp
        ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)))
  exact Measurable.ite hE h_br1.measurable h_br0.measurable

private lemma integrable_realPlanRoundCost {d : ℕ}
    (x : Fin d → ℝ) (a : RealTradePlan d)
    (μ : Measure (UnitBallPair d)) [IsProbabilityMeasure μ] :
    Integrable (fun w : UnitBallPair d => realPlanRoundCost x a w.seller w.buyer) μ := by
  have h_meas : Measurable (fun w : UnitBallPair d => realPlanRoundCost x a w.seller w.buyer) :=
    (measurable_realPlanRoundCost_joint x).comp (measurable_const.prodMk measurable_id)
  let br1 : C(UnitBallPair d, ℝ) :=
    ⟨fun w => (2 ^ 10 : ℝ) *
        tradeQuadPotential a.succ1.mS a.succ1.mB a.succ1.RS a.succ1.RB w.seller w.buyer,
     continuous_const.mul
       (continuous_tradeQuadPotential_fixed a.succ1.mS a.succ1.mB a.succ1.RS a.succ1.RB)⟩
  let br0 : C(UnitBallPair d, ℝ) :=
    ⟨fun w => max (dotProduct x w.buyer - dotProduct x w.seller) 0 +
        (2 ^ 10 : ℝ) *
          tradeQuadPotential a.succ0.mS a.succ0.mB a.succ0.RS a.succ0.RB w.seller w.buyer,
     (((continuous_dotProduct_buyer x).sub (continuous_dotProduct_seller x)).max continuous_const).add
       (continuous_const.mul
         (continuous_tradeQuadPotential_fixed a.succ0.mS a.succ0.mB a.succ0.RS a.succ0.RB))⟩
  refine Integrable.of_bound h_meas.aestronglyMeasurable (max ‖br1‖ ‖br0‖)
    (Filter.Eventually.of_forall fun w => ?_)
  unfold realPlanRoundCost
  dsimp only
  split_ifs
  · exact (ContinuousMap.norm_coe_le_norm br1 w).trans (le_max_left _ _)
  · exact (ContinuousMap.norm_coe_le_norm br0 w).trans (le_max_right _ _)

private lemma integrable_realPlanExcessCost {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (a : RealTradePlan d)
    (μ : Measure (UnitBallPair d)) [IsProbabilityMeasure μ] :
    Integrable (realPlanExcessCost mS mB RS RB x a) μ := by
  have h0_cont : Continuous (fun w : UnitBallPair d =>
      (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer) :=
    continuous_const.mul (continuous_tradeQuadPotential_fixed mS mB RS RB)
  have h0_int : Integrable (fun w : UnitBallPair d =>
      (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer) μ :=
    h0_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (integrable_realPlanRoundCost x a μ).sub h0_int

/-! ## Weak Duality and Lower Finiteness (`V_B ≠ ⊥` and `V_B ≤ V_W`) -/

private lemma lem_weak_duality_and_ne_bot {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (hRS : RS.PosDef) (hRB : RB.PosDef) (x : Fin d → ℝ) :
    tradeBayesianValue mS mB RS RB x ≠ ⊥ ∧
    tradeBayesianValue mS mB RS RB x ≤ tradeWorstCaseLotteryValue mS mB RS RB x := by
  let Φ₀ : C(UnitBallPair d, ℝ) :=
    ⟨fun w => (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer,
     continuous_const.mul (continuous_tradeQuadPotential_fixed mS mB RS RB)⟩
  have hΦ₀_nn : ∀ w : UnitBallPair d, 0 ≤ Φ₀ w := fun w =>
    mul_nonneg (by positivity) (tradeQuadPotential_nonneg hRS hRB)
  have hΦ₀_int : ∀ μ : Measure (UnitBallPair d), IsProbabilityMeasure μ → Integrable Φ₀ μ := by
    intro μ _
    exact Φ₀.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let st₀ : PDTradeState d := PDTradeState.mk' mS mB RS RB hRS hRB
  let a₀ : RealTradePlan d := (0, st₀, st₀)
  let w₀ : UnitBallPair d := Classical.arbitrary (UnitBallPair d)

  refine ⟨?_, ?_⟩
  · -- V_B ≥ -Φ₀(w₀) > ⊥ via Dirac prior at w₀
    let ρ₀ : ProbabilityMeasure (UnitBallPair d) := ⟨Measure.dirac w₀, inferInstance⟩
    have h_lb : ((-Φ₀ w₀ : ℝ) : EReal) ≤
        ⨅ a : RealTradePlan d,
          ((∫ w, realPlanExcessCost mS mB RS RB x a w ∂(ρ₀ : Measure (UnitBallPair d)) : ℝ) : EReal) := by
      refine le_iInf fun a => ?_
      have h_dir : (∫ w, realPlanExcessCost mS mB RS RB x a w ∂(Measure.dirac w₀)) =
          realPlanExcessCost mS mB RS RB x a w₀ := integral_dirac _ w₀
      change ((-Φ₀ w₀ : ℝ) : EReal) ≤
        ((∫ w, realPlanExcessCost mS mB RS RB x a w ∂(Measure.dirac w₀) : ℝ) : EReal)
      rw [h_dir, EReal.coe_le_coe_iff]
      have h_nn := realPlanRoundCost_nonneg x a w₀.seller w₀.buyer
      change -Φ₀ w₀ ≤ realPlanRoundCost x a w₀.seller w₀.buyer - Φ₀ w₀
      linarith
    have h_vb : ((-Φ₀ w₀ : ℝ) : EReal) ≤ tradeBayesianValue mS mB RS RB x :=
      h_lb.trans (le_iSup (fun ρ : ProbabilityMeasure (UnitBallPair d) =>
        ⨅ a : RealTradePlan d,
          ((∫ w, realPlanExcessCost mS mB RS RB x a w ∂(ρ : Measure (UnitBallPair d)) : ℝ) : EReal)) ρ₀)
    intro h_bot
    rw [h_bot] at h_vb
    exact not_lt_of_ge h_vb (EReal.bot_lt_coe (-Φ₀ w₀))
  · -- Weak duality V_B ≤ V_W via Tonelli on realPlanRoundCost ≥ 0
    refine iSup_le fun ρ => le_iInf fun Q => ?_
    let μ : Measure (UnitBallPair d) := (ρ : Measure (UnitBallPair d))
    let ν : Measure (RealTradePlan d) := (Q : Measure (RealTradePlan d))
    set L_ρ : EReal := ⨅ a : RealTradePlan d,
      ((∫ w, realPlanExcessCost mS mB RS RB x a w ∂μ : ℝ) : EReal)
    set S_Q : EReal := ⨆ w : UnitBallPair d, lotteryExpectedExcessCost mS mB RS RB x Q w
    by_cases hL_bot : L_ρ = ⊥
    · rw [hL_bot]; exact bot_le
    by_cases hS_top : S_Q = ⊤
    · rw [hS_top]; exact le_top
    have hL_top : L_ρ ≠ ⊤ := by
      intro h_top
      have h_le : L_ρ ≤ ((∫ w, realPlanExcessCost mS mB RS RB x a₀ w ∂μ : ℝ) : EReal) :=
        iInf_le _ a₀
      rw [h_top] at h_le
      exact not_top_lt (lt_of_le_of_lt h_le (EReal.coe_lt_top _))
    have hS_bot : S_Q ≠ ⊥ := by
      intro h_bot
      have h_ge : ((-Φ₀ w₀ : ℝ) : EReal) ≤ lotteryExpectedExcessCost mS mB RS RB x Q w₀ := by
        unfold lotteryExpectedExcessCost
        change ((-Φ₀ w₀ : ℝ) : EReal) ≤ _ - (Φ₀ w₀ : EReal)
        rw [EReal.coe_neg]
        simpa only [sub_eq_add_neg, zero_add] using
          add_le_add_left (EReal.coe_ennreal_nonneg _) (-(Φ₀ w₀ : EReal))
      have h_le : lotteryExpectedExcessCost mS mB RS RB x Q w₀ ≤ S_Q := le_iSup _ w₀
      have h_comb := h_ge.trans h_le
      rw [h_bot] at h_comb
      exact not_lt_of_ge h_comb (EReal.bot_lt_coe (-Φ₀ w₀))
    set l_ρ : ℝ := L_ρ.toReal
    set s_Q : ℝ := S_Q.toReal
    have hl_coe : (l_ρ : EReal) = L_ρ := EReal.coe_toReal hL_top hL_bot
    have hs_coe : (s_Q : EReal) = S_Q := EReal.coe_toReal hS_top hS_bot
    set C_ρ : ℝ := ∫ w, Φ₀ w ∂μ
    have hC_nn : 0 ≤ C_ρ := integral_nonneg hΦ₀_nn
    let g_enn : RealTradePlan d → UnitBallPair d → ENNReal :=
      fun a w => ENNReal.ofReal (realPlanRoundCost x a w.seller w.buyer)
    have hg_meas : Measurable (Function.uncurry g_enn) :=
      ENNReal.measurable_ofReal.comp (measurable_realPlanRoundCost_joint x)
    have h_tonelli :
        (∫⁻ a, (∫⁻ w, g_enn a w ∂μ) ∂ν) = ∫⁻ w, (∫⁻ a, g_enn a w ∂ν) ∂μ :=
      lintegral_lintegral_swap hg_meas.aemeasurable

    have h_lhs_le : ∀ a : RealTradePlan d,
        ENNReal.ofReal (l_ρ + C_ρ) ≤ ∫⁻ w, g_enn a w ∂μ := by
      intro a
      have ha_int := integrable_realPlanRoundCost x a μ
      have h0_int := hΦ₀_int μ inferInstance
      have h_split : (∫ w, realPlanExcessCost mS mB RS RB x a w ∂μ) =
          (∫ w, realPlanRoundCost x a w.seller w.buyer ∂μ) - C_ρ := by
        change (∫ w, (realPlanRoundCost x a w.seller w.buyer - Φ₀ w) ∂μ) = _
        exact integral_sub ha_int h0_int
      have h_le_er : (l_ρ : EReal) ≤
          ((∫ w, realPlanExcessCost mS mB RS RB x a w ∂μ : ℝ) : EReal) := by
        rw [hl_coe]; exact iInf_le _ a
      have h_le_r : l_ρ ≤ (∫ w, realPlanRoundCost x a w.seller w.buyer ∂μ) - C_ρ := by
        rw [← h_split]; exact EReal.coe_le_coe_iff.mp h_le_er
      have h_ofR : ENNReal.ofReal (∫ w, realPlanRoundCost x a w.seller w.buyer ∂μ) =
          ∫⁻ w, g_enn a w ∂μ :=
        ofReal_integral_eq_lintegral_ofReal ha_int
          (Filter.Eventually.of_forall fun w => realPlanRoundCost_nonneg x a w.seller w.buyer)
      rw [← h_ofR]
      exact ENNReal.ofReal_le_ofReal (by linarith)

    have h_int_lhs : ENNReal.ofReal (l_ρ + C_ρ) ≤ ∫⁻ a, (∫⁻ w, g_enn a w ∂μ) ∂ν := by
      calc ENNReal.ofReal (l_ρ + C_ρ)
          = ∫⁻ _a, ENNReal.ofReal (l_ρ + C_ρ) ∂ν := by
              rw [lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ a, (∫⁻ w, g_enn a w ∂μ) ∂ν := lintegral_mono h_lhs_le

    have h_rhs_pt : ∀ w : UnitBallPair d,
        0 ≤ s_Q + Φ₀ w ∧ (∫⁻ a, g_enn a w ∂ν) ≤ ENNReal.ofReal (s_Q + Φ₀ w) := by
      intro w
      set J : ENNReal := ∫⁻ a, g_enn a w ∂ν
      have h_le_er : J.toEReal - (Φ₀ w : EReal) ≤ (s_Q : EReal) := by
        rw [hs_coe]
        exact le_iSup (fun w' => lotteryExpectedExcessCost mS mB RS RB x Q w') w
      have hJ_ne_top : J ≠ ⊤ := by
        intro htop
        rw [htop, EReal.coe_ennreal_top, EReal.top_sub_coe] at h_le_er
        exact not_top_lt (lt_of_le_of_lt h_le_er (EReal.coe_lt_top s_Q))
      rw [← ENNReal.ofReal_toReal hJ_ne_top, EReal.coe_ennreal_ofReal,
          max_eq_left ENNReal.toReal_nonneg, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h_le_er
      have h_nn : 0 ≤ s_Q + Φ₀ w := by linarith [ENNReal.toReal_nonneg (a := J)]
      refine ⟨h_nn, ?_⟩
      rw [← ENNReal.ofReal_toReal hJ_ne_top]
      exact ENNReal.ofReal_le_ofReal (by linarith)

    have h_sΦ_int : Integrable (fun w : UnitBallPair d => s_Q + Φ₀ w) μ :=
      (integrable_const s_Q).add (hΦ₀_int μ inferInstance)
    have h_sΦ_int_val : (∫ w, (s_Q + Φ₀ w) ∂μ) = s_Q + C_ρ := by
      rw [integral_add (integrable_const s_Q) (hΦ₀_int μ inferInstance),
          integral_const, probReal_univ, one_smul]
    have h_sC_nn : 0 ≤ s_Q + C_ρ := by
      rw [← h_sΦ_int_val]
      exact integral_nonneg fun w => (h_rhs_pt w).1
    have h_int_rhs : (∫⁻ w, (∫⁻ a, g_enn a w ∂ν) ∂μ) ≤ ENNReal.ofReal (s_Q + C_ρ) := by
      calc (∫⁻ w, (∫⁻ a, g_enn a w ∂ν) ∂μ)
          ≤ ∫⁻ w, ENNReal.ofReal (s_Q + Φ₀ w) ∂μ :=
              lintegral_mono fun w => (h_rhs_pt w).2
        _ = ENNReal.ofReal (∫ w, (s_Q + Φ₀ w) ∂μ) :=
              (ofReal_integral_eq_lintegral_ofReal h_sΦ_int
                (Filter.Eventually.of_forall fun w => (h_rhs_pt w).1)).symm
        _ = ENNReal.ofReal (s_Q + C_ρ) := by rw [h_sΦ_int_val]

    have h_ofR_le : ENNReal.ofReal (l_ρ + C_ρ) ≤ ENNReal.ofReal (s_Q + C_ρ) := by
      calc ENNReal.ofReal (l_ρ + C_ρ)
          ≤ ∫⁻ a, (∫⁻ w, g_enn a w ∂μ) ∂ν := h_int_lhs
        _ = ∫⁻ w, (∫⁻ a, g_enn a w ∂ν) ∂μ := h_tonelli
        _ ≤ ENNReal.ofReal (s_Q + C_ρ) := h_int_rhs
    have h_r_le : l_ρ ≤ s_Q := by
      linarith [(ENNReal.ofReal_le_ofReal_iff h_sC_nn).mp h_ofR_le]
    rw [← hl_coe, ← hs_coe, EReal.coe_le_coe_iff]
    exact h_r_le

/-! ## Bayesian Upper Bound (`V_B ≤ 0`) -/

private lemma lem_bayesian_value_nonpos {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (hRS : RS.PosDef) (hRB : RB.PosDef)
    (x : Fin d → ℝ) (hx : vecL2Norm x ≤ 1) :
    tradeBayesianValue mS mB RS RB x ≤ 0 := by
  refine iSup_le fun ρ => ?_
  let μ : Measure (UnitBallPair d) := (ρ : Measure (UnitBallPair d))
  let st₀ : PDTradeState d := PDTradeState.mk' mS mB RS RB hRS hRB
  let WS : UnitBallPair d → (Fin d → ℝ) := UnitBallPair.seller
  let WB : UnitBallPair d → (Fin d → ℝ) := UnitBallPair.buyer

  have hWS_lp : ∀ ν : Measure (UnitBallPair d), IsProbabilityMeasure ν →
      ∀ i : Fin d, MemLp (fun w => WS w i) 2 ν := by
    intro ν _ i
    have hc : Continuous (fun w : UnitBallPair d => WS w i) :=
      (continuous_apply i).comp (continuous_unitBallPair_seller d)
    let f_c : C(UnitBallPair d, ℝ) := ⟨fun w => WS w i, hc⟩
    exact MemLp.of_bound hc.aestronglyMeasurable ‖f_c‖
      (Filter.Eventually.of_forall fun w => ContinuousMap.norm_coe_le_norm f_c w)
  have hWB_lp : ∀ ν : Measure (UnitBallPair d), IsProbabilityMeasure ν →
      ∀ i : Fin d, MemLp (fun w => WB w i) 2 ν := by
    intro ν _ i
    have hc : Continuous (fun w : UnitBallPair d => WB w i) :=
      (continuous_apply i).comp (continuous_unitBallPair_buyer d)
    let f_c : C(UnitBallPair d, ℝ) := ⟨fun w => WB w i, hc⟩
    exact MemLp.of_bound hc.aestronglyMeasurable ‖f_c‖
      (Filter.Eventually.of_forall fun w => ContinuousMap.norm_coe_le_norm f_c w)

  let S_rv : UnitBallPair d → ℝ := fun w => dotProduct x (WS w)
  let B_rv : UnitBallPair d → ℝ := fun w => dotProduct x (WB w)
  have hS_lp : MemLp S_rv 2 μ := by
    simpa only [S_rv, dotProduct] using
      memLp_finset_sum Finset.univ fun i _ => (hWS_lp μ inferInstance i).const_mul (x i)
  have hB_lp : MemLp B_rv 2 μ := by
    simpa only [B_rv, dotProduct] using
      memLp_finset_sum Finset.univ fun i _ => (hWB_lp μ inferInstance i).const_mul (x i)

  obtain ⟨p_star, hp_toi⟩ := lem_toi μ S_rv B_rv hS_lp hB_lp
  let E : Set (UnitBallPair d) := tradeEvent S_rv B_rv p_star
  have hE_meas : MeasurableSet E :=
    ((isClosed_le (continuous_dotProduct_seller x) continuous_const).inter
      (isClosed_le continuous_const (continuous_dotProduct_buyer x))).measurableSet

  have h_branch_opt : ∀ (F : Set (UnitBallPair d)), MeasurableSet F → ∀ η' : ℝ, 0 < η' →
      ∃ st : PDTradeState d,
        (∫ w in F, tradeQuadPotential st.mS st.mB st.RS st.RB (WS w) (WB w) ∂μ) <
          2 * μ.real F *
            (psdTraceSqrt (rvCovMat WS (ProbabilityTheory.cond μ F)) +
             psdTraceSqrt (rvCovMat WB (ProbabilityTheory.cond μ F))) + η' := by
    intro F _ η' hη'
    by_cases hF0 : μ F = 0
    · refine ⟨st₀, ?_⟩
      have h_rest : μ.restrict F = 0 := Measure.restrict_eq_zero.mpr hF0
      have h_real0 : μ.real F = 0 := by simp [measureReal_def, hF0]
      rw [h_rest, integral_zero_measure, h_real0]
      linarith
    · let ν : Measure (UnitBallPair d) := ProbabilityTheory.cond μ F
      haveI : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hF0
      have hpF_pos : 0 < μ.real F := ENNReal.toReal_pos hF0 (measure_ne_top μ F)
      have hpF_le1 : μ.real F ≤ 1 := by
        rw [measureReal_def, ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top
          ((measure_mono (Set.subset_univ F)).trans_eq measure_univ)
      have h_glbS := (quad_potential_variational ν WS (hWS_lp ν inferInstance)).2.1
      have h_glbB := (quad_potential_variational ν WB (hWB_lp ν inferInstance)).2.1
      have h_exS : ∃ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef ∧
          (∫ w, quadPotential m R (WS w) ∂ν) <
            2 * psdTraceSqrt (rvCovMat WS ν) + η' / 2 := by
        by_contra h_all
        push_neg at h_all
        have h_lb : 2 * psdTraceSqrt (rvCovMat WS ν) + η' / 2 ∈
            lowerBounds {v : ℝ | ∃ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ),
              R.PosDef ∧ v = ∫ w, quadPotential m R (WS w) ∂ν} := by
          rintro v ⟨m, R, hR, rfl⟩
          exact h_all m R hR
        linarith [h_glbS.2 h_lb]
      have h_exB : ∃ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef ∧
          (∫ w, quadPotential m R (WB w) ∂ν) <
            2 * psdTraceSqrt (rvCovMat WB ν) + η' / 2 := by
        by_contra h_all
        push_neg at h_all
        have h_lb : 2 * psdTraceSqrt (rvCovMat WB ν) + η' / 2 ∈
            lowerBounds {v : ℝ | ∃ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ),
              R.PosDef ∧ v = ∫ w, quadPotential m R (WB w) ∂ν} := by
          rintro v ⟨m, R, hR, rfl⟩
          exact h_all m R hR
        linarith [h_glbB.2 h_lb]
      rcases h_exS with ⟨mS_F, RS_F, hRS_F, hS_lt⟩
      rcases h_exB with ⟨mB_F, RB_F, hRB_F, hB_lt⟩
      let st_F : PDTradeState d := PDTradeState.mk' mS_F mB_F RS_F RB_F hRS_F hRB_F
      refine ⟨st_F, ?_⟩
      have h_intS_ν := ((quad_potential_variational ν WS (hWS_lp ν inferInstance)).1 mS_F RS_F hRS_F).1
      have h_intB_ν := ((quad_potential_variational ν WB (hWB_lp ν inferInstance)).1 mB_F RB_F hRB_F).1
      have h_cond_eq : (∫ w, tradeQuadPotential st_F.mS st_F.mB st_F.RS st_F.RB (WS w) (WB w) ∂ν) =
          (μ.real F)⁻¹ *
            ∫ w in F, tradeQuadPotential st_F.mS st_F.mB st_F.RS st_F.RB (WS w) (WB w) ∂μ := by
        change (∫ w, tradeQuadPotential st_F.mS st_F.mB st_F.RS st_F.RB (WS w) (WB w)
          ∂((μ F)⁻¹ • μ.restrict F)) = _
        rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv, ← measureReal_def]
      have h_sum_ν : (∫ w, tradeQuadPotential st_F.mS st_F.mB st_F.RS st_F.RB (WS w) (WB w) ∂ν) =
          (∫ w, quadPotential mS_F RS_F (WS w) ∂ν) +
          (∫ w, quadPotential mB_F RB_F (WB w) ∂ν) := by
        change (∫ w, (quadPotential mS_F RS_F (WS w) + quadPotential mB_F RB_F (WB w)) ∂ν) = _
        exact integral_add h_intS_ν h_intB_ν
      have h_mul := mul_lt_mul_of_pos_left (by linarith [h_sum_ν, hS_lt, hB_lt] :
          (∫ w, tradeQuadPotential st_F.mS st_F.mB st_F.RS st_F.RB (WS w) (WB w) ∂ν) <
            2 * (psdTraceSqrt (rvCovMat WS ν) + psdTraceSqrt (rvCovMat WB ν)) + η') hpF_pos
      rw [h_cond_eq] at h_mul
      have h_canc : μ.real F *
          ((μ.real F)⁻¹ *
            ∫ w in F, tradeQuadPotential st_F.mS st_F.mB st_F.RS st_F.RB (WS w) (WB w) ∂μ) =
          ∫ w in F, tradeQuadPotential st_F.mS st_F.mB st_F.RS st_F.RB (WS w) (WB w) ∂μ := by
        field_simp [hpF_pos.ne']
      rw [h_canc] at h_mul
      nlinarith

  -- Show ⨅ a, (∫ realPlanExcessCost ... a ∂μ : EReal) ≤ 0 by ruling out any positive lower bound
  by_contra h_not_le
  have h_gt : (0 : EReal) <
      ⨅ a : RealTradePlan d, ((∫ w, realPlanExcessCost mS mB RS RB x a w ∂μ : ℝ) : EReal) :=
    lt_of_not_ge h_not_le
  set L_ρ : EReal :=
    ⨅ a : RealTradePlan d, ((∫ w, realPlanExcessCost mS mB RS RB x a w ∂μ : ℝ) : EReal)
  have hL_ne_top : L_ρ ≠ ⊤ := by
    intro htop
    have h_le : L_ρ ≤ ((∫ w, realPlanExcessCost mS mB RS RB x (0, st₀, st₀) w ∂μ : ℝ) : EReal) :=
      iInf_le _ (0, st₀, st₀)
    rw [htop] at h_le
    exact not_top_lt (lt_of_le_of_lt h_le (EReal.coe_lt_top _))
  have hL_ne_bot : L_ρ ≠ ⊥ := by
    intro hbot; rw [hbot] at h_gt; exact not_lt_bot h_gt
  set δ : ℝ := L_ρ.toReal
  have hδ_coe : (δ : EReal) = L_ρ := EReal.coe_toReal hL_ne_top hL_ne_bot
  have hδ_pos : 0 < δ := by
    rw [← hδ_coe] at h_gt
    exact EReal.coe_pos.mp h_gt

  set η' : ℝ := δ / (2 ^ 11 : ℝ)
  have hη'_pos : 0 < η' := by dsimp [η']; positivity
  obtain ⟨st1, h_st1⟩ := h_branch_opt E hE_meas η' hη'_pos
  obtain ⟨st0, h_st0⟩ := h_branch_opt Eᶜ hE_meas.compl η' hη'_pos
  let a_opt : RealTradePlan d := (p_star, st0, st1)

  have h_sdS := (lem_directional_sd_decrease_binary μ WS (hWS_lp μ inferInstance)
    E hE_meas.nullMeasurableSet x hx).2.2
  have h_sdB := (lem_directional_sd_decrease_binary μ WB (hWB_lp μ inferInstance)
    E hE_meas.nullMeasurableSet x hx).2.2
  have h_varS := (quad_potential_variational μ WS (hWS_lp μ inferInstance)).1 mS RS hRS
  have h_varB := (quad_potential_variational μ WB (hWB_lp μ inferInstance)).1 mB RB hRB

  have h_loss_int : Integrable (fun w : UnitBallPair d =>
      max (B_rv w - S_rv w) 0 * (if S_rv w ≤ p_star ∧ p_star ≤ B_rv w then 0 else 1)) μ := by
    have h_m : Measurable (fun w : UnitBallPair d =>
        max (B_rv w - S_rv w) 0 * (if S_rv w ≤ p_star ∧ p_star ≤ B_rv w then 0 else 1)) := by
      refine (((continuous_dotProduct_buyer x).sub (continuous_dotProduct_seller x)).max
        continuous_const).measurable.mul ?_
      exact Measurable.ite hE_meas measurable_const measurable_const
    let g_b : C(UnitBallPair d, ℝ) :=
      ⟨fun w => max (B_rv w - S_rv w) 0,
       ((continuous_dotProduct_buyer x).sub (continuous_dotProduct_seller x)).max continuous_const⟩
    refine Integrable.of_bound h_m.aestronglyMeasurable ‖g_b‖ (Filter.Eventually.of_forall fun w => ?_)
    by_cases h_if : S_rv w ≤ p_star ∧ p_star ≤ B_rv w
    · rw [if_pos h_if, mul_zero, norm_zero]
      exact norm_nonneg g_b
    · rw [if_neg h_if, mul_one]
      exact ContinuousMap.norm_coe_le_norm g_b w

  have h_pot1_cont : Continuous (fun w : UnitBallPair d =>
      (2 ^ 10 : ℝ) * tradeQuadPotential st1.mS st1.mB st1.RS st1.RB (WS w) (WB w)) :=
    continuous_const.mul (continuous_tradeQuadPotential_fixed st1.mS st1.mB st1.RS st1.RB)
  have h_pot0_cont : Continuous (fun w : UnitBallPair d =>
      (2 ^ 10 : ℝ) * tradeQuadPotential st0.mS st0.mB st0.RS st0.RB (WS w) (WB w)) :=
    continuous_const.mul (continuous_tradeQuadPotential_fixed st0.mS st0.mB st0.RS st0.RB)
  have h_ind1_int : Integrable (E.indicator fun w : UnitBallPair d =>
      (2 ^ 10 : ℝ) * tradeQuadPotential st1.mS st1.mB st1.RS st1.RB (WS w) (WB w)) μ :=
    (h_pot1_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).indicator hE_meas
  have h_ind0_int : Integrable (Eᶜ.indicator fun w : UnitBallPair d =>
      (2 ^ 10 : ℝ) * tradeQuadPotential st0.mS st0.mB st0.RS st0.RB (WS w) (WB w)) μ :=
    (h_pot0_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).indicator hE_meas.compl

  have h_round_pt : (fun w : UnitBallPair d => realPlanRoundCost x a_opt (WS w) (WB w)) =
      fun w =>
        (max (B_rv w - S_rv w) 0 * (if S_rv w ≤ p_star ∧ p_star ≤ B_rv w then 0 else 1) +
         E.indicator (fun w' =>
           (2 ^ 10 : ℝ) * tradeQuadPotential st1.mS st1.mB st1.RS st1.RB (WS w') (WB w')) w) +
        Eᶜ.indicator (fun w' =>
          (2 ^ 10 : ℝ) * tradeQuadPotential st0.mS st0.mB st0.RS st0.RB (WS w') (WB w')) w := by
    ext w
    unfold realPlanRoundCost
    dsimp only [a_opt, RealTradePlan.price, RealTradePlan.succ0, RealTradePlan.succ1, S_rv, B_rv, E, tradeEvent]
    by_cases hw : dotProduct x (WS w) ≤ p_star ∧ p_star ≤ dotProduct x (WB w)
    · have hmem : w ∈ {w' : UnitBallPair d | dotProduct x (WS w') ≤ p_star ∧ p_star ≤ dotProduct x (WB w')} := hw
      have hnmem : w ∉ ({w' : UnitBallPair d | dotProduct x (WS w') ≤ p_star ∧ p_star ≤ dotProduct x (WB w')})ᶜ :=
        fun hc => hc hmem
      rw [if_pos hw, if_pos hw, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnmem]
      ring
    · have hnmem : w ∉ {w' : UnitBallPair d | dotProduct x (WS w') ≤ p_star ∧ p_star ≤ dotProduct x (WB w')} := hw
      have hmem : w ∈ ({w' : UnitBallPair d | dotProduct x (WS w') ≤ p_star ∧ p_star ≤ dotProduct x (WB w')})ᶜ := hw
      rw [if_neg hw, if_neg hw, Set.indicator_of_notMem hnmem, Set.indicator_of_mem hmem]
      ring

  have h_round_int_eq : (∫ w, realPlanRoundCost x a_opt (WS w) (WB w) ∂μ) =
      expectedLostGain S_rv B_rv μ p_star +
      (2 ^ 10 : ℝ) *
        ((∫ w in E, tradeQuadPotential st1.mS st1.mB st1.RS st1.RB (WS w) (WB w) ∂μ) +
         (∫ w in Eᶜ, tradeQuadPotential st0.mS st0.mB st0.RS st0.RB (WS w) (WB w) ∂μ)) := by
    have h_sum12_int : Integrable (fun w : UnitBallPair d =>
        max (B_rv w - S_rv w) 0 * (if S_rv w ≤ p_star ∧ p_star ≤ B_rv w then 0 else 1) +
        E.indicator (fun w' =>
          (2 ^ 10 : ℝ) * tradeQuadPotential st1.mS st1.mB st1.RS st1.RB (WS w') (WB w')) w) μ :=
      h_loss_int.add h_ind1_int
    rw [h_round_pt, integral_add h_sum12_int h_ind0_int,
        integral_add h_loss_int h_ind1_int,
        integral_indicator hE_meas, integral_indicator hE_meas.compl,
        integral_const_mul, integral_const_mul]
    unfold expectedLostGain
    ring

  have h_init_int_eq :
      (∫ w, (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB (WS w) (WB w) ∂μ) =
        (2 ^ 10 : ℝ) * ((∫ w, quadPotential mS RS (WS w) ∂μ) +
          (∫ w, quadPotential mB RB (WB w) ∂μ)) := by
    rw [integral_const_mul]
    congr 1
    change (∫ w, (quadPotential mS RS (WS w) + quadPotential mB RB (WB w)) ∂μ) = _
    exact integral_add h_varS.1 h_varB.1

  have h_exc_eq : (∫ w, realPlanExcessCost mS mB RS RB x a_opt w ∂μ) =
      (∫ w, realPlanRoundCost x a_opt (WS w) (WB w) ∂μ) -
      (∫ w, (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB (WS w) (WB w) ∂μ) := by
    have h0_cont : Continuous (fun w : UnitBallPair d =>
        (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB (WS w) (WB w)) :=
      continuous_const.mul (continuous_tradeQuadPotential_fixed mS mB RS RB)
    exact integral_sub (integrable_realPlanRoundCost x a_opt μ)
      (h0_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

  have h_exc_lt_δ : (∫ w, realPlanExcessCost mS mB RS RB x a_opt w ∂μ) < δ := by
    rw [h_exc_eq, h_round_int_eq, h_init_int_eq]
    unfold totalInfoDrop agentInfoDrop at hp_toi
    dsimp only [E, S_rv, B_rv] at hp_toi h_sdS h_sdB ⊢
    have h210 : (2 ^ 10 : ℝ) * (η' + η') = δ := by dsimp [η']; ring
    linarith [hp_toi, h_sdS, h_sdB, h_varS.2.2, h_varB.2.2, h_st1, h_st0, h210]

  have h_ge_δ : (δ : EReal) ≤
      ((∫ w, realPlanExcessCost mS mB RS RB x a_opt w ∂μ : ℝ) : EReal) := by
    rw [hδ_coe]; exact iInf_le _ a_opt
  linarith [EReal.coe_le_coe_iff.mp h_ge_δ, h_exc_lt_δ]

/-! ## Affine Pushforward, Convex Hull Representation, and Sion Exchange Helpers -/

private lemma affine_uniform_pushforward (r c pa : ℝ) (hr : 0 < r) (hc : 0 < c) :
    let μU : Measure ℝ :=
      volume.withDensity ((Set.Icc (-r) r).indicator fun _ => ENNReal.ofReal ((2 * r)⁻¹))
    μU.map (fun u => (pa - u) / c) =
      volume.withDensity
        ((Set.Icc ((pa - r) / c) ((pa + r) / c)).indicator fun _ => ENNReal.ofReal (c / (2 * r))) := by
  intro μU
  set f : ℝ → ℝ := fun u => (pa - u) / c
  set I_r : Set ℝ := Set.Icc (-r) r
  set J : Set ℝ := Set.Icc ((pa - r) / c) ((pa + r) / c)
  have hf : Measurable f := (measurable_const.sub measurable_id).div_const c
  have hI_meas : MeasurableSet I_r := isClosed_Icc.measurableSet
  have hJ_meas : MeasurableSet J := isClosed_Icc.measurableSet
  have h_map_vol : Measure.map f volume = ENNReal.ofReal c • volume := by
    have h_eq : f = (fun x => pa / c + x) ∘ (fun u => (-c⁻¹) * u) := by
      ext u; dsimp [f]; ring
    have hc_inv_ne : -c⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hc.ne')
    rw [h_eq, ← Measure.map_map (measurable_const_add (pa / c)) (measurable_const_mul (-c⁻¹)),
        Real.map_volume_mul_left hc_inv_ne,
        Measure.map_smul, map_add_left_eq_self, inv_neg, inv_inv, abs_neg, abs_of_pos hc]
  have h_pre_I : f ⁻¹' J = I_r := by
    ext u
    simp only [Set.mem_preimage, f, J, I_r, Set.mem_Icc]
    rw [div_le_div_iff_of_pos_right hc, div_le_div_iff_of_pos_right hc]
    constructor <;> intro h <;> constructor <;> linarith
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
      lintegral_indicator hI_meas, lintegral_indicator hJ_meas,
      Measure.restrict_restrict hI_meas, Measure.restrict_restrict hJ_meas,
      lintegral_const, lintegral_const, Measure.restrict_apply_univ, Measure.restrict_apply_univ]
  have h_inter : I_r ∩ f ⁻¹' s = f ⁻¹' (J ∩ s) := by
    rw [Set.preimage_inter, h_pre_I]
  rw [h_inter, ← Measure.map_apply hf (hJ_meas.inter hs), h_map_vol, Measure.smul_apply,
      smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

private lemma mem_convexHull_range_fin {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (base : ι → E) {g : E} (hg : g ∈ convexHull ℝ (Set.range base)) :
    ∃ (N : ℕ) (_ : 0 < N) (α : Fin N → ℝ) (as : Fin N → ι),
      (∀ i : Fin N, 0 ≤ α i) ∧ (∑ i : Fin N, α i = 1) ∧
      g = ∑ i : Fin N, α i • base (as i) := by
  rw [convexHull_eq] at hg
  rcases hg with ⟨κ, t, w, z, hw0, hw1, hz, hcm⟩
  have ht_ne : t.Nonempty := by
    rcases t.eq_empty_or_nonempty with rfl | hne
    · simp at hw1
    · exact hne
  let N : ℕ := t.card
  have hN : 0 < N := Finset.Nonempty.card_pos ht_ne
  let e : Fin N ≃ t := (t.equivFinOfCardEq rfl).symm
  have ha_ex : ∀ i : Fin N, ∃ a : ι, base a = z (e i).1 := fun i => hz (e i).1 (e i).2
  choose as has using ha_ex
  let α : Fin N → ℝ := fun i => w (e i).1
  refine ⟨N, hN, α, as, fun i => hw0 (e i).1 (e i).2, ?_, ?_⟩
  · calc ∑ i : Fin N, w (e i).1
        = ∑ x : t, w x.1 := e.sum_comp (fun x : t => w x.1)
      _ = ∑ x ∈ t, w x := Finset.sum_coe_sort t w
      _ = 1 := hw1
  · rw [← hcm, Finset.centerMass_eq_of_sum_1 t z hw1]
    calc ∑ x ∈ t, w x • z x
        = ∑ x : t, w x.1 • z x.1 := (Finset.sum_coe_sort t (fun x => w x • z x)).symm
      _ = ∑ i : Fin N, w (e i).1 • z (e i).1 := (e.sum_comp (fun x : t => w x.1 • z x.1)).symm
      _ = ∑ i : Fin N, α i • base (as i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [has i]

private lemma sion_convexHull_exchange {K idx : Type*}
    [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K] [BorelSpace K]
    [Nonempty idx] (base : idx → C(K, ℝ)) :
    let G : Set C(K, ℝ) := convexHull ℝ (Set.range base)
    (⨅ g : G, ⨆ w : K, (g.1 w : EReal)) =
      ⨆ ρ : ProbabilityMeasure K,
        ⨅ a : idx, ((∫ w, (base a) w ∂(ρ : Measure K) : ℝ) : EReal) := by
  intro G
  let a₀ : idx := Classical.arbitrary idx
  have hG_ne : G.Nonempty := ⟨base a₀, subset_convexHull ℝ (Set.range base) ⟨a₀, rfl⟩⟩
  have hG_conv : Convex ℝ G := convex_convexHull ℝ (Set.range base)
  let F : G → ProbabilityMeasure K → ℝ := fun g ρ => ∫ w, g.1 w ∂(ρ : Measure K)
  have h_int_c : ∀ (f : C(K, ℝ)) (ρ : ProbabilityMeasure K), Integrable f (ρ : Measure K) :=
    fun f ρ => f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hF_cont_left : ∀ ρ : ProbabilityMeasure K, Continuous (fun g : G => F g ρ) := by
    intro ρ
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun g₁ g₂ => ?_).continuous
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    have h_sub : F g₁ ρ - F g₂ ρ = ∫ w, (g₁.1 w - g₂.1 w) ∂(ρ : Measure K) :=
      (integral_sub (h_int_c g₁.1 ρ) (h_int_c g₂.1 ρ)).symm
    rw [h_sub]
    calc |∫ w, (g₁.1 w - g₂.1 w) ∂(ρ : Measure K)|
        ≤ ∫ w, |g₁.1 w - g₂.1 w| ∂(ρ : Measure K) := abs_integral_le_integral_abs
      _ ≤ ∫ _w, ‖g₁.1 - g₂.1‖ ∂(ρ : Measure K) := by
            refine integral_mono ((h_int_c (g₁.1 - g₂.1) ρ).abs) (integrable_const _) fun w => ?_
            exact ContinuousMap.norm_coe_le_norm (g₁.1 - g₂.1) w
      _ = ‖g₁.1 - g₂.1‖ := by rw [integral_const, probReal_univ, one_smul]
      _ = dist g₁ g₂ := (dist_eq_norm g₁.1 g₂.1).symm
  have hF_cont_right : ∀ g : G, Continuous (fun ρ : ProbabilityMeasure K => F g ρ) :=
    fun g => ProbabilityMeasure.continuous_integral_continuousMap g.1
  have hF_aff_left : ∀ (g₁ g₂ : G) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
      (ρ : ProbabilityMeasure K),
      F ⟨t • g₁.1 + (1 - t) • g₂.1,
          hG_conv g₁.2 g₂.2 ht0 (sub_nonneg.mpr ht1) (add_sub_cancel t 1)⟩ ρ =
        t * F g₁ ρ + (1 - t) * F g₂ ρ := by
    intro g₁ g₂ t _ _ ρ
    change (∫ w, (t * g₁.1 w + (1 - t) * g₂.1 w) ∂(ρ : Measure K)) = _
    rw [integral_add ((h_int_c g₁.1 ρ).const_mul t) ((h_int_c g₂.1 ρ).const_mul (1 - t)),
        integral_const_mul, integral_const_mul]
  have hF_aff_right : ∀ (g : G) (ρ₁ ρ₂ : ProbabilityMeasure K)
      (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
      F g (probMeasureConvexComb t ht0 ht1 ρ₁ ρ₂) =
        t * F g ρ₁ + (1 - t) * F g ρ₂ :=
    fun g ρ₁ ρ₂ t ht0 ht1 => integral_probMeasureConvexComb t ht0 ht1 ρ₁ ρ₂ g.1

  have h_sion := cor_sion_affine G hG_ne hG_conv F
    hF_cont_left hF_cont_right hF_aff_left hF_aff_right

  have h_sup_eq : ∀ g : G,
      (⨆ ρ : ProbabilityMeasure K, (F g ρ : EReal)) = ⨆ w : K, (g.1 w : EReal) := by
    intro g
    apply le_antisymm
    · refine iSup_le fun ρ => ?_
      obtain ⟨w_max, _, hw_max⟩ :=
        isCompact_univ.exists_isMaxOn Set.univ_nonempty g.1.continuous.continuousOn
      have h_le : F g ρ ≤ g.1 w_max := by
        calc (∫ w, g.1 w ∂(ρ : Measure K))
            ≤ ∫ _w, g.1 w_max ∂(ρ : Measure K) :=
                integral_mono (h_int_c g.1 ρ) (integrable_const _) fun w =>
                  hw_max (Set.mem_univ w)
          _ = g.1 w_max := by rw [integral_const, probReal_univ, one_smul]
      exact (EReal.coe_le_coe_iff.mpr h_le).trans (le_iSup (fun w : K => (g.1 w : EReal)) w_max)
    · refine iSup_le fun w => ?_
      let δ_w : ProbabilityMeasure K := ⟨Measure.dirac w, inferInstance⟩
      have h_dir : F g δ_w = g.1 w := integral_dirac g.1 w
      rw [← h_dir]
      exact le_iSup (fun ρ : ProbabilityMeasure K => (F g ρ : EReal)) δ_w

  have h_inf_eq : ∀ ρ : ProbabilityMeasure K,
      (⨅ g : G, (F g ρ : EReal)) =
        ⨅ a : idx, ((∫ w, (base a) w ∂(ρ : Measure K) : ℝ) : EReal) := by
    intro ρ
    apply le_antisymm
    · refine le_iInf fun a => ?_
      let g_a : G := ⟨base a, subset_convexHull ℝ (Set.range base) ⟨a, rfl⟩⟩
      exact iInf_le (fun g : G => (F g ρ : EReal)) g_a
    · refine le_iInf fun g => ?_
      obtain ⟨N, hN, α, as, hα_nn, hα_sum, hg_eq⟩ := mem_convexHull_range_fin base g.2
      have h_eval : F g ρ = ∑ i : Fin N, α i * ∫ w, (base (as i)) w ∂(ρ : Measure K) := by
        have h_pt : (g.1 : K → ℝ) = fun w => ∑ i : Fin N, α i * (base (as i)) w := by
          ext w
          have := congr_arg (fun f : C(K, ℝ) => f w) hg_eq
          simpa [ContinuousMap.coe_sum, Pi.smul_apply, smul_eq_mul] using this
        change (∫ w, g.1 w ∂(ρ : Measure K)) = _
        rw [h_pt, integral_finset_sum Finset.univ fun i _ =>
          (h_int_c (base (as i)) ρ).const_mul (α i)]
        refine Finset.sum_congr rfl fun i _ => integral_const_mul (α i) _
      set inf_er : EReal := ⨅ a : idx, ((∫ w, (base a) w ∂(ρ : Measure K) : ℝ) : EReal)
      by_cases h_bot : inf_er = ⊥
      · rw [h_bot]; exact bot_le
      have h_ne_top : inf_er ≠ ⊤ := by
        intro htop
        have h_le : inf_er ≤ ((∫ w, (base a₀) w ∂(ρ : Measure K) : ℝ) : EReal) := iInf_le _ a₀
        rw [htop] at h_le
        exact not_top_lt (lt_of_le_of_lt h_le (EReal.coe_lt_top _))
      set c_inf : ℝ := inf_er.toReal
      have hc_coe : (c_inf : EReal) = inf_er := EReal.coe_toReal h_ne_top h_bot
      have h_ge : c_inf ≤ F g ρ := by
        rw [h_eval]
        calc c_inf
            = (∑ i : Fin N, α i) * c_inf := by rw [hα_sum, one_mul]
          _ = ∑ i : Fin N, α i * c_inf := Finset.sum_mul _ _ _
          _ ≤ ∑ i : Fin N, α i * ∫ w, (base (as i)) w ∂(ρ : Measure K) := by
                refine Finset.sum_le_sum fun i _ => ?_
                have hi_er : (c_inf : EReal) ≤
                    ((∫ w, (base (as i)) w ∂(ρ : Measure K) : ℝ) : EReal) := by
                  rw [hc_coe]; exact iInf_le _ (as i)
                exact mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp hi_er) (hα_nn i)
      rw [← hc_coe, EReal.coe_le_coe_iff]
      exact h_ge

  calc (⨅ g : G, ⨆ w : K, (g.1 w : EReal))
      = ⨅ g : G, ⨆ ρ : ProbabilityMeasure K, (F g ρ : EReal) := by
          congr 1; ext g; exact (h_sup_eq g).symm
    _ = ⨆ ρ : ProbabilityMeasure K, ⨅ g : G, (F g ρ : EReal) := h_sion
    _ = ⨆ ρ : ProbabilityMeasure K,
          ⨅ a : idx, ((∫ w, (base a) w ∂(ρ : Measure K) : ℝ) : EReal) := by
          congr 1; ext ρ; exact h_inf_eq ρ

/-! ## Finite Mixture Implementation Helper -/

private lemma mixture_lottery_props {d N : ℕ} (_hN : 0 < N)
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ)
    (α : Fin N → ℝ) (hα_nn : ∀ i : Fin N, 0 ≤ α i) (hα_sum : ∑ i : Fin N, α i = 1)
    (μU : Measure ℝ) [IsProbabilityMeasure μU]
    (I_supp : Set ℝ) (hI_cpt : IsCompact I_supp) (hI_null : μU I_suppᶜ = 0)
    (st0_fn st1_fn : Fin N → ℝ → PDTradeState d)
    (hst0_cont : ∀ i : Fin N, Continuous (st0_fn i))
    (hst1_cont : ∀ i : Fin N, Continuous (st1_fn i))
    (pr_fn : Fin N → ℝ → ℝ) (hpr_cont : ∀ i : Fin N, Continuous (pr_fn i))
    (f_i : Fin N → ℝ → ENNReal) (hf_i_meas : ∀ i : Fin N, Measurable (f_i i))
    (hf_i_map : ∀ i : Fin N, μU.map (pr_fn i) = volume.withDensity (f_i i))
    (M_dens : ℝ) (hM_nn : 0 ≤ M_dens)
    (hf_i_bd : ∀ (i : Fin N) (p : ℝ), f_i i p ≤ ENNReal.ofReal M_dens)
    (p_min p_max : ℝ) (_hp_le : p_min ≤ p_max)
    (hf_i_supp : ∀ (i : Fin N) (p : ℝ), p ∉ Set.Icc p_min p_max → f_i i p = 0)
    (h_int_round : ∀ (i : Fin N) (w : UnitBallPair d),
      Integrable (fun u : ℝ =>
        realPlanRoundCost x (pr_fn i u, st0_fn i u, st1_fn i u) w.seller w.buyer) μU) :
    ∃ (Q : ProbabilityMeasure (RealTradePlan d))
      (f_dens : ℝ → ENNReal) (K_st : Set (PDTradeState d)),
      Measurable f_dens ∧ IsCompact K_st ∧
      (∀ w : UnitBallPair d,
        lotteryExpectedExcessCost mS mB RS RB x Q w =
          ((∑ i : Fin N, α i *
            ∫ u, realPlanExcessCost mS mB RS RB x
              (pr_fn i u, st0_fn i u, st1_fn i u) w ∂μU : ℝ) : EReal)) ∧
      (Q : Measure (RealTradePlan d)).map RealTradePlan.price = volume.withDensity f_dens ∧
      (∀ p : ℝ, f_dens p ≤ ENNReal.ofReal M_dens) ∧
      (∀ p : ℝ, p ∉ Set.Icc p_min p_max → f_dens p = 0) ∧
      (Q : Measure (RealTradePlan d)) {a | a.succ0 ∈ K_st ∧ a.succ1 ∈ K_st}ᶜ = 0 := by
  let plan_fn : Fin N → ℝ → RealTradePlan d :=
    fun i u => (pr_fn i u, st0_fn i u, st1_fn i u)
  have hplan_meas : ∀ i : Fin N, Measurable (plan_fn i) := fun i =>
    (hpr_cont i).measurable.prodMk ((hst0_cont i).measurable.prodMk (hst1_cont i).measurable)
  let ν_i : Fin N → Measure (RealTradePlan d) := fun i => μU.map (plan_fn i)
  let Q_meas : Measure (RealTradePlan d) := ∑ i : Fin N, ENNReal.ofReal (α i) • ν_i i
  have hQ_prob : IsProbabilityMeasure Q_meas := by
    constructor
    rw [Measure.finset_sum_apply]
    have h_each : ∀ i : Fin N, (ENNReal.ofReal (α i) • ν_i i) Set.univ = ENNReal.ofReal (α i) := by
      intro i
      rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hplan_meas i) MeasurableSet.univ,
          Set.preimage_univ, measure_univ, mul_one]
    simp_rw [h_each]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hα_nn i), hα_sum, ENNReal.ofReal_one]
  let Q : ProbabilityMeasure (RealTradePlan d) := ⟨Q_meas, hQ_prob⟩
  let f_dens : ℝ → ENNReal := fun p => ∑ i : Fin N, ENNReal.ofReal (α i) * f_i i p
  have hf_dens_meas : Measurable f_dens :=
    Finset.measurable_sum Finset.univ fun i _ => measurable_const.mul (hf_i_meas i)
  let K_st : Set (PDTradeState d) :=
    ⋃ i : Fin N, ((st0_fn i '' I_supp) ∪ (st1_fn i '' I_supp))
  have hK_cpt : IsCompact K_st :=
    isCompact_iUnion fun i =>
      (hI_cpt.image (hst0_cont i)).union (hI_cpt.image (hst1_cont i))

  refine ⟨Q, f_dens, K_st, hf_dens_meas, hK_cpt, ?_, ?_, ?_, ?_, ?_⟩
  · -- Expected excess cost evaluation
    intro w
    set Φ₀_w : ℝ := (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer
    let φ : RealTradePlan d → ENNReal :=
      fun a' => ENNReal.ofReal (realPlanRoundCost x a' w.seller w.buyer)
    have hφ_meas : Measurable φ :=
      ENNReal.measurable_ofReal.comp
        ((measurable_realPlanRoundCost_joint x).comp (measurable_id.prodMk measurable_const))
    have h_lint : (∫⁻ a', φ a' ∂Q_meas) =
        ENNReal.ofReal (∑ i : Fin N, α i *
          ∫ u, realPlanRoundCost x (plan_fn i u) w.seller w.buyer ∂μU) := by
      rw [lintegral_finset_sum_measure]
      have h_term : ∀ i : Fin N,
          (∫⁻ a', φ a' ∂(ENNReal.ofReal (α i) • ν_i i)) =
            ENNReal.ofReal (α i *
              ∫ u, realPlanRoundCost x (plan_fn i u) w.seller w.buyer ∂μU) := by
        intro i
        have hi_nn : 0 ≤ ∫ u, realPlanRoundCost x (plan_fn i u) w.seller w.buyer ∂μU :=
          integral_nonneg fun u => realPlanRoundCost_nonneg x (plan_fn i u) w.seller w.buyer
        rw [lintegral_smul_measure, smul_eq_mul,
            lintegral_map hφ_meas (hplan_meas i),
            ← ofReal_integral_eq_lintegral_ofReal (h_int_round i w)
              (Filter.Eventually.of_forall fun u =>
                realPlanRoundCost_nonneg x (plan_fn i u) w.seller w.buyer),
            ← ENNReal.ofReal_mul (hα_nn i)]
      simp_rw [h_term]
      exact (ENNReal.ofReal_sum_of_nonneg fun i _ =>
        mul_nonneg (hα_nn i)
          (integral_nonneg fun u => realPlanRoundCost_nonneg x (plan_fn i u) w.seller w.buyer)).symm
    have h_sum_nn : 0 ≤ ∑ i : Fin N, α i *
        ∫ u, realPlanRoundCost x (plan_fn i u) w.seller w.buyer ∂μU :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hα_nn i)
        (integral_nonneg fun u => realPlanRoundCost_nonneg x (plan_fn i u) w.seller w.buyer)
    unfold lotteryExpectedExcessCost
    change (∫⁻ a', φ a' ∂Q_meas).toEReal - (Φ₀_w : EReal) = _
    rw [h_lint, EReal.coe_ennreal_ofReal, max_eq_left h_sum_nn, ← EReal.coe_sub]
    congr 1
    change _ = ∑ i : Fin N, α i * ∫ u, realPlanExcessCost mS mB RS RB x (plan_fn i u) w ∂μU
    have h_sub_each : ∀ i : Fin N,
        (∫ u, realPlanExcessCost mS mB RS RB x (plan_fn i u) w ∂μU) =
          (∫ u, realPlanRoundCost x (plan_fn i u) w.seller w.buyer ∂μU) - Φ₀_w := by
      intro i
      change (∫ u, (realPlanRoundCost x (plan_fn i u) w.seller w.buyer - Φ₀_w) ∂μU) = _
      rw [integral_sub (h_int_round i w) (integrable_const Φ₀_w),
          integral_const, probReal_univ, one_smul]
    simp_rw [h_sub_each, mul_sub]
    rw [Finset.sum_sub_distrib]
    have h_c : (∑ i : Fin N, α i * Φ₀_w) = Φ₀_w := by
      rw [← Finset.sum_mul, hα_sum, one_mul]
    rw [h_c]
  · -- Price pushforward density
    have hp_meas : Measurable (RealTradePlan.price (d := d)) := continuous_fst.measurable
    change Q_meas.map RealTradePlan.price = volume.withDensity f_dens
    ext s hs
    rw [Measure.map_apply hp_meas hs, Measure.finset_sum_apply, withDensity_apply _ hs]
    have h_lhs : ∀ i : Fin N,
        (ENNReal.ofReal (α i) • ν_i i) (RealTradePlan.price ⁻¹' s) =
          ∫⁻ p in s, ENNReal.ofReal (α i) * f_i i p ∂volume := by
      intro i
      have h_comp : RealTradePlan.price ∘ plan_fn i = pr_fn i := rfl
      have h_map_i : (ν_i i).map RealTradePlan.price = volume.withDensity (f_i i) := by
        dsimp [ν_i]
        rw [Measure.map_map hp_meas (hplan_meas i), h_comp, hf_i_map i]
      rw [Measure.smul_apply, smul_eq_mul, ← Measure.map_apply hp_meas hs,
          h_map_i, withDensity_apply _ hs, ← lintegral_const_mul _ (hf_i_meas i)]
    simp_rw [h_lhs]
    exact (lintegral_finset_sum Finset.univ fun i _ => measurable_const.mul (hf_i_meas i)).symm
  · -- Density upper bound
    intro p
    calc f_dens p
        ≤ ∑ i : Fin N, ENNReal.ofReal (α i) * ENNReal.ofReal M_dens :=
            Finset.sum_le_sum fun i _ => mul_le_mul_right (hf_i_bd i p) _
      _ = ∑ i : Fin N, ENNReal.ofReal (α i * M_dens) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← ENNReal.ofReal_mul (hα_nn i)]
      _ = ENNReal.ofReal (∑ i : Fin N, α i * M_dens) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hα_nn i) hM_nn).symm
      _ = ENNReal.ofReal M_dens := by rw [← Finset.sum_mul, hα_sum, one_mul]
  · -- Density compact support
    intro p hp
    exact Finset.sum_eq_zero fun i _ => by rw [hf_i_supp i p hp, mul_zero]
  · -- Successor states in K_st almost surely
    let E_good : Set (RealTradePlan d) := {a | a.succ0 ∈ K_st ∧ a.succ1 ∈ K_st}
    have hE_closed : IsClosed E_good :=
      (hK_cpt.isClosed.preimage (continuous_fst.comp continuous_snd)).inter
        (hK_cpt.isClosed.preimage (continuous_snd.comp continuous_snd))
    have hEc_meas : MeasurableSet E_goodᶜ := hE_closed.measurableSet.compl
    change Q_meas E_goodᶜ = 0
    rw [Measure.finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hplan_meas i) hEc_meas]
    have h_sub : plan_fn i ⁻¹' E_goodᶜ ⊆ I_suppᶜ := by
      intro u hu hu_in
      apply hu
      refine ⟨Set.mem_iUnion.mpr ⟨i, Or.inl ⟨u, hu_in, rfl⟩⟩,
              Set.mem_iUnion.mpr ⟨i, Or.inr ⟨u, hu_in, rfl⟩⟩⟩
    rw [measure_mono_null h_sub hI_null, mul_zero]

/-! ## Claim D.5: Main Theorem -/

/-- **Claim D.5 (Minimax Duality and Regular Near-Optimal Lotteries, `cl:trade-minimax`)**:
For any positive-definite block-diagonal bilateral-trade state `((m_S, m_B), diag(R_S, R_B))` and
unit-ball context `x` (`‖x‖₂ ≤ 1`):
1. The Bayesian value `V_B = tradeBayesianValue mS mB RS RB x` is finite and nonpositive
   (`V_B ≠ ⊥ ∧ V_B ≤ 0`),
2. Strong minimax duality holds over Borel probability lotteries `Q` on `RealTradePlan d`:
   `V_B = V_W` (`tradeBayesianValue mS mB RS RB x = tradeWorstCaseLotteryValue mS mB RS RB x`),
3. For every `η > 0`, there exists a probability lottery `Q` with
   `sup_{w ∈ K} E_{a ~ Q}[f_a(w)] < V_W + η` whose price distribution has a bounded Lebesgue
   density supported on a compact interval `[p_min, p_max]`, and whose successor states lie
   `Q`-almost surely in a compact set `K_st` of positive-definite block-diagonal states. -/
theorem claim_trade_minimax {d : ℕ}
    (mS mB : Fin d → ℝ) (RS RB : Matrix (Fin d) (Fin d) ℝ)
    (hRS : RS.PosDef) (hRB : RB.PosDef)
    (x : Fin d → ℝ) (hx : vecL2Norm x ≤ 1) :
    (tradeBayesianValue mS mB RS RB x ≠ ⊥ ∧ tradeBayesianValue mS mB RS RB x ≤ 0) ∧
    tradeBayesianValue mS mB RS RB x = tradeWorstCaseLotteryValue mS mB RS RB x ∧
    (∀ η : ℝ, 0 < η →
      ∃ (Q : ProbabilityMeasure (RealTradePlan d))
        (f_dens : ℝ → ENNReal) (M_dens p_min p_max : ℝ)
        (K_st : Set (PDTradeState d)),
        Measurable f_dens ∧ 0 ≤ M_dens ∧ p_min ≤ p_max ∧ IsCompact K_st ∧
        (⨆ w : UnitBallPair d, lotteryExpectedExcessCost mS mB RS RB x Q w) <
          tradeWorstCaseLotteryValue mS mB RS RB x + (η : EReal) ∧
        (Q : Measure (RealTradePlan d)).map RealTradePlan.price =
          volume.withDensity f_dens ∧
        (∀ p : ℝ, f_dens p ≤ ENNReal.ofReal M_dens) ∧
        (∀ p : ℝ, p ∉ Set.Icc p_min p_max → f_dens p = 0) ∧
        (Q : Measure (RealTradePlan d)) {a | a.succ0 ∈ K_st ∧ a.succ1 ∈ K_st}ᶜ = 0) := by
  obtain ⟨hVB_ne_bot, h_weak⟩ := lem_weak_duality_and_ne_bot mS mB RS RB hRS hRB x
  have hVB_le_zero : tradeBayesianValue mS mB RS RB x ≤ 0 :=
    lem_bayesian_value_nonpos mS mB RS RB hRS hRB x hx
  have hVB_ne_top : tradeBayesianValue mS mB RS RB x ≠ ⊤ := by
    intro htop
    rw [htop] at hVB_le_zero
    exact not_top_lt (lt_of_le_of_lt hVB_le_zero (EReal.coe_lt_top (0 : ℝ)))
  set v_B : ℝ := (tradeBayesianValue mS mB RS RB x).toReal
  have hvB_coe : (v_B : EReal) = tradeBayesianValue mS mB RS RB x :=
    EReal.coe_toReal hVB_ne_top hVB_ne_bot
  have hvB_nonpos : v_B ≤ 0 := by
    have h0 : (v_B : EReal) ≤ ((0 : ℝ) : EReal) := by simpa [hvB_coe] using hVB_le_zero
    exact EReal.coe_le_coe_iff.mp h0

  let st₀ : PDTradeState d := PDTradeState.mk' mS mB RS RB hRS hRB
  haveI : Nonempty (RealTradePlan d) := ⟨(0, st₀, st₀)⟩

  -- Suffices to show: for every η > 0, there exists a regular lottery Q with sup_K E_Q[f_a] < v_B + η
  suffices h_reg_lot : ∀ η : ℝ, 0 < η →
      ∃ (Q : ProbabilityMeasure (RealTradePlan d))
        (f_dens : ℝ → ENNReal) (M_dens p_min p_max : ℝ)
        (K_st : Set (PDTradeState d)),
        Measurable f_dens ∧ 0 ≤ M_dens ∧ p_min ≤ p_max ∧ IsCompact K_st ∧
        (⨆ w : UnitBallPair d, lotteryExpectedExcessCost mS mB RS RB x Q w) <
          ((v_B + η : ℝ) : EReal) ∧
        (Q : Measure (RealTradePlan d)).map RealTradePlan.price =
          volume.withDensity f_dens ∧
        (∀ p : ℝ, f_dens p ≤ ENNReal.ofReal M_dens) ∧
        (∀ p : ℝ, p ∉ Set.Icc p_min p_max → f_dens p = 0) ∧
        (Q : Measure (RealTradePlan d)) {a | a.succ0 ∈ K_st ∧ a.succ1 ∈ K_st}ᶜ = 0 by
    have hVW_le_VB : tradeWorstCaseLotteryValue mS mB RS RB x ≤
        tradeBayesianValue mS mB RS RB x := by
      rw [← hvB_coe]
      by_contra h_not
      have h_lt : (v_B : EReal) < tradeWorstCaseLotteryValue mS mB RS RB x := lt_of_not_ge h_not
      by_cases hVW_top : tradeWorstCaseLotteryValue mS mB RS RB x = ⊤
      · obtain ⟨Q₁, _, _, _, _, _, _, _, _, _, hQ₁_lt, _, _, _, _⟩ := h_reg_lot 1 one_pos
        have h_le : tradeWorstCaseLotteryValue mS mB RS RB x ≤
            ⨆ w : UnitBallPair d, lotteryExpectedExcessCost mS mB RS RB x Q₁ w := iInf_le _ Q₁
        rw [hVW_top] at h_le
        exact not_top_lt (lt_of_le_of_lt h_le (hQ₁_lt.trans (EReal.coe_lt_top _)))
      · have hVW_bot : tradeWorstCaseLotteryValue mS mB RS RB x ≠ ⊥ := by
          intro hbot; rw [hbot] at h_lt; exact not_lt_bot h_lt
        set v_W : ℝ := (tradeWorstCaseLotteryValue mS mB RS RB x).toReal
        have hvW_coe : (v_W : EReal) = tradeWorstCaseLotteryValue mS mB RS RB x :=
          EReal.coe_toReal hVW_top hVW_bot
        rw [← hvW_coe, EReal.coe_lt_coe_iff] at h_lt
        set η₀ : ℝ := (v_W - v_B) / 2
        have hη₀ : 0 < η₀ := by dsimp [η₀]; linarith
        obtain ⟨Q₀, _, _, _, _, _, _, _, _, _, hQ₀_lt, _, _, _, _⟩ := h_reg_lot η₀ hη₀
        have h_le : (v_W : EReal) ≤
            ⨆ w : UnitBallPair d, lotteryExpectedExcessCost mS mB RS RB x Q₀ w := by
          rw [hvW_coe]; exact iInf_le _ Q₀
        have h_comb := EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt h_le hQ₀_lt)
        dsimp [η₀] at h_comb
        linarith
    have h_eq_val : tradeBayesianValue mS mB RS RB x = tradeWorstCaseLotteryValue mS mB RS RB x :=
      le_antisymm h_weak hVW_le_VB
    refine ⟨⟨hVB_ne_bot, hVB_le_zero⟩, h_eq_val, fun η hη => ?_⟩
    obtain ⟨Q, f_dens, M_dens, p_min, p_max, K_st, hf_m, hM, hp, hK, hQ_lt, hmap, hbd, hsp, hK0⟩ :=
      h_reg_lot η hη
    refine ⟨Q, f_dens, M_dens, p_min, p_max, K_st, hf_m, hM, hp, hK, ?_, hmap, hbd, hsp, hK0⟩
    rwa [← h_eq_val, ← hvB_coe, ← EReal.coe_add]

  -- Prove h_reg_lot by splitting on x = 0 vs x ≠ 0
  intro η hη
  by_cases hx0 : x = 0
  · -- Degenerate context x = 0: payoffs are already continuous on K; mix with Unif[1, 2] price
    subst hx0
    let st_eff : RealTradePlan d → PDTradeState d :=
      fun a => if 0 ≤ a.price ∧ a.price ≤ 0 then a.succ1 else a.succ0
    have h_round_zero : ∀ (a : RealTradePlan d) (s b : Fin d → ℝ),
        realPlanRoundCost 0 a s b =
          (2 ^ 10 : ℝ) *
            tradeQuadPotential (st_eff a).mS (st_eff a).mB (st_eff a).RS (st_eff a).RB s b := by
      intro a s b
      unfold realPlanRoundCost st_eff
      simp only [zero_dotProduct]
      split_ifs with h
      · rfl
      · simp
    let base0 : RealTradePlan d → C(UnitBallPair d, ℝ) := fun a =>
      ⟨fun w => realPlanExcessCost mS mB RS RB 0 a w, by
        have h_eq : (fun w : UnitBallPair d => realPlanExcessCost mS mB RS RB 0 a w) =
            fun w => (2 ^ 10 : ℝ) *
              tradeQuadPotential (st_eff a).mS (st_eff a).mB (st_eff a).RS (st_eff a).RB
                w.seller w.buyer -
              (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer := by
          ext w; unfold realPlanExcessCost; rw [h_round_zero]
        rw [h_eq]
        exact (continuous_const.mul
          (continuous_tradeQuadPotential_fixed (st_eff a).mS (st_eff a).mB
            (st_eff a).RS (st_eff a).RB)).sub
          (continuous_const.mul (continuous_tradeQuadPotential_fixed mS mB RS RB))⟩
    let G0 : Set C(UnitBallPair d, ℝ) := convexHull ℝ (Set.range base0)
    have h_exch0 : (⨅ g : G0, ⨆ w : UnitBallPair d, (g.1 w : EReal)) = (v_B : EReal) := by
      rw [hvB_coe]
      exact sion_convexHull_exchange base0
    have h_lt_sup : (⨅ g : G0, ⨆ w : UnitBallPair d, (g.1 w : EReal)) < ((v_B + η : ℝ) : EReal) := by
      rw [h_exch0, EReal.coe_lt_coe_iff]; linarith
    rw [iInf_lt_iff] at h_lt_sup
    rcases h_lt_sup with ⟨g, hg_lt⟩
    obtain ⟨N, hN, α, as, hα_nn, hα_sum, hg_eq⟩ := mem_convexHull_range_fin base0 g.2

    -- Uniform price distribution on [1, 2] = [3/2 - 1/2, 3/2 + 1/2]
    let I_12 : Set ℝ := Set.Icc (1 : ℝ) 2
    let f_u0 : ℝ → ENNReal := I_12.indicator fun _ => 1
    let μU0 : Measure ℝ := volume.withDensity f_u0
    have hI12_meas : MeasurableSet I_12 := isClosed_Icc.measurableSet
    have hμU0_prob : IsProbabilityMeasure μU0 := by
      constructor
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          lintegral_indicator hI12_meas, lintegral_const, Measure.restrict_apply_univ,
          Real.volume_Icc]
      norm_num
    have hI12_null : μU0 I_12ᶜ = 0 := by
      rw [withDensity_apply _ hI12_meas.compl, lintegral_indicator hI12_meas,
          Measure.restrict_restrict hI12_meas, Set.inter_compl_self, Measure.restrict_empty,
          lintegral_zero_measure]

    have h_int_r0 : ∀ (i : Fin N) (w : UnitBallPair d),
        Integrable (fun u : ℝ =>
          realPlanRoundCost 0 (u, st_eff (as i), st_eff (as i)) w.seller w.buyer) μU0 := by
      intro i w
      have h_cst : (fun u : ℝ =>
          realPlanRoundCost 0 (u, st_eff (as i), st_eff (as i)) w.seller w.buyer) =
          fun _ => (2 ^ 10 : ℝ) *
            tradeQuadPotential (st_eff (as i)).mS (st_eff (as i)).mB
              (st_eff (as i)).RS (st_eff (as i)).RB w.seller w.buyer := by
        ext u
        unfold realPlanRoundCost
        simp only [zero_dotProduct, RealTradePlan.price, RealTradePlan.succ0, RealTradePlan.succ1]
        split_ifs <;> simp
      rw [h_cst]
      exact integrable_const _

    obtain ⟨Q, f_dens, K_st, hf_m, hK, hQ_eval, hmap, hbd, hsp, hK0⟩ :=
      mixture_lottery_props hN mS mB RS RB 0 α hα_nn hα_sum μU0 I_12 isCompact_Icc hI12_null
        (fun i _ => st_eff (as i)) (fun i _ => st_eff (as i))
        (fun _ => continuous_const) (fun _ => continuous_const)
        (fun _ u => u) (fun _ => continuous_id)
        (fun _ => f_u0) (fun _ => measurable_const.indicator hI12_meas)
        (fun _ => Measure.map_id)
        1 zero_le_one
        (fun _ p => by
          dsimp [f_u0]
          by_cases hp : p ∈ I_12 <;> simp [hp])
        1 2 (by norm_num)
        (fun _ p hp => Set.indicator_of_notMem hp _)
        h_int_r0

    have hQ_eq_g : ∀ w : UnitBallPair d,
        lotteryExpectedExcessCost mS mB RS RB 0 Q w = (g.1 w : EReal) := by
      intro w
      rw [hQ_eval w]
      congr 1
      have h_each : ∀ i : Fin N,
          (∫ u, realPlanExcessCost mS mB RS RB 0
            (u, st_eff (as i), st_eff (as i)) w ∂μU0) = (base0 (as i)) w := by
        intro i
        have h_cst : (fun u : ℝ =>
            realPlanExcessCost mS mB RS RB 0 (u, st_eff (as i), st_eff (as i)) w) =
            fun _ => (base0 (as i)) w := by
          ext u
          change realPlanRoundCost 0 (u, st_eff (as i), st_eff (as i)) w.seller w.buyer - _ =
            realPlanRoundCost 0 (as i) w.seller w.buyer - _
          congr 1
          rw [h_round_zero (as i)]
          unfold realPlanRoundCost
          simp only [zero_dotProduct, RealTradePlan.price, RealTradePlan.succ0, RealTradePlan.succ1]
          split_ifs <;> simp
        rw [h_cst, integral_const, probReal_univ, one_smul]
      simp_rw [h_each]
      have := congr_arg (fun f : C(UnitBallPair d, ℝ) => f w) hg_eq
      simpa [ContinuousMap.coe_sum, Pi.smul_apply, smul_eq_mul] using this.symm

    refine ⟨Q, f_dens, 1, 1, 2, K_st, hf_m, zero_le_one, by norm_num, hK, ?_, hmap, hbd, hsp, hK0⟩
    simpa [hQ_eq_g] using hg_lt

  · -- Nonzero context x ≠ 0: smooth prices uniformly on [-ε ‖x‖₂, ε ‖x‖₂] and apply Corollary D.7
    obtain ⟨C0, _, hC0_pos, _, h_ball, h_drift, _⟩ :=
      lem_initial_potential_jitter_and_lip mS mB RS RB hRS hRB x hx0 hx
    let nx : ℝ := vecL2Norm x
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx0
    have hnx_pos : 0 < nx :=
      Real.sqrt_pos.mpr (lt_of_lt_of_le (sq_pos_of_ne_zero hi₀)
        (Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i₀)))
    let v : Fin d → ℝ := ((nx ^ 2)⁻¹) • x
    have hxv : dotProduct x v = 1 := by
      have hxx : dotProduct x x = nx ^ 2 := by
        dsimp [nx, vecL2Norm, dotProduct]
        rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
        refine Finset.sum_congr rfl fun i _ => by ring
      dsimp [v]
      rw [dotProduct_smul, smul_eq_mul, hxx, inv_mul_cancel₀ (sq_pos_of_pos hnx_pos).ne']

    -- Choose 0 < ε ≤ 1/4 with C0 * ε < η / 2; since v_B ≤ 0, v_B / (1 - ε) ≤ v_B automatically!
    set ε : ℝ := min (1 / 4 : ℝ) (η / (4 * C0))
    have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε ≤ 1 / 4 := min_le_left _ _
    have hC0ε_lt : C0 * ε < η := by
      have h_le : ε ≤ η / (4 * C0) := min_le_right _ _
      have h_mul : C0 * ε ≤ C0 * (η / (4 * C0)) := mul_le_mul_of_nonneg_left h_le hC0_pos.le
      have h_simp : C0 * (η / (4 * C0)) = η / 4 := by field_simp [hC0_pos.ne']
      linarith

    set c : ℝ := 1 - ε
    have hc_pos : 0 < c := by dsimp [c]; linarith
    set r_ε : ℝ := ε * nx
    have hr_pos : 0 < r_ε := mul_pos hε0 hnx_pos
    let I_ε : Set ℝ := Set.Icc (-r_ε) r_ε
    have hIε_meas : MeasurableSet I_ε := isClosed_Icc.measurableSet
    let μU : Measure ℝ :=
      volume.withDensity (I_ε.indicator fun _ => ENNReal.ofReal ((2 * r_ε)⁻¹))
    have hμU_prob : IsProbabilityMeasure μU := by
      constructor
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          lintegral_indicator hIε_meas, lintegral_const, Measure.restrict_apply_univ,
          Real.volume_Icc]
      have h_len : r_ε - -r_ε = 2 * r_ε := by ring
      rw [h_len, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
          ENNReal.ofReal_one]
    have hIε_null : μU I_εᶜ = 0 := by
      rw [withDensity_apply _ hIε_meas.compl, lintegral_indicator hIε_meas,
          Measure.restrict_restrict hIε_meas, Set.inter_compl_self, Measure.restrict_empty,
          lintegral_zero_measure]

    -- Perturbed state map Ψ_state and plan map Ψ_plan
    let Ψ_state : PDTradeState d → ℝ → PDTradeState d := fun st u =>
      PDTradeState.mk'
        (c⁻¹ • (st.mS - u • v))
        (c⁻¹ • (st.mB - u • v))
        (c⁻¹ • st.RS)
        (c⁻¹ • st.RB)
        (st.posDef_RS.smul (inv_pos.mpr hc_pos))
        (st.posDef_RB.smul (inv_pos.mpr hc_pos))
    have hΨ_state_cont : ∀ st : PDTradeState d, Continuous (Ψ_state st) := by
      intro st
      refine Continuous.subtype_mk ?_ _
      refine (continuous_pi fun i => continuous_const.mul
        (continuous_const.sub (continuous_id.mul continuous_const))).prodMk ?_
      refine (continuous_pi fun i => continuous_const.mul
        (continuous_const.sub (continuous_id.mul continuous_const))).prodMk ?_
      exact continuous_const.prodMk continuous_const

    let Ψ_plan : RealTradePlan d → ℝ → RealTradePlan d := fun a u =>
      ((a.price - u) / c, Ψ_state a.succ0 u, Ψ_state a.succ1 u)
    have hΨ_plan_cont : ∀ a : RealTradePlan d, Continuous (Ψ_plan a) := fun a =>
      ((continuous_const.sub continuous_id).div_const c).prodMk
        ((hΨ_state_cont a.succ0).prodMk (hΨ_state_cont a.succ1))
    have hΨ_price : ∀ (a : RealTradePlan d) (u : ℝ), (Ψ_plan a u).price = (a.price - u) / c :=
      fun _ _ => rfl
    have hΨ_succ0 : ∀ (a : RealTradePlan d) (u : ℝ), (Ψ_plan a u).succ0 = Ψ_state a.succ0 u :=
      fun _ _ => rfl
    have hΨ_succ1 : ∀ (a : RealTradePlan d) (u : ℝ), (Ψ_plan a u).succ1 = Ψ_state a.succ1 u :=
      fun _ _ => rfl

    -- Algebraic scaling identity for agentQuadPotential, tradeQuadPotential, and realPlanRoundCost
    have h_inv_smul : ∀ (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef → (c⁻¹ • R)⁻¹ = c • R⁻¹ := by
      intro R hR
      have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
      have hRRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hdet
      have h_mul : (c⁻¹ • R) * (c • R⁻¹) = 1 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc_pos.ne', one_smul, hRRinv]
      have hdet' : IsUnit (c⁻¹ • R).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp (hR.smul (inv_pos.mpr hc_pos)).isUnit
      calc (c⁻¹ • R)⁻¹
          = (c⁻¹ • R)⁻¹ * ((c⁻¹ • R) * (c • R⁻¹)) := by rw [h_mul, Matrix.mul_one]
        _ = ((c⁻¹ • R)⁻¹ * (c⁻¹ • R)) * (c • R⁻¹) := by rw [Matrix.mul_assoc]
        _ = c • R⁻¹ := by rw [Matrix.nonsing_inv_mul _ hdet', Matrix.one_mul]

    have h_ag_scale : ∀ (m z : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef → ∀ u : ℝ,
        agentQuadPotential (c⁻¹ • (m - u • v)) (c⁻¹ • R) z =
          c⁻¹ * agentQuadPotential m R (c • z + u • v) := by
      intro m z R hR u
      have h_diff : z - c⁻¹ • (m - u • v) = c⁻¹ • ((c • z + u • v) - m) := by
        ext i
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        field_simp [hc_pos.ne']
        ring
      unfold agentQuadPotential
      rw [h_inv_smul R hR, h_diff, Matrix.trace_smul, Matrix.smul_mulVec, Matrix.mulVec_smul,
          smul_dotProduct, dotProduct_smul, dotProduct_smul]
      simp only [smul_eq_mul]
      field_simp [hc_pos.ne']

    have h_tr_scale : ∀ (st : PDTradeState d) (s b : Fin d → ℝ) (u : ℝ),
        tradeQuadPotential (Ψ_state st u).mS (Ψ_state st u).mB
          (Ψ_state st u).RS (Ψ_state st u).RB s b =
          c⁻¹ * tradeQuadPotential st.mS st.mB st.RS st.RB (c • s + u • v) (c • b + u • v) := by
      intro st s b u
      unfold tradeQuadPotential
      change agentQuadPotential (c⁻¹ • (st.mS - u • v)) (c⁻¹ • st.RS) s +
          agentQuadPotential (c⁻¹ • (st.mB - u • v)) (c⁻¹ • st.RB) b = _
      rw [h_ag_scale st.mS s st.RS st.posDef_RS u,
          h_ag_scale st.mB b st.RB st.posDef_RB u, mul_add]

    have h_round_scale : ∀ (a : RealTradePlan d) (s b : Fin d → ℝ) (u : ℝ),
        realPlanRoundCost x (Ψ_plan a u) s b =
          c⁻¹ * realPlanRoundCost x a (c • s + u • v) (c • b + u • v) := by
      intro a s b u
      have hS_dot : dotProduct x (c • s + u • v) = c * dotProduct x s + u := by
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hxv, mul_one]
      have hB_dot : dotProduct x (c • b + u • v) = c * dotProduct x b + u := by
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hxv, mul_one]
      have h_iff : (dotProduct x s ≤ (a.price - u) / c ∧ (a.price - u) / c ≤ dotProduct x b) ↔
          (dotProduct x (c • s + u • v) ≤ a.price ∧ a.price ≤ dotProduct x (c • b + u • v)) := by
        rw [hS_dot, hB_dot, le_div_iff₀ hc_pos, div_le_iff₀ hc_pos]
        constructor <;> intro h <;> constructor <;> [linarith [h.1]; linarith [h.2]; linarith [h.1]; linarith [h.2]]
      unfold realPlanRoundCost
      dsimp only
      rw [hΨ_price, hΨ_succ1, hΨ_succ0]
      by_cases h_tr : dotProduct x s ≤ (a.price - u) / c ∧ (a.price - u) / c ≤ dotProduct x b
      · have h_tr' := h_iff.mp h_tr
        rw [if_pos h_tr, if_pos h_tr', h_tr_scale a.succ1 s b u]
        ring
      · have h_tr' : ¬(dotProduct x (c • s + u • v) ≤ a.price ∧
            a.price ≤ dotProduct x (c • b + u • v)) := fun h => h_tr (h_iff.mpr h)
        rw [if_neg h_tr, if_neg h_tr', h_tr_scale a.succ0 s b u, hS_dot, hB_dot]
        have h_diff : (c * dotProduct x b + u) - (c * dotProduct x s + u) =
            c * (dotProduct x b - dotProduct x s) := by ring
        rw [h_diff, ← mul_zero c, ← mul_max_of_nonneg _ _ hc_pos.le, mul_zero]
        field_simp [hc_pos.ne']

    -- Boundedness and continuity of smoothed payoff g_a^ε(w) = ∫ u, realPlanExcessCost ... (Ψ_plan a u) w ∂μU
    let clamp : ℝ → ℝ := fun u => max (-r_ε) (min r_ε u)
    have hclamp_cont : Continuous clamp :=
      continuous_const.max (continuous_const.min continuous_id)
    have hclamp_mem : ∀ u : ℝ, clamp u ∈ I_ε := by
      intro u
      refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    have hclamp_eq : ∀ u ∈ I_ε, clamp u = u := by
      intro u hu
      dsimp [clamp]
      rw [min_eq_right hu.2, max_eq_right hu.1]
    have hclamp_ae : ∀ᵐ u ∂μU, clamp u = u := by
      filter_upwards [ae_iff.mpr hIε_null] with u hu
      exact hclamp_eq u hu

    -- Uniform bound of realPlanRoundCost and realPlanExcessCost along clamped u for fixed a
    have h_round_int_u : ∀ (a : RealTradePlan d) (w : UnitBallPair d),
        Integrable (fun u : ℝ => realPlanRoundCost x (Ψ_plan a u) w.seller w.buyer) μU := by
      intro a w
      have h_m : Measurable (fun u : ℝ => realPlanRoundCost x (Ψ_plan a u) w.seller w.buyer) :=
        (measurable_realPlanRoundCost_joint x).comp
          ((hΨ_plan_cont a).measurable.prodMk measurable_const)
      let br1_c : C(Set.Icc (-r_ε) r_ε, ℝ) :=
        ⟨fun u => (2 ^ 10 : ℝ) *
            tradeQuadPotential (Ψ_state a.succ1 u.1).mS (Ψ_state a.succ1 u.1).mB
              (Ψ_state a.succ1 u.1).RS (Ψ_state a.succ1 u.1).RB w.seller w.buyer,
         continuous_const.mul ((continuous_tradeQuadPotential_pd d).comp
           (((hΨ_state_cont a.succ1).comp continuous_subtype_val).prodMk continuous_const))⟩
      let br0_c : C(Set.Icc (-r_ε) r_ε, ℝ) :=
        ⟨fun u => max (dotProduct x w.buyer - dotProduct x w.seller) 0 +
            (2 ^ 10 : ℝ) *
              tradeQuadPotential (Ψ_state a.succ0 u.1).mS (Ψ_state a.succ0 u.1).mB
                (Ψ_state a.succ0 u.1).RS (Ψ_state a.succ0 u.1).RB w.seller w.buyer,
         continuous_const.add (continuous_const.mul ((continuous_tradeQuadPotential_pd d).comp
           (((hΨ_state_cont a.succ0).comp continuous_subtype_val).prodMk continuous_const)))⟩
      haveI : CompactSpace (Set.Icc (-r_ε) r_ε) := isCompact_iff_compactSpace.mp isCompact_Icc
      refine Integrable.of_bound h_m.aestronglyMeasurable (max ‖br1_c‖ ‖br0_c‖) ?_
      filter_upwards [ae_iff.mpr hIε_null] with u hu_in
      unfold realPlanRoundCost
      dsimp only
      rw [hΨ_price, hΨ_succ1, hΨ_succ0]
      split_ifs
      · exact (ContinuousMap.norm_coe_le_norm br1_c ⟨u, hu_in⟩).trans (le_max_left _ _)
      · exact (ContinuousMap.norm_coe_le_norm br0_c ⟨u, hu_in⟩).trans (le_max_right _ _)

    -- Continuity of g_a^ε on UnitBallPair d via dominated convergence (`continuousAt_of_dominated`)
    have h_smoothed_cont : ∀ a : RealTradePlan d,
        Continuous (fun w : UnitBallPair d =>
          ∫ u, realPlanExcessCost mS mB RS RB x (Ψ_plan a u) w ∂μU) := by
      intro a
      let br1_uw : C(UnitBallPair d × ℝ, ℝ) :=
        ⟨fun wu => (2 ^ 10 : ℝ) *
            tradeQuadPotential (Ψ_state a.succ1 (clamp wu.2)).mS (Ψ_state a.succ1 (clamp wu.2)).mB
              (Ψ_state a.succ1 (clamp wu.2)).RS (Ψ_state a.succ1 (clamp wu.2)).RB
              wu.1.seller wu.1.buyer -
            (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB wu.1.seller wu.1.buyer,
         (continuous_const.mul ((continuous_tradeQuadPotential_pd d).comp
           (((hΨ_state_cont a.succ1).comp (hclamp_cont.comp continuous_snd)).prodMk
             continuous_fst))).sub
           (continuous_const.mul
             ((continuous_tradeQuadPotential_fixed mS mB RS RB).comp continuous_fst))⟩
      let br0_uw : C(UnitBallPair d × ℝ, ℝ) :=
        ⟨fun wu => max (dotProduct x wu.1.buyer - dotProduct x wu.1.seller) 0 +
            (2 ^ 10 : ℝ) *
              tradeQuadPotential (Ψ_state a.succ0 (clamp wu.2)).mS (Ψ_state a.succ0 (clamp wu.2)).mB
                (Ψ_state a.succ0 (clamp wu.2)).RS (Ψ_state a.succ0 (clamp wu.2)).RB
                wu.1.seller wu.1.buyer -
            (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB wu.1.seller wu.1.buyer,
         ((((((continuous_dotProduct_buyer x).comp continuous_fst).sub
              ((continuous_dotProduct_seller x).comp continuous_fst)).max continuous_const)).add
           (continuous_const.mul ((continuous_tradeQuadPotential_pd d).comp
             (((hΨ_state_cont a.succ0).comp (hclamp_cont.comp continuous_snd)).prodMk
               continuous_fst)))).sub
           (continuous_const.mul
             ((continuous_tradeQuadPotential_fixed mS mB RS RB).comp continuous_fst))⟩
      have h_br1_bdd : IsCompact ((Set.univ : Set (UnitBallPair d)) ×ˢ (Set.Icc (-r_ε) r_ε)) :=
        isCompact_univ.prod isCompact_Icc
      obtain ⟨M1, hM1⟩ := h_br1_bdd.bddAbove_image (continuous_norm.comp br1_uw.continuous).continuousOn
      obtain ⟨M0, hM0⟩ := h_br1_bdd.bddAbove_image (continuous_norm.comp br0_uw.continuous).continuousOn
      set B_a : ℝ := max (max M1 M0) 0

      rw [continuous_iff_continuousAt]
      intro w₀
      refine continuousAt_of_dominated (bound := fun _ : ℝ => B_a) ?_ ?_ (integrable_const B_a) ?_
      · refine Filter.Eventually.of_forall fun w => ?_
        have hm : Measurable (fun u : ℝ => realPlanExcessCost mS mB RS RB x (Ψ_plan a u) w) :=
          ((measurable_realPlanRoundCost_joint x).comp
            ((hΨ_plan_cont a).measurable.prodMk measurable_const)).sub measurable_const
        exact hm.aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun w => ?_
        filter_upwards [hclamp_ae, ae_iff.mpr hIε_null] with u hu_cl hu_mem
        have h_wumem : (w, u) ∈ (Set.univ : Set (UnitBallPair d)) ×ˢ Set.Icc (-r_ε) r_ε :=
          ⟨Set.mem_univ w, hu_mem⟩
        unfold realPlanExcessCost realPlanRoundCost
        dsimp only
        rw [hΨ_price, hΨ_succ1, hΨ_succ0]
        split_ifs
        · have h_eq : (2 ^ 10 : ℝ) *
              tradeQuadPotential (Ψ_state a.succ1 u).mS (Ψ_state a.succ1 u).mB
                (Ψ_state a.succ1 u).RS (Ψ_state a.succ1 u).RB w.seller w.buyer -
              (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer = br1_uw (w, u) := by
            dsimp [br1_uw]; rw [hu_cl]
          rw [h_eq]
          exact (hM1 ⟨(w, u), h_wumem, rfl⟩).trans ((le_max_left M1 M0).trans (le_max_left _ _))
        · have h_eq : max (dotProduct x w.buyer - dotProduct x w.seller) 0 +
              (2 ^ 10 : ℝ) *
                tradeQuadPotential (Ψ_state a.succ0 u).mS (Ψ_state a.succ0 u).mB
                  (Ψ_state a.succ0 u).RS (Ψ_state a.succ0 u).RB w.seller w.buyer -
              (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer = br0_uw (w, u) := by
            dsimp [br0_uw]; rw [hu_cl]
          rw [h_eq]
          exact (hM0 ⟨(w, u), h_wumem, rfl⟩).trans ((le_max_right M1 M0).trans (le_max_left _ _))
      · -- Pointwise continuity at w₀ for all u outside the two-point set {a.price - c * S₀, a.price - c * B₀}
        let u₁ : ℝ := a.price - c * dotProduct x w₀.seller
        let u₂ : ℝ := a.price - c * dotProduct x w₀.buyer
        have h_pair_vol : volume ({u₁, u₂} : Set ℝ) = 0 := by
          rw [Set.insert_eq, measure_union_null Real.volume_singleton Real.volume_singleton]
        have h_pair_μU : μU ({u₁, u₂} : Set ℝ) = 0 :=
          withDensity_absolutelyContinuous volume _ h_pair_vol
        have h_pair_ae : ∀ᵐ u ∂μU, u ∉ ({u₁, u₂} : Set ℝ) := by
          rw [ae_iff]
          have h_eq_set : {u : ℝ | ¬u ∉ ({u₁, u₂} : Set ℝ)} = {u₁, u₂} := by
            ext u; exact Classical.not_not
          rw [h_eq_set]
          exact h_pair_μU
        filter_upwards [h_pair_ae] with u hu_not
        have hu₁ : u ≠ u₁ := fun h => hu_not (Set.mem_insert_iff.mpr (Or.inl h))
        have hu₂ : u ≠ u₂ := fun h =>
          hu_not (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h)))
        set p_u : ℝ := (a.price - u) / c
        have hp_u_eq : (a.price - u) / c = p_u := rfl
        have hS_ne : dotProduct x w₀.seller ≠ p_u := by
          intro h_eq
          apply hu₁
          dsimp [p_u] at h_eq
          have := (eq_div_iff hc_pos.ne').mp h_eq
          dsimp [u₁]; linarith
        have hB_ne : dotProduct x w₀.buyer ≠ p_u := by
          intro h_eq
          apply hu₂
          dsimp [p_u] at h_eq
          have := (eq_div_iff hc_pos.ne').mp h_eq
          dsimp [u₂]; linarith
        have h_br1_w : Continuous (fun w : UnitBallPair d =>
            (2 ^ 10 : ℝ) *
              tradeQuadPotential (Ψ_state a.succ1 u).mS (Ψ_state a.succ1 u).mB
                (Ψ_state a.succ1 u).RS (Ψ_state a.succ1 u).RB w.seller w.buyer -
            (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer) :=
          (continuous_const.mul
            (continuous_tradeQuadPotential_fixed (Ψ_state a.succ1 u).mS (Ψ_state a.succ1 u).mB
              (Ψ_state a.succ1 u).RS (Ψ_state a.succ1 u).RB)).sub
            (continuous_const.mul (continuous_tradeQuadPotential_fixed mS mB RS RB))
        have h_br0_w : Continuous (fun w : UnitBallPair d =>
            max (dotProduct x w.buyer - dotProduct x w.seller) 0 +
              (2 ^ 10 : ℝ) *
                tradeQuadPotential (Ψ_state a.succ0 u).mS (Ψ_state a.succ0 u).mB
                  (Ψ_state a.succ0 u).RS (Ψ_state a.succ0 u).RB w.seller w.buyer -
            (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB w.seller w.buyer) :=
          ((((continuous_dotProduct_buyer x).sub (continuous_dotProduct_seller x)).max
            continuous_const).add
            (continuous_const.mul
              (continuous_tradeQuadPotential_fixed (Ψ_state a.succ0 u).mS (Ψ_state a.succ0 u).mB
                (Ψ_state a.succ0 u).RS (Ψ_state a.succ0 u).RB))).sub
            (continuous_const.mul (continuous_tradeQuadPotential_fixed mS mB RS RB))
        by_cases h_tr0 : dotProduct x w₀.seller ≤ p_u ∧ p_u ≤ dotProduct x w₀.buyer
        · have h_lt1 : dotProduct x w₀.seller < p_u := lt_of_le_of_ne h_tr0.1 hS_ne
          have h_lt2 : p_u < dotProduct x w₀.buyer := lt_of_le_of_ne h_tr0.2 hB_ne.symm
          let U_open : Set (UnitBallPair d) :=
            {w | dotProduct x w.seller < p_u ∧ p_u < dotProduct x w.buyer}
          have hU_open : IsOpen U_open :=
            (isOpen_lt (continuous_dotProduct_seller x) continuous_const).inter
              (isOpen_lt continuous_const (continuous_dotProduct_buyer x))
          refine h_br1_w.continuousAt.congr ?_
          filter_upwards [hU_open.mem_nhds ⟨h_lt1, h_lt2⟩] with w hw
          have hw_le : dotProduct x w.seller ≤ p_u ∧ p_u ≤ dotProduct x w.buyer :=
            ⟨hw.1.le, hw.2.le⟩
          unfold realPlanExcessCost
          congr 1
          unfold realPlanRoundCost
          dsimp only
          rw [hΨ_price, hΨ_succ1, hΨ_succ0, hp_u_eq, if_pos hw_le]
        · have h_out : p_u < dotProduct x w₀.seller ∨ dotProduct x w₀.buyer < p_u := by
            rcases not_and_or.mp h_tr0 with h1 | h2
            · exact Or.inl (lt_of_not_ge h1)
            · exact Or.inr (lt_of_not_ge h2)
          let V_open : Set (UnitBallPair d) :=
            {w | p_u < dotProduct x w.seller ∨ dotProduct x w.buyer < p_u}
          have hV_open : IsOpen V_open :=
            (isOpen_lt continuous_const (continuous_dotProduct_seller x)).union
              (isOpen_lt (continuous_dotProduct_buyer x) continuous_const)
          refine h_br0_w.continuousAt.congr ?_
          filter_upwards [hV_open.mem_nhds h_out] with w hw
          have hw_not : ¬(dotProduct x w.seller ≤ p_u ∧ p_u ≤ dotProduct x w.buyer) := by
            rintro ⟨h1, h2⟩
            rcases hw with ha | hb <;> linarith
          unfold realPlanExcessCost
          congr 1
          unfold realPlanRoundCost
          dsimp only
          rw [hΨ_price, hΨ_succ1, hΨ_succ0, hp_u_eq, if_neg hw_not]

    -- Define base_ε and convex hull G_ε ⊆ C(UnitBallPair d, ℝ)
    let base_ε : RealTradePlan d → C(UnitBallPair d, ℝ) := fun a =>
      ⟨fun w => ∫ u, realPlanExcessCost mS mB RS RB x (Ψ_plan a u) w ∂μU, h_smoothed_cont a⟩
    let G_ε : Set C(UnitBallPair d, ℝ) := convexHull ℝ (Set.range base_ε)

    -- Perturbed hidden-pair map T_pair : ℝ × UnitBallPair d → UnitBallPair d (using clamped u)
    let T_pair : ℝ × UnitBallPair d → UnitBallPair d := fun uw =>
      let u' := clamp uw.1
      let s' : Fin d → ℝ := c • uw.2.seller + u' • v
      let b' : Fin d → ℝ := c • uw.2.buyer + u' • v
      ⟨WithLp.toLp 2 (WithLp.toLp 2 s', WithLp.toLp 2 b'), by
        have hu_mem := hclamp_mem uw.1
        have hu_abs : |u'| ≤ r_ε := abs_le.mpr ⟨by linarith [hu_mem.1], hu_mem.2⟩
        have hs' : vecL2Norm s' ≤ 1 :=
          h_ball ε u' hε0 hε1 hu_abs uw.2.seller (vecL2Norm_unitBallPair_seller uw.2)
        have hb' : vecL2Norm b' ≤ 1 :=
          h_ball ε u' hε0 hε1 hu_abs uw.2.buyer (vecL2Norm_unitBallPair_buyer uw.2)
        rw [vecL2Norm_eq_eucNorm] at hs' hb'
        exact ⟨hs', hb'⟩⟩
    have hT_cont : Continuous T_pair := by
      refine Continuous.subtype_mk ?_ _
      refine (WithLp.prod_continuous_toLp 2 (EucVec d) (EucVec d)).comp (Continuous.prodMk ?_ ?_)
      · refine (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp (continuous_pi fun i => ?_)
        exact (continuous_const.mul
          ((continuous_apply i).comp ((continuous_unitBallPair_seller d).comp continuous_snd))).add
          ((hclamp_cont.comp continuous_fst).mul continuous_const)
      · refine (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp (continuous_pi fun i => ?_)
        exact (continuous_const.mul
          ((continuous_apply i).comp ((continuous_unitBallPair_buyer d).comp continuous_snd))).add
          ((hclamp_cont.comp continuous_fst).mul continuous_const)

    -- Prior pushforward bound: ∀ ρ, ⨅ a, ∫ base_ε a ∂ρ ≤ v_B / c + C0 * ε
    have h_prior_bound : ∀ ρ : ProbabilityMeasure (UnitBallPair d),
        (⨅ a : RealTradePlan d,
          ((∫ w, (base_ε a) w ∂(ρ : Measure (UnitBallPair d)) : ℝ) : EReal)) ≤
          ((v_B / c + C0 * ε : ℝ) : EReal) := by
      intro ρ
      let μ : Measure (UnitBallPair d) := (ρ : Measure (UnitBallPair d))
      let ν_prod : Measure (ℝ × UnitBallPair d) := μU.prod μ
      haveI : IsProbabilityMeasure ν_prod := inferInstance
      let ρ_ε : ProbabilityMeasure (UnitBallPair d) :=
        ⟨ν_prod.map T_pair, Measure.isProbabilityMeasure_map hT_cont.measurable.aemeasurable⟩

      have h_plan_ineq : ∀ a : RealTradePlan d,
          (∫ w, (base_ε a) w ∂μ) ≤
            c⁻¹ * (∫ w', realPlanExcessCost mS mB RS RB x a w' ∂(ρ_ε : Measure (UnitBallPair d))) +
              C0 * ε := by
        intro a
        let F_cl : ℝ × UnitBallPair d → ℝ :=
          fun uw => realPlanExcessCost mS mB RS RB x (Ψ_plan a (clamp uw.1)) uw.2
        let drift_cl : ℝ × UnitBallPair d → ℝ :=
          fun uw => (2 ^ 10 : ℝ) *
            (c⁻¹ * tradeQuadPotential mS mB RS RB (T_pair uw).seller (T_pair uw).buyer -
              tradeQuadPotential mS mB RS RB uw.2.seller uw.2.buyer)
        have hF_meas : Measurable F_cl :=
          ((measurable_realPlanRoundCost_joint x).comp
            (((hΨ_plan_cont a).comp hclamp_cont).measurable.comp measurable_fst |>.prodMk
              measurable_snd)).sub
            (continuous_const.mul
              ((continuous_tradeQuadPotential_fixed mS mB RS RB).comp continuous_snd)).measurable
        have hdr_cont : Continuous drift_cl :=
          continuous_const.mul
            ((continuous_const.mul
              ((continuous_tradeQuadPotential_fixed mS mB RS RB).comp hT_cont)).sub
              ((continuous_tradeQuadPotential_fixed mS mB RS RB).comp continuous_snd))
        have hdr_bd : ∀ uw : ℝ × UnitBallPair d, |drift_cl uw| ≤ C0 * ε := by
          intro uw
          have hu_mem := hclamp_mem uw.1
          have hu_abs : |clamp uw.1| ≤ r_ε := abs_le.mpr ⟨by linarith [hu_mem.1], hu_mem.2⟩
          exact h_drift ε (clamp uw.1) hε0 hε1 hu_abs
            uw.2.seller uw.2.buyer
            (vecL2Norm_unitBallPair_seller uw.2) (vecL2Norm_unitBallPair_buyer uw.2)
        have hdr_int : Integrable drift_cl ν_prod :=
          Integrable.of_bound hdr_cont.measurable.aestronglyMeasurable (C0 * ε)
            (Filter.Eventually.of_forall hdr_bd)
        have h_T_int : Integrable
            (fun uw : ℝ × UnitBallPair d => realPlanExcessCost mS mB RS RB x a (T_pair uw)) ν_prod := by
          have h_base_int := integrable_realPlanExcessCost mS mB RS RB x a (ρ_ε : Measure (UnitBallPair d))
          exact (integrable_map_measure h_base_int.aestronglyMeasurable
            hT_cont.measurable.aemeasurable).mp h_base_int
        have hF_decomp : ∀ uw : ℝ × UnitBallPair d,
            F_cl uw = c⁻¹ * realPlanExcessCost mS mB RS RB x a (T_pair uw) + drift_cl uw := by
          intro uw
          dsimp [F_cl, drift_cl]
          unfold realPlanExcessCost
          rw [h_round_scale a uw.2.seller uw.2.buyer (clamp uw.1)]
          dsimp [T_pair, UnitBallPair.seller, UnitBallPair.buyer]
          ring
        have hF_int : Integrable F_cl ν_prod := by
          have h_eq_fn : F_cl =
              fun uw => c⁻¹ * realPlanExcessCost mS mB RS RB x a (T_pair uw) + drift_cl uw :=
            funext hF_decomp
          rw [h_eq_fn]
          exact (h_T_int.const_mul c⁻¹).add hdr_int

        have h_g_eq : ∀ w : UnitBallPair d, (base_ε a) w = ∫ u, F_cl (u, w) ∂μU := by
          intro w
          refine integral_congr_ae ?_
          filter_upwards [hclamp_ae] with u hu
          dsimp [F_cl]
          rw [hu]
        have h_fub : (∫ w, (base_ε a) w ∂μ) = ∫ uw, F_cl uw ∂ν_prod := by
          simp_rw [h_g_eq]
          exact (integral_prod_symm F_cl hF_int).symm
        have h_map_int : (∫ w', realPlanExcessCost mS mB RS RB x a w' ∂(ρ_ε : Measure (UnitBallPair d))) =
            ∫ uw, realPlanExcessCost mS mB RS RB x a (T_pair uw) ∂ν_prod :=
          integral_map hT_cont.measurable.aemeasurable
            (integrable_realPlanExcessCost mS mB RS RB x a (ρ_ε : Measure (UnitBallPair d))).aestronglyMeasurable
        have hdr_le : (∫ uw, drift_cl uw ∂ν_prod) ≤ C0 * ε := by
          calc (∫ uw, drift_cl uw ∂ν_prod)
              ≤ ∫ _uw, C0 * ε ∂ν_prod :=
                  integral_mono hdr_int (integrable_const _) fun uw => (le_abs_self _).trans (hdr_bd uw)
            _ = C0 * ε := by rw [integral_const, probReal_univ, one_smul]
        rw [h_fub]
        have h_eq_fn : F_cl =
            fun uw => c⁻¹ * realPlanExcessCost mS mB RS RB x a (T_pair uw) + drift_cl uw :=
          funext hF_decomp
        rw [h_eq_fn, integral_add (h_T_int.const_mul c⁻¹) hdr_int, integral_const_mul, ← h_map_int]
        linarith

      -- Deduce inf_a ∫ base_ε a ∂μ ≤ v_B / c + C0 * ε from inf_a ∫ f_a ∂ρ_ε ≤ v_B
      have h_vb_le :
          (⨅ a : RealTradePlan d,
            ((∫ w', realPlanExcessCost mS mB RS RB x a w' ∂(ρ_ε : Measure (UnitBallPair d)) : ℝ) : EReal)) ≤
            (v_B : EReal) := by
        rw [hvB_coe]
        exact le_iSup (fun ρ' : ProbabilityMeasure (UnitBallPair d) =>
          ⨅ a : RealTradePlan d,
            ((∫ w', realPlanExcessCost mS mB RS RB x a w' ∂(ρ' : Measure (UnitBallPair d)) : ℝ) : EReal)) ρ_ε
      by_contra h_not
      have h_gt := lt_of_not_ge h_not
      -- Pick any ξ > 0 and a plan a_ξ with ∫ f_{a_ξ} ∂ρ_ε < v_B + c * ξ
      have h_ex_plan : ∀ ξ : ℝ, 0 < ξ → ∃ a : RealTradePlan d,
          (∫ w', realPlanExcessCost mS mB RS RB x a w' ∂(ρ_ε : Measure (UnitBallPair d))) <
            v_B + c * ξ := by
        intro ξ hξ
        have h_lt_er :
            (⨅ a : RealTradePlan d,
              ((∫ w', realPlanExcessCost mS mB RS RB x a w' ∂(ρ_ε : Measure (UnitBallPair d)) : ℝ) : EReal)) <
              ((v_B + c * ξ : ℝ) : EReal) :=
          lt_of_le_of_lt h_vb_le (EReal.coe_lt_coe_iff.mpr (by nlinarith))
        rw [iInf_lt_iff] at h_lt_er
        rcases h_lt_er with ⟨a, ha⟩
        exact ⟨a, EReal.coe_lt_coe_iff.mp ha⟩
      -- Note inf_a ∫ base_ε a ∂μ > v_B / c + C0 * ε implies ∃ r > v_B / c + C0 * ε below the infimum
      obtain ⟨r_mid, hr_gt, hr_le_inf⟩ := exists_between h_gt
      have hr_ne_bot : r_mid ≠ ⊥ := by
        intro hb; rw [hb] at hr_gt; exact not_lt_bot hr_gt
      have hr_ne_top : r_mid ≠ ⊤ := by
        intro ht
        have h0_le := hr_le_inf.le.trans (iInf_le _ (0, st₀, st₀))
        rw [ht] at h0_le
        exact not_top_lt (lt_of_le_of_lt h0_le (EReal.coe_lt_top _))
      set r_val : ℝ := r_mid.toReal
      have hr_coe : (r_val : EReal) = r_mid := EReal.coe_toReal hr_ne_top hr_ne_bot
      rw [← hr_coe, EReal.coe_lt_coe_iff] at hr_gt
      set ξ₀ : ℝ := (r_val - (v_B / c + C0 * ε)) / 2
      have hξ₀ : 0 < ξ₀ := by dsimp [ξ₀]; linarith
      obtain ⟨a_ξ, ha_ξ⟩ := h_ex_plan ξ₀ hξ₀
      have h_up := h_plan_ineq a_ξ
      have h_div_id : c⁻¹ * (v_B + c * ξ₀) = v_B / c + ξ₀ := by field_simp [hc_pos.ne']
      have h_lt_r : (∫ w, (base_ε a_ξ) w ∂μ) < r_val := by
        have h_mul := mul_lt_mul_of_pos_left ha_ξ (inv_pos.mpr hc_pos)
        rw [h_div_id] at h_mul
        dsimp [ξ₀] at h_mul
        linarith
      have h_ge_r : (r_val : EReal) ≤ ((∫ w, (base_ε a_ξ) w ∂μ : ℝ) : EReal) := by
        rw [hr_coe]; exact hr_le_inf.le.trans (iInf_le _ a_ξ)
      linarith [EReal.coe_le_coe_iff.mp h_ge_r, h_lt_r]

    -- Apply Sion exchange (`cor_sion_affine`) to G_ε
    have h_exch_ε :
        (⨅ g : G_ε, ⨆ w : UnitBallPair d, (g.1 w : EReal)) ≤
          ((v_B / c + C0 * ε : ℝ) : EReal) := by
      rw [sion_convexHull_exchange base_ε]
      exact iSup_le h_prior_bound

    -- Since v_B ≤ 0 and 0 < c = 1 - ε < 1, v_B / c ≤ v_B, hence v_B / c + C0 * ε < v_B + η
    have hvB_div_le : v_B / c ≤ v_B := by
      rw [div_le_iff₀ hc_pos]
      have hc_le1 : c ≤ 1 := by dsimp [c]; linarith
      nlinarith
    have h_lt_target :
        (⨅ g : G_ε, ⨆ w : UnitBallPair d, (g.1 w : EReal)) < ((v_B + η : ℝ) : EReal) :=
      lt_of_le_of_lt h_exch_ε (EReal.coe_lt_coe_iff.mpr (by linarith))

    rw [iInf_lt_iff] at h_lt_target
    rcases h_lt_target with ⟨g, hg_lt⟩
    obtain ⟨N, hN, α, as, hα_nn, hα_sum, hg_eq⟩ := mem_convexHull_range_fin base_ε g.2

    -- Construct the regular mixture lottery Q implementing g
    let f_i : Fin N → ℝ → ENNReal := fun i =>
      (Set.Icc (((as i).price - r_ε) / c) (((as i).price + r_ε) / c)).indicator
        fun _ => ENNReal.ofReal (c / (2 * r_ε))
    have hf_i_meas : ∀ i : Fin N, Measurable (f_i i) := fun i =>
      measurable_const.indicator isClosed_Icc.measurableSet
    have hf_i_map : ∀ i : Fin N,
        μU.map (fun u => ((as i).price - u) / c) = volume.withDensity (f_i i) := fun i =>
      affine_uniform_pushforward r_ε c (as i).price hr_pos hc_pos
    have hN_univ : (Finset.univ : Finset (Fin N)).Nonempty :=
      ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    set p_min : ℝ := Finset.univ.inf' hN_univ fun i : Fin N => ((as i).price - r_ε) / c
    set p_max : ℝ := Finset.univ.sup' hN_univ fun i : Fin N => ((as i).price + r_ε) / c
    have hp_le : p_min ≤ p_max := by
      let i0 : Fin N := ⟨0, hN⟩
      have h1 : p_min ≤ ((as i0).price - r_ε) / c :=
        Finset.inf'_le (f := fun j : Fin N => ((as j).price - r_ε) / c) (Finset.mem_univ i0)
      have h2 : ((as i0).price + r_ε) / c ≤ p_max :=
        Finset.le_sup' (f := fun j : Fin N => ((as j).price + r_ε) / c) (Finset.mem_univ i0)
      have h_mid : ((as i0).price - r_ε) / c ≤ ((as i0).price + r_ε) / c :=
        div_le_div_of_nonneg_right (by linarith) hc_pos.le
      linarith
    have hf_i_supp : ∀ (i : Fin N) (p : ℝ), p ∉ Set.Icc p_min p_max → f_i i p = 0 := by
      intro i p hp_out
      apply Set.indicator_of_notMem
      intro hp_in
      apply hp_out
      refine ⟨(Finset.inf'_le (f := fun j : Fin N => ((as j).price - r_ε) / c)
                (Finset.mem_univ i)).trans hp_in.1,
              hp_in.2.trans
                (Finset.le_sup' (f := fun j : Fin N => ((as j).price + r_ε) / c)
                  (Finset.mem_univ i))⟩

    obtain ⟨Q, f_dens, K_st, hf_m, hK, hQ_eval, hmap, hbd, hsp, hK0⟩ :=
      mixture_lottery_props hN mS mB RS RB x α hα_nn hα_sum μU I_ε isCompact_Icc hIε_null
        (fun i => Ψ_state (as i).succ0) (fun i => Ψ_state (as i).succ1)
        (fun i => hΨ_state_cont (as i).succ0) (fun i => hΨ_state_cont (as i).succ1)
        (fun i u => ((as i).price - u) / c)
        (fun i => (continuous_const.sub continuous_id).div_const c)
        f_i hf_i_meas hf_i_map
        (c / (2 * r_ε)) (by positivity)
        (fun i p => by
          dsimp [f_i]
          by_cases hp : p ∈ Set.Icc (((as i).price - r_ε) / c) (((as i).price + r_ε) / c) <;>
            simp [hp])
        p_min p_max hp_le hf_i_supp
        (fun i w => h_round_int_u (as i) w)

    have hQ_eq_g : ∀ w : UnitBallPair d,
        lotteryExpectedExcessCost mS mB RS RB x Q w = (g.1 w : EReal) := by
      intro w
      rw [hQ_eval w]
      congr 1
      have := congr_arg (fun f : C(UnitBallPair d, ℝ) => f w) hg_eq
      simpa [ContinuousMap.coe_sum, Pi.smul_apply, smul_eq_mul, base_ε, Ψ_plan] using this.symm

    refine ⟨Q, f_dens, c / (2 * r_ε), p_min, p_max, K_st, hf_m, by positivity, hp_le, hK,
      ?_, hmap, hbd, hsp, hK0⟩
    simpa [hQ_eq_g] using hg_lt

end TraceSqrt
