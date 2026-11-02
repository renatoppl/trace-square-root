import TraceSqrt.Defs
import TraceSqrt.Trade.Displacement

set_option maxHeartbeats 4000000

/-!
# Claim D.4: Uniform Bound on the Trade Profile (`cl:trade-profile`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Appendix D.1, Claim D.4 `cl:trade-profile`).
-/

namespace TraceSqrt

/-- Detailed tail, central-interval, and half-line integral bounds on the trade profile `α(p)`
for seller and buyer marginals (used to establish Claim D.4 and Eqs. (38)–(39)). -/
theorem lem_trade_profile_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S B : Ω → ℝ) (hS : MeasureTheory.MemLp S 2 μ) (hB : MeasureTheory.MemLp B 2 μ) :
    let muS := ∫ ω, S ω ∂μ
    let muB := ∫ ω, B ω ∂μ
    let sigS := rvStdDev S μ
    let sigB := rvStdDev B μ
    let Dbar := supInfoDrop S B μ
    (∀ p : ℝ, p < muS → tradeProfile S B μ p ≤ 2 * sigS * Dbar / (muS - p) ^ 2) ∧
    (0 < sigS → ∀ p : ℝ, |p - muS| ≤ sigS / 3 →
      tradeProfile S B μ p ≤ (225 / 2 : ℝ) * Dbar / sigS) ∧
    MeasureTheory.IntegrableOn (tradeProfile S B μ) (Set.Iic (muS + sigS / 3)) MeasureTheory.volume ∧
    (∫ p in Set.Iic (muS + sigS / 3), tradeProfile S B μ p) ≤ 81 * Dbar ∧
    (∀ p : ℝ, muB < p → tradeProfile S B μ p ≤ 2 * sigB * Dbar / (p - muB) ^ 2) ∧
    (0 < sigB → ∀ p : ℝ, |p - muB| ≤ sigB / 3 →
      tradeProfile S B μ p ≤ (225 / 2 : ℝ) * Dbar / sigB) ∧
    MeasureTheory.IntegrableOn (tradeProfile S B μ) (Set.Ici (muB - sigB / 3)) MeasureTheory.volume ∧
    (∫ p in Set.Ici (muB - sigB / 3), tradeProfile S B μ p) ≤ 81 * Dbar :=
by
  have h_var_drop :
      ∀ (Z : Ω → ℝ), MeasureTheory.MemLp Z 2 μ →
        ∀ (E : Set Ω), MeasurableSet E →
          let muZ := ∫ ω, Z ω ∂μ
          let sigZ := rvStdDev Z μ
          let d := sigZ - (μ.real E * condStdDev Z μ E + μ.real Eᶜ * condStdDev Z μ Eᶜ)
          (0 ≤ d ∧ d ≤ sigZ) ∧
          (∫ ω in E, (Z ω - muZ) ∂μ) ^ 2 ≤ 2 * μ.real E * sigZ * d ∧
          (Real.sqrt (μ.real E) * sigZ -
            Real.sqrt (∫ ω in E, (Z ω - muZ) ^ 2 ∂μ)) ^ 2 ≤ 2 * sigZ * d := by
    intro Z hZ E hE
    set muZ : ℝ := ∫ ω, Z ω ∂μ
    set sigZ : ℝ := rvStdDev Z μ
    let W : Ω → ℝ := fun ω => Z ω - muZ
    have hW : MeasureTheory.MemLp W 2 μ := hZ.sub (MeasureTheory.memLp_const muZ)
    have hW2_int : MeasureTheory.Integrable (fun ω => (W ω) ^ 2) μ := hW.integrable_sq
    have hsigZ_nonneg : 0 ≤ sigZ := Real.sqrt_nonneg _
    have hsigZ_sq : sigZ ^ 2 = ∫ ω, (W ω) ^ 2 ∂μ := by
      calc sigZ ^ 2 = ProbabilityTheory.variance Z μ :=
             Real.sq_sqrt (ProbabilityTheory.variance_nonneg Z μ)
        _ = ∫ ω, (W ω) ^ 2 ∂μ :=
             ProbabilityTheory.variance_eq_integral hZ.aemeasurable
    have h_branch : ∀ (A : Set Ω), MeasurableSet A →
        (μ.real A * condStdDev Z μ A) ^ 2 =
          μ.real A * (∫ ω in A, (W ω) ^ 2 ∂μ) - (∫ ω in A, W ω ∂μ) ^ 2 := by
      intro A hA
      by_cases hμA : μ A = 0
      · have hqA : μ.real A = 0 := by simp [MeasureTheory.measureReal_def, hμA]
        have hrest : μ.restrict A = 0 := MeasureTheory.Measure.restrict_eq_zero.mpr hμA
        simp [hqA, hrest]
      · set ν := ProbabilityTheory.cond μ A
        haveI : MeasureTheory.IsProbabilityMeasure ν :=
          ProbabilityTheory.cond_isProbabilityMeasure hμA
        have h_le : ν ≤ (μ A)⁻¹ • μ := by
          rw [MeasureTheory.Measure.le_iff]
          intro t _
          rw [ProbabilityTheory.cond_apply hA, MeasureTheory.Measure.smul_apply, smul_eq_mul]
          gcongr
          exact Set.inter_subset_right
        have hZ_ν : MeasureTheory.MemLp Z 2 ν :=
          hZ.of_measure_le_smul (ENNReal.inv_ne_top.mpr hμA) h_le
        have hW_ν : MeasureTheory.MemLp W 2 ν := hZ_ν.sub (MeasureTheory.memLp_const muZ)
        have h_var1 : ProbabilityTheory.variance W ν =
            (∫ ω, (W ω) ^ 2 ∂ν) - (∫ ω, W ω ∂ν) ^ 2 := by
          simpa [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub hW_ν
        have h_var2 : ProbabilityTheory.variance W ν = (condStdDev Z μ A) ^ 2 := by
          rw [ProbabilityTheory.variance_sub_const hZ_ν.aestronglyMeasurable muZ]
          exact (Real.sq_sqrt (ProbabilityTheory.variance_nonneg Z ν)).symm
        have h_smul_ν : μ A • ν = μ.restrict A := by
          change μ A • ((μ A)⁻¹ • μ.restrict A) = μ.restrict A
          rw [smul_smul, ENNReal.mul_inv_cancel hμA (MeasureTheory.measure_ne_top μ A), one_smul]
        have h_int_A : ∀ g : Ω → ℝ, ∫ ω in A, g ω ∂μ = μ.real A * ∫ ω, g ω ∂ν := fun g => by
          rw [← h_smul_ν, MeasureTheory.integral_smul_measure, smul_eq_mul,
              MeasureTheory.measureReal_def]
        rw [h_int_A W, h_int_A (fun ω => (W ω) ^ 2)]
        linear_combination (μ.real A) ^ 2 * (h_var2.symm.trans h_var1)
    set q1 : ℝ := μ.real E
    set q0 : ℝ := μ.real Eᶜ
    set s1 : ℝ := condStdDev Z μ E
    set s0 : ℝ := condStdDev Z μ Eᶜ
    set m1 : ℝ := ∫ ω in E, W ω ∂μ
    set v1 : ℝ := ∫ ω in E, (W ω) ^ 2 ∂μ
    set m0 : ℝ := ∫ ω in Eᶜ, W ω ∂μ
    set v0 : ℝ := ∫ ω in Eᶜ, (W ω) ^ 2 ∂μ
    set d : ℝ := sigZ - (q1 * s1 + q0 * s0)
    have hq1 : 0 ≤ q1 := MeasureTheory.measureReal_nonneg
    have hq0 : 0 ≤ q0 := MeasureTheory.measureReal_nonneg
    have hs1 : 0 ≤ s1 := Real.sqrt_nonneg _
    have hs0 : 0 ≤ s0 := Real.sqrt_nonneg _
    have hv1 : 0 ≤ v1 := MeasureTheory.setIntegral_nonneg hE fun ω _ => sq_nonneg (W ω)
    have hv0 : 0 ≤ v0 := MeasureTheory.setIntegral_nonneg hE.compl fun ω _ => sq_nonneg (W ω)
    have hq_sum : q1 + q0 = 1 := MeasureTheory.probReal_add_probReal_compl hE
    have hv_sum : v1 + v0 = sigZ ^ 2 := by
      rw [hsigZ_sq]
      exact MeasureTheory.integral_add_compl hE hW2_int
    have hb1 : (q1 * s1) ^ 2 = q1 * v1 - m1 ^ 2 := h_branch E hE
    have hb0 : (q0 * s0) ^ 2 = q0 * v0 - m0 ^ 2 := h_branch Eᶜ hE.compl
    set rq1 : ℝ := Real.sqrt q1
    set rv1 : ℝ := Real.sqrt v1
    set rq0 : ℝ := Real.sqrt q0
    set rv0 : ℝ := Real.sqrt v0
    have hrq1_nn : 0 ≤ rq1 := Real.sqrt_nonneg _
    have hrv1_nn : 0 ≤ rv1 := Real.sqrt_nonneg _
    have hrq0_nn : 0 ≤ rq0 := Real.sqrt_nonneg _
    have hrv0_nn : 0 ≤ rv0 := Real.sqrt_nonneg _
    have hrq1_sq : rq1 ^ 2 = q1 := Real.sq_sqrt hq1
    have hrv1_sq : rv1 ^ 2 = v1 := Real.sq_sqrt hv1
    have hrq0_sq : rq0 ^ 2 = q0 := Real.sq_sqrt hq0
    have hrv0_sq : rv0 ^ 2 = v0 := Real.sq_sqrt hv0
    have hqs1_le : q1 * s1 ≤ rq1 * rv1 := by
      have h_nn1 : 0 ≤ q1 * s1 := mul_nonneg hq1 hs1
      have h_nn2 : 0 ≤ rq1 * rv1 := mul_nonneg hrq1_nn hrv1_nn
      have h_sq : (q1 * s1) ^ 2 ≤ (rq1 * rv1) ^ 2 := by
        calc (q1 * s1) ^ 2 = q1 * v1 - m1 ^ 2 := hb1
          _ ≤ q1 * v1 := by linarith [sq_nonneg m1]
          _ = rq1 ^ 2 * rv1 ^ 2 := by rw [hrq1_sq, hrv1_sq]
          _ = (rq1 * rv1) ^ 2 := by ring
      nlinarith
    have hqs0_le : q0 * s0 ≤ rq0 * rv0 := by
      have h_nn1 : 0 ≤ q0 * s0 := mul_nonneg hq0 hs0
      have h_nn2 : 0 ≤ rq0 * rv0 := mul_nonneg hrq0_nn hrv0_nn
      have h_sq : (q0 * s0) ^ 2 ≤ (rq0 * rv0) ^ 2 := by
        calc (q0 * s0) ^ 2 = q0 * v0 - m0 ^ 2 := hb0
          _ ≤ q0 * v0 := by linarith [sq_nonneg m0]
          _ = rq0 ^ 2 * rv0 ^ 2 := by rw [hrq0_sq, hrv0_sq]
          _ = (rq0 * rv0) ^ 2 := by ring
      nlinarith
    have hd_le : d ≤ sigZ := by
      nlinarith [mul_nonneg hq1 hs1, mul_nonneg hq0 hs0]
    have hd_nn : 0 ≤ d := by
      have h_lagrange : (rq1 * rv1 + rq0 * rv0) ^ 2 ≤ sigZ ^ 2 := by
        have h_id : (rq1 * rv1 + rq0 * rv0) ^ 2 + (rq1 * rv0 - rq0 * rv1) ^ 2 =
            (rq1 ^ 2 + rq0 ^ 2) * (rv1 ^ 2 + rv0 ^ 2) := by ring
        rw [hrq1_sq, hrq0_sq, hrv1_sq, hrv0_sq, hq_sum, hv_sum, one_mul] at h_id
        linarith [sq_nonneg (rq1 * rv0 - rq0 * rv1)]
      have h_sum_nn : 0 ≤ rq1 * rv1 + rq0 * rv0 :=
        add_nonneg (mul_nonneg hrq1_nn hrv1_nn) (mul_nonneg hrq0_nn hrv0_nn)
      have h_sum_le : rq1 * rv1 + rq0 * rv0 ≤ sigZ := by nlinarith
      linarith
    have h_master : q1 * sigZ ^ 2 - 2 * sigZ * (q1 * s1) + v1 ≤ 2 * sigZ * d := by
      have h_amgm0 : 2 * sigZ * (rq0 * rv0) ≤ q0 * sigZ ^ 2 + v0 := by
        have h_sq0 : 0 ≤ (rq0 * sigZ - rv0) ^ 2 := sq_nonneg _
        have h_exp0 : (rq0 * sigZ - rv0) ^ 2 =
            rq0 ^ 2 * sigZ ^ 2 - 2 * sigZ * (rq0 * rv0) + rv0 ^ 2 := by ring
        rw [hrq0_sq, hrv0_sq] at h_exp0
        linarith
      have h_mul0 : 2 * sigZ * (q0 * s0) ≤ 2 * sigZ * (rq0 * rv0) := by
        nlinarith [hsigZ_nonneg, hqs0_le]
      have h_2sd : 2 * sigZ * d =
          (q1 + q0) * sigZ ^ 2 + (v1 + v0) - 2 * sigZ * (q1 * s1) - 2 * sigZ * (q0 * s0) := by
        calc 2 * sigZ * d
            = 1 * sigZ ^ 2 + sigZ ^ 2 - 2 * sigZ * (q1 * s1 + q0 * s0) := by
                dsimp [d]
                ring
          _ = (q1 + q0) * sigZ ^ 2 + (v1 + v0) - 2 * sigZ * (q1 * s1) - 2 * sigZ * (q0 * s0) := by
                rw [← hq_sum, ← hv_sum]
                ring
      linarith
    have h_rad : (rq1 * sigZ - rv1) ^ 2 ≤ 2 * sigZ * d := by
      have h_exp1 : (rq1 * sigZ - rv1) ^ 2 =
          q1 * sigZ ^ 2 - 2 * sigZ * (rq1 * rv1) + v1 := by
        calc (rq1 * sigZ - rv1) ^ 2
            = rq1 ^ 2 * sigZ ^ 2 - 2 * sigZ * (rq1 * rv1) + rv1 ^ 2 := by ring
          _ = q1 * sigZ ^ 2 - 2 * sigZ * (rq1 * rv1) + v1 := by rw [hrq1_sq, hrv1_sq]
      have h_mul1 : 2 * sigZ * (q1 * s1) ≤ 2 * sigZ * (rq1 * rv1) := by
        nlinarith [hsigZ_nonneg, hqs1_le]
      linarith
    have h_mean : m1 ^ 2 ≤ 2 * q1 * sigZ * d := by
      have h_mulq : q1 * (q1 * sigZ ^ 2 - 2 * sigZ * (q1 * s1) + v1) ≤ q1 * (2 * sigZ * d) :=
        mul_le_mul_of_nonneg_left h_master hq1
      have h_id1 : q1 * (q1 * sigZ ^ 2 - 2 * sigZ * (q1 * s1) + v1) =
          (q1 * sigZ - q1 * s1) ^ 2 + m1 ^ 2 := by
        linear_combination -hb1
      nlinarith [sq_nonneg (q1 * sigZ - q1 * s1)]
    exact ⟨⟨hd_nn, hd_le⟩, h_mean, h_rad⟩

  have h_seller_meas :
      ∀ (S₀ B₀ : Ω → ℝ), Measurable S₀ → Measurable B₀ →
        MeasureTheory.MemLp S₀ 2 μ → MeasureTheory.MemLp B₀ 2 μ →
        let muS₀ := ∫ ω, S₀ ω ∂μ
        let sigS₀ := rvStdDev S₀ μ
        let Dbar₀ := supInfoDrop S₀ B₀ μ
        (∀ p : ℝ, p < muS₀ → tradeProfile S₀ B₀ μ p ≤ 2 * sigS₀ * Dbar₀ / (muS₀ - p) ^ 2) ∧
        (0 < sigS₀ → ∀ p : ℝ, |p - muS₀| ≤ sigS₀ / 3 →
          tradeProfile S₀ B₀ μ p ≤ (225 / 2 : ℝ) * Dbar₀ / sigS₀) ∧
        MeasureTheory.IntegrableOn (tradeProfile S₀ B₀ μ) (Set.Iic (muS₀ + sigS₀ / 3))
          MeasureTheory.volume ∧
        (∫ p in Set.Iic (muS₀ + sigS₀ / 3), tradeProfile S₀ B₀ μ p) ≤ 81 * Dbar₀ := by
    intro S₀ B₀ hSm hBm hS₀ hB₀
    set muS₀ : ℝ := ∫ ω, S₀ ω ∂μ
    set sigS₀ : ℝ := rvStdDev S₀ μ
    set sigB₀ : ℝ := rvStdDev B₀ μ
    set Dbar₀ : ℝ := supInfoDrop S₀ B₀ μ
    have hsigS_nn : 0 ≤ sigS₀ := Real.sqrt_nonneg _
    have hEq : ∀ q : ℝ, MeasurableSet (tradeEvent S₀ B₀ q) := fun q =>
      (measurableSet_le hSm measurable_const).inter (measurableSet_le measurable_const hBm)
    have hS_drop := fun q : ℝ => h_var_drop S₀ hS₀ (tradeEvent S₀ B₀ q) (hEq q)
    have hB_drop := fun q : ℝ => h_var_drop B₀ hB₀ (tradeEvent S₀ B₀ q) (hEq q)
    have h_bdd : BddAbove (Set.range (totalInfoDrop S₀ B₀ μ)) := by
      refine ⟨sigS₀ + sigB₀, ?_⟩
      rintro _ ⟨q, rfl⟩
      have h1 := (hS_drop q).1.2
      have h2 := (hB_drop q).1.2
      change agentInfoDrop S₀ S₀ B₀ μ q + agentInfoDrop B₀ S₀ B₀ μ q ≤ sigS₀ + sigB₀
      dsimp only [agentInfoDrop] at *
      linarith
    have h_dS_le_Dbar : ∀ q : ℝ, agentInfoDrop S₀ S₀ B₀ μ q ≤ Dbar₀ := fun q => by
      have h_tot : totalInfoDrop S₀ B₀ μ q ≤ Dbar₀ := le_csSup h_bdd ⟨q, rfl⟩
      have hB_nn : 0 ≤ agentInfoDrop B₀ S₀ B₀ μ q := (hB_drop q).1.1
      dsimp only [totalInfoDrop] at h_tot
      linarith
    have hDbar_nn : 0 ≤ Dbar₀ := le_trans (hS_drop 0).1.1 (h_dS_le_Dbar 0)
    have h_mean_sq : ∀ q : ℝ,
        (∫ ω in tradeEvent S₀ B₀ q, (S₀ ω - muS₀) ∂μ) ^ 2 ≤
          2 * tradeProfile S₀ B₀ μ q * sigS₀ * Dbar₀ := fun q => by
      have hm := (hS_drop q).2.1
      have hd := h_dS_le_Dbar q
      have h_fac_nn : 0 ≤ 2 * tradeProfile S₀ B₀ μ q * sigS₀ :=
        mul_nonneg (mul_nonneg (by norm_num) MeasureTheory.measureReal_nonneg) hsigS_nn
      exact le_trans hm (mul_le_mul_of_nonneg_left hd h_fac_nn)
    have h_rad_sq : ∀ q : ℝ,
        (Real.sqrt (tradeProfile S₀ B₀ μ q) * sigS₀ -
          Real.sqrt (∫ ω in tradeEvent S₀ B₀ q, (S₀ ω - muS₀) ^ 2 ∂μ)) ^ 2 ≤
          2 * sigS₀ * Dbar₀ := fun q => by
      have hr := (hS_drop q).2.2
      have hd := h_dS_le_Dbar q
      have h_fac_nn : 0 ≤ 2 * sigS₀ := mul_nonneg (by norm_num) hsigS_nn
      exact le_trans hr (mul_le_mul_of_nonneg_left hd h_fac_nn)

    have h_tail : ∀ p : ℝ, p < muS₀ →
        tradeProfile S₀ B₀ μ p ≤ 2 * sigS₀ * Dbar₀ / (muS₀ - p) ^ 2 := by
      intro p hp
      set E := tradeEvent S₀ B₀ p
      set α := tradeProfile S₀ B₀ μ p
      have hα_nn : 0 ≤ α := MeasureTheory.measureReal_nonneg
      have h_diff_pos : 0 < muS₀ - p := sub_pos.mpr hp
      have h_sq_pos : 0 < (muS₀ - p) ^ 2 := sq_pos_of_pos h_diff_pos
      rcases eq_or_lt_of_le hα_nn with hα0 | hα_pos
      · rw [← hα0]
        positivity
      · have hW_int : MeasureTheory.IntegrableOn (fun ω => S₀ ω - muS₀) E μ :=
          ((hS₀.integrable one_le_two).sub (MeasureTheory.integrable_const muS₀)).integrableOn
        have hC_int : MeasureTheory.IntegrableOn (fun _ : Ω => p - muS₀) E μ :=
          MeasureTheory.integrableOn_const
        have h_mono : ∫ ω in E, (S₀ ω - muS₀) ∂μ ≤ ∫ _ in E, (p - muS₀) ∂μ :=
          MeasureTheory.setIntegral_mono_on hW_int hC_int (hEq p) fun ω hω => by
            linarith [hω.1]
        rw [MeasureTheory.setIntegral_const, smul_eq_mul] at h_mono
        have h_sq_le : α ^ 2 * (muS₀ - p) ^ 2 ≤ (∫ ω in E, (S₀ ω - muS₀) ∂μ) ^ 2 := by
          have h_pos_prod : 0 ≤ α * (muS₀ - p) := mul_nonneg hα_nn h_diff_pos.le
          have h_le_neg : α * (muS₀ - p) ≤ -(∫ ω in E, (S₀ ω - muS₀) ∂μ) := by
            change α * (p - muS₀) ≥ _ at h_mono
            linarith
          nlinarith
        have h_comb : α ^ 2 * (muS₀ - p) ^ 2 ≤ 2 * α * sigS₀ * Dbar₀ :=
          le_trans h_sq_le (h_mean_sq p)
        have h_canc : α * (muS₀ - p) ^ 2 ≤ 2 * sigS₀ * Dbar₀ := by nlinarith
        exact (le_div_iff₀ h_sq_pos).mpr h_canc

    have h_cent : 0 < sigS₀ → ∀ p : ℝ, |p - muS₀| ≤ sigS₀ / 3 →
        tradeProfile S₀ B₀ μ p ≤ (225 / 2 : ℝ) * Dbar₀ / sigS₀ := by
      intro hsig_pos p hp
      set η : ℝ := sigS₀ / 3
      have hη_pos : 0 < η := by positivity
      obtain ⟨hp_lo, hp_hi⟩ := abs_le.mp hp
      set p' : ℝ := muS₀ - η
      set E := tradeEvent S₀ B₀ p
      set E' := tradeEvent S₀ B₀ p'
      set α : ℝ := tradeProfile S₀ B₀ μ p
      set q' : ℝ := tradeProfile S₀ B₀ μ p'
      let f : Ω → ℝ := fun ω => (S₀ ω - muS₀) ^ 2
      have hf_int : MeasureTheory.Integrable f μ :=
        (hS₀.sub (MeasureTheory.memLp_const muS₀)).integrable_sq
      set v : ℝ := ∫ ω in E, f ω ∂μ
      set v' : ℝ := ∫ ω in E', f ω ∂μ
      have hα_nn : 0 ≤ α := MeasureTheory.measureReal_nonneg
      have hq'_nn : 0 ≤ q' := MeasureTheory.measureReal_nonneg
      have hv_nn : 0 ≤ v := MeasureTheory.setIntegral_nonneg (hEq p) fun ω _ => sq_nonneg _
      have hv'_nn : 0 ≤ v' := MeasureTheory.setIntegral_nonneg (hEq p') fun ω _ => sq_nonneg _
      have h_ind_le : ∀ ω : Ω,
          E.indicator f ω ≤ E.indicator (fun _ => η ^ 2) ω + E'.indicator f ω := by
        intro ω
        by_cases hω : ω ∈ E
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
          by_cases hS_le : S₀ ω ≤ p'
          · have hω' : ω ∈ E' := ⟨hS_le, by linarith [hω.2]⟩
            rw [Set.indicator_of_mem hω']
            linarith [sq_nonneg η]
          · push_neg at hS_le
            have hf_le : f ω ≤ η ^ 2 := by
              dsimp [f]
              have h1 : -η ≤ S₀ ω - muS₀ := by linarith
              have h2 : S₀ ω - muS₀ ≤ η := by linarith [hω.1]
              nlinarith
            have h_ind_nn : 0 ≤ E'.indicator f ω :=
              Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
            linarith
        · simp only [Set.indicator, hω, ↓reduceIte, zero_add]
          split_ifs
          · exact sq_nonneg _
          · exact le_rfl
      have hv_split : v ≤ η ^ 2 * α + v' := by
        have h_i1 : MeasureTheory.Integrable (E.indicator f) μ := hf_int.indicator (hEq p)
        have h_i2 : MeasureTheory.Integrable (E.indicator (fun _ => η ^ 2)) μ :=
          (MeasureTheory.integrable_const (η ^ 2)).indicator (hEq p)
        have h_i3 : MeasureTheory.Integrable (E'.indicator f) μ := hf_int.indicator (hEq p')
        have h_mono : ∫ ω, E.indicator f ω ∂μ ≤
            ∫ ω, (E.indicator (fun _ => η ^ 2) ω + E'.indicator f ω) ∂μ :=
          MeasureTheory.integral_mono h_i1 (h_i2.add h_i3) h_ind_le
        rw [MeasureTheory.integral_add h_i2 h_i3,
            MeasureTheory.integral_indicator (hEq p),
            MeasureTheory.integral_indicator (hEq p),
            MeasureTheory.integral_indicator (hEq p'),
            MeasureTheory.setIntegral_const, smul_eq_mul] at h_mono
        change v ≤ α * η ^ 2 + v' at h_mono
        linarith
      set R : ℝ := Real.sqrt (2 * sigS₀ * Dbar₀)
      have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
      have hR_sq : R ^ 2 = 2 * sigS₀ * Dbar₀ := Real.sq_sqrt (by positivity)
      have hq'_tail : q' ≤ 2 * sigS₀ * Dbar₀ / (muS₀ - p') ^ 2 :=
        h_tail p' (by dsimp [p']; linarith)
      have hq'_mul : q' * sigS₀ ^ 2 ≤ 9 * R ^ 2 := by
        have h_denom : muS₀ - p' = sigS₀ / 3 := by dsimp [p', η]; ring
        rw [h_denom] at hq'_tail
        have h_pos_den : 0 < (sigS₀ / 3) ^ 2 := by positivity
        have h_c := (le_div_iff₀ h_pos_den).mp hq'_tail
        nlinarith [hR_sq]
      have hrq'_sig : Real.sqrt q' * sigS₀ ≤ 3 * R := by
        have h_sq1 : (Real.sqrt q' * sigS₀) ^ 2 = q' * sigS₀ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hq'_nn]
        have h_nn1 : 0 ≤ Real.sqrt q' * sigS₀ := mul_nonneg (Real.sqrt_nonneg _) hsig_pos.le
        nlinarith
      have hrv'_sub : Real.sqrt v' - Real.sqrt q' * sigS₀ ≤ R := by
        have hr' := h_rad_sq p'
        rw [← hR_sq] at hr'
        nlinarith [hR_nn]
      have hv'_le : v' ≤ 16 * R ^ 2 := by
        have hrv'_le : Real.sqrt v' ≤ 4 * R := by linarith
        have hrv'_nn : 0 ≤ Real.sqrt v' := Real.sqrt_nonneg _
        have hrv'_sq : (Real.sqrt v') ^ 2 = v' := Real.sq_sqrt hv'_nn
        nlinarith
      have hrv_le : Real.sqrt v ≤ η * Real.sqrt α + 4 * R := by
        have hrα_nn : 0 ≤ Real.sqrt α := Real.sqrt_nonneg _
        have hrα_sq : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hα_nn
        have hrv_nn : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
        have hrv_sq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv_nn
        have h_sum_sq : (Real.sqrt v) ^ 2 ≤ (η * Real.sqrt α + 4 * R) ^ 2 := by
          calc (Real.sqrt v) ^ 2 = v := hrv_sq
            _ ≤ η ^ 2 * α + 16 * R ^ 2 := by linarith [hv_split, hv'_le]
            _ = η ^ 2 * (Real.sqrt α) ^ 2 + 16 * R ^ 2 := by rw [hrα_sq]
            _ ≤ (η * Real.sqrt α + 4 * R) ^ 2 := by nlinarith [mul_nonneg hη_pos.le hrα_nn, hR_nn]
        have h_rhs_nn : 0 ≤ η * Real.sqrt α + 4 * R := by positivity
        nlinarith
      have hrα_sub : Real.sqrt α * sigS₀ - Real.sqrt v ≤ R := by
        have hr := h_rad_sq p
        rw [← hR_sq] at hr
        nlinarith [hR_nn]
      have h_lin : (2 / 3 : ℝ) * sigS₀ * Real.sqrt α ≤ 5 * R := by
        dsimp [η] at hrv_le
        linarith
      have h_sq_final : (4 / 9 : ℝ) * sigS₀ ^ 2 * α ≤ 50 * sigS₀ * Dbar₀ := by
        have hrα_nn : 0 ≤ Real.sqrt α := Real.sqrt_nonneg _
        have hrα_sq : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hα_nn
        have h1 : ((2 / 3 : ℝ) * sigS₀ * Real.sqrt α) ^ 2 ≤ (5 * R) ^ 2 := by
          nlinarith [mul_nonneg hsig_pos.le hrα_nn, hR_nn]
        nlinarith [hR_sq, hrα_sq]
      have h_canc : α * sigS₀ ≤ (225 / 2 : ℝ) * Dbar₀ := by nlinarith
      exact (le_div_iff₀ hsig_pos).mpr h_canc

    have hα_meas : Measurable (tradeProfile S₀ B₀ μ) := by
      let M : Set (ℝ × Ω) := {x | S₀ x.2 ≤ x.1 ∧ x.1 ≤ B₀ x.2}
      have hM : MeasurableSet M :=
        (measurableSet_le (hSm.comp measurable_snd) measurable_fst).inter
          (measurableSet_le measurable_fst (hBm.comp measurable_snd))
      have hm1 : Measurable (fun p : ℝ => μ (Prod.mk p ⁻¹' M)) :=
        measurable_measure_prodMk_left_finite hM
      exact ENNReal.measurable_toReal.comp hm1
    have hα_nn : ∀ p : ℝ, 0 ≤ tradeProfile S₀ B₀ μ p :=
      fun _ => MeasureTheory.measureReal_nonneg
    have h_halfline :
        MeasureTheory.IntegrableOn (tradeProfile S₀ B₀ μ) (Set.Iic (muS₀ + sigS₀ / 3))
          MeasureTheory.volume ∧
        (∫ p in Set.Iic (muS₀ + sigS₀ / 3), tradeProfile S₀ B₀ μ p) ≤ 81 * Dbar₀ := by
      rcases eq_or_lt_of_le hsigS_nn with hsig0 | hsig_pos
      · have h_end : muS₀ + sigS₀ / 3 = muS₀ := by rw [← hsig0]; ring
        rw [h_end]
        have h_eq0 : Set.EqOn (fun _ : ℝ => (0 : ℝ)) (tradeProfile S₀ B₀ μ) (Set.Iio muS₀) := by
          intro p hp
          have ht := h_tail p hp
          rw [← hsig0] at ht
          have h0 : 2 * (0 : ℝ) * Dbar₀ / (muS₀ - p) ^ 2 = 0 := by ring
          linarith [hα_nn p]
        have h_int_Iio : MeasureTheory.IntegrableOn (tradeProfile S₀ B₀ μ)
            (Set.Iio muS₀) MeasureTheory.volume :=
          MeasureTheory.integrableOn_zero.congr_fun h_eq0 measurableSet_Iio
        have h_int_Iic : MeasureTheory.IntegrableOn (tradeProfile S₀ B₀ μ)
            (Set.Iic muS₀) MeasureTheory.volume :=
          h_int_Iio.congr_set_ae MeasureTheory.Iio_ae_eq_Iic.symm
        have h_val : (∫ p in Set.Iic muS₀, tradeProfile S₀ B₀ μ p) = 0 := by
          rw [MeasureTheory.integral_Iic_eq_integral_Iio,
              MeasureTheory.setIntegral_congr_fun measurableSet_Iio h_eq0.symm,
              MeasureTheory.integral_zero]
        exact ⟨h_int_Iic, by rw [h_val]; positivity⟩
      · set a : ℝ := muS₀ - sigS₀ / 3
        set b : ℝ := muS₀ + sigS₀ / 3
        let g : ℝ → ℝ := fun x => -(muS₀ + x)⁻¹
        let g' : ℝ → ℝ := fun x => ((muS₀ + x) ^ 2)⁻¹
        have h_deriv : ∀ x ∈ Set.Ici (-a), HasDerivAt g (g' x) x := by
          intro x hx
          have hpos : 0 < muS₀ + x := by
            have : -a ≤ x := hx
            dsimp [a] at this
            linarith
          have hd_lin : HasDerivAt (fun y : ℝ => muS₀ + y) 1 x := by
            simpa using (hasDerivAt_id x).const_add muS₀
          have hd_inv : HasDerivAt (fun y : ℝ => (muS₀ + y)⁻¹) (-1 / (muS₀ + x) ^ 2) x :=
            hd_lin.inv hpos.ne'
          have hd_neg := hd_inv.neg
          convert hd_neg using 1
          ring
        have h_g'_nn : ∀ x ∈ Set.Ioi (-a), 0 ≤ g' x := fun x _ => by
          dsimp [g']
          positivity
        have h_tendsto : Filter.Tendsto g Filter.atTop (nhds 0) := by
          have ht1 : Filter.Tendsto (fun x : ℝ => muS₀ + x) Filter.atTop Filter.atTop :=
            Filter.tendsto_atTop_add_const_left Filter.atTop muS₀ Filter.tendsto_id
          have ht2 : Filter.Tendsto (fun x : ℝ => (muS₀ + x)⁻¹) Filter.atTop (nhds 0) :=
            tendsto_inv_atTop_zero.comp ht1
          simpa using ht2.neg
        have h_g'_int_Ioi : MeasureTheory.IntegrableOn g' (Set.Ioi (-a)) MeasureTheory.volume :=
          MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' h_deriv h_g'_nn h_tendsto
        have h_g'_val_Ioi : (∫ x in Set.Ioi (-a), g' x) = 3 / sigS₀ := by
          have h_cont : ContinuousWithinAt g (Set.Ici (-a)) (-a) :=
            (h_deriv (-a) Set.self_mem_Ici).continuousAt.continuousWithinAt
          have h_int := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg h_cont
            (fun x hx => h_deriv x (Set.Ioi_subset_Ici_self hx)) h_g'_nn h_tendsto
          rw [h_int]
          have h_sum : muS₀ + -a = sigS₀ / 3 := by dsimp [a]; ring
          dsimp [g]
          rw [h_sum]
          have hsig_ne : sigS₀ ≠ 0 := hsig_pos.ne'
          field_simp
          ring
        have h_g'_int_Ici : MeasureTheory.IntegrableOn g' (Set.Ici (-a)) MeasureTheory.volume :=
          h_g'_int_Ioi.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
        have h_neg_int_Iic : MeasureTheory.IntegrableOn (fun p => g' (-p))
            (Set.Iic a) MeasureTheory.volume :=
          h_g'_int_Ici.comp_neg_Iic
        have h_neg_int_Iio : MeasureTheory.IntegrableOn (fun p => g' (-p))
            (Set.Iio a) MeasureTheory.volume :=
          h_neg_int_Iic.congr_set_ae MeasureTheory.Iio_ae_eq_Iic
        have h_neg_val_Iio : (∫ p in Set.Iio a, g' (-p)) = 3 / sigS₀ := by
          rw [← MeasureTheory.integral_indicator measurableSet_Iio]
          have h_pt : (fun p : ℝ => (Set.Iio a).indicator (fun q => g' (-q)) p) =
              fun p : ℝ => (Set.Ioi (-a)).indicator g' (-p) := by
            ext p
            by_cases hp : p < a
            · have hnp : -a < -p := by linarith
              simp [Set.indicator, hp, hnp]
            · have hnp : ¬ (-a < -p) := by linarith
              simp [Set.indicator, hp, hnp]
          rw [h_pt, MeasureTheory.integral_neg_eq_self,
              MeasureTheory.integral_indicator measurableSet_Ioi, h_g'_val_Ioi]
        let env_tail : ℝ → ℝ := fun p => (2 * sigS₀ * Dbar₀) * g' (-p)
        have h_env_tail_int : MeasureTheory.IntegrableOn env_tail
            (Set.Iio a) MeasureTheory.volume :=
          h_neg_int_Iio.const_mul (2 * sigS₀ * Dbar₀)
        have h_α_int_tail : MeasureTheory.IntegrableOn (tradeProfile S₀ B₀ μ)
            (Set.Iio a) MeasureTheory.volume := by
          refine MeasureTheory.Integrable.mono' h_env_tail_int
            hα_meas.aestronglyMeasurable ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iio] with p hp
          rw [Real.norm_of_nonneg (hα_nn p)]
          have hp_mu : p < muS₀ := by
            have hp' : p < a := hp
            dsimp [a] at hp'
            linarith
          have ht := h_tail p hp_mu
          have h_eq_env : 2 * sigS₀ * Dbar₀ / (muS₀ - p) ^ 2 = env_tail p := by
            dsimp [env_tail, g']
            rw [div_eq_mul_inv, sub_eq_add_neg]
          rwa [← h_eq_env]
        have h_α_val_tail : (∫ p in Set.Iio a, tradeProfile S₀ B₀ μ p) ≤ 6 * Dbar₀ := by
          have h_le := MeasureTheory.setIntegral_mono_on h_α_int_tail h_env_tail_int
            measurableSet_Iio fun p hp => by
              have hp_mu : p < muS₀ := by
                have hp' : p < a := hp
                dsimp [a] at hp'
                linarith
              have ht := h_tail p hp_mu
              have h_eq_env : 2 * sigS₀ * Dbar₀ / (muS₀ - p) ^ 2 = env_tail p := by
                dsimp [env_tail, g']
                rw [div_eq_mul_inv, sub_eq_add_neg]
              rwa [← h_eq_env]
          have h_env_val : (∫ p in Set.Iio a, env_tail p) = 6 * Dbar₀ := by
            dsimp [env_tail]
            rw [MeasureTheory.integral_const_mul, h_neg_val_Iio]
            have hsig_ne : sigS₀ ≠ 0 := hsig_pos.ne'
            field_simp
            ring
          linarith

        set C : ℝ := (225 / 2 : ℝ) * Dbar₀ / sigS₀
        have h_vol_Icc : MeasureTheory.volume (Set.Icc a b) ≠ ⊤ := by
          rw [Real.volume_Icc]
          exact ENNReal.ofReal_ne_top
        have h_C_int : MeasureTheory.IntegrableOn (fun _ : ℝ => C)
            (Set.Icc a b) MeasureTheory.volume := by
          haveI : Fact (MeasureTheory.volume (Set.Icc a b) < ⊤) := ⟨lt_top_iff_ne_top.mpr h_vol_Icc⟩
          exact MeasureTheory.integrableOn_const
        have h_cent_on : ∀ p ∈ Set.Icc a b, tradeProfile S₀ B₀ μ p ≤ C := by
          intro p hp
          rcases hp with ⟨hp1, hp2⟩
          dsimp [a, b] at hp1 hp2
          refine h_cent hsig_pos p (abs_le.mpr ⟨?_, ?_⟩)
          · linarith
          · linarith
        have h_α_int_cent : MeasureTheory.IntegrableOn (tradeProfile S₀ B₀ μ)
            (Set.Icc a b) MeasureTheory.volume := by
          refine MeasureTheory.Integrable.mono' h_C_int hα_meas.aestronglyMeasurable ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with p hp
          rw [Real.norm_of_nonneg (hα_nn p)]
          exact h_cent_on p hp
        have h_α_val_cent : (∫ p in Set.Icc a b, tradeProfile S₀ B₀ μ p) ≤ 75 * Dbar₀ := by
          have h_le := MeasureTheory.setIntegral_mono_on h_α_int_cent h_C_int
            measurableSet_Icc h_cent_on
          rw [MeasureTheory.setIntegral_const, smul_eq_mul,
              Real.volume_real_Icc_of_le (by dsimp [a, b]; linarith)] at h_le
          have h_prod : (b - a) * C = 75 * Dbar₀ := by
            dsimp [a, b, C]
            have hsig_ne : sigS₀ ≠ 0 := hsig_pos.ne'
            field_simp
            ring
          linarith

        have h_union_eq : Set.Iio a ∪ Set.Icc a b = Set.Iic b := by
          ext p
          simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Iic]
          constructor
          · rintro (hp | ⟨_, hp⟩)
            · dsimp [a, b] at *; linarith
            · exact hp
          · intro hp
            by_cases hpa : p < a
            · exact Or.inl hpa
            · exact Or.inr ⟨not_lt.mp hpa, hp⟩
        have h_disj : Disjoint (Set.Iio a) (Set.Icc a b) :=
          Set.disjoint_left.mpr fun p hp1 hp2 => not_le_of_gt hp1 hp2.1
        have h_int_union : MeasureTheory.IntegrableOn (tradeProfile S₀ B₀ μ)
            (Set.Iic b) MeasureTheory.volume := by
          rw [← h_union_eq]
          exact h_α_int_tail.union h_α_int_cent
        have h_val_union : (∫ p in Set.Iic b, tradeProfile S₀ B₀ μ p) ≤ 81 * Dbar₀ := by
          rw [← h_union_eq,
              MeasureTheory.setIntegral_union h_disj measurableSet_Icc h_α_int_tail h_α_int_cent]
          linarith
        exact ⟨h_int_union, h_val_union⟩
    exact ⟨h_tail, h_cent, h_halfline.1, h_halfline.2⟩

  have h_seller_all :
      ∀ (S₀ B₀ : Ω → ℝ), MeasureTheory.MemLp S₀ 2 μ → MeasureTheory.MemLp B₀ 2 μ →
        let muS₀ := ∫ ω, S₀ ω ∂μ
        let sigS₀ := rvStdDev S₀ μ
        let Dbar₀ := supInfoDrop S₀ B₀ μ
        (∀ p : ℝ, p < muS₀ → tradeProfile S₀ B₀ μ p ≤ 2 * sigS₀ * Dbar₀ / (muS₀ - p) ^ 2) ∧
        (0 < sigS₀ → ∀ p : ℝ, |p - muS₀| ≤ sigS₀ / 3 →
          tradeProfile S₀ B₀ μ p ≤ (225 / 2 : ℝ) * Dbar₀ / sigS₀) ∧
        MeasureTheory.IntegrableOn (tradeProfile S₀ B₀ μ) (Set.Iic (muS₀ + sigS₀ / 3))
          MeasureTheory.volume ∧
        (∫ p in Set.Iic (muS₀ + sigS₀ / 3), tradeProfile S₀ B₀ μ p) ≤ 81 * Dbar₀ := by
    intro S₀ B₀ hS₀ hB₀
    let S' : Ω → ℝ := AEMeasurable.mk S₀ hS₀.aemeasurable
    let B' : Ω → ℝ := AEMeasurable.mk B₀ hB₀.aemeasurable
    have hSm : Measurable S' := hS₀.aemeasurable.measurable_mk
    have hBm : Measurable B' := hB₀.aemeasurable.measurable_mk
    have hSS' : S₀ =ᵐ[μ] S' := hS₀.aemeasurable.ae_eq_mk
    have hBB' : B₀ =ᵐ[μ] B' := hB₀.aemeasurable.ae_eq_mk
    have hS' : MeasureTheory.MemLp S' 2 μ := hS₀.ae_eq hSS'
    have hB' : MeasureTheory.MemLp B' 2 μ := hB₀.ae_eq hBB'
    have h_mu_eq : (∫ ω, S' ω ∂μ) = ∫ ω, S₀ ω ∂μ :=
      MeasureTheory.integral_congr_ae hSS'.symm
    have h_sigS_eq : rvStdDev S' μ = rvStdDev S₀ μ := by
      dsimp [rvStdDev]
      rw [ProbabilityTheory.variance_congr hSS'.symm]
    have h_sigB_eq : rvStdDev B' μ = rvStdDev B₀ μ := by
      dsimp [rvStdDev]
      rw [ProbabilityTheory.variance_congr hBB'.symm]
    have h_event_ae : ∀ p : ℝ, (tradeEvent S₀ B₀ p : Set Ω) =ᵐ[μ] tradeEvent S' B' p := by
      intro p
      filter_upwards [hSS', hBB'] with ω h1 h2
      change (S₀ ω ≤ p ∧ p ≤ B₀ ω) = (S' ω ≤ p ∧ p ≤ B' ω)
      rw [h1, h2]
    have h_prof_eq : tradeProfile S' B' μ = tradeProfile S₀ B₀ μ := by
      ext p
      dsimp [tradeProfile, MeasureTheory.measureReal_def]
      rw [MeasureTheory.measure_congr (h_event_ae p)]
    have h_cond_eq : ∀ {A A' : Set Ω}, A =ᵐ[μ] A' →
        ProbabilityTheory.cond μ A = ProbabilityTheory.cond μ A' := by
      intro A A' hAA'
      change (μ A)⁻¹ • μ.restrict A = (μ A')⁻¹ • μ.restrict A'
      rw [MeasureTheory.measure_congr hAA', MeasureTheory.Measure.restrict_congr_set hAA']
    have h_tot_eq : totalInfoDrop S' B' μ = totalInfoDrop S₀ B₀ μ := by
      ext p
      set E := tradeEvent S₀ B₀ p
      set E' := tradeEvent S' B' p
      have hEE' : E =ᵐ[μ] E' := h_event_ae p
      have hEE'c : (Eᶜ : Set Ω) =ᵐ[μ] E'ᶜ := hEE'.compl
      have hμE : μ.real E' = μ.real E := by
        simp [MeasureTheory.measureReal_def, MeasureTheory.measure_congr hEE']
      have hμEc : μ.real E'ᶜ = μ.real Eᶜ := by
        simp [MeasureTheory.measureReal_def, MeasureTheory.measure_congr hEE'c]
      have hcE : ProbabilityTheory.cond μ E = ProbabilityTheory.cond μ E' := h_cond_eq hEE'
      have hcEc : ProbabilityTheory.cond μ Eᶜ = ProbabilityTheory.cond μ E'ᶜ := h_cond_eq hEE'c
      have h_csS1 : condStdDev S' μ E' = condStdDev S₀ μ E := by
        dsimp [condStdDev, rvStdDev]
        rw [hcE, ProbabilityTheory.variance_congr
          (ProbabilityTheory.cond_absolutelyContinuous.ae_eq hSS'.symm)]
      have h_csS0 : condStdDev S' μ E'ᶜ = condStdDev S₀ μ Eᶜ := by
        dsimp [condStdDev, rvStdDev]
        rw [hcEc, ProbabilityTheory.variance_congr
          (ProbabilityTheory.cond_absolutelyContinuous.ae_eq hSS'.symm)]
      have h_csB1 : condStdDev B' μ E' = condStdDev B₀ μ E := by
        dsimp [condStdDev, rvStdDev]
        rw [hcE, ProbabilityTheory.variance_congr
          (ProbabilityTheory.cond_absolutelyContinuous.ae_eq hBB'.symm)]
      have h_csB0 : condStdDev B' μ E'ᶜ = condStdDev B₀ μ Eᶜ := by
        dsimp [condStdDev, rvStdDev]
        rw [hcEc, ProbabilityTheory.variance_congr
          (ProbabilityTheory.cond_absolutelyContinuous.ae_eq hBB'.symm)]
      dsimp [totalInfoDrop, agentInfoDrop]
      rw [h_sigS_eq, h_sigB_eq, hμE, hμEc, h_csS1, h_csS0, h_csB1, h_csB0]
    have h_sup_eq : supInfoDrop S' B' μ = supInfoDrop S₀ B₀ μ := by
      dsimp [supInfoDrop]
      rw [h_tot_eq]
    have h_res := h_seller_meas S' B' hSm hBm hS' hB'
    dsimp only at h_res ⊢
    rwa [h_mu_eq, h_sigS_eq, h_prof_eq, h_sup_eq] at h_res

  obtain ⟨hc1, hc2, hc3, hc4⟩ := h_seller_all S B hS hB
  obtain ⟨hb1, hb2, hb3, hb4⟩ := h_seller_all (-B) (-S) hB.neg hS.neg
  have h_mu_neg : (∫ ω, (-B) ω ∂μ) = -∫ ω, B ω ∂μ := MeasureTheory.integral_neg B
  have h_sig_neg : ∀ (Z : Ω → ℝ) (ν : MeasureTheory.Measure Ω),
      rvStdDev (-Z) ν = rvStdDev Z ν := fun Z ν => by
    dsimp [rvStdDev]
    rw [ProbabilityTheory.variance_neg]
  have h_ev_neg : ∀ q : ℝ, tradeEvent (-B) (-S) q = tradeEvent S B (-q) := by
    intro q
    ext ω
    simp only [tradeEvent, Pi.neg_apply, Set.mem_setOf_eq]
    constructor <;> intro h <;> constructor <;> linarith
  have h_prof_neg : ∀ p : ℝ, tradeProfile (-B) (-S) μ (-p) = tradeProfile S B μ p := by
    intro p
    dsimp [tradeProfile]
    rw [h_ev_neg (-p), neg_neg]
  have h_Dbar_neg : supInfoDrop (-B) (-S) μ = supInfoDrop S B μ := by
    have h_tot_neg : ∀ q : ℝ, totalInfoDrop (-B) (-S) μ q = totalInfoDrop S B μ (-q) := by
      intro q
      dsimp [totalInfoDrop, agentInfoDrop, condStdDev]
      rw [h_ev_neg q, h_sig_neg B μ, h_sig_neg S μ,
          h_sig_neg B (ProbabilityTheory.cond μ (tradeEvent S B (-q))),
          h_sig_neg B (ProbabilityTheory.cond μ (tradeEvent S B (-q))ᶜ),
          h_sig_neg S (ProbabilityTheory.cond μ (tradeEvent S B (-q))),
          h_sig_neg S (ProbabilityTheory.cond μ (tradeEvent S B (-q))ᶜ)]
      ring
    have h_range : Set.range (totalInfoDrop (-B) (-S) μ) = Set.range (totalInfoDrop S B μ) := by
      ext y
      simp only [Set.mem_range]
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨-q, (h_tot_neg q).symm⟩
      · rintro ⟨q, rfl⟩
        exact ⟨-q, by rw [h_tot_neg (-q), neg_neg]⟩
    dsimp [supInfoDrop]
    rw [h_range]

  rw [h_mu_neg, h_sig_neg B μ] at hb1 hb2 hb3 hb4
  rw [h_Dbar_neg] at hb1 hb2 hb4
  set muB : ℝ := ∫ ω, B ω ∂μ
  set sigB : ℝ := rvStdDev B μ
  set Dbar : ℝ := supInfoDrop S B μ
  have hc5 : ∀ p : ℝ, muB < p → tradeProfile S B μ p ≤ 2 * sigB * Dbar / (p - muB) ^ 2 := by
    intro p hp
    have h := hb1 (-p) (by linarith)
    rw [h_prof_neg p] at h
    have h_sq : (-muB - -p) ^ 2 = (p - muB) ^ 2 := by ring
    rwa [h_sq] at h
  have hc6 : 0 < sigB → ∀ p : ℝ, |p - muB| ≤ sigB / 3 →
      tradeProfile S B μ p ≤ (225 / 2 : ℝ) * Dbar / sigB := by
    intro hsig p hp
    have h_abs : |-p - -muB| ≤ sigB / 3 := by
      have : -p - -muB = -(p - muB) := by ring
      rwa [this, abs_neg]
    have h := hb2 hsig (-p) h_abs
    rwa [h_prof_neg p] at h
  set c_end : ℝ := muB - sigB / 3
  have h_end_eq : -muB + sigB / 3 = -c_end := by dsimp [c_end]; ring
  rw [h_end_eq] at hb3 hb4
  have hc7 : MeasureTheory.IntegrableOn (tradeProfile S B μ)
      (Set.Ici c_end) MeasureTheory.volume := by
    have h_comp := hb3.comp_neg_Ici
    have h_fn : (fun p : ℝ => tradeProfile (-B) (-S) μ (-p)) = tradeProfile S B μ :=
      funext h_prof_neg
    rwa [h_fn] at h_comp
  have hc8 : (∫ p in Set.Ici c_end, tradeProfile S B μ p) ≤ 81 * Dbar := by
    have h_eq_int : (∫ p in Set.Ici c_end, tradeProfile S B μ p) =
        ∫ q in Set.Iic (-c_end), tradeProfile (-B) (-S) μ q := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ici,
          ← MeasureTheory.integral_indicator measurableSet_Iic]
      have h_pt : (fun p : ℝ => (Set.Ici c_end).indicator (tradeProfile S B μ) p) =
          fun p : ℝ => (Set.Iic (-c_end)).indicator (tradeProfile (-B) (-S) μ) (-p) := by
        ext p
        by_cases hp : c_end ≤ p
        · have hnp : -p ≤ -c_end := by linarith
          simp [Set.indicator, hp, hnp, h_prof_neg p]
        · have hnp : ¬ (-p ≤ -c_end) := by linarith
          simp [Set.indicator, hp, hnp]
      rw [h_pt, MeasureTheory.integral_neg_eq_self]
    linarith
  exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩

/-- In the non-degenerate regime `0 < σ_S` and `0 < σ_B` (where `tradeProfileEnvelope` is invoked in
the proof of Lemma 3.1), `tradeProfileEnvelope` simplifies to the exact 5-branch formula of
Appendix D.1 without any zero-variance fallback. -/
theorem tradeProfileEnvelope_of_pos {Ω : Type*} [MeasurableSpace Ω]
    (S B : Ω → ℝ) (μ : MeasureTheory.Measure Ω)
    (hsigS : 0 < rvStdDev S μ) (hsigB : 0 < rvStdDev B μ) (p : ℝ) :
    tradeProfileEnvelope S B μ p =
      let muS := ∫ ω, S ω ∂μ
      let muB := ∫ ω, B ω ∂μ
      let sigS := rvStdDev S μ
      let sigB := rvStdDev B μ
      let Dbar := supInfoDrop S B μ
      if p < muS - sigS / 3 then
        (2 * sigS * Dbar) / (muS - p) ^ 2
      else if p ≤ muS + sigS / 3 then
        (225 * Dbar) / (2 * sigS)
      else if p < muB - sigB / 3 then
        1
      else if p ≤ muB + sigB / 3 then
        (225 * Dbar) / (2 * sigB)
      else
        (2 * sigB * Dbar) / (p - muB) ^ 2 := by
  unfold tradeProfileEnvelope
  simp [hsigS.ne', hsigB.ne']

/-- **Claim D.4 (Uniform bound on the trade profile, `cl:trade-profile`)**:
For every square-integrable pair `(S, B)` on a probability space `(Ω, μ)` and every price `p ∈ ℝ`,
`α(p) ≤ H(p)`. -/
theorem claim_trade_profile {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S B : Ω → ℝ) (hS : MeasureTheory.MemLp S 2 μ) (hB : MeasureTheory.MemLp B 2 μ)
    (p : ℝ) :
    tradeProfile S B μ p ≤ tradeProfileEnvelope S B μ p := by
  obtain ⟨hc1, hc2, _, _, hc5, hc6, _, _⟩ := lem_trade_profile_bounds μ S B hS hB
  set muS : ℝ := ∫ ω, S ω ∂μ
  set muB : ℝ := ∫ ω, B ω ∂μ
  set sigS : ℝ := rvStdDev S μ
  set sigB : ℝ := rvStdDev B μ
  set Dbar : ℝ := supInfoDrop S B μ
  have hsigS_nn : 0 ≤ sigS := Real.sqrt_nonneg _
  have hsigB_nn : 0 ≤ sigB := Real.sqrt_nonneg _
  have hα_le_one : tradeProfile S B μ p ≤ 1 := by
    calc tradeProfile S B μ p = μ.real (tradeEvent S B p) := rfl
      _ ≤ μ.real Set.univ := MeasureTheory.measureReal_mono (Set.subset_univ _)
      _ = 1 := MeasureTheory.probReal_univ
  unfold tradeProfileEnvelope
  change tradeProfile S B μ p ≤
    if p < muS - sigS / 3 then (2 * sigS * Dbar) / (muS - p) ^ 2
    else if p ≤ muS + sigS / 3 then (if sigS = 0 then 1 else (225 * Dbar) / (2 * sigS))
    else if p < muB - sigB / 3 then 1
    else if p ≤ muB + sigB / 3 then (if sigB = 0 then 1 else (225 * Dbar) / (2 * sigB))
    else (2 * sigB * Dbar) / (p - muB) ^ 2
  split_ifs with h1 h2 hsigS0 h3 h4 hsigB0
  · exact hc1 p (by linarith)
  · exact hα_le_one
  · have hsigS_pos : 0 < sigS := lt_of_le_of_ne hsigS_nn (Ne.symm hsigS0)
    have hp_abs : |p - muS| ≤ sigS / 3 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h_cent := hc2 hsigS_pos p hp_abs
    have h_eq : (225 / 2 : ℝ) * Dbar / sigS = (225 * Dbar) / (2 * sigS) := by ring
    rwa [h_eq] at h_cent
  · exact hα_le_one
  · exact hα_le_one
  · have hsigB_pos : 0 < sigB := lt_of_le_of_ne hsigB_nn (Ne.symm hsigB0)
    have hp_abs : |p - muB| ≤ sigB / 3 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h_cent := hc6 hsigB_pos p hp_abs
    have h_eq : (225 / 2 : ℝ) * Dbar / sigB = (225 * Dbar) / (2 * sigB) := by ring
    rwa [h_eq] at h_cent
  · exact hc5 p (by linarith)

/-- Alias for `lem_trade_profile_bounds`. -/
alias lem_trade_profile := lem_trade_profile_bounds

end TraceSqrt
