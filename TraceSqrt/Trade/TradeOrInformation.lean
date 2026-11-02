import TraceSqrt.Defs
import TraceSqrt.Trade.SmallGain

set_option maxHeartbeats 4000000

/-!
# Lemma 3.1: Trade or Information (`lem:toi`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 3.1 Lemma 3.1 `lem:toi`, proved in Appendix D.1).
-/

namespace TraceSqrt

/-- **Lemma 3.1 (Trade or information, `lem:toi`)**:
For every pair `(S, B)` of square-integrable real random variables on a probability space
`(Ω, μ)`, there exists a common price `p ∈ ℝ` such that `L(p) ≤ 2^{11} D(p)`. -/
theorem lem_toi {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S B : Ω → ℝ) (hS : MeasureTheory.MemLp S 2 μ) (hB : MeasureTheory.MemLp B 2 μ) :
    ∃ p : ℝ, expectedLostGain S B μ p ≤ (2 ^ 11 : ℝ) * totalInfoDrop S B μ p :=
by
  let S' : Ω → ℝ := hS.aemeasurable.mk S
  let B' : Ω → ℝ := hB.aemeasurable.mk B
  have hS'_meas : Measurable S' := hS.aemeasurable.measurable_mk
  have hB'_meas : Measurable B' := hB.aemeasurable.measurable_mk
  have hSS' : S =ᵐ[μ] S' := hS.aemeasurable.ae_eq_mk
  have hBB' : B =ᵐ[μ] B' := hB.aemeasurable.ae_eq_mk
  have hS' : MeasureTheory.MemLp S' 2 μ := (MeasureTheory.memLp_congr_ae hSS').mp hS
  have hB' : MeasureTheory.MemLp B' 2 μ := (MeasureTheory.memLp_congr_ae hBB').mp hB

  have h_event_ae : ∀ p : ℝ, (tradeEvent S B p : Set Ω) =ᵐ[μ] tradeEvent S' B' p := by
    intro p
    rw [Filter.eventuallyEq_set]
    filter_upwards [hSS', hBB'] with ω hωS hωB
    simp [tradeEvent, hωS, hωB]

  have h_loss_eq : ∀ p : ℝ, expectedLostGain S B μ p = expectedLostGain S' B' μ p := by
    intro p
    unfold expectedLostGain
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hSS', hBB'] with ω hωS hωB
    rw [hωS, hωB]

  have h_sdS_eq : rvStdDev S μ = rvStdDev S' μ := by
    unfold rvStdDev
    rw [ProbabilityTheory.variance_congr hSS']

  have h_sdB_eq : rvStdDev B μ = rvStdDev B' μ := by
    unfold rvStdDev
    rw [ProbabilityTheory.variance_congr hBB']

  have h_cond_eq : ∀ {A A' : Set Ω}, A =ᵐ[μ] A' →
      ProbabilityTheory.cond μ A = ProbabilityTheory.cond μ A' := by
    intro A A' hAA'
    ext t ht
    rw [ProbabilityTheory.cond_apply' ht, ProbabilityTheory.cond_apply' ht]
    have h1 : μ A = μ A' := MeasureTheory.measure_congr hAA'
    have h2 : μ (A ∩ t) = μ (A' ∩ t) :=
      MeasureTheory.measure_congr (hAA'.inter (Filter.EventuallyEq.refl _ t))
    rw [h1, h2]

  have h_condStdDev_eq : ∀ {Z Z' : Ω → ℝ} {A A' : Set Ω},
      Z =ᵐ[μ] Z' → A =ᵐ[μ] A' → condStdDev Z μ A = condStdDev Z' μ A' := by
    intro Z Z' A A' hZZ' hAA'
    unfold condStdDev rvStdDev
    rw [h_cond_eq hAA',
        ProbabilityTheory.variance_congr (ProbabilityTheory.cond_absolutelyContinuous.ae_eq hZZ')]

  have h_tot_eq : ∀ p : ℝ, totalInfoDrop S B μ p = totalInfoDrop S' B' μ p := by
    intro p
    have hE := h_event_ae p
    have hEc := hE.compl
    unfold totalInfoDrop agentInfoDrop
    dsimp only
    rw [h_sdS_eq, h_sdB_eq,
        MeasureTheory.measureReal_congr hE, MeasureTheory.measureReal_congr hEc,
        h_condStdDev_eq hSS' hE, h_condStdDev_eq hSS' hEc,
        h_condStdDev_eq hBB' hE, h_condStdDev_eq hBB' hEc]

  suffices h_main : ∃ p : ℝ,
      expectedLostGain S' B' μ p ≤ (2 ^ 11 : ℝ) * totalInfoDrop S' B' μ p by
    rcases h_main with ⟨p, hp⟩
    exact ⟨p, by rwa [h_loss_eq p, h_tot_eq p]⟩

  have h_l1_le_sd : ∀ (Z : Ω → ℝ), MeasureTheory.MemLp Z 2 μ →
      (∫ ω, |Z ω - ∫ ω', Z ω' ∂μ| ∂μ) ≤ rvStdDev Z μ := by
    intro Z hZ
    set muZ : ℝ := ∫ ω', Z ω' ∂μ
    set sigZ : ℝ := rvStdDev Z μ
    let W : Ω → ℝ := fun ω => Z ω - muZ
    have hW : MeasureTheory.MemLp W 2 μ := hZ.sub (MeasureTheory.memLp_const muZ)
    have hW_abs_int : MeasureTheory.Integrable (fun ω => |W ω|) μ :=
      (hW.integrable one_le_two).abs
    have hW2_int : MeasureTheory.Integrable (fun ω => (W ω) ^ 2) μ := hW.integrable_sq
    set M1 : ℝ := ∫ ω, |W ω| ∂μ
    have hM1_nn : 0 ≤ M1 := MeasureTheory.integral_nonneg fun ω => abs_nonneg (W ω)
    have hsigZ_nn : 0 ≤ sigZ := Real.sqrt_nonneg _
    have hsigZ_sq : sigZ ^ 2 = ∫ ω, (W ω) ^ 2 ∂μ := by
      calc sigZ ^ 2 = ProbabilityTheory.variance Z μ :=
             Real.sq_sqrt (ProbabilityTheory.variance_nonneg Z μ)
        _ = ∫ ω, (W ω) ^ 2 ∂μ :=
             ProbabilityTheory.variance_eq_integral hZ.aemeasurable
    have h_pt : ∀ ω : Ω, 2 * M1 * |W ω| - M1 ^ 2 ≤ (W ω) ^ 2 := fun ω => by
      nlinarith [sq_abs (W ω), sq_nonneg (|W ω| - M1)]
    have h_lhs_int : MeasureTheory.Integrable (fun ω => 2 * M1 * |W ω| - M1 ^ 2) μ :=
      (hW_abs_int.const_mul (2 * M1)).sub (MeasureTheory.integrable_const (M1 ^ 2))
    have h_int_le : (∫ ω, (2 * M1 * |W ω| - M1 ^ 2) ∂μ) ≤ ∫ ω, (W ω) ^ 2 ∂μ :=
      MeasureTheory.integral_mono h_lhs_int hW2_int h_pt
    rw [MeasureTheory.integral_sub (hW_abs_int.const_mul (2 * M1))
          (MeasureTheory.integrable_const (M1 ^ 2)),
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] at h_int_le
    change 2 * M1 * M1 - M1 ^ 2 ≤ ∫ ω, (W ω) ^ 2 ∂μ at h_int_le
    rw [← hsigZ_sq] at h_int_le
    nlinarith

  have h_sd_zero_ae : ∀ (Z : Ω → ℝ), MeasureTheory.MemLp Z 2 μ →
      rvStdDev Z μ = 0 → Z =ᵐ[μ] (fun _ => ∫ ω', Z ω' ∂μ) := by
    intro Z hZ h0
    set muZ : ℝ := ∫ ω', Z ω' ∂μ
    let W : Ω → ℝ := fun ω => Z ω - muZ
    have hW : MeasureTheory.MemLp W 2 μ := hZ.sub (MeasureTheory.memLp_const muZ)
    have hW2_int : MeasureTheory.Integrable (fun ω => (W ω) ^ 2) μ := hW.integrable_sq
    have h_int0 : (∫ ω, (W ω) ^ 2 ∂μ) = 0 := by
      rw [← ProbabilityTheory.variance_eq_integral hZ.aemeasurable,
          ← Real.sq_sqrt (ProbabilityTheory.variance_nonneg Z μ)]
      change (rvStdDev Z μ) ^ 2 = 0
      rw [h0, sq, mul_zero]
    have h_ae0 : (fun ω => (W ω) ^ 2) =ᵐ[μ] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg (W ω)) hW2_int).mp h_int0
    filter_upwards [h_ae0] with ω hω
    have hW0 : W ω = 0 := sq_eq_zero_iff.mp hω
    dsimp [W] at hW0
    linarith

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

  set μS : ℝ := ∫ ω, S' ω ∂μ
  set μB : ℝ := ∫ ω, B' ω ∂μ
  set σS : ℝ := rvStdDev S' μ
  set σB : ℝ := rvStdDev B' μ
  set σ : ℝ := σS + σB
  set m : ℝ := μB - μS
  set G : ℝ := ∫ ω, max (B' ω - S' ω) 0 ∂μ

  have h_small_gain : ∀ (D : ℝ), 0 ≤ D → (∀ p : ℝ, totalInfoDrop S' B' μ p ≤ D) →
      min G (σ / 3) ≤ 162 * D := by
    intro D _hD_nn h_tot_D
    have h_sg := (lem_trade_small_gain μ S' B' hS' hB').2.2.2.2.2
    have h_sup_le : supInfoDrop S' B' μ ≤ D := by
      unfold supInfoDrop
      exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨p, rfl⟩; exact h_tot_D p)
    change min (availableGain S' B' μ) ((rvStdDev S' μ + rvStdDev B' μ) / 3) ≤ 162 * D
    linarith

  have hEq' : ∀ p : ℝ, MeasurableSet (tradeEvent S' B' p) := fun p =>
    (measurableSet_le hS'_meas measurable_const).inter
      (measurableSet_le measurable_const hB'_meas)
  have hσS_nn : 0 ≤ σS := Real.sqrt_nonneg _
  have hσB_nn : 0 ≤ σB := Real.sqrt_nonneg _
  have hσ_nn : 0 ≤ σ := add_nonneg hσS_nn hσB_nn
  have hDS_nn : ∀ p : ℝ, 0 ≤ agentInfoDrop S' S' B' μ p := fun p =>
    (h_var_drop S' hS' (tradeEvent S' B' p) (hEq' p)).1.1
  have hDB_nn : ∀ p : ℝ, 0 ≤ agentInfoDrop B' S' B' μ p := fun p =>
    (h_var_drop B' hB' (tradeEvent S' B' p) (hEq' p)).1.1
  have hD_nn_all : ∀ p : ℝ, 0 ≤ totalInfoDrop S' B' μ p := fun p =>
    add_nonneg (hDS_nn p) (hDB_nn p)
  have hmax_int : MeasureTheory.Integrable (fun ω => max (B' ω - S' ω) 0) μ :=
    ((hB'.integrable one_le_two).sub (hS'.integrable one_le_two)).sup
      (MeasureTheory.integrable_zero Ω ℝ μ)

  have h_loss_eq_setInt : ∀ p : ℝ,
      expectedLostGain S' B' μ p = ∫ ω in (tradeEvent S' B' p)ᶜ, max (B' ω - S' ω) 0 ∂μ := by
    intro p
    unfold expectedLostGain
    have h_pt : (fun ω => max (B' ω - S' ω) 0 * (if S' ω ≤ p ∧ p ≤ B' ω then 0 else 1)) =
        (tradeEvent S' B' p)ᶜ.indicator (fun ω => max (B' ω - S' ω) 0) := by
      ext ω
      by_cases hω : S' ω ≤ p ∧ p ≤ B' ω <;> simp [tradeEvent, hω]
    rw [h_pt, MeasureTheory.integral_indicator (hEq' p).compl]

  have h_loss_le_G : ∀ p : ℝ, expectedLostGain S' B' μ p ≤ G := by
    intro p
    rw [h_loss_eq_setInt p, ← MeasureTheory.integral_indicator (hEq' p).compl]
    refine MeasureTheory.integral_mono
      ((MeasureTheory.integrable_indicator_iff (hEq' p).compl).mpr hmax_int.integrableOn)
      hmax_int fun ω => ?_
    by_cases hω : ω ∈ (tradeEvent S' B' p)ᶜ
    · simp [hω]
    · simp [hω]

  rcases eq_or_lt_of_le hσ_nn with hσ0 | hσ_pos
  · have hσS0 : σS = 0 := by dsimp [σ] at hσ0; linarith
    have hσB0 : σB = 0 := by dsimp [σ] at hσ0; linarith
    have hS_const := h_sd_zero_ae S' hS' hσS0
    have hB_const := h_sd_zero_ae B' hB' hσB0
    refine ⟨μS, ?_⟩
    have h_zero_ae : (fun ω => max (B' ω - S' ω) 0 *
        (if S' ω ≤ μS ∧ μS ≤ B' ω then (0 : ℝ) else 1)) =ᵐ[μ] 0 := by
      filter_upwards [hS_const, hB_const] with ω hωS hωB
      change max (B' ω - S' ω) 0 * (if S' ω ≤ μS ∧ μS ≤ B' ω then (0 : ℝ) else 1) = 0
      change S' ω = μS at hωS
      change B' ω = μB at hωB
      rw [hωS, hωB]
      by_cases hle : μS ≤ μB
      · have hcond : μS ≤ μS ∧ μS ≤ μB := ⟨le_rfl, hle⟩
        simp [hcond]
      · have hmax : max (μB - μS) 0 = 0 := max_eq_right (by linarith)
        rw [hmax, zero_mul]
    have hL0 : expectedLostGain S' B' μ μS = 0 :=
      MeasureTheory.integral_eq_zero_of_ae h_zero_ae
    rw [hL0]
    have hD := hD_nn_all μS
    positivity
  · by_cases hm : m < 3 * σ
    · have hG_lt_4σ : G < 4 * σ := by
        let f_c : Ω → ℝ := fun _ => max m 0
        let f_B : Ω → ℝ := fun ω => |B' ω - μB|
        let f_S : Ω → ℝ := fun ω => |S' ω - μS|
        let f_ub : Ω → ℝ := fun ω => (f_c + f_B) ω + f_S ω
        have hf_c_int : MeasureTheory.Integrable f_c μ :=
          MeasureTheory.integrable_const (max m 0)
        have hf_B_int : MeasureTheory.Integrable f_B μ :=
          ((hB'.sub (MeasureTheory.memLp_const μB)).integrable one_le_two).abs
        have hf_S_int : MeasureTheory.Integrable f_S μ :=
          ((hS'.sub (MeasureTheory.memLp_const μS)).integrable one_le_two).abs
        have hf_ub_int : MeasureTheory.Integrable f_ub μ :=
          (hf_c_int.add hf_B_int).add hf_S_int
        have h_pt_ub : ∀ ω : Ω, max (B' ω - S' ω) 0 ≤ f_ub ω := by
          intro ω
          change max (B' ω - S' ω) 0 ≤ max m 0 + |B' ω - μB| + |S' ω - μS|
          have h1 : B' ω - S' ω ≤ max m 0 + |B' ω - μB| + |S' ω - μS| := by
            have hm_le : m ≤ max m 0 := le_max_left m 0
            have hB_le : B' ω - μB ≤ |B' ω - μB| := le_abs_self _
            have hS_le : -(S' ω - μS) ≤ |S' ω - μS| := neg_le_abs _
            dsimp [m] at hm_le
            linarith
          have h2 : 0 ≤ max m 0 + |B' ω - μB| + |S' ω - μS| := by positivity
          exact max_le h1 h2
        have h_mono := MeasureTheory.integral_mono hmax_int hf_ub_int h_pt_ub
        change G ≤ ∫ ω, ((f_c + f_B) ω + f_S ω) ∂μ at h_mono
        rw [MeasureTheory.integral_add (hf_c_int.add hf_B_int) hf_S_int] at h_mono
        have h_12 : (∫ ω, (f_c + f_B) ω ∂μ) = (∫ ω, f_c ω ∂μ) + ∫ ω, f_B ω ∂μ :=
          MeasureTheory.integral_add hf_c_int hf_B_int
        have h_c_val : (∫ ω, f_c ω ∂μ) = max m 0 := by
          dsimp [f_c]
          rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
        rw [h_12, h_c_val] at h_mono
        have hl1B : (∫ ω, f_B ω ∂μ) ≤ σB := h_l1_le_sd B' hB'
        have hl1S : (∫ ω, f_S ω ∂μ) ≤ σS := h_l1_le_sd S' hS'
        have hm_max : max m 0 < 3 * σ := max_lt hm (by positivity)
        dsimp [σ] at *
        linarith
      by_contra h_no
      push_neg at h_no
      have h_all_lt_G : ∀ p : ℝ, (2 ^ 11 : ℝ) * totalInfoDrop S' B' μ p < G :=
        fun p => lt_of_lt_of_le (h_no p) (h_loss_le_G p)
      have hG_pos : 0 < G :=
        lt_of_le_of_lt (by have := hD_nn_all 0; positivity) (h_all_lt_G 0)
      set Dbar : ℝ := G / (2 ^ 11 : ℝ)
      have hDbar_nn : 0 ≤ Dbar := by positivity
      have h_tot_le : ∀ p : ℝ, totalInfoDrop S' B' μ p ≤ Dbar := fun p => by
        have hp := (h_all_lt_G p).le
        dsimp [Dbar]
        linarith
      have h_sg : min G (σ / 3) ≤ 162 * Dbar := h_small_gain Dbar hDbar_nn h_tot_le
      have hG_le_12 : G ≤ 12 * min G (σ / 3) := by
        by_cases hGσ : G ≤ σ / 3
        · rw [min_eq_left hGσ]; linarith
        · push_neg at hGσ; rw [min_eq_right hGσ.le]; linarith
      dsimp [Dbar] at h_sg
      linarith
    · push_neg at hm
      set p_hat : ℝ := (μS + μB) / 2
      refine ⟨p_hat, ?_⟩
      set E : Set Ω := tradeEvent S' B' p_hat
      set F : Set Ω := Eᶜ
      have hE_meas : MeasurableSet E := hEq' p_hat
      have hF_meas : MeasurableSet F := hE_meas.compl
      rw [h_loss_eq_setInt p_hat]
      change (∫ ω in F, max (B' ω - S' ω) 0 ∂μ) ≤ (2 ^ 11 : ℝ) * totalInfoDrop S' B' μ p_hat
      by_cases hμF : μ F = 0
      · have hrest : μ.restrict F = 0 := MeasureTheory.Measure.restrict_eq_zero.mpr hμF
        rw [hrest, MeasureTheory.integral_zero_measure]
        have hD := hD_nn_all p_hat
        positivity
      · set β : ℝ := μ.real F
        have hβ_pos : 0 < β := ENNReal.toReal_pos hμF (MeasureTheory.measure_ne_top μ F)
        have hβ_nn : 0 ≤ β := hβ_pos.le
        set rβ : ℝ := Real.sqrt β
        have hrβ_pos : 0 < rβ := Real.sqrt_pos.mpr hβ_pos
        have hrβ_nn : 0 ≤ rβ := hrβ_pos.le
        have hrβ_sq : rβ ^ 2 = β := Real.sq_sqrt hβ_nn
        have hS2_int : MeasureTheory.Integrable (fun ω => (S' ω - μS) ^ 2) μ :=
          (hS'.sub (MeasureTheory.memLp_const μS)).integrable_sq
        have hB2_int : MeasureTheory.Integrable (fun ω => (B' ω - μB) ^ 2) μ :=
          (hB'.sub (MeasureTheory.memLp_const μB)).integrable_sq
        set VS : ℝ := ∫ ω in F, (S' ω - μS) ^ 2 ∂μ
        set VB : ℝ := ∫ ω in F, (B' ω - μB) ^ 2 ∂μ
        have hVS_nn : 0 ≤ VS := MeasureTheory.setIntegral_nonneg hF_meas fun ω _ => sq_nonneg _
        have hVB_nn : 0 ≤ VB := MeasureTheory.setIntegral_nonneg hF_meas fun ω _ => sq_nonneg _
        set rS : ℝ := Real.sqrt VS
        set rB : ℝ := Real.sqrt VB
        set W : ℝ := Real.sqrt (VS + VB)
        have hrS_nn : 0 ≤ rS := Real.sqrt_nonneg _
        have hrB_nn : 0 ≤ rB := Real.sqrt_nonneg _
        have hW_nn : 0 ≤ W := Real.sqrt_nonneg _
        have hrS_sq : rS ^ 2 = VS := Real.sq_sqrt hVS_nn
        have hrB_sq : rB ^ 2 = VB := Real.sq_sqrt hVB_nn
        have hW_sq : W ^ 2 = VS + VB := Real.sq_sqrt (add_nonneg hVS_nn hVB_nn)
        have hm_pos : 0 < m := by linarith
        have h_pt_F : ∀ ω ∈ F, (m / 2) ^ 2 ≤ (S' ω - μS) ^ 2 + (B' ω - μB) ^ 2 := by
          intro ω hω
          have hnot : ¬ (S' ω ≤ p_hat ∧ p_hat ≤ B' ω) := hω
          by_cases hSp : S' ω ≤ p_hat
          · have hBp : B' ω < p_hat := by push_neg at hnot; exact hnot hSp
            have hdiff : m / 2 < μB - B' ω := by dsimp [p_hat, m] at *; linarith
            nlinarith [sq_nonneg (S' ω - μS)]
          · push_neg at hSp
            have hdiff : m / 2 < S' ω - μS := by dsimp [p_hat, m] at *; linarith
            nlinarith [sq_nonneg (B' ω - μB)]
        have h_W2_lb : β * (m / 2) ^ 2 ≤ W ^ 2 := by
          have hc_int : MeasureTheory.IntegrableOn (fun _ : Ω => (m / 2) ^ 2) F μ :=
            MeasureTheory.integrableOn_const (MeasureTheory.measure_ne_top μ F)
          have hsum_int :
              MeasureTheory.IntegrableOn (fun ω => (S' ω - μS) ^ 2 + (B' ω - μB) ^ 2) F μ :=
            (hS2_int.add hB2_int).integrableOn
          have h_mono := MeasureTheory.setIntegral_mono_on hc_int hsum_int hF_meas h_pt_F
          rw [MeasureTheory.setIntegral_const, smul_eq_mul,
              MeasureTheory.integral_add hS2_int.integrableOn hB2_int.integrableOn] at h_mono
          change β * (m / 2) ^ 2 ≤ VS + VB at h_mono
          linarith [hW_sq]
        have hW_lb : (3 / 2 : ℝ) * rβ * σ ≤ W := by
          have h1 : ((3 / 2 : ℝ) * rβ * σ) ^ 2 ≤ W ^ 2 := by
            have h_m_sq : ((3 / 2 : ℝ) * σ) ^ 2 ≤ (m / 2) ^ 2 := by nlinarith
            calc ((3 / 2 : ℝ) * rβ * σ) ^ 2
                = rβ ^ 2 * ((3 / 2 : ℝ) * σ) ^ 2 := by ring
              _ = β * ((3 / 2 : ℝ) * σ) ^ 2 := by rw [hrβ_sq]
              _ ≤ β * (m / 2) ^ 2 := mul_le_mul_of_nonneg_left h_m_sq hβ_nn
              _ ≤ W ^ 2 := h_W2_lb
          have h_lhs_nn : 0 ≤ (3 / 2 : ℝ) * rβ * σ := by positivity
          nlinarith
        have hW_pos : 0 < W := lt_of_lt_of_le (by positivity) hW_lb
        set ν : ℝ := W / rβ
        have hν_pos : 0 < ν := div_pos hW_pos hrβ_pos
        have hrβ_ν : rβ * ν = W := mul_div_cancel₀ W hrβ_pos.ne'
        have hβ_ν2 : β * ν ^ 2 = VS + VB := by
          calc β * ν ^ 2 = (rβ * ν) ^ 2 := by rw [mul_pow, hrβ_sq]
            _ = W ^ 2 := by rw [hrβ_ν]
            _ = VS + VB := hW_sq
        have h_pt_loss : ∀ ω ∈ F,
            ν * max (B' ω - S' ω) 0 ≤ 2 * ((S' ω - μS) ^ 2 + (B' ω - μB) ^ 2) + 2 * ν ^ 2 := by
          intro ω hω
          set u : ℝ := S' ω - μS
          set v : ℝ := B' ω - μB
          have huv : (m / 2) ^ 2 ≤ u ^ 2 + v ^ 2 := h_pt_F ω hω
          have hBS_eq : B' ω - S' ω = m + v - u := by dsimp [u, v, m]; ring
          have h_sos : 2 * (u ^ 2 + v ^ 2) + 2 * ν ^ 2 - ν * (m + v - u) =
              (u ^ 2 + v ^ 2 - (m / 2) ^ 2) + (m / 2 - ν) ^ 2 +
              (u + ν / 2) ^ 2 + (v - ν / 2) ^ 2 + ν ^ 2 / 2 := by ring
          have h_lin : ν * (B' ω - S' ω) ≤ 2 * (u ^ 2 + v ^ 2) + 2 * ν ^ 2 := by
            rw [hBS_eq]
            nlinarith [h_sos, huv, sq_nonneg (m / 2 - ν),
                       sq_nonneg (u + ν / 2), sq_nonneg (v - ν / 2), sq_nonneg ν]
          have h_nn_rhs : 0 ≤ 2 * (u ^ 2 + v ^ 2) + 2 * ν ^ 2 := by positivity
          by_cases hpos : 0 ≤ B' ω - S' ω
          · rwa [max_eq_left hpos]
          · push_neg at hpos
            rw [max_eq_right hpos.le, mul_zero]
            exact h_nn_rhs
        have h_int_loss : ν * (∫ ω in F, max (B' ω - S' ω) 0 ∂μ) ≤ 4 * β * ν ^ 2 := by
          have h1_int : MeasureTheory.IntegrableOn (fun ω => ν * max (B' ω - S' ω) 0) F μ :=
            (hmax_int.const_mul ν).integrableOn
          have h_quad_int :
              MeasureTheory.Integrable (fun ω => 2 * ((S' ω - μS) ^ 2 + (B' ω - μB) ^ 2)) μ :=
            (hS2_int.add hB2_int).const_mul 2
          have h_const_int : MeasureTheory.Integrable (fun _ : Ω => 2 * ν ^ 2) μ :=
            MeasureTheory.integrable_const (2 * ν ^ 2)
          have h2_int : MeasureTheory.IntegrableOn
              (fun ω => 2 * ((S' ω - μS) ^ 2 + (B' ω - μB) ^ 2) + 2 * ν ^ 2) F μ :=
            (h_quad_int.add h_const_int).integrableOn
          have h_mono := MeasureTheory.setIntegral_mono_on h1_int h2_int hF_meas h_pt_loss
          rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_add h_quad_int.integrableOn h_const_int.integrableOn,
              MeasureTheory.integral_const_mul,
              MeasureTheory.integral_add hS2_int.integrableOn hB2_int.integrableOn,
              MeasureTheory.setIntegral_const, smul_eq_mul] at h_mono
          change ν * (∫ ω in F, max (B' ω - S' ω) 0 ∂μ) ≤ 2 * (VS + VB) + β * (2 * ν ^ 2) at h_mono
          linarith [hβ_ν2]
        have hL_ub : (∫ ω in F, max (B' ω - S' ω) 0 ∂μ) ≤ 4 * rβ * W := by
          have h1 : (∫ ω in F, max (B' ω - S' ω) 0 ∂μ) ≤ 4 * β * ν := by nlinarith
          have h2 : 4 * β * ν = 4 * rβ * W := by
            calc 4 * β * ν = 4 * rβ * (rβ * ν) := by rw [← hrβ_sq]; ring
              _ = 4 * rβ * W := by rw [hrβ_ν]
          linarith
        have h_radS_F : (rβ * σS - rS) ^ 2 ≤ 2 * σS * agentInfoDrop S' S' B' μ p_hat := by
          have hr := (h_var_drop S' hS' F hF_meas).2.2
          have h_eq_d : σS - (μ.real F * condStdDev S' μ F + μ.real Fᶜ * condStdDev S' μ Fᶜ) =
              agentInfoDrop S' S' B' μ p_hat := by
            unfold agentInfoDrop
            dsimp only [F, E]
            rw [compl_compl, add_comm]
          rwa [h_eq_d] at hr
        have h_radB_F : (rβ * σB - rB) ^ 2 ≤ 2 * σB * agentInfoDrop B' S' B' μ p_hat := by
          have hr := (h_var_drop B' hB' F hF_meas).2.2
          have h_eq_d : σB - (μ.real F * condStdDev B' μ F + μ.real Fᶜ * condStdDev B' μ Fᶜ) =
              agentInfoDrop B' S' B' μ p_hat := by
            unfold agentInfoDrop
            dsimp only [F, E]
            rw [compl_compl, add_comm]
          rwa [h_eq_d] at hr
        have h_sum_rad :
            (rS - rβ * σS) ^ 2 + (rB - rβ * σB) ^ 2 ≤
              2 * σ * totalInfoDrop S' B' μ p_hat := by
          have hDS := hDS_nn p_hat
          have hDB := hDB_nn p_hat
          have h1 : 2 * σS * agentInfoDrop S' S' B' μ p_hat ≤
              2 * σ * agentInfoDrop S' S' B' μ p_hat := by nlinarith
          have h2 : 2 * σB * agentInfoDrop B' S' B' μ p_hat ≤
              2 * σ * agentInfoDrop B' S' B' μ p_hat := by nlinarith
          unfold totalInfoDrop
          nlinarith
        have hrSrB_lb : W ≤ rS + rB := by
          have hsq : W ^ 2 ≤ (rS + rB) ^ 2 := by
            nlinarith [hW_sq, hrS_sq, hrB_sq, mul_nonneg hrS_nn hrB_nn]
          nlinarith [hrS_nn, hrB_nn]
        set a : ℝ := rS - rβ * σS
        set b : ℝ := rB - rβ * σB
        have hab_lb : W / 3 ≤ a + b := by
          dsimp [a, b, σ] at *
          linarith
        have hab_sq : W ^ 2 / 18 ≤ a ^ 2 + b ^ 2 := by
          have h1 : (W / 3) ^ 2 ≤ (a + b) ^ 2 := by nlinarith
          have h2 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
          linarith
        have hW2_prod : (rβ * W * σ) / 12 ≤ W ^ 2 / 18 := by
          have hmul : W * ((3 / 2 : ℝ) * rβ * σ) ≤ W * W :=
            mul_le_mul_of_nonneg_left hW_lb hW_nn
          linarith
        have hD_lb : rβ * W ≤ 24 * totalInfoDrop S' B' μ p_hat := by
          have h_comb : (rβ * W * σ) / 12 ≤ 2 * σ * totalInfoDrop S' B' μ p_hat :=
            le_trans hW2_prod (le_trans hab_sq h_sum_rad)
          nlinarith
        have hD_nn := hD_nn_all p_hat
        linarith

/-- Alias for `lem_toi`. -/
alias lem_trade_or_information := lem_toi

end TraceSqrt
