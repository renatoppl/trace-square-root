import TraceSqrt.Defs

set_option maxHeartbeats 4000000

/-!
# Claims D.1, D.2, and D.3: Nonnegative Information, Gain Decomposition, and Displacement

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Appendix D.1, Claims D.1 `cl:D_pos`, D.2 `cl:decomposition`, and D.3 `cl:trade-displacement`).
-/

namespace TraceSqrt

/-- **Claim D.1 (`cl:D_pos`)**:
For every pair `(S, B)` of square-integrable real random variables on a probability space `(Ω, μ)`
and every common price `p ∈ ℝ`, each marginal information drop `D_S(p), D_B(p)` is nonnegative and
hence `D(p) = D_S(p) + D_B(p) ≥ 0`. -/
theorem claim_D_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S B : Ω → ℝ) (hS : MeasureTheory.MemLp S 2 μ) (hB : MeasureTheory.MemLp B 2 μ)
    (p : ℝ) :
    0 ≤ agentInfoDrop S S B μ p ∧
    0 ≤ agentInfoDrop B S B μ p ∧
    0 ≤ totalInfoDrop S B μ p := by
  have h_one : ∀ (Z : Ω → ℝ), MeasureTheory.MemLp Z 2 μ →
      ∀ (E : Set Ω), MeasureTheory.NullMeasurableSet E μ →
        0 ≤ rvStdDev Z μ - (μ.real E * condStdDev Z μ E + μ.real Eᶜ * condStdDev Z μ Eᶜ) := by
    intro Z hZ E hE_nm
    let Z' : Ω → ℝ := hZ.aemeasurable.mk Z
    have hZZ' : Z =ᵐ[μ] Z' := hZ.aemeasurable.ae_eq_mk
    have hZ' : MeasureTheory.MemLp Z' 2 μ := hZ.ae_eq hZZ'
    obtain ⟨E', hE'_meas, hEE'⟩ := hE_nm
    have hEE'c : (Eᶜ : Set Ω) =ᵐ[μ] E'ᶜ := hEE'.compl
    have h_cond_eq : ∀ {A A' : Set Ω}, A =ᵐ[μ] A' →
        ProbabilityTheory.cond μ A = ProbabilityTheory.cond μ A' := by
      intro A A' hAA'
      change (μ A)⁻¹ • μ.restrict A = (μ A')⁻¹ • μ.restrict A'
      rw [MeasureTheory.measure_congr hAA', MeasureTheory.Measure.restrict_congr_set hAA']
    have h_sig_eq : rvStdDev Z μ = rvStdDev Z' μ := by
      unfold rvStdDev; rw [ProbabilityTheory.variance_congr hZZ']
    have h_cs1 : condStdDev Z μ E = condStdDev Z' μ E' := by
      unfold condStdDev rvStdDev
      rw [h_cond_eq hEE', ProbabilityTheory.variance_congr
        (ProbabilityTheory.cond_absolutelyContinuous.ae_eq hZZ')]
    have h_cs0 : condStdDev Z μ Eᶜ = condStdDev Z' μ E'ᶜ := by
      unfold condStdDev rvStdDev
      rw [h_cond_eq hEE'c, ProbabilityTheory.variance_congr
        (ProbabilityTheory.cond_absolutelyContinuous.ae_eq hZZ')]
    rw [h_sig_eq, MeasureTheory.measureReal_congr hEE', MeasureTheory.measureReal_congr hEE'c,
        h_cs1, h_cs0]
    set muZ : ℝ := ∫ ω, Z' ω ∂μ
    set sigZ : ℝ := rvStdDev Z' μ
    let W : Ω → ℝ := fun ω => Z' ω - muZ
    have hW : MeasureTheory.MemLp W 2 μ := hZ'.sub (MeasureTheory.memLp_const muZ)
    have hW2_int : MeasureTheory.Integrable (fun ω => (W ω) ^ 2) μ := hW.integrable_sq
    have hsigZ_sq : sigZ ^ 2 = ∫ ω, (W ω) ^ 2 ∂μ := by
      calc sigZ ^ 2 = ProbabilityTheory.variance Z' μ :=
             Real.sq_sqrt (ProbabilityTheory.variance_nonneg Z' μ)
        _ = ∫ ω, (W ω) ^ 2 ∂μ :=
             ProbabilityTheory.variance_eq_integral hZ'.aemeasurable
    have h_branch : ∀ (A : Set Ω), MeasurableSet A →
        (μ.real A * condStdDev Z' μ A) ^ 2 =
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
          gcongr; exact Set.inter_subset_right
        have hZ_ν : MeasureTheory.MemLp Z' 2 ν :=
          hZ'.of_measure_le_smul (ENNReal.inv_ne_top.mpr hμA) h_le
        have hW_ν : MeasureTheory.MemLp W 2 ν := hZ_ν.sub (MeasureTheory.memLp_const muZ)
        have h_var1 : ProbabilityTheory.variance W ν =
            (∫ ω, (W ω) ^ 2 ∂ν) - (∫ ω, W ω ∂ν) ^ 2 := by
          simpa [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub hW_ν
        have h_var2 : ProbabilityTheory.variance W ν = (condStdDev Z' μ A) ^ 2 := by
          rw [ProbabilityTheory.variance_sub_const hZ_ν.aestronglyMeasurable muZ]
          exact (Real.sq_sqrt (ProbabilityTheory.variance_nonneg Z' ν)).symm
        have h_smul_ν : μ A • ν = μ.restrict A := by
          change μ A • ((μ A)⁻¹ • μ.restrict A) = μ.restrict A
          rw [smul_smul, ENNReal.mul_inv_cancel hμA (MeasureTheory.measure_ne_top μ A), one_smul]
        have h_int_A : ∀ g : Ω → ℝ, ∫ ω in A, g ω ∂μ = μ.real A * ∫ ω, g ω ∂ν := fun g => by
          rw [← h_smul_ν, MeasureTheory.integral_smul_measure, smul_eq_mul,
              MeasureTheory.measureReal_def]
        rw [h_int_A W, h_int_A (fun ω => (W ω) ^ 2)]
        linear_combination (μ.real A) ^ 2 * (h_var2.symm.trans h_var1)
    set q1 : ℝ := μ.real E'
    set q0 : ℝ := μ.real E'ᶜ
    set s1 : ℝ := condStdDev Z' μ E'
    set s0 : ℝ := condStdDev Z' μ E'ᶜ
    set v1 : ℝ := ∫ ω in E', (W ω) ^ 2 ∂μ
    set v0 : ℝ := ∫ ω in E'ᶜ, (W ω) ^ 2 ∂μ
    have hq1 : 0 ≤ q1 := MeasureTheory.measureReal_nonneg
    have hq0 : 0 ≤ q0 := MeasureTheory.measureReal_nonneg
    have hs1 : 0 ≤ s1 := Real.sqrt_nonneg _
    have hs0 : 0 ≤ s0 := Real.sqrt_nonneg _
    have hv1 : 0 ≤ v1 := MeasureTheory.setIntegral_nonneg hE'_meas fun ω _ => sq_nonneg (W ω)
    have hv0 : 0 ≤ v0 := MeasureTheory.setIntegral_nonneg hE'_meas.compl fun ω _ => sq_nonneg (W ω)
    have hq_sum : q1 + q0 = 1 := MeasureTheory.probReal_add_probReal_compl hE'_meas
    have hv_sum : v1 + v0 = sigZ ^ 2 := by
      rw [hsigZ_sq]; exact MeasureTheory.integral_add_compl hE'_meas hW2_int
    have hb1 := h_branch E' hE'_meas
    have hb0 := h_branch E'ᶜ hE'_meas.compl
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
      have h_sq : (q1 * s1) ^ 2 ≤ (rq1 * rv1) ^ 2 := by
        calc (q1 * s1) ^ 2 = q1 * v1 - (∫ ω in E', W ω ∂μ) ^ 2 := hb1
          _ ≤ q1 * v1 := by linarith [sq_nonneg (∫ ω in E', W ω ∂μ)]
          _ = rq1 ^ 2 * rv1 ^ 2 := by rw [hrq1_sq, hrv1_sq]
          _ = (rq1 * rv1) ^ 2 := by ring
      nlinarith [mul_nonneg hq1 hs1, mul_nonneg hrq1_nn hrv1_nn]
    have hqs0_le : q0 * s0 ≤ rq0 * rv0 := by
      have h_sq : (q0 * s0) ^ 2 ≤ (rq0 * rv0) ^ 2 := by
        calc (q0 * s0) ^ 2 = q0 * v0 - (∫ ω in E'ᶜ, W ω ∂μ) ^ 2 := hb0
          _ ≤ q0 * v0 := by linarith [sq_nonneg (∫ ω in E'ᶜ, W ω ∂μ)]
          _ = rq0 ^ 2 * rv0 ^ 2 := by rw [hrq0_sq, hrv0_sq]
          _ = (rq0 * rv0) ^ 2 := by ring
      nlinarith [mul_nonneg hq0 hs0, mul_nonneg hrq0_nn hrv0_nn]
    have h_lagrange : (rq1 * rv1 + rq0 * rv0) ^ 2 ≤ sigZ ^ 2 := by
      have h_id : (rq1 * rv1 + rq0 * rv0) ^ 2 + (rq1 * rv0 - rq0 * rv1) ^ 2 =
          (rq1 ^ 2 + rq0 ^ 2) * (rv1 ^ 2 + rv0 ^ 2) := by ring
      rw [hrq1_sq, hrq0_sq, hrv1_sq, hrv0_sq, hq_sum, hv_sum, one_mul] at h_id
      linarith [sq_nonneg (rq1 * rv0 - rq0 * rv1)]
    have hsigZ_nn : 0 ≤ sigZ := Real.sqrt_nonneg _
    have h_sum_nn : 0 ≤ rq1 * rv1 + rq0 * rv0 :=
      add_nonneg (mul_nonneg hrq1_nn hrv1_nn) (mul_nonneg hrq0_nn hrv0_nn)
    have h_sum_le : rq1 * rv1 + rq0 * rv0 ≤ sigZ := by nlinarith
    linarith

  have hE_pre : tradeEvent S B p = S ⁻¹' Set.Iic p ∩ B ⁻¹' Set.Ici p := by
    ext ω; simp [tradeEvent]
  have hE_nm : MeasureTheory.NullMeasurableSet (tradeEvent S B p) μ := by
    rw [hE_pre]
    exact (hS.aemeasurable.nullMeasurableSet_preimage measurableSet_Iic).inter
      (hB.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici)
  have h1 : 0 ≤ agentInfoDrop S S B μ p := h_one S hS (tradeEvent S B p) hE_nm
  have h2 : 0 ≤ agentInfoDrop B S B μ p := h_one B hB (tradeEvent S B p) hE_nm
  exact ⟨h1, h2, add_nonneg h1 h2⟩

/-- **Claim D.2 (Gain-from-trade decomposition, `cl:decomposition`)**:
1. **Unconditional `ℝ≥0∞` form** (requiring no independence and no moment bounds, holding even when
   both sides equal `∞`): for any a.e.-measurable real random variables `S, B` on `(Ω, μ)`,
   `∫⁻ ω, ENNReal.ofReal (max (B ω - S ω) 0) ∂μ = ∫⁻ p : ℝ, ENNReal.ofReal (tradeProfile S B μ p)`.
2. **Integrable Bochner form**: whenever `S` and `B` are integrable, `tradeProfile S B μ` is
   Lebesgue integrable on `ℝ` and `G = E[(B - S)_+] = ∫ p : ℝ, α(p) dp`. -/
theorem claim_gain_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S B : Ω → ℝ) (hS_ae : AEMeasurable S μ) (hB_ae : AEMeasurable B μ) :
    ((∫⁻ ω, ENNReal.ofReal (max (B ω - S ω) 0) ∂μ) =
      ∫⁻ p : ℝ, ENNReal.ofReal (tradeProfile S B μ p) ∂MeasureTheory.volume) ∧
    (MeasureTheory.Integrable S μ → MeasureTheory.Integrable B μ →
      MeasureTheory.Integrable (tradeProfile S B μ) MeasureTheory.volume ∧
      (∫ p : ℝ, tradeProfile S B μ p) = availableGain S B μ) := by
  let S' : Ω → ℝ := hS_ae.mk S
  let B' : Ω → ℝ := hB_ae.mk B
  have hSm : Measurable S' := hS_ae.measurable_mk
  have hBm : Measurable B' := hB_ae.measurable_mk
  have hSS' : S =ᵐ[μ] S' := hS_ae.ae_eq_mk
  have hBB' : B =ᵐ[μ] B' := hB_ae.ae_eq_mk
  have h_event_ae : ∀ p : ℝ, (tradeEvent S B p : Set Ω) =ᵐ[μ] tradeEvent S' B' p := by
    intro p
    rw [Filter.eventuallyEq_set]
    filter_upwards [hSS', hBB'] with ω hωS hωB
    simp [tradeEvent, hωS, hωB]
  have h_prof_eq : tradeProfile S B μ = tradeProfile S' B' μ := by
    ext p
    exact MeasureTheory.measureReal_congr (h_event_ae p)

  let A : Set (Ω × ℝ) := {q | S' q.1 ≤ q.2 ∧ q.2 ≤ B' q.1}
  have hA_meas : MeasurableSet A :=
    (measurableSet_le (hSm.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hBm.comp measurable_fst))

  -- Part 1: Unconditional ℝ≥0∞ Tonelli identity
  have h_lint : (∫⁻ ω, ENNReal.ofReal (max (B ω - S ω) 0) ∂μ) =
      ∫⁻ p : ℝ, ENNReal.ofReal (tradeProfile S B μ p) ∂MeasureTheory.volume := by
    have h_lhs_congr : (∫⁻ ω, ENNReal.ofReal (max (B ω - S ω) 0) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal (max (B' ω - S' ω) 0) ∂μ := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [hSS', hBB'] with ω hωS hωB
      rw [hωS, hωB]
    rw [h_lhs_congr, h_prof_eq]
    let Fe : Ω × ℝ → ENNReal := A.indicator (fun _ => (1 : ENNReal))
    have hFe_meas : Measurable Fe := measurable_const.indicator hA_meas
    have h_slice_ω : ∀ ω : Ω,
        (∫⁻ p : ℝ, Fe (ω, p) ∂MeasureTheory.volume) = ENNReal.ofReal (max (B' ω - S' ω) 0) := by
      intro ω
      have h_ind : (fun p : ℝ => Fe (ω, p)) =
          (Set.Icc (S' ω) (B' ω)).indicator (fun _ => (1 : ENNReal)) := by
        ext p; by_cases hp : S' ω ≤ p ∧ p ≤ B' ω <;> simp [Fe, A, Set.mem_Icc, hp]
      rw [h_ind, MeasureTheory.lintegral_indicator_const measurableSet_Icc, one_mul,
          Real.volume_Icc]
      by_cases hle : S' ω ≤ B' ω
      · rw [max_eq_left (sub_nonneg.mpr hle)]
      · push_neg at hle
        rw [max_eq_right (by linarith), ENNReal.ofReal_of_nonpos (by linarith), ENNReal.ofReal_zero]
    have h_slice_p : ∀ p : ℝ,
        (∫⁻ ω : Ω, Fe (ω, p) ∂μ) = ENNReal.ofReal (tradeProfile S' B' μ p) := by
      intro p
      have h_event_meas : MeasurableSet (tradeEvent S' B' p) :=
        (measurableSet_le hSm measurable_const).inter (measurableSet_le measurable_const hBm)
      have h_ind : (fun ω : Ω => Fe (ω, p)) =
          (tradeEvent S' B' p).indicator (fun _ => (1 : ENNReal)) := by
        ext ω; by_cases hω : S' ω ≤ p ∧ p ≤ B' ω <;> simp [Fe, A, tradeEvent, hω]
      rw [h_ind, MeasureTheory.lintegral_indicator_const h_event_meas, one_mul]
      rw [tradeProfile, MeasureTheory.measureReal_def,
          ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top μ _)]
    calc ∫⁻ ω, ENNReal.ofReal (max (B' ω - S' ω) 0) ∂μ
        = ∫⁻ ω, (∫⁻ p : ℝ, Fe (ω, p) ∂MeasureTheory.volume) ∂μ := by
            simp_rw [h_slice_ω]
      _ = ∫⁻ q : Ω × ℝ, Fe q ∂(μ.prod MeasureTheory.volume) :=
            (MeasureTheory.lintegral_prod Fe hFe_meas.aemeasurable).symm
      _ = ∫⁻ p : ℝ, (∫⁻ ω : Ω, Fe (ω, p) ∂μ) ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_prod_symm Fe hFe_meas.aemeasurable
      _ = ∫⁻ p : ℝ, ENNReal.ofReal (tradeProfile S' B' μ p) ∂MeasureTheory.volume := by
            simp_rw [h_slice_p]

  refine ⟨h_lint, ?_⟩
  intro hS_int hB_int
  have hS'_int : MeasureTheory.Integrable S' μ := (MeasureTheory.integrable_congr hSS').mp hS_int
  have hB'_int : MeasureTheory.Integrable B' μ := (MeasureTheory.integrable_congr hBB').mp hB_int
  have h_gain_eq : availableGain S B μ = availableGain S' B' μ := by
    unfold availableGain
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hSS', hBB'] with ω hωS hωB
    rw [hωS, hωB]
  rw [h_prof_eq, h_gain_eq]
  let F : Ω × ℝ → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hF_meas : Measurable F := measurable_const.indicator hA_meas
  have h_F_nonneg : ∀ q : Ω × ℝ, 0 ≤ F q :=
    fun q => Set.indicator_nonneg (fun _ _ => zero_le_one) q
  have h_slice_h : ∀ ω : Ω,
      (fun p : ℝ => F (ω, p)) = (Set.Icc (S' ω) (B' ω)).indicator (fun _ => (1 : ℝ)) := by
    intro ω; ext p
    by_cases hp : S' ω ≤ p ∧ p ≤ B' ω <;> simp [F, A, Set.mem_Icc, hp]
  have h_slice_int : ∀ ω : Ω,
      MeasureTheory.Integrable (fun p : ℝ => F (ω, p)) MeasureTheory.volume := by
    intro ω
    rw [h_slice_h ω, MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have h_slice_val : ∀ ω : Ω, (∫ p : ℝ, F (ω, p)) = max (B' ω - S' ω) 0 := by
    intro ω
    rw [h_slice_h ω, MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Icc,
        smul_eq_mul, mul_one, Real.volume_real_Icc]
  have h_slice_norm : ∀ ω : Ω, (∫ p : ℝ, ‖F (ω, p)‖) = max (B' ω - S' ω) 0 := by
    intro ω
    have h_eq : (fun p : ℝ => ‖F (ω, p)‖) = (fun p : ℝ => F (ω, p)) := by
      ext p; exact Real.norm_of_nonneg (h_F_nonneg (ω, p))
    rw [h_eq, h_slice_val ω]
  have hBS_int : MeasureTheory.Integrable (fun ω => max (B' ω - S' ω) 0) μ :=
    (hB'_int.sub hS'_int).sup (MeasureTheory.integrable_zero Ω ℝ μ)
  have hF_int : MeasureTheory.Integrable F (μ.prod MeasureTheory.volume) := by
    rw [MeasureTheory.integrable_prod_iff hF_meas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall h_slice_int, ?_⟩
    simpa only [h_slice_norm] using hBS_int
  have h_slice_v : ∀ p : ℝ,
      (fun ω : Ω => F (ω, p)) = (tradeEvent S' B' p).indicator (fun _ => (1 : ℝ)) := by
    intro p; ext ω
    by_cases hω : S' ω ≤ p ∧ p ≤ B' ω <;> simp [F, A, tradeEvent, hω]
  have h_event_meas : ∀ p : ℝ, MeasurableSet (tradeEvent S' B' p) := fun p =>
    (measurableSet_le hSm measurable_const).inter (measurableSet_le measurable_const hBm)
  have h_slice_v_val : ∀ p : ℝ, (∫ ω : Ω, F (ω, p) ∂μ) = tradeProfile S' B' μ p := by
    intro p
    rw [h_slice_v p, MeasureTheory.integral_indicator_const (1 : ℝ) (h_event_meas p),
        smul_eq_mul, mul_one]
    rfl
  have h_prof_int : MeasureTheory.Integrable (tradeProfile S' B' μ) MeasureTheory.volume := by
    simpa only [h_slice_v_val] using hF_int.integral_prod_right
  have h_prof_area : (∫ p : ℝ, tradeProfile S' B' μ p) = availableGain S' B' μ := by
    calc (∫ p : ℝ, tradeProfile S' B' μ p)
        = ∫ p : ℝ, (∫ ω : Ω, F (ω, p) ∂μ) := by simp only [h_slice_v_val]
      _ = ∫ q : Ω × ℝ, F q ∂(μ.prod MeasureTheory.volume) :=
            (MeasureTheory.integral_prod_symm F hF_int).symm
      _ = ∫ ω : Ω, (∫ p : ℝ, F (ω, p)) ∂μ := MeasureTheory.integral_prod F hF_int
      _ = availableGain S' B' μ := by simp only [h_slice_val]; rfl
  exact ⟨h_prof_int, h_prof_area⟩

/-- **Claim D.3 (Information is displacement, `cl:trade-displacement`)**:
For a square-integrable real random variable `Z` on a probability space `(Ω, μ)` and a measurable
binary signal `Y : Ω → Bool`:
1. `∑ y, P(Y = y) δ_{Z|{Y=y}}^2 = 2 σ_Z (σ_Z - ∑ y, P(Y = y) sd(Z | Y = y))`
   (with zero-probability branches contributing zero).
2. For any measurable event `E` with `μ E ≠ 0`:
   `|E[Z | E] - μ_Z| ≤ δ_{Z|E}`, `|ϱ_{Z|E} - σ_Z| ≤ δ_{Z|E}`, and if
   `|E[Z | E] - μ_Z| ≥ η > 0`, then `ϱ_{Z|E} ≤ (1 + σ_Z / η) δ_{Z|E}`. -/
theorem claim_trade_displacement {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : MeasureTheory.MemLp Z 2 μ)
    (Y : Ω → Bool) (hY : Measurable Y) :
    (∑ b : Bool, μ.real {ω | Y ω = b} * posteriorDeltaSq Z μ {ω | Y ω = b} =
      2 * rvStdDev Z μ *
        (rvStdDev Z μ - ∑ b : Bool, μ.real {ω | Y ω = b} * condStdDev Z μ {ω | Y ω = b})) ∧
    (∀ E : Set Ω, MeasurableSet E → μ E ≠ 0 →
      |condMean Z μ E - ∫ ω, Z ω ∂μ| ≤ posteriorDelta Z μ E ∧
      |posteriorVarrho Z μ E - rvStdDev Z μ| ≤ posteriorDelta Z μ E ∧
      (∀ η : ℝ, 0 < η → η ≤ |condMean Z μ E - ∫ ω, Z ω ∂μ| →
        posteriorVarrho Z μ E ≤ (1 + rvStdDev Z μ / η) * posteriorDelta Z μ E)) :=
by
  let μZ : ℝ := ∫ ω, Z ω ∂μ
  let σZ : ℝ := rvStdDev Z μ
  have hσZ_nonneg : 0 ≤ σZ := Real.sqrt_nonneg _
  have hσZ_sq : σZ ^ 2 = ∫ ω, (Z ω - μZ) ^ 2 ∂μ := by
    calc σZ ^ 2 = ProbabilityTheory.variance Z μ :=
           Real.sq_sqrt (ProbabilityTheory.variance_nonneg Z μ)
      _ = ∫ ω, (Z ω - μZ) ^ 2 ∂μ :=
           ProbabilityTheory.variance_eq_integral hZ.aemeasurable
  have h_cond_sq : ∀ (E : Set Ω), MeasurableSet E → μ E ≠ 0 →
      ∫ ω, (Z ω - μZ) ^ 2 ∂(ProbabilityTheory.cond μ E) =
        (condMean Z μ E - μZ) ^ 2 + (condStdDev Z μ E) ^ 2 := by
    intro E hE hμE
    set ν := ProbabilityTheory.cond μ E
    haveI : MeasureTheory.IsProbabilityMeasure ν :=
      ProbabilityTheory.cond_isProbabilityMeasure hμE
    have h_le : ν ≤ (μ E)⁻¹ • μ := by
      rw [MeasureTheory.Measure.le_iff]
      intro t _
      rw [ProbabilityTheory.cond_apply hE, MeasureTheory.Measure.smul_apply, smul_eq_mul]
      gcongr
      exact Set.inter_subset_right
    have hZ_ν : MeasureTheory.MemLp Z 2 ν :=
      hZ.of_measure_le_smul (ENNReal.inv_ne_top.mpr hμE) h_le
    have hW : MeasureTheory.MemLp (fun ω => Z ω - μZ) 2 ν :=
      hZ_ν.sub (MeasureTheory.memLp_const μZ)
    have h_var1 : ProbabilityTheory.variance (fun ω => Z ω - μZ) ν =
        (∫ ω, (Z ω - μZ) ^ 2 ∂ν) - (∫ ω, (Z ω - μZ) ∂ν) ^ 2 := by
      simpa [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub hW
    have h_var2 : ProbabilityTheory.variance (fun ω => Z ω - μZ) ν =
        (condStdDev Z μ E) ^ 2 := by
      rw [ProbabilityTheory.variance_sub_const hZ_ν.aestronglyMeasurable μZ]
      exact (Real.sq_sqrt (ProbabilityTheory.variance_nonneg Z ν)).symm
    have h_int_W : ∫ ω, (Z ω - μZ) ∂ν = condMean Z μ E - μZ := by
      rw [MeasureTheory.integral_sub (hZ_ν.integrable one_le_two) (MeasureTheory.integrable_const μZ),
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
      rfl
    rw [h_int_W] at h_var1
    linarith
  constructor
  · let f : Ω → ℝ := fun ω => (Z ω - μZ) ^ 2
    have hf : MeasureTheory.Integrable f μ :=
      (hZ.sub (MeasureTheory.memLp_const μZ)).integrable_sq
    have h_pre : ∀ b : Bool, Y ⁻¹' {b} = {ω | Y ω = b} := fun b => by
      ext ω
      simp
    have h_prob_sum : ∑ b : Bool, μ.real {ω | Y ω = b} = 1 := by
      rw [Fintype.sum_bool]
      have h_compl : {ω | Y ω = false} = {ω | Y ω = true}ᶜ := by
        ext ω
        simp
      have h_meas_true : MeasurableSet {ω | Y ω = true} := by
        rw [← h_pre true]
        exact hY (measurableSet_singleton true)
      rw [h_compl]
      exact MeasureTheory.probReal_add_probReal_compl h_meas_true
    have h_meas_sum := ProbabilityTheory.sum_meas_smul_cond_fiber hY μ
    let ν_meas : Bool → MeasureTheory.Measure Ω :=
      fun b => μ (Y ⁻¹' {b}) • ProbabilityTheory.cond μ (Y ⁻¹' {b})
    have h_int_le : ∀ b ∈ (Finset.univ : Finset Bool), MeasureTheory.Integrable f (ν_meas b) := by
      intro b _
      apply hf.mono_measure
      rw [← h_meas_sum, Fintype.sum_bool, MeasureTheory.Measure.le_iff]
      intro s _
      rw [MeasureTheory.Measure.add_apply]
      cases b <;> simp [ν_meas]
    have h_f_sum : ∫ ω, f ω ∂μ =
        ∑ b : Bool, μ.real {ω | Y ω = b} * ∫ ω, f ω ∂(ProbabilityTheory.cond μ {ω | Y ω = b}) := by
      conv_lhs => rw [← h_meas_sum]
      rw [MeasureTheory.integral_finset_sum_measure h_int_le]
      refine Finset.sum_congr rfl fun b _ => ?_
      dsimp [ν_meas]
      rw [MeasureTheory.integral_smul_measure, smul_eq_mul, h_pre b, MeasureTheory.measureReal_def]
    have h_term : ∀ b : Bool,
        μ.real {ω | Y ω = b} * ∫ ω, f ω ∂(ProbabilityTheory.cond μ {ω | Y ω = b}) =
        μ.real {ω | Y ω = b} * ((condMean Z μ {ω | Y ω = b} - μZ) ^ 2 +
          (condStdDev Z μ {ω | Y ω = b}) ^ 2) := by
      intro b
      by_cases hμb : μ {ω | Y ω = b} = 0
      · have hpb : μ.real {ω | Y ω = b} = 0 := by simp [MeasureTheory.measureReal_def, hμb]
        simp [hpb]
      · have hEb : MeasurableSet {ω | Y ω = b} := by
          rw [← h_pre b]
          exact hY (measurableSet_singleton b)
        rw [h_cond_sq {ω | Y ω = b} hEb hμb]
    have h_tot_var : σZ ^ 2 =
        ∑ b : Bool, μ.real {ω | Y ω = b} *
          ((condMean Z μ {ω | Y ω = b} - μZ) ^ 2 + (condStdDev Z μ {ω | Y ω = b}) ^ 2) := by
      rw [hσZ_sq]
      change ∫ ω, f ω ∂μ = _
      rw [h_f_sum]
      exact Finset.sum_congr rfl fun b _ => h_term b
    simp only [Fintype.sum_bool, posteriorDeltaSq] at h_prob_sum h_tot_var ⊢
    change μ.real {ω | Y ω = true} * ((condMean Z μ {ω | Y ω = true} - μZ) ^ 2 +
          (condStdDev Z μ {ω | Y ω = true} - σZ) ^ 2) +
        μ.real {ω | Y ω = false} * ((condMean Z μ {ω | Y ω = false} - μZ) ^ 2 +
          (condStdDev Z μ {ω | Y ω = false} - σZ) ^ 2) =
      2 * σZ * (σZ - (μ.real {ω | Y ω = true} * condStdDev Z μ {ω | Y ω = true} +
        μ.real {ω | Y ω = false} * condStdDev Z μ {ω | Y ω = false}))
    linear_combination -h_tot_var + σZ ^ 2 * h_prob_sum
  · intro E hE hμE
    set d : ℝ := condMean Z μ E - μZ
    set σE : ℝ := condStdDev Z μ E
    have hσE_nonneg : 0 ≤ σE := Real.sqrt_nonneg _
    set δ : ℝ := posteriorDelta Z μ E
    set ϱ : ℝ := posteriorVarrho Z μ E
    have hδ_def : δ = Real.sqrt (d ^ 2 + (σE - σZ) ^ 2) := rfl
    have hϱ_def : ϱ = Real.sqrt (d ^ 2 + σE ^ 2) := by
      change Real.sqrt (∫ ω, (Z ω - μZ) ^ 2 ∂(ProbabilityTheory.cond μ E)) = _
      rw [h_cond_sq E hE hμE]
    have hδ_nonneg : 0 ≤ δ := Real.sqrt_nonneg _
    have hδ_sq : δ ^ 2 = d ^ 2 + (σE - σZ) ^ 2 := by
      rw [hδ_def]
      exact Real.sq_sqrt (by positivity)
    have hϱ_sq : ϱ ^ 2 = d ^ 2 + σE ^ 2 := by
      rw [hϱ_def]
      exact Real.sq_sqrt (by positivity)
    have hb1 : |d| ≤ δ := by
      rw [← Real.sqrt_sq_eq_abs d, hδ_def]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hb2 : |ϱ - σZ| ≤ δ := by
      have hσE_le_ϱ : σE ≤ ϱ := by
        rw [← Real.sqrt_sq hσE_nonneg, hϱ_def]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have h_sq_le : (ϱ - σZ) ^ 2 ≤ δ ^ 2 := by
        nlinarith [mul_nonneg hσZ_nonneg (sub_nonneg.mpr hσE_le_ϱ)]
      rw [← Real.sqrt_sq_eq_abs (ϱ - σZ), ← Real.sqrt_sq hδ_nonneg]
      exact Real.sqrt_le_sqrt h_sq_le
    refine ⟨hb1, hb2, ?_⟩
    intro η hη hηd
    have hϱ_le : ϱ ≤ δ + σZ := by
      linarith [(abs_le.mp hb2).2]
    have hη_le_δ : η ≤ δ := le_trans hηd hb1
    have hσZ_le : σZ ≤ (σZ / η) * δ := by
      have h_div_nonneg : 0 ≤ σZ / η := div_nonneg hσZ_nonneg (le_of_lt hη)
      have h_mul := mul_le_mul_of_nonneg_left hη_le_δ h_div_nonneg
      rwa [div_mul_cancel₀ σZ (ne_of_gt hη)] at h_mul
    calc ϱ ≤ δ + σZ := hϱ_le
      _ ≤ δ + (σZ / η) * δ := by linarith
      _ = (1 + σZ / η) * δ := by ring

/-- Alias for `claim_trade_displacement`. -/
alias lem_trade_displacement := claim_trade_displacement

end TraceSqrt
