import TraceSqrt.Defs

set_option maxHeartbeats 4000000

/-!
# Lemma 2.2: One-Bit Deviation Contraction (`lem:deviation-contraction`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 2.1 Lemma 2.2, proved in Appendix C.2).
-/

namespace TraceSqrt

/-- **Lemma 2.2 (One-bit deviation contraction, `lem:deviation-contraction`)**:
For any square-integrable real random variable `Z` on a probability space `(Ω, μ)`,
posting `P = E[Z] + (sd(Z) / 2) ε` with independent uniform `ε ∈ {-1, 1}` and observing
`Y = sign(Z - P)` satisfies `E[sd(Z | P, Y)] ≤ (23 / 24) sd(Z)`. -/
theorem lem_deviation_contraction {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : MeasureTheory.MemLp Z 2 μ) :
    expectedPosteriorStdDev Z μ ≤ (23 / 24 : ℝ) * rvStdDev Z μ :=
by
  let muZ : ℝ := ∫ ω, Z ω ∂μ
  let sigmaZ : ℝ := rvStdDev Z μ
  have h_sigma_nonneg : 0 ≤ sigmaZ := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le h_sigma_nonneg with h_zero | h_pos
  · have h_var_zero : ProbabilityTheory.variance Z μ = 0 := by
      have h_sqrt0 : Real.sqrt (ProbabilityTheory.variance Z μ) = 0 := h_zero.symm
      have h_le : ProbabilityTheory.variance Z μ ≤ 0 := Real.sqrt_eq_zero'.mp h_sqrt0
      exact le_antisymm h_le (ProbabilityTheory.variance_nonneg Z μ)
    have h_int_sq_zero : (∫ ω, (Z ω - muZ) ^ 2 ∂μ) = 0 := by
      have hv := ProbabilityTheory.variance_eq_integral hZ.aemeasurable
      dsimp only [muZ]
      linarith
    have h_event_zero : ∀ E : Set Ω, μ.real E * condStdDev Z μ E = 0 := by
      intro E
      by_cases hE0 : μ E = 0
      · simp [MeasureTheory.measureReal_def, hE0]
      · haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond μ E) :=
          ProbabilityTheory.cond_isProbabilityMeasure hE0
        have hinv_top : (μ E)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hE0
        have hZ_cond : MeasureTheory.MemLp Z 2 (ProbabilityTheory.cond μ E) :=
          (hZ.restrict E).smul_measure hinv_top
        have hZ_sub : MeasureTheory.MemLp (fun ω => Z ω - muZ) 2 (ProbabilityTheory.cond μ E) :=
          hZ_cond.sub (MeasureTheory.memLp_const muZ)
        have hv1 : ProbabilityTheory.variance Z (ProbabilityTheory.cond μ E) =
            ProbabilityTheory.variance (fun ω => Z ω - muZ) (ProbabilityTheory.cond μ E) :=
          (ProbabilityTheory.variance_sub_const hZ_cond.1 muZ).symm
        have hv2 : ProbabilityTheory.variance (fun ω => Z ω - muZ) (ProbabilityTheory.cond μ E) ≤
            ∫ ω, (Z ω - muZ) ^ 2 ∂(ProbabilityTheory.cond μ E) :=
          ProbabilityTheory.variance_le_expectation_sq hZ_sub.1
        have hv3 : (∫ ω, (Z ω - muZ) ^ 2 ∂(ProbabilityTheory.cond μ E)) =
            ((μ E)⁻¹).toReal * ∫ ω in E, (Z ω - muZ) ^ 2 ∂μ := by
          change (∫ ω, (Z ω - muZ) ^ 2 ∂((μ E)⁻¹ • μ.restrict E)) = _
          rw [MeasureTheory.integral_smul_measure, smul_eq_mul]
        have hint_sq : MeasureTheory.Integrable (fun ω => (Z ω - muZ) ^ 2) μ :=
          (hZ.sub (MeasureTheory.memLp_const muZ)).integrable_sq
        have h_set_le : (∫ ω in E, (Z ω - muZ) ^ 2 ∂μ) ≤ 0 := by
          calc (∫ ω in E, (Z ω - muZ) ^ 2 ∂μ)
              ≤ ∫ ω, (Z ω - muZ) ^ 2 ∂μ :=
                MeasureTheory.setIntegral_le_integral hint_sq
                  (Filter.Eventually.of_forall fun _ => sq_nonneg _)
            _ = 0 := h_int_sq_zero
        have h_cond_le : (∫ ω, (Z ω - muZ) ^ 2 ∂(ProbabilityTheory.cond μ E)) ≤ 0 := by
          rw [hv3]
          exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg h_set_le
        have h_cond_var0 : ProbabilityTheory.variance Z (ProbabilityTheory.cond μ E) = 0 := by
          have h_nonneg := ProbabilityTheory.variance_nonneg Z (ProbabilityTheory.cond μ E)
          linarith
        have h_csd0 : condStdDev Z μ E = 0 := by
          simp [condStdDev, rvStdDev, h_cond_var0]
        rw [h_csd0, mul_zero]
    have h_exp0 : expectedPosteriorStdDev Z μ = 0 := by
      unfold expectedPosteriorStdDev
      dsimp only
      simp only [Fintype.sum_bool, h_event_zero]
      ring
    rw [h_exp0, show rvStdDev Z μ = 0 from h_zero.symm]
    norm_num
  · have h_quad_int : ∀ a m r : ℝ,
        MeasureTheory.Integrable (fun ω => a + (m - Z ω) ^ 2 / r) μ := by
      intro a m r
      have hm : MeasureTheory.MemLp (fun _ : Ω => m) 2 μ := MeasureTheory.memLp_const m
      exact (MeasureTheory.integrable_const a).add ((hm.sub hZ).integrable_sq.div_const r)
    have h_event_bound : ∀ (E : Set Ω) (m r : ℝ), 0 < r →
        2 * (μ.real E * condStdDev Z μ E) ≤ ∫ ω in E, (r + (m - Z ω) ^ 2 / r) ∂μ := by
      intro E m r hr
      by_cases hE0 : μ E = 0
      · have hlhs : 2 * (μ.real E * condStdDev Z μ E) = 0 := by
          simp [MeasureTheory.measureReal_def, hE0]
        rw [hlhs]
        refine MeasureTheory.integral_nonneg fun ω => ?_
        show 0 ≤ r + (m - Z ω) ^ 2 / r
        have h_div : 0 ≤ (m - Z ω) ^ 2 / r := div_nonneg (sq_nonneg _) hr.le
        linarith
      · have hE_top : μ E ≠ ⊤ := MeasureTheory.measure_ne_top μ E
        set p : ℝ := μ.real E
        have hp_pos : 0 < p := by
          dsimp [p]
          rw [MeasureTheory.measureReal_def]
          exact ENNReal.toReal_pos hE0 hE_top
        have hp_ne : p ≠ 0 := hp_pos.ne'
        have hr_ne : r ≠ 0 := hr.ne'
        haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond μ E) :=
          ProbabilityTheory.cond_isProbabilityMeasure hE0
        have hinv_top : (μ E)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hE0
        have hZ_cond : MeasureTheory.MemLp Z 2 (ProbabilityTheory.cond μ E) :=
          (hZ.restrict E).smul_measure hinv_top
        have hZ_sub : MeasureTheory.MemLp (fun ω => Z ω - m) 2 (ProbabilityTheory.cond μ E) :=
          hZ_cond.sub (MeasureTheory.memLp_const m)
        set v : ℝ := ProbabilityTheory.variance Z (ProbabilityTheory.cond μ E)
        set s : ℝ := condStdDev Z μ E
        have hv_nonneg : 0 ≤ v := ProbabilityTheory.variance_nonneg Z (ProbabilityTheory.cond μ E)
        have hs_sq : s ^ 2 = v := Real.sq_sqrt hv_nonneg
        have hv1 : v = ProbabilityTheory.variance (fun ω => Z ω - m) (ProbabilityTheory.cond μ E) :=
          (ProbabilityTheory.variance_sub_const hZ_cond.1 m).symm
        have hv2 : ProbabilityTheory.variance (fun ω => Z ω - m) (ProbabilityTheory.cond μ E) ≤
            ∫ ω, (Z ω - m) ^ 2 ∂(ProbabilityTheory.cond μ E) :=
          ProbabilityTheory.variance_le_expectation_sq hZ_sub.1
        have hv3 : (∫ ω, (Z ω - m) ^ 2 ∂(ProbabilityTheory.cond μ E)) =
            p⁻¹ * ∫ ω in E, (m - Z ω) ^ 2 ∂μ := by
          have h_sq : (fun ω => (Z ω - m) ^ 2) = (fun ω => (m - Z ω) ^ 2) := by
            ext ω; ring
          rw [h_sq]
          change (∫ ω, (m - Z ω) ^ 2 ∂((μ E)⁻¹ • μ.restrict E)) = _
          rw [MeasureTheory.integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
            ← MeasureTheory.measureReal_def]
        have hpv_le : p * v ≤ ∫ ω in E, (m - Z ω) ^ 2 ∂μ := by
          have hv_le : v ≤ p⁻¹ * ∫ ω in E, (m - Z ω) ^ 2 ∂μ := by linarith
          have hmul := mul_le_mul_of_nonneg_left hv_le hp_pos.le
          have hcancel : p * (p⁻¹ * ∫ ω in E, (m - Z ω) ^ 2 ∂μ) = ∫ ω in E, (m - Z ω) ^ 2 ∂μ := by
            field_simp
          linarith
        have h_amgm : 2 * s ≤ r + v / r := by
          have hsq : 0 ≤ (r - s) ^ 2 := sq_nonneg (r - s)
          have halg : (r - s) ^ 2 / r = r - 2 * s + v / r := by
            rw [sub_sq, hs_sq]
            field_simp
          have hdiv_nonneg : 0 ≤ (r - s) ^ 2 / r := div_nonneg hsq hr.le
          linarith
        have h_lhs_le : 2 * (p * s) ≤ p * r + (∫ ω in E, (m - Z ω) ^ 2 ∂μ) / r := by
          have h1 : p * (2 * s) ≤ p * (r + v / r) := mul_le_mul_of_nonneg_left h_amgm hp_pos.le
          have h2 : (p * v) / r ≤ (∫ ω in E, (m - Z ω) ^ 2 ∂μ) / r :=
            div_le_div_of_nonneg_right hpv_le hr.le
          have h3 : p * (r + v / r) = p * r + (p * v) / r := by ring
          linarith
        have hint_r : MeasureTheory.IntegrableOn (fun _ : Ω => r) E μ :=
          (MeasureTheory.integrable_const r).integrableOn
        have hint_q : MeasureTheory.IntegrableOn (fun ω => (m - Z ω) ^ 2 / r) E μ :=
          (((MeasureTheory.memLp_const m).sub hZ).integrable_sq.div_const r).integrableOn
        have h_rhs_eq : (∫ ω in E, (r + (m - Z ω) ^ 2 / r) ∂μ) =
            p * r + (∫ ω in E, (m - Z ω) ^ 2 ∂μ) / r := by
          rw [MeasureTheory.integral_add hint_r hint_q, MeasureTheory.setIntegral_const,
            smul_eq_mul, MeasureTheory.integral_div]
        linarith
    have h_recombine : ∀ (m r eps : ℝ) (ft ff : Ω → ℝ),
        MeasureTheory.Integrable ft μ → MeasureTheory.Integrable ff μ →
        MeasureTheory.Integrable
          (fun ω => if 0 ≤ Z ω - (m + (r / 2) * eps) then ft ω else ff ω) μ ∧
        (∫ ω in searchBranchEvent Z m r eps true, ft ω ∂μ) +
            (∫ ω in searchBranchEvent Z m r eps false, ff ω ∂μ) =
          ∫ ω, (if 0 ≤ Z ω - (m + (r / 2) * eps) then ft ω else ff ω) ∂μ := by
      intro m r eps ft ff hft hff
      let t := m + (r / 2) * eps
      let S := searchBranchEvent Z m r eps true
      have hS_eq : S = Z ⁻¹' Set.Ici t := by
        ext ω
        simp [S, t, searchBranchEvent, sub_nonneg]
      have hSf_eq : searchBranchEvent Z m r eps false = Sᶜ := by
        ext ω
        simp [S, searchBranchEvent]
      have hS_nm : MeasureTheory.NullMeasurableSet S μ := by
        rw [hS_eq]
        exact hZ.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici
      have hg_eq : (fun ω => if 0 ≤ Z ω - (m + (r / 2) * eps) then ft ω else ff ω) =
          (fun ω => S.indicator ft ω + Sᶜ.indicator ff ω) := by
        ext ω
        by_cases h : 0 ≤ Z ω - (m + (r / 2) * eps)
        · have hmem : ω ∈ S := by
            show decide (0 ≤ Z ω - (m + (r / 2) * eps)) = true
            exact decide_eq_true h
          simp [Set.indicator, h, hmem]
        · have hnmem : ω ∉ S := by
            intro hm
            exact h (of_decide_eq_true hm)
          simp [Set.indicator, h, hnmem]
      have hint_t : MeasureTheory.Integrable (S.indicator ft) μ := hft.indicator₀ hS_nm
      have hint_f : MeasureTheory.Integrable (Sᶜ.indicator ff) μ := hff.indicator₀ hS_nm.compl
      refine ⟨?_, ?_⟩
      · rw [hg_eq]
        exact hint_t.add hint_f
      · rw [hg_eq, MeasureTheory.integral_add hint_t hint_f,
          MeasureTheory.integral_indicator₀ hS_nm, MeasureTheory.integral_indicator₀ hS_nm.compl,
          hSf_eq]
    let psi : ℝ → ℝ → ℝ → ℝ → ℝ := fun m r eps z =>
      if 0 ≤ z - (m + (r / 2) * eps) then
        3 * r / (3 - eps) + (m + r / (3 - eps) - z) ^ 2 / (3 * r / (3 - eps))
      else
        3 * r / (3 + eps) + (m - r / (3 + eps) - z) ^ 2 / (3 * r / (3 + eps))
    have h_pointwise : ∀ (m r z : ℝ), 0 < r →
        (1 / 2 : ℝ) * (psi m r (-1) z + psi m r 1 z) ≤
          (11 / 12 : ℝ) * r + (m - z) ^ 2 / r := by
      intro m r z hr
      have hr_ne : r ≠ 0 := hr.ne'
      rcases lt_or_ge z (m - r / 2) with hzL | hzM
      · have h1 : ¬(0 ≤ z - (m + (r / 2) * (-1))) := by linarith
        have h2 : ¬(0 ≤ z - (m + (r / 2) * 1)) := by linarith
        have hp1 : psi m r (-1) z =
            3 * r / (3 + (-1)) + (m - r / (3 + (-1)) - z) ^ 2 / (3 * r / (3 + (-1))) :=
          if_neg h1
        have hp2 : psi m r 1 z =
            3 * r / (3 + 1) + (m - r / (3 + 1) - z) ^ 2 / (3 * r / (3 + 1)) :=
          if_neg h2
        rw [hp1, hp2]
        have h_diff : ((11 / 12 : ℝ) * r + (m - z) ^ 2 / r) -
            (1 / 2 : ℝ) *
              ((3 * r / (3 + (-1)) + (m - r / (3 + (-1)) - z) ^ 2 / (3 * r / (3 + (-1)))) +
               (3 * r / (3 + 1) + (m - r / (3 + 1) - z) ^ 2 / (3 * r / (3 + 1)))) =
            (2 / 3 : ℝ) * (m - z) - (1 / 3 : ℝ) * r := by
          norm_num
          field_simp
          ring
        linarith
      · rcases lt_or_ge z (m + r / 2) with hzM2 | hzR
        · have h1 : 0 ≤ z - (m + (r / 2) * (-1)) := by linarith
          have h2 : ¬(0 ≤ z - (m + (r / 2) * 1)) := by linarith
          have hp1 : psi m r (-1) z =
              3 * r / (3 - (-1)) + (m + r / (3 - (-1)) - z) ^ 2 / (3 * r / (3 - (-1))) :=
            if_pos h1
          have hp2 : psi m r 1 z =
              3 * r / (3 + 1) + (m - r / (3 + 1) - z) ^ 2 / (3 * r / (3 + 1)) :=
            if_neg h2
          rw [hp1, hp2]
          have h_diff : ((11 / 12 : ℝ) * r + (m - z) ^ 2 / r) -
              (1 / 2 : ℝ) *
                ((3 * r / (3 - (-1)) + (m + r / (3 - (-1)) - z) ^ 2 / (3 * r / (3 - (-1)))) +
                 (3 * r / (3 + 1) + (m - r / (3 + 1) - z) ^ 2 / (3 * r / (3 + 1)))) =
              r / 12 - (m - z) ^ 2 / (3 * r) := by
            norm_num
            field_simp
            ring
          have h_sq_div : (m - z) ^ 2 / (3 * r) ≤ r / 12 := by
            rw [div_le_iff₀ (by linarith : 0 < 3 * r)]
            nlinarith
          linarith
        · have h1 : 0 ≤ z - (m + (r / 2) * (-1)) := by linarith
          have h2 : 0 ≤ z - (m + (r / 2) * 1) := by linarith
          have hp1 : psi m r (-1) z =
              3 * r / (3 - (-1)) + (m + r / (3 - (-1)) - z) ^ 2 / (3 * r / (3 - (-1))) :=
            if_pos h1
          have hp2 : psi m r 1 z =
              3 * r / (3 - 1) + (m + r / (3 - 1) - z) ^ 2 / (3 * r / (3 - 1)) :=
            if_pos h2
          rw [hp1, hp2]
          have h_diff : ((11 / 12 : ℝ) * r + (m - z) ^ 2 / r) -
              (1 / 2 : ℝ) *
                ((3 * r / (3 - (-1)) + (m + r / (3 - (-1)) - z) ^ 2 / (3 * r / (3 - (-1)))) +
                 (3 * r / (3 - 1) + (m + r / (3 - 1) - z) ^ 2 / (3 * r / (3 - 1)))) =
              (2 / 3 : ℝ) * (z - m) - (1 / 3 : ℝ) * r := by
            norm_num
            field_simp
            ring
          linarith
    have h_coin : ∀ eps : ℝ, 0 < 3 - eps → 0 < 3 + eps →
        MeasureTheory.Integrable (fun ω => psi muZ sigmaZ eps (Z ω)) μ ∧
        2 * (∑ b : Bool,
          μ.real (searchBranchEvent Z muZ sigmaZ eps b) *
            condStdDev Z μ (searchBranchEvent Z muZ sigmaZ eps b)) ≤
          ∫ ω, psi muZ sigmaZ eps (Z ω) ∂μ := by
      intro eps h3m h3p
      let rt : ℝ := 3 * sigmaZ / (3 - eps)
      let mt : ℝ := muZ + sigmaZ / (3 - eps)
      let rf : ℝ := 3 * sigmaZ / (3 + eps)
      let mf : ℝ := muZ - sigmaZ / (3 + eps)
      have hrt_pos : 0 < rt := div_pos (by linarith) h3m
      have hrf_pos : 0 < rf := div_pos (by linarith) h3p
      have hft_int : MeasureTheory.Integrable (fun ω => rt + (mt - Z ω) ^ 2 / rt) μ :=
        h_quad_int rt mt rt
      have hff_int : MeasureTheory.Integrable (fun ω => rf + (mf - Z ω) ^ 2 / rf) μ :=
        h_quad_int rf mf rf
      obtain ⟨hint_psi, hsum_eq⟩ := h_recombine muZ sigmaZ eps
        (fun ω => rt + (mt - Z ω) ^ 2 / rt)
        (fun ω => rf + (mf - Z ω) ^ 2 / rf)
        hft_int hff_int
      refine ⟨hint_psi, ?_⟩
      rw [Fintype.sum_bool, mul_add]
      have hb_t := h_event_bound (searchBranchEvent Z muZ sigmaZ eps true) mt rt hrt_pos
      have hb_f := h_event_bound (searchBranchEvent Z muZ sigmaZ eps false) mf rf hrf_pos
      linarith
    obtain ⟨hint_neg, hbound_neg⟩ := h_coin (-1) (by norm_num) (by norm_num)
    obtain ⟨hint_pos, hbound_pos⟩ := h_coin 1 (by norm_num) (by norm_num)
    have hint_avg : MeasureTheory.Integrable
        (fun ω => (1 / 2 : ℝ) * (psi muZ sigmaZ (-1) (Z ω) + psi muZ sigmaZ 1 (Z ω))) μ :=
      (hint_neg.add hint_pos).const_mul (1 / 2 : ℝ)
    have hint_rhs : MeasureTheory.Integrable
        (fun ω => (11 / 12 : ℝ) * sigmaZ + (muZ - Z ω) ^ 2 / sigmaZ) μ :=
      h_quad_int ((11 / 12 : ℝ) * sigmaZ) muZ sigmaZ
    have h_avg_eq : (1 / 2 : ℝ) *
        ((∫ ω, psi muZ sigmaZ (-1) (Z ω) ∂μ) + (∫ ω, psi muZ sigmaZ 1 (Z ω) ∂μ)) =
        ∫ ω, (1 / 2 : ℝ) * (psi muZ sigmaZ (-1) (Z ω) + psi muZ sigmaZ 1 (Z ω)) ∂μ := by
      rw [← MeasureTheory.integral_add hint_neg hint_pos, ← MeasureTheory.integral_const_mul]
    have h_mono : (∫ ω, (1 / 2 : ℝ) * (psi muZ sigmaZ (-1) (Z ω) + psi muZ sigmaZ 1 (Z ω)) ∂μ) ≤
        ∫ ω, ((11 / 12 : ℝ) * sigmaZ + (muZ - Z ω) ^ 2 / sigmaZ) ∂μ :=
      MeasureTheory.integral_mono hint_avg hint_rhs fun ω =>
        h_pointwise muZ sigmaZ (Z ω) h_pos
    have h_prior_eval : (∫ ω, ((11 / 12 : ℝ) * sigmaZ + (muZ - Z ω) ^ 2 / sigmaZ) ∂μ) =
        (23 / 12 : ℝ) * sigmaZ := by
      have hc_int : MeasureTheory.Integrable (fun _ : Ω => (11 / 12 : ℝ) * sigmaZ) μ :=
        MeasureTheory.integrable_const _
      have hq_int : MeasureTheory.Integrable (fun ω => (muZ - Z ω) ^ 2 / sigmaZ) μ :=
        (((MeasureTheory.memLp_const muZ).sub hZ).integrable_sq).div_const sigmaZ
      rw [MeasureTheory.integral_add hc_int hq_int, MeasureTheory.integral_const,
        MeasureTheory.probReal_univ, one_smul, MeasureTheory.integral_div]
      have h_sq_comm : (∫ ω, (muZ - Z ω) ^ 2 ∂μ) = ProbabilityTheory.variance Z μ := by
        have hfun : (fun ω => (muZ - Z ω) ^ 2) = (fun ω => (Z ω - muZ) ^ 2) := by
          ext ω; ring
        rw [hfun, ProbabilityTheory.variance_eq_integral hZ.aemeasurable]
      have h_var_sq : ProbabilityTheory.variance Z μ = sigmaZ ^ 2 :=
        (Real.sq_sqrt (ProbabilityTheory.variance_nonneg Z μ)).symm
      have h_sigma_ne : sigmaZ ≠ 0 := h_pos.ne'
      rw [h_sq_comm, h_var_sq]
      field_simp
      ring
    have h_exp_def : 2 * expectedPosteriorStdDev Z μ =
        (1 / 2 : ℝ) *
          (2 * (∑ b : Bool,
              μ.real (searchBranchEvent Z muZ sigmaZ (-1) b) *
                condStdDev Z μ (searchBranchEvent Z muZ sigmaZ (-1) b)) +
           2 * (∑ b : Bool,
              μ.real (searchBranchEvent Z muZ sigmaZ 1 b) *
                condStdDev Z μ (searchBranchEvent Z muZ sigmaZ 1 b))) := by
      unfold expectedPosteriorStdDev
      dsimp only [muZ, sigmaZ]
      ring
    change expectedPosteriorStdDev Z μ ≤ (23 / 24 : ℝ) * sigmaZ
    linarith

end TraceSqrt
