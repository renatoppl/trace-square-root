import TraceSqrt.Defs
import TraceSqrt.Potential.GapEnvelope
import TraceSqrt.Trade.TradeOrInformation

set_option maxHeartbeats 4000000

/-!
# Theorem 3.2: Bayesian Contextual Bilateral Trade (`thm:trade-bayes`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 3.1, Algorithm 3 and Theorem 3.2 `thm:trade-bayes`).
-/

namespace TraceSqrt

/-- **Theorem 3.2 (Bayesian Bilateral Trade, `thm:trade-bayes`)**:
For every known joint prior `μ` on `(W_S, W_B)` with finite second moments, every full-history
adaptive unit-ball context strategy `ctxPolicy` (`𝓕_{t-1}`), and every horizon `T`:
1. `0 ≤ E[Reg_T] ≤ 2^{11} Ψ_tr(μ)` (Eq. (18)),
2. If `(W_S, W_B)` is supported on `K = B_2^d × B_2^d`, `E[Reg_T] ≤ 2^{12} √d`, and
3. If `(W_S, W_B)` is supported on `[-1, 1]^d × [-1, 1]^d`, `E[Reg_T] ≤ 2^{12} d`. -/
theorem thm_bayesian_bilateral_trade {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (WS WB : Ω → (Fin d → ℝ))
    (hWS : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => WS ω i) 2 μ)
    (hWB : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => WB ω i) 2 μ)
    (ctxPolicy : List (BayesTradeObs d) → (Fin d → ℝ))
    (hCtx : ∀ hist : List (BayesTradeObs d), vecL2Norm (ctxPolicy hist) ≤ 1)
    (T : ℕ) :
    0 ≤ alg3ExpectedRegret WS WB ctxPolicy T μ [] ∧
    alg3ExpectedRegret WS WB ctxPolicy T μ [] ≤
      (2 ^ 11 : ℝ) * tradeBayesPotential WS WB μ ∧
    ((∀ ω : Ω, vecL2Norm (WS ω) ≤ 1 ∧ vecL2Norm (WB ω) ≤ 1) →
      alg3ExpectedRegret WS WB ctxPolicy T μ [] ≤ (2 ^ 12 : ℝ) * Real.sqrt d) ∧
    ((∀ ω : Ω, (∀ i : Fin d, |WS ω i| ≤ 1) ∧ (∀ i : Fin d, |WB ω i| ≤ 1)) →
      alg3ExpectedRegret WS WB ctxPolicy T μ [] ≤ (2 ^ 12 : ℝ) * (d : ℝ)) :=
by
  have h_psd_tr_eq : ∀ {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef),
      psdTraceSqrt A = Matrix.trace hA.sqrt := by
    clear hWS hWB hCtx WS WB ctxPolicy T
    intro A hA
    unfold psdTraceSqrt
    rw [dif_pos hA]
    congr 1
    have h_dec : (fun a b : Fin d => Classical.propDecidable (a = b)) = instDecidableEqFin d :=
      Subsingleton.elim _ _
    rw [h_dec]

  have h_sqrt_psd : ∀ {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef), hA.sqrt.PosSemidef := by
    clear hWS hWB hCtx WS WB ctxPolicy T
    intro A hA
    unfold Matrix.PosSemidef.sqrt
    let f : Fin d → ℝ := RCLike.ofReal ∘ (fun x : ℝ => √x) ∘ hA.isHermitian.eigenvalues
    have hdiag : (Matrix.diagonal f).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr fun i => by
        simp [f, Real.sqrt_nonneg]
    simpa only [Matrix.star_eq_conjTranspose] using
      hdiag.mul_mul_conjTranspose_same hA.isHermitian.eigenvectorUnitary.val

  have h_sqrt_sq : ∀ {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef), hA.sqrt * hA.sqrt = A := by
    clear hWS hWB hCtx WS WB ctxPolicy T
    intro A hA
    unfold Matrix.PosSemidef.sqrt
    let U : Matrix (Fin d) (Fin d) ℝ := hA.isHermitian.eigenvectorUnitary.val
    have hU_mem : U ∈ Matrix.unitaryGroup (Fin d) ℝ := hA.isHermitian.eigenvectorUnitary.prop
    have hstarU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU_mem
    let f : Fin d → ℝ := RCLike.ofReal ∘ (fun x : ℝ => √x) ∘ hA.isHermitian.eigenvalues
    change (U * Matrix.diagonal f * star U) * (U * Matrix.diagonal f * star U) = A
    have h_assoc : (U * Matrix.diagonal f * star U) * (U * Matrix.diagonal f * star U) =
        U * (Matrix.diagonal f * Matrix.diagonal f) * star U := by
      calc (U * Matrix.diagonal f * star U) * (U * Matrix.diagonal f * star U)
          = U * Matrix.diagonal f * (star U * U) * Matrix.diagonal f * star U := by
              simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal f * Matrix.diagonal f) * star U := by
              rw [hstarU, Matrix.mul_one]
              simp only [Matrix.mul_assoc]
    rw [h_assoc, Matrix.diagonal_mul_diagonal]
    have h_diag_eq :
        (Matrix.diagonal fun i => f i * f i) =
          Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) := by
      congr 1; ext i
      have h_ev : 0 ≤ hA.isHermitian.eigenvalues i := hA.eigenvalues_nonneg i
      simp [f, RCLike.ofReal_real_eq_id, ← sq, Real.sq_sqrt h_ev]
    rw [h_diag_eq]
    simpa [Unitary.conjStarAlgAut_apply, U] using (hA.isHermitian.spectral_theorem).symm

  have h_psd_drop : ∀ (x : Fin d → ℝ), vecL2Norm x ≤ 1 →
      ∀ (S S₁ S₂ : Matrix (Fin d) (Fin d) ℝ),
        S.PosSemidef → S₁.PosSemidef → S₂.PosSemidef →
        ∀ (p₁ p₂ : ℝ), 0 ≤ p₁ → 0 ≤ p₂ → p₁ + p₂ = 1 →
        (S - (p₁ • S₁ + p₂ • S₂)).PosSemidef →
        Real.sqrt (dotProduct x (S.mulVec x)) -
          (p₁ * Real.sqrt (dotProduct x (S₁.mulVec x)) +
           p₂ * Real.sqrt (dotProduct x (S₂.mulVec x))) ≤
        psdTraceSqrt S - (p₁ * psdTraceSqrt S₁ + p₂ * psdTraceSqrt S₂) := by
    clear hWS hWB hCtx WS WB ctxPolicy T
    intro x hx S S₁ S₂ hS hS₁ hS₂ p₁ p₂ hp₁ hp₂ hp hDom
    have hComb : (p₁ • S₁ + p₂ • S₂).PosSemidef :=
      (hS₁.smul hp₁).add (hS₂.smul hp₂)
    have h_env := lem_gap_envelope x hx
    have h_conc := h_env.2.2.2.2 S₁ S₂ hS₁ hS₂ p₁ p₂ hp₁ hp₂ hp hComb
    have h_mono := h_env.2.2.2.1 (p₁ • S₁ + p₂ • S₂) S hComb hS hDom
    unfold gapPotential at h_conc h_mono
    rw [h_psd_tr_eq hS, h_psd_tr_eq hS₁, h_psd_tr_eq hS₂]
    linarith

  have h_cov_props : ∀ (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
      (W : Ω → (Fin d → ℝ)),
      (∀ i : Fin d, MeasureTheory.MemLp (fun ω => W ω i) 2 ν) →
      (rvCovMat W ν).PosSemidef ∧
      0 ≤ psdTraceSqrt (rvCovMat W ν) ∧
      (∀ x : Fin d → ℝ,
        MeasureTheory.MemLp (fun ω => dotProduct x (W ω)) 2 ν ∧
        dotProduct x ((rvCovMat W ν).mulVec x) =
          ProbabilityTheory.variance (fun ω => dotProduct x (W ω)) ν ∧
        Real.sqrt (dotProduct x ((rvCovMat W ν).mulVec x)) =
          rvStdDev (fun ω => dotProduct x (W ω)) ν) ∧
      ((∀ ω : Ω, vecL2Norm (W ω) ≤ 1) → psdTraceSqrt (rvCovMat W ν) ≤ Real.sqrt d) ∧
      ((∀ ω : Ω, ∀ i : Fin d, |W ω i| ≤ 1) → psdTraceSqrt (rvCovMat W ν) ≤ (d : ℝ)) := by
    clear h_psd_drop hWS hWB hCtx WS WB ctxPolicy T
    intro ν _ W hWν
    let mu : Fin d → ℝ := rvMeanVec W ν
    let D : Fin d → Ω → ℝ := fun i ω => W ω i - mu i
    have hD_lp : ∀ i : Fin d, MeasureTheory.MemLp (D i) 2 ν :=
      fun i => (hWν i).sub (MeasureTheory.memLp_const (mu i))
    have hD_mul_int : ∀ i j : Fin d, MeasureTheory.Integrable (fun ω => D i ω * D j ω) ν :=
      fun i j => by simpa using (hD_lp i).integrable_mul (hD_lp j)
    have hW_int : ∀ i : Fin d, MeasureTheory.Integrable (fun ω => W ω i) ν :=
      fun i => (hWν i).integrable one_le_two
    have h_proj : ∀ x : Fin d → ℝ,
        MeasureTheory.MemLp (fun ω => dotProduct x (W ω)) 2 ν ∧
        dotProduct x ((rvCovMat W ν).mulVec x) =
          ProbabilityTheory.variance (fun ω => dotProduct x (W ω)) ν ∧
        Real.sqrt (dotProduct x ((rvCovMat W ν).mulVec x)) =
          rvStdDev (fun ω => dotProduct x (W ω)) ν := by
      intro x
      have hZ_lp : MeasureTheory.MemLp (fun ω => dotProduct x (W ω)) 2 ν := by
        simpa only [dotProduct] using
          MeasureTheory.memLp_finset_sum Finset.univ (fun i _ => (hWν i).const_mul (x i))
      have h_mean : dotProduct x (rvMeanVec W ν) = ∫ ω, dotProduct x (W ω) ∂ν := by
        calc dotProduct x (rvMeanVec W ν)
            = ∑ i : Fin d, x i * (∫ ω, W ω i ∂ν) := rfl
          _ = ∑ i : Fin d, ∫ ω, x i * W ω i ∂ν := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [MeasureTheory.integral_const_mul]
          _ = ∫ ω, ∑ i : Fin d, x i * W ω i ∂ν := by
                rw [← MeasureTheory.integral_finset_sum Finset.univ
                  (fun i _ => (hW_int i).const_mul (x i))]
          _ = ∫ ω, dotProduct x (W ω) ∂ν := rfl
      have h_var : dotProduct x ((rvCovMat W ν).mulVec x) =
          ProbabilityTheory.variance (fun ω => dotProduct x (W ω)) ν := by
        have h_term_int : ∀ i j : Fin d,
            MeasureTheory.Integrable (fun ω => (x i * x j) * (D i ω * D j ω)) ν :=
          fun i j => (hD_mul_int i j).const_mul (x i * x j)
        have h_inner_int : ∀ i : Fin d,
            MeasureTheory.Integrable (fun ω => ∑ j : Fin d, (x i * x j) * (D i ω * D j ω)) ν :=
          fun i => MeasureTheory.integrable_finset_sum Finset.univ (fun j _ => h_term_int i j)
        calc dotProduct x ((rvCovMat W ν).mulVec x)
            = ∑ i : Fin d, ∑ j : Fin d, (x i * x j) * (∫ ω, D i ω * D j ω ∂ν) := by
                simp only [dotProduct, Matrix.mulVec, rvCovMat, Matrix.of_apply, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                dsimp [D, mu]; ring
          _ = ∑ i : Fin d, ∑ j : Fin d, ∫ ω, (x i * x j) * (D i ω * D j ω) ∂ν := by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                rw [MeasureTheory.integral_const_mul]
          _ = ∑ i : Fin d, ∫ ω, (∑ j : Fin d, (x i * x j) * (D i ω * D j ω)) ∂ν := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [← MeasureTheory.integral_finset_sum Finset.univ (fun j _ => h_term_int i j)]
          _ = ∫ ω, (∑ i : Fin d, ∑ j : Fin d, (x i * x j) * (D i ω * D j ω)) ∂ν := by
                rw [← MeasureTheory.integral_finset_sum Finset.univ (fun i _ => h_inner_int i)]
          _ = ∫ ω, (dotProduct x (W ω) - ∫ ω', dotProduct x (W ω') ∂ν) ^ 2 ∂ν := by
                congr 1; ext ω
                rw [← h_mean]
                have h_lin : ∑ i : Fin d, x i * D i ω =
                    dotProduct x (W ω) - dotProduct x (rvMeanVec W ν) := by
                  simp only [dotProduct, D, mu, mul_sub, Finset.sum_sub_distrib]
                calc ∑ i : Fin d, ∑ j : Fin d, (x i * x j) * (D i ω * D j ω)
                    = ∑ i : Fin d, (x i * D i ω) * (∑ j : Fin d, x j * D j ω) := by
                        refine Finset.sum_congr rfl fun i _ => ?_
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl fun j _ => ?_; ring
                  _ = (∑ i : Fin d, x i * D i ω) * (∑ j : Fin d, x j * D j ω) := by
                        rw [← Finset.sum_mul]
                  _ = (dotProduct x (W ω) - dotProduct x (rvMeanVec W ν)) ^ 2 := by
                        rw [h_lin, sq]
          _ = ProbabilityTheory.variance (fun ω => dotProduct x (W ω)) ν :=
                (ProbabilityTheory.variance_eq_integral hZ_lp.aemeasurable).symm
      exact ⟨hZ_lp, h_var, by unfold rvStdDev; rw [h_var]⟩
    have hS_herm : (rvCovMat W ν).IsHermitian := by
      ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, rvCovMat, Matrix.of_apply]
      congr 1; ext ω; ring
    have hS_psd : (rvCovMat W ν).PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hS_herm fun v => ?_
      simp only [star_trivial]
      rw [(h_proj v).2.1]
      exact ProbabilityTheory.variance_nonneg _ ν
    have h_tr_nonneg : 0 ≤ psdTraceSqrt (rvCovMat W ν) := by
      rw [h_psd_tr_eq hS_psd]
      exact (h_sqrt_psd hS_psd).trace_nonneg
    set S := rvCovMat W ν
    set R := hS_psd.sqrt
    have hR_psd := h_sqrt_psd hS_psd
    have hR_sq := h_sqrt_sq hS_psd
    have hR_symm : ∀ i j : Fin d, R j i = R i j := fun i j => by
      have := congr_fun (congr_fun hR_psd.isHermitian.eq i) j
      simpa [Matrix.conjTranspose_apply] using this
    have hR_diag_sq : ∀ i : Fin d, (R i i) ^ 2 ≤ S i i := by
      intro i
      have hSS : S i i = ∑ j : Fin d, (R i j) ^ 2 := by
        calc S i i = (R * R) i i := by rw [hR_sq]
          _ = ∑ j : Fin d, R i j * R j i := Matrix.mul_apply
          _ = ∑ j : Fin d, (R i j) ^ 2 := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hR_symm i j, sq]
      rw [hSS]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (R i j)) (Finset.mem_univ i)
    have h_sum_R_le_S : ∑ i : Fin d, (R i i) ^ 2 ≤ ∑ i : Fin d, S i i :=
      Finset.sum_le_sum fun i _ => hR_diag_sq i
    have hS_diag_le : ∀ i : Fin d, S i i ≤ ∫ ω, (W ω i) ^ 2 ∂ν := by
      intro i
      have h_eq : S i i = ProbabilityTheory.variance (fun ω => W ω i) ν := by
        calc S i i
            = ∫ ω, (W ω i - ∫ ω', W ω' i ∂ν) ^ 2 ∂ν := by
                simp only [S, rvCovMat, rvMeanVec, Matrix.of_apply, sq]
          _ = ProbabilityTheory.variance (fun ω => W ω i) ν :=
                (ProbabilityTheory.variance_eq_integral (hWν i).aemeasurable).symm
      rw [h_eq]
      exact ProbabilityTheory.variance_le_expectation_sq (hWν i).aestronglyMeasurable
    have h_cs : (Matrix.trace R) ^ 2 ≤ (∑ i : Fin d, (R i i) ^ 2) * (d : ℝ) := by
      have h0 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin d => R i i) (fun _ : Fin d => (1 : ℝ))
      have h_lhs : (∑ i : Fin d, R i i * (1 : ℝ)) = Matrix.trace R := by
        simp [Matrix.trace, Matrix.diag]
      have h_rhs2 : (∑ _ : Fin d, (1 : ℝ) ^ 2) = (d : ℝ) := by simp
      rwa [h_lhs, h_rhs2] at h0
    refine ⟨hS_psd, h_tr_nonneg, h_proj, ?_, ?_⟩
    · intro hBall
      have h_trS_le_one : ∑ i : Fin d, S i i ≤ 1 := by
        have h1 : ∑ i : Fin d, S i i ≤ ∑ i : Fin d, ∫ ω, (W ω i) ^ 2 ∂ν :=
          Finset.sum_le_sum fun i _ => hS_diag_le i
        have h2 : ∑ i : Fin d, ∫ ω, (W ω i) ^ 2 ∂ν = ∫ ω, (∑ i : Fin d, (W ω i) ^ 2) ∂ν :=
          (MeasureTheory.integral_finset_sum Finset.univ fun i _ => (hWν i).integrable_sq).symm
        have h_pw : ∀ ω : Ω, ∑ i : Fin d, (W ω i) ^ 2 ≤ 1 := by
          intro ω
          have hb := hBall ω
          unfold vecL2Norm at hb
          have h_nn : 0 ≤ ∑ i : Fin d, (W ω i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
          calc ∑ i : Fin d, (W ω i) ^ 2
              = (Real.sqrt (∑ i : Fin d, (W ω i) ^ 2)) ^ 2 := (Real.sq_sqrt h_nn).symm
            _ ≤ 1 ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
            _ = 1 := one_pow 2
        have h_sum_int : MeasureTheory.Integrable (fun ω => ∑ i : Fin d, (W ω i) ^ 2) ν :=
          MeasureTheory.integrable_finset_sum Finset.univ fun i _ => (hWν i).integrable_sq
        have h3 : ∫ ω, (∑ i : Fin d, (W ω i) ^ 2) ∂ν ≤ 1 := by
          calc ∫ ω, (∑ i : Fin d, (W ω i) ^ 2) ∂ν
              ≤ ∫ _ : Ω, (1 : ℝ) ∂ν :=
                MeasureTheory.integral_mono h_sum_int (MeasureTheory.integrable_const 1) h_pw
            _ = 1 := by rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
        linarith
      have h_tr_sq : (Matrix.trace R) ^ 2 ≤ (d : ℝ) := by
        have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        have h_sum_le_one : ∑ i : Fin d, (R i i) ^ 2 ≤ 1 := le_trans h_sum_R_le_S h_trS_le_one
        calc (Matrix.trace R) ^ 2
            ≤ (∑ i : Fin d, (R i i) ^ 2) * (d : ℝ) := h_cs
          _ ≤ 1 * (d : ℝ) := mul_le_mul_of_nonneg_right h_sum_le_one hd_nn
          _ = (d : ℝ) := one_mul _
      rw [h_psd_tr_eq hS_psd]
      exact Real.le_sqrt_of_sq_le h_tr_sq
    · intro hCube
      have h_trS_le_d : ∑ i : Fin d, S i i ≤ (d : ℝ) := by
        have h_each : ∀ i : Fin d, S i i ≤ 1 := fun i => by
          have h_pw : ∀ ω : Ω, (W ω i) ^ 2 ≤ 1 := fun ω => by
            have hc := hCube ω i
            nlinarith [sq_abs (W ω i), abs_nonneg (W ω i)]
          have h_int_le : ∫ ω, (W ω i) ^ 2 ∂ν ≤ 1 := by
            calc ∫ ω, (W ω i) ^ 2 ∂ν
                ≤ ∫ _ : Ω, (1 : ℝ) ∂ν :=
                  MeasureTheory.integral_mono (hWν i).integrable_sq
                    (MeasureTheory.integrable_const 1) h_pw
              _ = 1 := by rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
          exact le_trans (hS_diag_le i) h_int_le
        calc ∑ i : Fin d, S i i
            ≤ ∑ _ : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => h_each i
          _ = (d : ℝ) := by simp
      have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have h_tr_nn : 0 ≤ Matrix.trace R := hR_psd.trace_nonneg
      have h_tr_sq : (Matrix.trace R) ^ 2 ≤ (d : ℝ) ^ 2 := by
        have h_sum_le_d : ∑ i : Fin d, (R i i) ^ 2 ≤ (d : ℝ) := le_trans h_sum_R_le_S h_trS_le_d
        calc (Matrix.trace R) ^ 2
            ≤ (∑ i : Fin d, (R i i) ^ 2) * (d : ℝ) := h_cs
          _ ≤ (d : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_right h_sum_le_d hd_nn
          _ = (d : ℝ) ^ 2 := (sq (d : ℝ)).symm
      rw [h_psd_tr_eq hS_psd]
      nlinarith

  have h_bin_cov : ∀ (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
      (W : Ω → (Fin d → ℝ)),
      (∀ i : Fin d, MeasureTheory.MemLp (fun ω => W ω i) 2 ν) →
      ∀ (E : Set Ω), MeasureTheory.NullMeasurableSet E ν →
      let p_tr := ν.real E
      let p_no := ν.real Eᶜ
      let ν_tr := ProbabilityTheory.cond ν E
      let ν_no := ProbabilityTheory.cond ν Eᶜ
      let S := rvCovMat W ν
      let S_tr := rvCovMat W ν_tr
      let S_no := rvCovMat W ν_no
      (0 ≤ p_tr ∧ 0 ≤ p_no ∧ p_tr + p_no = 1) ∧
      (S_tr.PosSemidef ∧ S_no.PosSemidef) ∧
      (S - (p_tr • S_tr + p_no • S_no)).PosSemidef ∧
      ∀ x : Fin d → ℝ,
        p_tr * Real.sqrt (dotProduct x (S_tr.mulVec x)) =
          p_tr * condStdDev (fun ω => dotProduct x (W ω)) ν E ∧
        p_no * Real.sqrt (dotProduct x (S_no.mulVec x)) =
          p_no * condStdDev (fun ω => dotProduct x (W ω)) ν Eᶜ := by
    clear h_psd_drop h_sqrt_sq h_sqrt_psd h_psd_tr_eq hWS hWB hCtx WS WB ctxPolicy T
    have h_cov_zero : ∀ W : Ω → (Fin d → ℝ), rvCovMat W (0 : MeasureTheory.Measure Ω) = 0 := by
      intro W; ext i j; simp [rvCovMat, MeasureTheory.integral_zero_measure]
    have h_cond_null : ∀ (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
        (G : Set Ω), ν G = 0 →
        ProbabilityTheory.cond ν G = 0 ∧ ProbabilityTheory.cond ν Gᶜ = ν := by
      intro ν _ G hG0
      have h1 : ProbabilityTheory.cond ν G = 0 :=
        ProbabilityTheory.cond_eq_zero.mpr (Or.inr hG0)
      have hae : ∀ᵐ ω ∂ν, ω ∈ Gᶜ := by
        rw [MeasureTheory.ae_iff]
        have hset : {ω : Ω | ¬(ω ∈ Gᶜ)} = G := by ext ω; simp
        rw [hset]; exact hG0
      have hrest : ν.restrict Gᶜ = ν := MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae
      have hGc1 : ν Gᶜ = 1 := by
        calc ν Gᶜ = (ν.restrict Gᶜ) Set.univ := (MeasureTheory.Measure.restrict_apply_univ Gᶜ).symm
          _ = ν Set.univ := by rw [hrest]
          _ = 1 := MeasureTheory.measure_univ
      have h2 : ProbabilityTheory.cond ν Gᶜ = ν := by
        change (ν Gᶜ)⁻¹ • ν.restrict Gᶜ = ν
        rw [hGc1, hrest, inv_one, one_smul]
      exact ⟨h1, h2⟩
    intro ν _ W hWν E hE
    dsimp only
    set p_tr : ℝ := ν.real E
    set p_no : ℝ := ν.real Eᶜ
    set ν_tr := ProbabilityTheory.cond ν E
    set ν_no := ProbabilityTheory.cond ν Eᶜ
    set S := rvCovMat W ν
    set S_tr := rvCovMat W ν_tr
    set S_no := rvCovMat W ν_no
    have hp_tr_nn : 0 ≤ p_tr := MeasureTheory.measureReal_nonneg
    have hp_no_nn : 0 ≤ p_no := MeasureTheory.measureReal_nonneg
    have hp_sum : p_tr + p_no = 1 := by
      have hc : p_no = 1 - p_tr := by
        dsimp [p_tr, p_no]
        rw [MeasureTheory.measureReal_compl₀ hE, MeasureTheory.probReal_univ]
      linarith
    obtain ⟨hS_psd, _, h_proj_ν, _, _⟩ := h_cov_props ν W hWν
    refine ⟨⟨hp_tr_nn, hp_no_nn, hp_sum⟩, ?_⟩
    by_cases hE0 : ν E = 0
    · obtain ⟨h_c0, h_c1⟩ := h_cond_null ν E hE0
      have hp0 : p_tr = 0 := by simp [p_tr, MeasureTheory.measureReal_def, hE0]
      have hp1 : p_no = 1 := by linarith
      have hS_tr0 : S_tr = 0 := by dsimp [S_tr, ν_tr]; rw [h_c0, h_cov_zero]
      have hS_noS : S_no = S := by dsimp [S_no, ν_no, S]; rw [h_c1]
      have h_dom : (S - (p_tr • S_tr + p_no • S_no)) = 0 := by
        rw [hp0, hp1, hS_tr0, hS_noS]; simp
      refine ⟨⟨by rw [hS_tr0]; exact Matrix.PosSemidef.zero,
               by rw [hS_noS]; exact hS_psd⟩,
              by rw [h_dom]; exact Matrix.PosSemidef.zero, ?_⟩
      intro x
      refine ⟨by rw [hp0]; simp, ?_⟩
      rw [hS_noS, (h_proj_ν x).2.2]
      unfold condStdDev
      rw [h_c1]
    · by_cases hEc0 : ν Eᶜ = 0
      · obtain ⟨h_c0, h_c1⟩ := h_cond_null ν Eᶜ hEc0
        have h_c1' : ProbabilityTheory.cond ν E = ν := by simpa [compl_compl] using h_c1
        have hp0 : p_no = 0 := by simp [p_no, MeasureTheory.measureReal_def, hEc0]
        have hp1 : p_tr = 1 := by linarith
        have hS_no0 : S_no = 0 := by dsimp [S_no, ν_no]; rw [h_c0, h_cov_zero]
        have hS_trS : S_tr = S := by dsimp [S_tr, ν_tr, S]; rw [h_c1']
        have h_dom : (S - (p_tr • S_tr + p_no • S_no)) = 0 := by
          rw [hp0, hp1, hS_no0, hS_trS]; simp
        refine ⟨⟨by rw [hS_trS]; exact hS_psd,
                 by rw [hS_no0]; exact Matrix.PosSemidef.zero⟩,
                by rw [h_dom]; exact Matrix.PosSemidef.zero, ?_⟩
        intro x
        refine ⟨?_, by rw [hp0]; simp⟩
        rw [hS_trS, (h_proj_ν x).2.2]
        unfold condStdDev
        rw [h_c1']
      · haveI : MeasureTheory.IsProbabilityMeasure ν_tr :=
          ProbabilityTheory.cond_isProbabilityMeasure hE0
        haveI : MeasureTheory.IsProbabilityMeasure ν_no :=
          ProbabilityTheory.cond_isProbabilityMeasure hEc0
        have hW_tr : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => W ω i) 2 ν_tr :=
          fun i => ((hWν i).restrict E).smul_measure (ENNReal.inv_ne_top.mpr hE0)
        have hW_no : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => W ω i) 2 ν_no :=
          fun i => ((hWν i).restrict Eᶜ).smul_measure (ENNReal.inv_ne_top.mpr hEc0)
        obtain ⟨hS_tr_psd, _, h_proj_tr, _, _⟩ := h_cov_props ν_tr W hW_tr
        obtain ⟨hS_no_psd, _, h_proj_no, _, _⟩ := h_cov_props ν_no W hW_no
        have hD_herm : (S - (p_tr • S_tr + p_no • S_no)).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
              Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
              hS_psd.isHermitian.eq, hS_tr_psd.isHermitian.eq, hS_no_psd.isHermitian.eq]
          simp only [star_trivial]; rfl
        have h_branch_var : ∀ (F : Set Ω) (hF0 : ν F ≠ 0) (v : Fin d → ℝ),
            let m := ∫ ω, dotProduct v (W ω) ∂ν
            ν.real F * ProbabilityTheory.variance (fun ω => dotProduct v (W ω))
              (ProbabilityTheory.cond ν F) ≤
              ∫ ω in F, (dotProduct v (W ω) - m) ^ 2 ∂ν := by
          intro F hF0 v m
          haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond ν F) :=
            ProbabilityTheory.cond_isProbabilityMeasure hF0
          have hU_ν : MeasureTheory.MemLp (fun ω => dotProduct v (W ω)) 2 ν := (h_proj_ν v).1
          have hU_F : MeasureTheory.MemLp (fun ω => dotProduct v (W ω)) 2
              (ProbabilityTheory.cond ν F) :=
            (hU_ν.restrict F).smul_measure (ENNReal.inv_ne_top.mpr hF0)
          have hU_sub : MeasureTheory.MemLp (fun ω => dotProduct v (W ω) - m) 2
              (ProbabilityTheory.cond ν F) :=
            hU_F.sub (MeasureTheory.memLp_const m)
          have hpF_pos : 0 < ν.real F :=
            ENNReal.toReal_pos hF0 (MeasureTheory.measure_ne_top ν F)
          have hv1 : ProbabilityTheory.variance (fun ω => dotProduct v (W ω))
              (ProbabilityTheory.cond ν F) =
              ProbabilityTheory.variance (fun ω => dotProduct v (W ω) - m)
                (ProbabilityTheory.cond ν F) :=
            (ProbabilityTheory.variance_sub_const hU_F.1 m).symm
          have hv2 : ProbabilityTheory.variance (fun ω => dotProduct v (W ω) - m)
              (ProbabilityTheory.cond ν F) ≤
              ∫ ω, (dotProduct v (W ω) - m) ^ 2 ∂(ProbabilityTheory.cond ν F) :=
            ProbabilityTheory.variance_le_expectation_sq hU_sub.1
          have hv3 : (∫ ω, (dotProduct v (W ω) - m) ^ 2 ∂(ProbabilityTheory.cond ν F)) =
              (ν.real F)⁻¹ * ∫ ω in F, (dotProduct v (W ω) - m) ^ 2 ∂ν := by
            change (∫ ω, (dotProduct v (W ω) - m) ^ 2 ∂((ν F)⁻¹ • ν.restrict F)) = _
            rw [MeasureTheory.integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
              ← MeasureTheory.measureReal_def]
          have h_le : ProbabilityTheory.variance (fun ω => dotProduct v (W ω))
              (ProbabilityTheory.cond ν F) ≤
              (ν.real F)⁻¹ * ∫ ω in F, (dotProduct v (W ω) - m) ^ 2 ∂ν := by linarith
          have hmul := mul_le_mul_of_nonneg_left h_le hpF_pos.le
          have hcancel : ν.real F * ((ν.real F)⁻¹ * ∫ ω in F, (dotProduct v (W ω) - m) ^ 2 ∂ν) =
              ∫ ω in F, (dotProduct v (W ω) - m) ^ 2 ∂ν := by field_simp
          linarith
        have h_dom : (S - (p_tr • S_tr + p_no • S_no)).PosSemidef := by
          refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hD_herm fun v => ?_
          simp only [star_trivial]
          let U : Ω → ℝ := fun ω => dotProduct v (W ω)
          let m : ℝ := ∫ ω, U ω ∂ν
          have hU_lp : MeasureTheory.MemLp U 2 ν := (h_proj_ν v).1
          have h_sq_int : MeasureTheory.Integrable (fun ω => (U ω - m) ^ 2) ν :=
            (hU_lp.sub (MeasureTheory.memLp_const m)).integrable_sq
          have hb_pos := h_branch_var E hE0 v
          have hb_neg := h_branch_var Eᶜ hEc0 v
          have h_sum_int : (∫ ω in E, (U ω - m) ^ 2 ∂ν) + (∫ ω in Eᶜ, (U ω - m) ^ 2 ∂ν) =
              ∫ ω, (U ω - m) ^ 2 ∂ν :=
            MeasureTheory.integral_add_compl₀ hE h_sq_int
          have h_tot_var : (∫ ω, (U ω - m) ^ 2 ∂ν) = dotProduct v (S.mulVec v) := by
            rw [← ProbabilityTheory.variance_eq_integral hU_lp.aemeasurable]
            exact ((h_proj_ν v).2.1).symm
          have h_quad_expand :
              dotProduct v ((S - (p_tr • S_tr + p_no • S_no)).mulVec v) =
                dotProduct v (S.mulVec v) -
                  (p_tr * ProbabilityTheory.variance U ν_tr +
                   p_no * ProbabilityTheory.variance U ν_no) := by
            simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
              dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
            rw [(h_proj_tr v).2.1, (h_proj_no v).2.1]
          rw [h_quad_expand]
          dsimp [U, m, p_tr, p_no, ν_tr, ν_no] at *
          linarith
        refine ⟨⟨hS_tr_psd, hS_no_psd⟩, h_dom, ?_⟩
        intro x
        rw [(h_proj_tr x).2.2, (h_proj_no x).2.2]
        exact ⟨rfl, rfl⟩

  have h_select_price : ∀ (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
      (S B : Ω → ℝ),
      MeasureTheory.MemLp S 2 ν →
      MeasureTheory.MemLp B 2 ν →
      expectedLostGain S B ν (alg3SelectPrice S B ν) ≤
        (2 ^ 11 : ℝ) * totalInfoDrop S B ν (alg3SelectPrice S B ν) := by
    intro ν _ S B hS hB
    have h_ex : ∃ q : ℝ, expectedLostGain S B ν q ≤ (2 ^ 11 : ℝ) * totalInfoDrop S B ν q :=
      lem_toi ν S B hS hB
    have hp_eq : alg3SelectPrice S B ν = Classical.choose h_ex := by
      unfold alg3SelectPrice
      exact dif_pos h_ex
    rw [hp_eq]
    exact Classical.choose_spec h_ex

  have h_ind : ∀ (n : ℕ) (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν],
      (∀ i : Fin d, MeasureTheory.MemLp (fun ω => WS ω i) 2 ν) →
      (∀ i : Fin d, MeasureTheory.MemLp (fun ω => WB ω i) 2 ν) →
      ∀ (hist : List (BayesTradeObs d)),
        0 ≤ alg3ExpectedRegret WS WB ctxPolicy n ν hist ∧
        alg3ExpectedRegret WS WB ctxPolicy n ν hist ≤
          (2 ^ 11 : ℝ) * tradeBayesPotential WS WB ν := by
    clear h_psd_tr_eq h_sqrt_psd h_sqrt_sq hWS hWB T
    intro n
    induction n with
    | zero =>
        intro ν _ hWSν hWBν hist
        simp only [alg3ExpectedRegret]
        have h1 : 0 ≤ psdTraceSqrt (rvCovMat WS ν) := (h_cov_props ν WS hWSν).2.1
        have h2 : 0 ≤ psdTraceSqrt (rvCovMat WB ν) := (h_cov_props ν WB hWBν).2.1
        have h_pot_nn : 0 ≤ tradeBayesPotential WS WB ν := add_nonneg h1 h2
        exact ⟨le_rfl, by positivity⟩
    | succ n ih =>
        intro ν _ hWSν hWBν hist
        set x : Fin d → ℝ := ctxPolicy hist
        have hx : vecL2Norm x ≤ 1 := hCtx hist
        set S : Ω → ℝ := fun ω => dotProduct x (WS ω)
        set B : Ω → ℝ := fun ω => dotProduct x (WB ω)
        set p : ℝ := alg3SelectPrice S B ν
        set E_tr : Set Ω := {ω | S ω ≤ p ∧ p ≤ B ω}
        have hS_lp : MeasureTheory.MemLp S 2 ν := ((h_cov_props ν WS hWSν).2.2.1 x).1
        have hB_lp : MeasureTheory.MemLp B 2 ν := ((h_cov_props ν WB hWBν).2.2.1 x).1
        have hE_pre : E_tr = S ⁻¹' Set.Iic p ∩ B ⁻¹' Set.Ici p := by
          ext ω; simp [E_tr]
        have hE_nm : MeasureTheory.NullMeasurableSet E_tr ν := by
          rw [hE_pre]
          exact (hS_lp.aemeasurable.nullMeasurableSet_preimage measurableSet_Iic).inter
            (hB_lp.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici)
        have h_pot_drop_W : ∀ (W : Ω → (Fin d → ℝ)),
            (∀ i : Fin d, MeasureTheory.MemLp (fun ω => W ω i) 2 ν) →
            let Z : Ω → ℝ := fun ω => dotProduct x (W ω)
            rvStdDev Z ν - (ν.real E_tr * condStdDev Z ν E_tr + ν.real E_trᶜ * condStdDev Z ν E_trᶜ) ≤
              psdTraceSqrt (rvCovMat W ν) -
                (ν.real E_tr * psdTraceSqrt (rvCovMat W (ProbabilityTheory.cond ν E_tr)) +
                 ν.real E_trᶜ * psdTraceSqrt (rvCovMat W (ProbabilityTheory.cond ν E_trᶜ))) := by
          intro W hWν Z
          obtain ⟨hCov_psd, _, hProj, _, _⟩ := h_cov_props ν W hWν
          have hZ_sd : Real.sqrt (dotProduct x ((rvCovMat W ν).mulVec x)) = rvStdDev Z ν :=
            (hProj x).2.2
          obtain ⟨⟨hp1, hp2, hpsum⟩, ⟨hS1, hS2⟩, hDom, h_dir⟩ :=
            h_bin_cov ν W hWν E_tr hE_nm
          obtain ⟨h_dir1, h_dir2⟩ := h_dir x
          have h_drop := h_psd_drop x hx (rvCovMat W ν)
            (rvCovMat W (ProbabilityTheory.cond ν E_tr))
            (rvCovMat W (ProbabilityTheory.cond ν E_trᶜ))
            hCov_psd hS1 hS2 (ν.real E_tr) (ν.real E_trᶜ) hp1 hp2 hpsum hDom
          rw [hZ_sd, h_dir1, h_dir2] at h_drop
          exact h_drop
        have h_tot_pot : totalInfoDrop S B ν p ≤
            tradeBayesPotential WS WB ν -
              (ν.real E_tr * tradeBayesPotential WS WB (ProbabilityTheory.cond ν E_tr) +
               ν.real E_trᶜ * tradeBayesPotential WS WB (ProbabilityTheory.cond ν E_trᶜ)) := by
          have h1 := h_pot_drop_W WS hWSν
          have h2 := h_pot_drop_W WB hWBν
          dsimp only at h1 h2
          change (rvStdDev S ν - (ν.real E_tr * condStdDev S ν E_tr +
                    ν.real E_trᶜ * condStdDev S ν E_trᶜ)) +
                 (rvStdDev B ν - (ν.real E_tr * condStdDev B ν E_tr +
                    ν.real E_trᶜ * condStdDev B ν E_trᶜ)) ≤
                 (psdTraceSqrt (rvCovMat WS ν) + psdTraceSqrt (rvCovMat WB ν)) -
                   (ν.real E_tr * (psdTraceSqrt (rvCovMat WS (ProbabilityTheory.cond ν E_tr)) +
                                   psdTraceSqrt (rvCovMat WB (ProbabilityTheory.cond ν E_tr))) +
                    ν.real E_trᶜ * (psdTraceSqrt (rvCovMat WS (ProbabilityTheory.cond ν E_trᶜ)) +
                                    psdTraceSqrt (rvCovMat WB (ProbabilityTheory.cond ν E_trᶜ))))
          linarith
        have h_cont : ∀ (F : Set Ω) (hist' : List (BayesTradeObs d)),
            0 ≤ (if ν F = 0 then 0
                 else ν.real F * alg3ExpectedRegret WS WB ctxPolicy n (ProbabilityTheory.cond ν F) hist') ∧
            (if ν F = 0 then 0
             else ν.real F * alg3ExpectedRegret WS WB ctxPolicy n (ProbabilityTheory.cond ν F) hist') ≤
              (2 ^ 11 : ℝ) * (ν.real F * tradeBayesPotential WS WB (ProbabilityTheory.cond ν F)) := by
          intro F hist'
          by_cases hF0 : ν F = 0
          · simp [hF0, MeasureTheory.measureReal_def]
          · rw [if_neg hF0]
            haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond ν F) :=
              ProbabilityTheory.cond_isProbabilityMeasure hF0
            have hWS_F : ∀ i : Fin d,
                MeasureTheory.MemLp (fun ω => WS ω i) 2 (ProbabilityTheory.cond ν F) :=
              fun i => ((hWSν i).restrict F).smul_measure (ENNReal.inv_ne_top.mpr hF0)
            have hWB_F : ∀ i : Fin d,
                MeasureTheory.MemLp (fun ω => WB ω i) 2 (ProbabilityTheory.cond ν F) :=
              fun i => ((hWBν i).restrict F).smul_measure (ENNReal.inv_ne_top.mpr hF0)
            obtain ⟨h_ih_nn, h_ih_le⟩ := ih (ProbabilityTheory.cond ν F) hWS_F hWB_F hist'
            have hp_nn : 0 ≤ ν.real F := MeasureTheory.measureReal_nonneg (μ := ν) (s := F)
            have h_mul := mul_le_mul_of_nonneg_left h_ih_le hp_nn
            exact ⟨mul_nonneg hp_nn h_ih_nn, by linarith⟩
        have h_cur_nn : 0 ≤ expectedLostGain S B ν p := by
          unfold expectedLostGain
          refine MeasureTheory.integral_nonneg fun ω => mul_nonneg (le_max_right _ _) ?_
          split_ifs <;> norm_num
        have h_cur : expectedLostGain S B ν p ≤ (2 ^ 11 : ℝ) * totalInfoDrop S B ν p :=
          h_select_price ν S B hS_lp hB_lp
        obtain ⟨h_c_tr_nn, h_c_tr⟩ := h_cont E_tr (hist ++ [⟨x, p, 1⟩])
        obtain ⟨h_c_no_nn, h_c_no⟩ := h_cont E_trᶜ (hist ++ [⟨x, p, 0⟩])
        have h_unfold : alg3ExpectedRegret WS WB ctxPolicy (n + 1) ν hist =
            expectedLostGain S B ν p +
            (if ν E_tr = 0 then 0
             else ν.real E_tr * alg3ExpectedRegret WS WB ctxPolicy n
               (ProbabilityTheory.cond ν E_tr) (hist ++ [⟨x, p, 1⟩])) +
            (if ν E_trᶜ = 0 then 0
             else ν.real E_trᶜ * alg3ExpectedRegret WS WB ctxPolicy n
               (ProbabilityTheory.cond ν E_trᶜ) (hist ++ [⟨x, p, 0⟩])) := rfl
        rw [h_unfold]
        have h211 : (2 ^ 11 : ℝ) = 2048 := by norm_num
        rw [h211] at h_cur h_c_tr h_c_no ⊢
        exact ⟨by linarith, by linarith⟩

  obtain ⟨h_part0, h_part1⟩ := h_ind T μ hWS hWB []
  refine ⟨h_part0, h_part1, ?_, ?_⟩
  · intro hBall
    have h_pot_WS : psdTraceSqrt (rvCovMat WS μ) ≤ Real.sqrt d :=
      (h_cov_props μ WS hWS).2.2.2.1 (fun ω => (hBall ω).1)
    have h_pot_WB : psdTraceSqrt (rvCovMat WB μ) ≤ Real.sqrt d :=
      (h_cov_props μ WB hWB).2.2.2.1 (fun ω => (hBall ω).2)
    have h_pot_sum : tradeBayesPotential WS WB μ ≤ 2 * Real.sqrt d := by
      unfold tradeBayesPotential
      linarith
    calc alg3ExpectedRegret WS WB ctxPolicy T μ []
        ≤ (2 ^ 11 : ℝ) * tradeBayesPotential WS WB μ := h_part1
      _ ≤ (2 ^ 11 : ℝ) * (2 * Real.sqrt d) :=
          mul_le_mul_of_nonneg_left h_pot_sum (by norm_num)
      _ = (2 ^ 12 : ℝ) * Real.sqrt d := by ring
  · intro hCube
    have h_pot_WS : psdTraceSqrt (rvCovMat WS μ) ≤ (d : ℝ) :=
      (h_cov_props μ WS hWS).2.2.2.2 (fun ω => (hCube ω).1)
    have h_pot_WB : psdTraceSqrt (rvCovMat WB μ) ≤ (d : ℝ) :=
      (h_cov_props μ WB hWB).2.2.2.2 (fun ω => (hCube ω).2)
    have h_pot_sum : tradeBayesPotential WS WB μ ≤ 2 * (d : ℝ) := by
      unfold tradeBayesPotential
      linarith
    calc alg3ExpectedRegret WS WB ctxPolicy T μ []
        ≤ (2 ^ 11 : ℝ) * tradeBayesPotential WS WB μ := h_part1
      _ ≤ (2 ^ 11 : ℝ) * (2 * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left h_pot_sum (by norm_num)
      _ = (2 ^ 12 : ℝ) * (d : ℝ) := by ring

/-- **Theorem 3.2 for randomized adaptive context strategies**:
Under any probability space `(Ξ, ν_ctx)` driving the context randomization independently of the
joint valuation prior `μ` (matching Section 1.4's conditional-independence assumption),
Algorithm 3's expected cumulative regret over `(μ, ν_ctx)` satisfies `E[Reg_T] ≤ 2^{11} Ψ_tr(μ)`
both as an unconditional extended Lebesgue integral and (when `AEStronglyMeasurable`) as a Bochner
integral. -/
theorem thm_bayesian_bilateral_trade_rand_ctx {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (WS WB : Ω → (Fin d → ℝ))
    (hWS : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => WS ω i) 2 μ)
    (hWB : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => WB ω i) 2 μ)
    {Ξ : Type*} [MeasurableSpace Ξ]
    (ν_ctx : MeasureTheory.Measure Ξ) [MeasureTheory.IsProbabilityMeasure ν_ctx]
    (ctxPolicy : Ξ → List (BayesTradeObs d) → (Fin d → ℝ))
    (hCtx : ∀ (ξ : Ξ) (hist : List (BayesTradeObs d)), vecL2Norm (ctxPolicy ξ hist) ≤ 1)
    (T : ℕ) :
    let L : Ξ → ℝ := fun ξ => alg3ExpectedRegret WS WB (ctxPolicy ξ) T μ []
    let B : ℝ := (2 ^ 11 : ℝ) * tradeBayesPotential WS WB μ
    (∀ ξ : Ξ, 0 ≤ L ξ ∧ L ξ ≤ B) ∧
    (∫⁻ ξ, ENNReal.ofReal (L ξ) ∂ν_ctx ≤ ENNReal.ofReal B) ∧
    (MeasureTheory.AEStronglyMeasurable L ν_ctx →
      MeasureTheory.Integrable L ν_ctx ∧
      0 ≤ (∫ ξ, L ξ ∂ν_ctx) ∧
      (∫ ξ, L ξ ∂ν_ctx) ≤ B) := by
  dsimp only
  have h_pw : ∀ ξ : Ξ,
      0 ≤ alg3ExpectedRegret WS WB (ctxPolicy ξ) T μ [] ∧
      alg3ExpectedRegret WS WB (ctxPolicy ξ) T μ [] ≤
        (2 ^ 11 : ℝ) * tradeBayesPotential WS WB μ := by
    intro ξ
    have h := thm_bayesian_bilateral_trade μ WS WB hWS hWB (ctxPolicy ξ) (hCtx ξ) T
    exact ⟨h.1, h.2.1⟩
  have h_exp := prob_expectation_le_of_pointwise ν_ctx _
    ((2 ^ 11 : ℝ) * tradeBayesPotential WS WB μ) h_pw
  exact ⟨h_pw, h_exp.1, h_exp.2⟩

end TraceSqrt
