import TraceSqrt.Defs
import TraceSqrt.Potential.GapEnvelope
import TraceSqrt.Search.DeviationContraction

set_option maxHeartbeats 4000000

/-!
# Theorem 2.1: Bayesian Contextual Search (`thm:bayesian-contextual-search`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 2.1, Algorithm 1 and Theorem 2.1).
-/

namespace TraceSqrt

/-- **Theorem 2.1 (Bayesian Contextual Search, `thm:bayesian-contextual-search`)**:
For any prior `μ` on `Z : Ω → ℝ^d` with finite second moments (`∀ i, MemLp (Z · i) 2 μ`),
every horizon `T`, and every full-history adaptive unit-ball context policy `ctxPolicy` (`𝓕_{t-1}`),
Algorithm 1's covariance `Σ₁ = Cov_μ(Z)` is positive semidefinite and its expected cumulative
loss over `T` rounds satisfies:
1. `0 ≤ E[∑_{t=1}^T ℓ_t] ≤ 24 Tr(√Σ₁)` (Eq. (7)),
2. If `Z` is supported on the Euclidean unit ball `B_2^d`, `E[∑_{t=1}^T ℓ_t] ≤ 24 √d`, and
3. If `Z` is supported on the hypercube `[-1, 1]^d`, `E[∑_{t=1}^T ℓ_t] ≤ 24 d`. -/
theorem thm_bayesian_contextual_search {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Ω → (Fin d → ℝ)) (hZ : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 μ)
    (ctxPolicy : List (SearchObs d) → (Fin d → ℝ))
    (hCtx : ∀ hist : List (SearchObs d), vecL2Norm (ctxPolicy hist) ≤ 1)
    (T : ℕ) :
    (rvCovMat Z μ).PosSemidef ∧
    0 ≤ alg1ExpectedLoss Z ctxPolicy T μ [] ∧
    alg1ExpectedLoss Z ctxPolicy T μ [] ≤ 24 * psdTraceSqrt (rvCovMat Z μ) ∧
    ((∀ ω : Ω, vecL2Norm (Z ω) ≤ 1) →
      alg1ExpectedLoss Z ctxPolicy T μ [] ≤ 24 * Real.sqrt d) ∧
    ((∀ ω : Ω, ∀ i : Fin d, |Z ω i| ≤ 1) →
      alg1ExpectedLoss Z ctxPolicy T μ [] ≤ 24 * (d : ℝ)) :=
by
  have h_psd_tr_eq : ∀ {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef),
      psdTraceSqrt A = Matrix.trace hA.sqrt := by
    intro A hA
    unfold psdTraceSqrt
    rw [dif_pos hA]
    congr 1
    have h_dec : (fun a b : Fin d => Classical.propDecidable (a = b)) = instDecidableEqFin d :=
      Subsingleton.elim _ _
    rw [h_dec]

  have h_sqrt_psd : ∀ {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef), hA.sqrt.PosSemidef := by
    intro A hA
    unfold Matrix.PosSemidef.sqrt
    let f : Fin d → ℝ := RCLike.ofReal ∘ (fun x : ℝ => √x) ∘ hA.isHermitian.eigenvalues
    have hdiag : (Matrix.diagonal f).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr fun i => by
        simp [f, Real.sqrt_nonneg]
    simpa only [Matrix.star_eq_conjTranspose] using
      hdiag.mul_mul_conjTranspose_same hA.isHermitian.eigenvectorUnitary.val

  have h_sqrt_sq : ∀ {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef), hA.sqrt * hA.sqrt = A := by
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

  have h_step1 : ∀ (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν],
      (∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 ν) →
      (rvCovMat Z ν).PosSemidef ∧
      0 ≤ psdTraceSqrt (rvCovMat Z ν) ∧
      (∀ x : Fin d → ℝ,
        MeasureTheory.MemLp (fun ω => dotProduct x (Z ω)) 2 ν ∧
        dotProduct x (rvMeanVec Z ν) = (∫ ω, dotProduct x (Z ω) ∂ν) ∧
        dotProduct x ((rvCovMat Z ν).mulVec x) =
          ProbabilityTheory.variance (fun ω => dotProduct x (Z ω)) ν) ∧
      ((∀ ω : Ω, vecL2Norm (Z ω) ≤ 1) → psdTraceSqrt (rvCovMat Z ν) ≤ Real.sqrt d) ∧
      ((∀ ω : Ω, ∀ i : Fin d, |Z ω i| ≤ 1) → psdTraceSqrt (rvCovMat Z ν) ≤ (d : ℝ)) := by
    intro ν _ hZν
    let mu : Fin d → ℝ := rvMeanVec Z ν
    let D : Fin d → Ω → ℝ := fun i ω => Z ω i - mu i
    have hD_lp : ∀ i : Fin d, MeasureTheory.MemLp (D i) 2 ν :=
      fun i => (hZν i).sub (MeasureTheory.memLp_const (mu i))
    have hD_mul_int : ∀ i j : Fin d, MeasureTheory.Integrable (fun ω => D i ω * D j ω) ν :=
      fun i j => by simpa using (hD_lp i).integrable_mul (hD_lp j)
    have hZ_int : ∀ i : Fin d, MeasureTheory.Integrable (fun ω => Z ω i) ν :=
      fun i => (hZν i).integrable one_le_two
    have h_proj : ∀ x : Fin d → ℝ,
        MeasureTheory.MemLp (fun ω => dotProduct x (Z ω)) 2 ν ∧
        dotProduct x (rvMeanVec Z ν) = (∫ ω, dotProduct x (Z ω) ∂ν) ∧
        dotProduct x ((rvCovMat Z ν).mulVec x) =
          ProbabilityTheory.variance (fun ω => dotProduct x (Z ω)) ν := by
      intro x
      have hW_lp : MeasureTheory.MemLp (fun ω => dotProduct x (Z ω)) 2 ν := by
        simpa only [dotProduct] using
          MeasureTheory.memLp_finset_sum Finset.univ (fun i _ => (hZν i).const_mul (x i))
      have h_mean : dotProduct x (rvMeanVec Z ν) = ∫ ω, dotProduct x (Z ω) ∂ν := by
        calc dotProduct x (rvMeanVec Z ν)
            = ∑ i : Fin d, x i * (∫ ω, Z ω i ∂ν) := rfl
          _ = ∑ i : Fin d, ∫ ω, x i * Z ω i ∂ν := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [MeasureTheory.integral_const_mul]
          _ = ∫ ω, ∑ i : Fin d, x i * Z ω i ∂ν := by
                rw [← MeasureTheory.integral_finset_sum Finset.univ
                  (fun i _ => (hZ_int i).const_mul (x i))]
          _ = ∫ ω, dotProduct x (Z ω) ∂ν := rfl
      have h_var : dotProduct x ((rvCovMat Z ν).mulVec x) =
          ProbabilityTheory.variance (fun ω => dotProduct x (Z ω)) ν := by
        have h_term_int : ∀ i j : Fin d,
            MeasureTheory.Integrable (fun ω => (x i * x j) * (D i ω * D j ω)) ν :=
          fun i j => (hD_mul_int i j).const_mul (x i * x j)
        have h_inner_int : ∀ i : Fin d,
            MeasureTheory.Integrable (fun ω => ∑ j : Fin d, (x i * x j) * (D i ω * D j ω)) ν :=
          fun i => MeasureTheory.integrable_finset_sum Finset.univ (fun j _ => h_term_int i j)
        calc dotProduct x ((rvCovMat Z ν).mulVec x)
            = ∑ i : Fin d, ∑ j : Fin d, (x i * x j) * (∫ ω, D i ω * D j ω ∂ν) := by
                simp only [dotProduct, Matrix.mulVec, rvCovMat, Matrix.of_apply, Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                dsimp [D, mu]
                ring
          _ = ∑ i : Fin d, ∑ j : Fin d, ∫ ω, (x i * x j) * (D i ω * D j ω) ∂ν := by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                rw [MeasureTheory.integral_const_mul]
          _ = ∑ i : Fin d, ∫ ω, (∑ j : Fin d, (x i * x j) * (D i ω * D j ω)) ∂ν := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [← MeasureTheory.integral_finset_sum Finset.univ (fun j _ => h_term_int i j)]
          _ = ∫ ω, (∑ i : Fin d, ∑ j : Fin d, (x i * x j) * (D i ω * D j ω)) ∂ν := by
                rw [← MeasureTheory.integral_finset_sum Finset.univ (fun i _ => h_inner_int i)]
          _ = ∫ ω, (dotProduct x (Z ω) - ∫ ω', dotProduct x (Z ω') ∂ν) ^ 2 ∂ν := by
                congr 1
                ext ω
                rw [← h_mean]
                have h_lin : ∑ i : Fin d, x i * D i ω =
                    dotProduct x (Z ω) - dotProduct x (rvMeanVec Z ν) := by
                  simp only [dotProduct, D, mu, mul_sub, Finset.sum_sub_distrib]
                calc ∑ i : Fin d, ∑ j : Fin d, (x i * x j) * (D i ω * D j ω)
                    = ∑ i : Fin d, (x i * D i ω) * (∑ j : Fin d, x j * D j ω) := by
                        refine Finset.sum_congr rfl fun i _ => ?_
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl fun j _ => ?_
                        ring
                  _ = (∑ i : Fin d, x i * D i ω) * (∑ j : Fin d, x j * D j ω) := by
                        rw [← Finset.sum_mul]
                  _ = (dotProduct x (Z ω) - dotProduct x (rvMeanVec Z ν)) ^ 2 := by
                        rw [h_lin, sq]
          _ = ProbabilityTheory.variance (fun ω => dotProduct x (Z ω)) ν :=
                (ProbabilityTheory.variance_eq_integral hW_lp.aemeasurable).symm
      exact ⟨hW_lp, h_mean, h_var⟩
    have hS_herm : (rvCovMat Z ν).IsHermitian := by
      ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, rvCovMat, Matrix.of_apply]
      congr 1
      ext ω
      ring
    have hS_psd : (rvCovMat Z ν).PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hS_herm fun v => ?_
      simp only [star_trivial]
      rw [(h_proj v).2.2]
      exact ProbabilityTheory.variance_nonneg _ ν
    have h_tr_nonneg : 0 ≤ psdTraceSqrt (rvCovMat Z ν) := by
      rw [h_psd_tr_eq hS_psd]
      exact (h_sqrt_psd hS_psd).trace_nonneg
    set S := rvCovMat Z ν
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
    have hS_diag_le : ∀ i : Fin d, S i i ≤ ∫ ω, (Z ω i) ^ 2 ∂ν := by
      intro i
      have h_eq : S i i = ProbabilityTheory.variance (fun ω => Z ω i) ν := by
        calc S i i
            = ∫ ω, (Z ω i - ∫ ω', Z ω' i ∂ν) ^ 2 ∂ν := by
                simp only [S, rvCovMat, rvMeanVec, Matrix.of_apply, sq]
          _ = ProbabilityTheory.variance (fun ω => Z ω i) ν :=
                (ProbabilityTheory.variance_eq_integral (hZν i).aemeasurable).symm
      rw [h_eq]
      exact ProbabilityTheory.variance_le_expectation_sq (hZν i).aestronglyMeasurable
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
        have h1 : ∑ i : Fin d, S i i ≤ ∑ i : Fin d, ∫ ω, (Z ω i) ^ 2 ∂ν :=
          Finset.sum_le_sum fun i _ => hS_diag_le i
        have h2 : ∑ i : Fin d, ∫ ω, (Z ω i) ^ 2 ∂ν = ∫ ω, (∑ i : Fin d, (Z ω i) ^ 2) ∂ν :=
          (MeasureTheory.integral_finset_sum Finset.univ fun i _ => (hZν i).integrable_sq).symm
        have h_pw : ∀ ω : Ω, ∑ i : Fin d, (Z ω i) ^ 2 ≤ 1 := by
          intro ω
          have hb := hBall ω
          unfold vecL2Norm at hb
          have h_nn : 0 ≤ ∑ i : Fin d, (Z ω i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
          calc ∑ i : Fin d, (Z ω i) ^ 2
              = (Real.sqrt (∑ i : Fin d, (Z ω i) ^ 2)) ^ 2 := (Real.sq_sqrt h_nn).symm
            _ ≤ 1 ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
            _ = 1 := one_pow 2
        have h_sum_int : MeasureTheory.Integrable (fun ω => ∑ i : Fin d, (Z ω i) ^ 2) ν :=
          MeasureTheory.integrable_finset_sum Finset.univ fun i _ => (hZν i).integrable_sq
        have h3 : ∫ ω, (∑ i : Fin d, (Z ω i) ^ 2) ∂ν ≤ 1 := by
          calc ∫ ω, (∑ i : Fin d, (Z ω i) ^ 2) ∂ν
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
          have h_pw : ∀ ω : Ω, (Z ω i) ^ 2 ≤ 1 := fun ω => by
            have hc := hCube ω i
            nlinarith [sq_abs (Z ω i), abs_nonneg (Z ω i)]
          have h_int_le : ∫ ω, (Z ω i) ^ 2 ∂ν ≤ 1 := by
            calc ∫ ω, (Z ω i) ^ 2 ∂ν
                ≤ ∫ _ : Ω, (1 : ℝ) ∂ν :=
                  MeasureTheory.integral_mono (hZν i).integrable_sq
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

  have h_step2 : ∀ (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
      (W : Ω → ℝ), MeasureTheory.MemLp W 2 ν →
      let muW := ∫ ω, W ω ∂ν
      let sigW := Real.sqrt (ProbabilityTheory.variance W ν)
      (1 / 2 : ℝ) *
        ((∫ ω, |W ω - (muW + (sigW / 2) * (-1))| ∂ν) +
         (∫ ω, |W ω - (muW + (sigW / 2) * 1)| ∂ν)) ≤ sigW := by
    intro ν _ W hW
    dsimp only
    set muW : ℝ := ∫ ω, W ω ∂ν
    set sigW : ℝ := Real.sqrt (ProbabilityTheory.variance W ν)
    have h_sig_nonneg : 0 ≤ sigW := Real.sqrt_nonneg _
    let u : Ω → ℝ := fun ω => W ω - muW
    have hu_lp : MeasureTheory.MemLp u 2 ν := hW.sub (MeasureTheory.memLp_const muW)
    have hu_int : MeasureTheory.Integrable u ν := hu_lp.integrable one_le_two
    have hu_sq_int : MeasureTheory.Integrable (fun ω => (u ω) ^ 2) ν := hu_lp.integrable_sq
    have h_var_eq : (∫ ω, (u ω) ^ 2 ∂ν) = sigW ^ 2 := by
      rw [Real.sq_sqrt (ProbabilityTheory.variance_nonneg W ν)]
      exact (ProbabilityTheory.variance_eq_integral hW.aemeasurable).symm
    let f1 : Ω → ℝ := fun ω => |W ω - (muW + (sigW / 2) * (-1))|
    let f2 : Ω → ℝ := fun ω => |W ω - (muW + (sigW / 2) * 1)|
    have hf1_eq : f1 = fun ω => |u ω + sigW / 2| := by
      ext ω; dsimp [f1, u]; congr 1; ring
    have hf2_eq : f2 = fun ω => |u ω - sigW / 2| := by
      ext ω; dsimp [f2, u]; congr 1; ring
    have hf1_int : MeasureTheory.Integrable f1 ν := by
      rw [hf1_eq]; exact (hu_int.add (MeasureTheory.integrable_const _)).abs
    have hf2_int : MeasureTheory.Integrable f2 ν := by
      rw [hf2_eq]; exact (hu_int.sub (MeasureTheory.integrable_const _)).abs
    set L : ℝ := (1 / 2 : ℝ) * ((∫ ω, f1 ω ∂ν) + (∫ ω, f2 ω ∂ν))
    have hL_eq : L = ∫ ω, (1 / 2 : ℝ) * (f1 ω + f2 ω) ∂ν := by
      dsimp [L]
      rw [← MeasureTheory.integral_add hf1_int hf2_int, ← MeasureTheory.integral_const_mul]
    have hL_int : MeasureTheory.Integrable (fun ω => (1 / 2 : ℝ) * (f1 ω + f2 ω)) ν :=
      (hf1_int.add hf2_int).const_mul (1 / 2 : ℝ)
    by_contra h_not_le
    push_neg at h_not_le
    let eps : ℝ := L - sigW
    have heps_pos : 0 < eps := sub_pos.mpr h_not_le
    let r : ℝ := sigW + eps
    have hr_pos : 0 < r := by linarith
    have hr_ne : r ≠ 0 := hr_pos.ne'
    have h_pw : ∀ ω : Ω, (1 / 2 : ℝ) * (f1 ω + f2 ω) ≤ r / 2 + (u ω) ^ 2 / (2 * r) := by
      intro ω
      have h1 : f1 ω = |u ω + sigW / 2| := congr_fun hf1_eq ω
      have h2 : f2 ω = |u ω - sigW / 2| := congr_fun hf2_eq ω
      rw [h1, h2]
      set t : ℝ := u ω
      rcases lt_or_ge t (-(sigW / 2)) with htL | htM
      · rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
        have hsq : 0 ≤ (t + r) ^ 2 / (2 * r) := div_nonneg (sq_nonneg _) (by linarith)
        have halg : (t + r) ^ 2 / (2 * r) = r / 2 + t ^ 2 / (2 * r) + t := by
          field_simp; ring
        linarith
      · rcases lt_or_ge t (sigW / 2) with htM2 | htR
        · rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)]
          have hsq : 0 ≤ t ^ 2 / (2 * r) := div_nonneg (sq_nonneg _) (by linarith)
          linarith
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          have hsq : 0 ≤ (t - r) ^ 2 / (2 * r) := div_nonneg (sq_nonneg _) (by linarith)
          have halg : (t - r) ^ 2 / (2 * r) = r / 2 + t ^ 2 / (2 * r) - t := by
            field_simp; ring
          linarith
    have h_rhs_int : MeasureTheory.Integrable (fun ω => r / 2 + (u ω) ^ 2 / (2 * r)) ν :=
      (MeasureTheory.integrable_const (r / 2)).add (hu_sq_int.div_const (2 * r))
    have h_mono : L ≤ ∫ ω, (r / 2 + (u ω) ^ 2 / (2 * r)) ∂ν := by
      rw [hL_eq]
      exact MeasureTheory.integral_mono hL_int h_rhs_int h_pw
    have h_eval : (∫ ω, (r / 2 + (u ω) ^ 2 / (2 * r)) ∂ν) = r / 2 + sigW ^ 2 / (2 * r) := by
      rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _) (hu_sq_int.div_const _),
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul,
          MeasureTheory.integral_div, h_var_eq]
    have h_frac_le : sigW ^ 2 / (2 * r) ≤ sigW / 2 := by
      rw [div_le_div_iff₀ (by linarith : 0 < 2 * r) (by norm_num : (0 : ℝ) < 2)]
      dsimp [r]
      nlinarith
    have hr_def : r = L := by dsimp [r, eps]; ring
    linarith

  have h_step3 : ∀ (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
      (W : Ω → ℝ), MeasureTheory.MemLp W 2 ν →
      let muW := ∫ ω, W ω ∂ν
      let sigW := Real.sqrt (ProbabilityTheory.variance W ν)
      let E_pos (eps : ℝ) : Set Ω := {ω | 0 ≤ W ω - (muW + (sigW / 2) * eps)}
      let E_neg (eps : ℝ) : Set Ω := (E_pos eps)ᶜ
      (1 / 2 : ℝ) *
        ((ν.real (E_pos (-1)) * Real.sqrt (ProbabilityTheory.variance W (ProbabilityTheory.cond ν (E_pos (-1)))) +
          ν.real (E_neg (-1)) * Real.sqrt (ProbabilityTheory.variance W (ProbabilityTheory.cond ν (E_neg (-1))))) +
         (ν.real (E_pos 1) * Real.sqrt (ProbabilityTheory.variance W (ProbabilityTheory.cond ν (E_pos 1))) +
          ν.real (E_neg 1) * Real.sqrt (ProbabilityTheory.variance W (ProbabilityTheory.cond ν (E_neg 1))))) ≤
        (23 / 24 : ℝ) * sigW := by
    intro ν _ W hW
    dsimp only
    have h_dc := lem_deviation_contraction ν W hW
    unfold expectedPosteriorStdDev condStdDev rvStdDev at h_dc
    dsimp only at h_dc
    rw [Fintype.sum_bool, Fintype.sum_bool] at h_dc
    have h_ev_true : ∀ eps : ℝ,
        searchBranchEvent W (∫ ω, W ω ∂ν) (Real.sqrt (ProbabilityTheory.variance W ν)) eps true =
          {ω | 0 ≤ W ω - ((∫ ω, W ω ∂ν) + (Real.sqrt (ProbabilityTheory.variance W ν) / 2) * eps)} := by
      intro eps; ext ω; simp [searchBranchEvent]
    have h_ev_false : ∀ eps : ℝ,
        searchBranchEvent W (∫ ω, W ω ∂ν) (Real.sqrt (ProbabilityTheory.variance W ν)) eps false =
          ({ω | 0 ≤ W ω - ((∫ ω, W ω ∂ν) + (Real.sqrt (ProbabilityTheory.variance W ν) / 2) * eps)})ᶜ := by
      intro eps; ext ω; simp [searchBranchEvent]
    rw [h_ev_true (-1), h_ev_false (-1), h_ev_true 1, h_ev_false 1] at h_dc
    linarith

  have h_step4 : ∀ (x : Fin d → ℝ), vecL2Norm x ≤ 1 →
      ∀ (S S₁ S₂ : Matrix (Fin d) (Fin d) ℝ),
        S.PosSemidef → S₁.PosSemidef → S₂.PosSemidef →
        ∀ (p₁ p₂ : ℝ), 0 ≤ p₁ → 0 ≤ p₂ → p₁ + p₂ = 1 →
        (S - (p₁ • S₁ + p₂ • S₂)).PosSemidef →
        Real.sqrt (dotProduct x (S.mulVec x)) -
          (p₁ * Real.sqrt (dotProduct x (S₁.mulVec x)) +
           p₂ * Real.sqrt (dotProduct x (S₂.mulVec x))) ≤
        psdTraceSqrt S - (p₁ * psdTraceSqrt S₁ + p₂ * psdTraceSqrt S₂) := by
    intro x hx S S₁ S₂ hS hS₁ hS₂ p₁ p₂ hp₁ hp₂ hp hDom
    have hComb : (p₁ • S₁ + p₂ • S₂).PosSemidef :=
      (hS₁.smul hp₁).add (hS₂.smul hp₂)
    have h_env := lem_envelope x hx
    have h_conc := h_env.2.2.2.2 S₁ S₂ hS₁ hS₂ p₁ p₂ hp₁ hp₂ hp hComb
    have h_mono := h_env.2.2.2.1 (p₁ • S₁ + p₂ • S₂) S hComb hS hDom
    unfold gapPotential at h_conc h_mono
    rw [h_psd_tr_eq hS, h_psd_tr_eq hS₁, h_psd_tr_eq hS₂]
    linarith

  have h_cov_zero : rvCovMat Z (0 : MeasureTheory.Measure Ω) = 0 := by
    ext i j
    simp [rvCovMat, MeasureTheory.integral_zero_measure]
  have h_cond_null : ∀ (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
      (G : Set Ω), ν G = 0 →
      ProbabilityTheory.cond ν G = 0 ∧ ProbabilityTheory.cond ν Gᶜ = ν := by
    intro ν _ G hG0
    have h1 : ProbabilityTheory.cond ν G = 0 :=
      ProbabilityTheory.cond_eq_zero.mpr (Or.inr hG0)
    have hae : ∀ᵐ ω ∂ν, ω ∈ Gᶜ := by
      rw [MeasureTheory.ae_iff]
      have hset : {ω : Ω | ¬(ω ∈ Gᶜ)} = G := by ext ω; simp
      rw [hset]
      exact hG0
    have hrest : ν.restrict Gᶜ = ν := MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae
    have hGc1 : ν Gᶜ = 1 := by
      calc ν Gᶜ = (ν.restrict Gᶜ) Set.univ := (MeasureTheory.Measure.restrict_apply_univ Gᶜ).symm
        _ = ν Set.univ := by rw [hrest]
        _ = 1 := MeasureTheory.measure_univ
    have h2 : ProbabilityTheory.cond ν Gᶜ = ν := by
      change (ν Gᶜ)⁻¹ • ν.restrict Gᶜ = ν
      rw [hGc1, hrest, inv_one, one_smul]
    exact ⟨h1, h2⟩

  have h_step5 : ∀ (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν],
      (∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 ν) →
      ∀ (E : Set Ω), MeasureTheory.NullMeasurableSet E ν →
      let p_pos := ν.real E
      let p_neg := ν.real Eᶜ
      let ν_pos := ProbabilityTheory.cond ν E
      let ν_neg := ProbabilityTheory.cond ν Eᶜ
      let S := rvCovMat Z ν
      let S_pos := rvCovMat Z ν_pos
      let S_neg := rvCovMat Z ν_neg
      (0 ≤ p_pos ∧ 0 ≤ p_neg ∧ p_pos + p_neg = 1) ∧
      (S_pos.PosSemidef ∧ S_neg.PosSemidef) ∧
      (S - (p_pos • S_pos + p_neg • S_neg)).PosSemidef ∧
      ∀ x : Fin d → ℝ,
        let W := fun ω => dotProduct x (Z ω)
        p_pos * Real.sqrt (dotProduct x (S_pos.mulVec x)) =
          p_pos * Real.sqrt (ProbabilityTheory.variance W ν_pos) ∧
        p_neg * Real.sqrt (dotProduct x (S_neg.mulVec x)) =
          p_neg * Real.sqrt (ProbabilityTheory.variance W ν_neg) := by
    intro ν _ hZν E hE
    dsimp only
    set p_pos : ℝ := ν.real E
    set p_neg : ℝ := ν.real Eᶜ
    set ν_pos := ProbabilityTheory.cond ν E
    set ν_neg := ProbabilityTheory.cond ν Eᶜ
    set S := rvCovMat Z ν
    set S_pos := rvCovMat Z ν_pos
    set S_neg := rvCovMat Z ν_neg
    have hp_pos_nn : 0 ≤ p_pos := MeasureTheory.measureReal_nonneg
    have hp_neg_nn : 0 ≤ p_neg := MeasureTheory.measureReal_nonneg
    have hp_sum : p_pos + p_neg = 1 := by
      have hc : p_neg = 1 - p_pos := by
        dsimp [p_pos, p_neg]
        rw [MeasureTheory.measureReal_compl₀ hE, MeasureTheory.probReal_univ]
      linarith
    obtain ⟨hS_psd, _, h_proj_ν, _, _⟩ := h_step1 ν hZν
    refine ⟨⟨hp_pos_nn, hp_neg_nn, hp_sum⟩, ?_⟩
    by_cases hE0 : ν E = 0
    · obtain ⟨h_c0, h_c1⟩ := h_cond_null ν E hE0
      have hp0 : p_pos = 0 := by simp [p_pos, MeasureTheory.measureReal_def, hE0]
      have hp1 : p_neg = 1 := by linarith
      have hS_pos0 : S_pos = 0 := by dsimp [S_pos, ν_pos]; rw [h_c0, h_cov_zero]
      have hS_negS : S_neg = S := by dsimp [S_neg, ν_neg, S]; rw [h_c1]
      have h_dom : (S - (p_pos • S_pos + p_neg • S_neg)) = 0 := by
        rw [hp0, hp1, hS_pos0, hS_negS]
        simp
      refine ⟨⟨by rw [hS_pos0]; exact Matrix.PosSemidef.zero,
               by rw [hS_negS]; exact hS_psd⟩,
              by rw [h_dom]; exact Matrix.PosSemidef.zero, ?_⟩
      intro x
      refine ⟨by rw [hp0]; simp, ?_⟩
      rw [hS_negS, (h_proj_ν x).2.2]
      dsimp [ν_neg]
      rw [h_c1]
    · by_cases hEc0 : ν Eᶜ = 0
      · obtain ⟨h_c0, h_c1⟩ := h_cond_null ν Eᶜ hEc0
        have h_c1' : ProbabilityTheory.cond ν E = ν := by simpa [compl_compl] using h_c1
        have hp0 : p_neg = 0 := by simp [p_neg, MeasureTheory.measureReal_def, hEc0]
        have hp1 : p_pos = 1 := by linarith
        have hS_neg0 : S_neg = 0 := by dsimp [S_neg, ν_neg]; rw [h_c0, h_cov_zero]
        have hS_posS : S_pos = S := by dsimp [S_pos, ν_pos, S]; rw [h_c1']
        have h_dom : (S - (p_pos • S_pos + p_neg • S_neg)) = 0 := by
          rw [hp0, hp1, hS_neg0, hS_posS]
          simp
        refine ⟨⟨by rw [hS_posS]; exact hS_psd,
                 by rw [hS_neg0]; exact Matrix.PosSemidef.zero⟩,
                by rw [h_dom]; exact Matrix.PosSemidef.zero, ?_⟩
        intro x
        refine ⟨?_, by rw [hp0]; simp⟩
        rw [hS_posS, (h_proj_ν x).2.2]
        dsimp [ν_pos]
        rw [h_c1']
      · haveI : MeasureTheory.IsProbabilityMeasure ν_pos :=
          ProbabilityTheory.cond_isProbabilityMeasure hE0
        haveI : MeasureTheory.IsProbabilityMeasure ν_neg :=
          ProbabilityTheory.cond_isProbabilityMeasure hEc0
        have hZ_pos : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 ν_pos :=
          fun i => ((hZν i).restrict E).smul_measure (ENNReal.inv_ne_top.mpr hE0)
        have hZ_neg : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 ν_neg :=
          fun i => ((hZν i).restrict Eᶜ).smul_measure (ENNReal.inv_ne_top.mpr hEc0)
        obtain ⟨hS_pos_psd, _, h_proj_pos, _, _⟩ := h_step1 ν_pos hZ_pos
        obtain ⟨hS_neg_psd, _, h_proj_neg, _, _⟩ := h_step1 ν_neg hZ_neg
        have hD_herm : (S - (p_pos • S_pos + p_neg • S_neg)).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
              Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
              hS_psd.isHermitian.eq, hS_pos_psd.isHermitian.eq, hS_neg_psd.isHermitian.eq]
          simp only [star_trivial]
          rfl
        have h_branch_var : ∀ (F : Set Ω) (hF0 : ν F ≠ 0) (v : Fin d → ℝ),
            let m := ∫ ω, dotProduct v (Z ω) ∂ν
            ν.real F * ProbabilityTheory.variance (fun ω => dotProduct v (Z ω))
              (ProbabilityTheory.cond ν F) ≤
              ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂ν := by
          intro F hF0 v m
          haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond ν F) :=
            ProbabilityTheory.cond_isProbabilityMeasure hF0
          have hU_ν : MeasureTheory.MemLp (fun ω => dotProduct v (Z ω)) 2 ν := (h_proj_ν v).1
          have hU_F : MeasureTheory.MemLp (fun ω => dotProduct v (Z ω)) 2
              (ProbabilityTheory.cond ν F) :=
            (hU_ν.restrict F).smul_measure (ENNReal.inv_ne_top.mpr hF0)
          have hU_sub : MeasureTheory.MemLp (fun ω => dotProduct v (Z ω) - m) 2
              (ProbabilityTheory.cond ν F) :=
            hU_F.sub (MeasureTheory.memLp_const m)
          have hpF_pos : 0 < ν.real F :=
            ENNReal.toReal_pos hF0 (MeasureTheory.measure_ne_top ν F)
          have hpF_ne : ν.real F ≠ 0 := hpF_pos.ne'
          have hv1 : ProbabilityTheory.variance (fun ω => dotProduct v (Z ω))
              (ProbabilityTheory.cond ν F) =
              ProbabilityTheory.variance (fun ω => dotProduct v (Z ω) - m)
                (ProbabilityTheory.cond ν F) :=
            (ProbabilityTheory.variance_sub_const hU_F.1 m).symm
          have hv2 : ProbabilityTheory.variance (fun ω => dotProduct v (Z ω) - m)
              (ProbabilityTheory.cond ν F) ≤
              ∫ ω, (dotProduct v (Z ω) - m) ^ 2 ∂(ProbabilityTheory.cond ν F) :=
            ProbabilityTheory.variance_le_expectation_sq hU_sub.1
          have hv3 : (∫ ω, (dotProduct v (Z ω) - m) ^ 2 ∂(ProbabilityTheory.cond ν F)) =
              (ν.real F)⁻¹ * ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂ν := by
            change (∫ ω, (dotProduct v (Z ω) - m) ^ 2 ∂((ν F)⁻¹ • ν.restrict F)) = _
            rw [MeasureTheory.integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
              ← MeasureTheory.measureReal_def]
          have h_le : ProbabilityTheory.variance (fun ω => dotProduct v (Z ω))
              (ProbabilityTheory.cond ν F) ≤
              (ν.real F)⁻¹ * ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂ν := by linarith
          have hmul := mul_le_mul_of_nonneg_left h_le hpF_pos.le
          have hcancel : ν.real F * ((ν.real F)⁻¹ * ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂ν) =
              ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂ν := by field_simp
          linarith
        have h_dom : (S - (p_pos • S_pos + p_neg • S_neg)).PosSemidef := by
          refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hD_herm fun v => ?_
          simp only [star_trivial]
          let U : Ω → ℝ := fun ω => dotProduct v (Z ω)
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
            exact ((h_proj_ν v).2.2).symm
          have h_quad_expand :
              dotProduct v ((S - (p_pos • S_pos + p_neg • S_neg)).mulVec v) =
                dotProduct v (S.mulVec v) -
                  (p_pos * ProbabilityTheory.variance U ν_pos +
                   p_neg * ProbabilityTheory.variance U ν_neg) := by
            simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
              dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
            rw [(h_proj_pos v).2.2, (h_proj_neg v).2.2]
          rw [h_quad_expand]
          dsimp [U, m, p_pos, p_neg, ν_pos, ν_neg] at *
          linarith
        refine ⟨⟨hS_pos_psd, hS_neg_psd⟩, h_dom, ?_⟩
        intro x
        rw [(h_proj_pos x).2.2, (h_proj_neg x).2.2]
        exact ⟨rfl, rfl⟩

  have h_ind : ∀ (n : ℕ) (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν],
      (∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 ν) →
      ∀ (hist : List (SearchObs d)),
        0 ≤ alg1ExpectedLoss Z ctxPolicy n ν hist ∧
        alg1ExpectedLoss Z ctxPolicy n ν hist ≤ 24 * psdTraceSqrt (rvCovMat Z ν) := by
    intro n
    induction n with
    | zero =>
        intro ν _ hZν hist
        simp only [alg1ExpectedLoss]
        have h_nonneg := (h_step1 ν hZν).2.1
        exact ⟨le_rfl, by linarith⟩
    | succ n ih =>
        intro ν _ hZν hist
        set x : Fin d → ℝ := ctxPolicy hist
        have hx : vecL2Norm x ≤ 1 := hCtx hist
        set S := rvCovMat Z ν
        set W : Ω → ℝ := fun ω => dotProduct x (Z ω)
        obtain ⟨hS_psd, _, h_proj, _, _⟩ := h_step1 ν hZν
        obtain ⟨hW_lp, h_mu, h_var⟩ := h_proj x
        set muW : ℝ := ∫ ω, W ω ∂ν
        set sigW : ℝ := Real.sqrt (ProbabilityTheory.variance W ν)
        have h_sig : Real.sqrt (dotProduct x (S.mulVec x)) = sigW := by
          dsimp [sigW, W]; rw [h_var]
        let P : ℝ → ℝ := fun eps => muW + (sigW / 2) * eps
        let E_pos : ℝ → Set Ω := fun eps => {ω | 0 ≤ W ω - P eps}
        let E_neg : ℝ → Set Ω := fun eps => (E_pos eps)ᶜ
        have h_coin_drop : ∀ eps : ℝ,
            sigW -
              (ν.real (E_pos eps) *
                Real.sqrt (ProbabilityTheory.variance W (ProbabilityTheory.cond ν (E_pos eps))) +
               ν.real (E_neg eps) *
                Real.sqrt (ProbabilityTheory.variance W (ProbabilityTheory.cond ν (E_neg eps)))) ≤
            psdTraceSqrt S -
              (ν.real (E_pos eps) *
                psdTraceSqrt (rvCovMat Z (ProbabilityTheory.cond ν (E_pos eps))) +
               ν.real (E_neg eps) *
                psdTraceSqrt (rvCovMat Z (ProbabilityTheory.cond ν (E_neg eps)))) := by
          intro eps
          have h_pre : E_pos eps = W ⁻¹' Set.Ici (P eps) := by
            ext ω; simp [E_pos, Set.mem_Ici, sub_nonneg]
          have hE_nm : MeasureTheory.NullMeasurableSet (E_pos eps) ν := by
            rw [h_pre]
            exact hW_lp.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici
          obtain ⟨⟨hp1, hp2, hpsum⟩, ⟨hS1, hS2⟩, hDom, h_dir⟩ :=
            h_step5 ν hZν (E_pos eps) hE_nm
          obtain ⟨h_dir1, h_dir2⟩ := h_dir x
          have h_drop := h_step4 x hx S
            (rvCovMat Z (ProbabilityTheory.cond ν (E_pos eps)))
            (rvCovMat Z (ProbabilityTheory.cond ν (E_neg eps)))
            hS_psd hS1 hS2 (ν.real (E_pos eps)) (ν.real (E_neg eps)) hp1 hp2 hpsum hDom
          rw [h_sig, h_dir1, h_dir2] at h_drop
          exact h_drop
        have h_cont : ∀ (F : Set Ω) (hist' : List (SearchObs d)),
            0 ≤ (if ν F = 0 then 0
                 else ν.real F * alg1ExpectedLoss Z ctxPolicy n (ProbabilityTheory.cond ν F) hist') ∧
            (if ν F = 0 then 0
             else ν.real F * alg1ExpectedLoss Z ctxPolicy n (ProbabilityTheory.cond ν F) hist') ≤
              24 * (ν.real F * psdTraceSqrt (rvCovMat Z (ProbabilityTheory.cond ν F))) := by
          intro F hist'
          by_cases hF0 : ν F = 0
          · simp [hF0, MeasureTheory.measureReal_def]
          · rw [if_neg hF0]
            haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond ν F) :=
              ProbabilityTheory.cond_isProbabilityMeasure hF0
            have hZF : ∀ i : Fin d,
                MeasureTheory.MemLp (fun ω => Z ω i) 2 (ProbabilityTheory.cond ν F) :=
              fun i => ((hZν i).restrict F).smul_measure (ENNReal.inv_ne_top.mpr hF0)
            obtain ⟨h_ih_nn, h_ih_le⟩ := ih (ProbabilityTheory.cond ν F) hZF hist'
            have hp_nn : 0 ≤ ν.real F := MeasureTheory.measureReal_nonneg (μ := ν) (s := F)
            have h_mul := mul_le_mul_of_nonneg_left h_ih_le hp_nn
            exact ⟨mul_nonneg hp_nn h_ih_nn, by linarith⟩
        have h_cur_nn_neg : 0 ≤ ∫ ω, |W ω - P (-1)| ∂ν :=
          MeasureTheory.integral_nonneg fun _ => abs_nonneg _
        have h_cur_nn_pos : 0 ≤ ∫ ω, |W ω - P 1| ∂ν :=
          MeasureTheory.integral_nonneg fun _ => abs_nonneg _
        have h_loss := h_step2 ν W hW_lp
        have h_contr := h_step3 ν W hW_lp
        have h_drop_neg := h_coin_drop (-1)
        have h_drop_pos := h_coin_drop 1
        obtain ⟨h_c1_nn, h_c1⟩ := h_cont (E_pos (-1)) (hist ++ [⟨x, -1, P (-1), 1⟩])
        obtain ⟨h_c2_nn, h_c2⟩ := h_cont (E_neg (-1)) (hist ++ [⟨x, -1, P (-1), -1⟩])
        obtain ⟨h_c3_nn, h_c3⟩ := h_cont (E_pos 1) (hist ++ [⟨x, 1, P 1, 1⟩])
        obtain ⟨h_c4_nn, h_c4⟩ := h_cont (E_neg 1) (hist ++ [⟨x, 1, P 1, -1⟩])
        have h_unfold : alg1ExpectedLoss Z ctxPolicy (n + 1) ν hist =
            (1 / 2 : ℝ) *
              (((∫ ω, |W ω - P (-1)| ∂ν) +
                (if ν (E_pos (-1)) = 0 then 0
                 else ν.real (E_pos (-1)) *
                   alg1ExpectedLoss Z ctxPolicy n (ProbabilityTheory.cond ν (E_pos (-1)))
                     (hist ++ [⟨x, -1, P (-1), 1⟩])) +
                (if ν (E_neg (-1)) = 0 then 0
                 else ν.real (E_neg (-1)) *
                   alg1ExpectedLoss Z ctxPolicy n (ProbabilityTheory.cond ν (E_neg (-1)))
                     (hist ++ [⟨x, -1, P (-1), -1⟩]))) +
               ((∫ ω, |W ω - P 1| ∂ν) +
                (if ν (E_pos 1) = 0 then 0
                 else ν.real (E_pos 1) *
                   alg1ExpectedLoss Z ctxPolicy n (ProbabilityTheory.cond ν (E_pos 1))
                     (hist ++ [⟨x, 1, P 1, 1⟩])) +
                (if ν (E_neg 1) = 0 then 0
                 else ν.real (E_neg 1) *
                   alg1ExpectedLoss Z ctxPolicy n (ProbabilityTheory.cond ν (E_neg 1))
                     (hist ++ [⟨x, 1, P 1, -1⟩])))) := by
          simp only [alg1ExpectedLoss]
          change (1 / 2 : ℝ) * _ = _
          have h_mu' : dotProduct x (rvMeanVec Z ν) = muW := h_mu
          have h_sig' : Real.sqrt (dotProduct x (S.mulVec x)) = sigW := h_sig
          dsimp [x, S, W, P, E_pos, E_neg] at *
          rw [h_mu', h_sig']
        rw [h_unfold]
        dsimp [W, P, muW, sigW, E_pos, E_neg] at h_cur_nn_neg h_cur_nn_pos h_loss h_contr
        dsimp [W, P, muW, sigW, E_pos, E_neg] at h_drop_neg h_drop_pos h_c1_nn h_c1 h_c2_nn h_c2
        dsimp [W, P, muW, sigW, E_pos, E_neg] at h_c3_nn h_c3 h_c4_nn h_c4 ⊢
        refine ⟨?_, ?_⟩
        · linarith
        · linarith

  obtain ⟨hS_psd, _, _, h_ball_pot, h_cube_pot⟩ := h_step1 μ hZ
  obtain ⟨h_loss_nn, h_loss_le⟩ := h_ind T μ hZ []
  refine ⟨hS_psd, h_loss_nn, h_loss_le, ?_, ?_⟩
  · intro hBall
    have h_pot := h_ball_pot hBall
    linarith
  · intro hCube
    have h_pot := h_cube_pot hCube
    linarith

/-- **Theorem 2.1 for randomized adaptive context strategies**:
Under any probability space `(Ξ, ν_ctx)` driving the context randomization independently of the
target prior `μ` (matching Section 1.4's conditional-independence assumption), Algorithm 1's
expected total loss over `(μ, ν_ctx)` and the learner's Rademacher coins is at most
`24 Tr(√Σ₁)` both as an unconditional extended Lebesgue integral and (when `AEStronglyMeasurable`)
as a Bochner integral. -/
theorem thm_bayesian_contextual_search_rand_ctx {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Ω → (Fin d → ℝ)) (hZ : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 μ)
    {Ξ : Type*} [MeasurableSpace Ξ]
    (ν_ctx : MeasureTheory.Measure Ξ) [MeasureTheory.IsProbabilityMeasure ν_ctx]
    (ctxPolicy : Ξ → List (SearchObs d) → (Fin d → ℝ))
    (hCtx : ∀ (ξ : Ξ) (hist : List (SearchObs d)), vecL2Norm (ctxPolicy ξ hist) ≤ 1)
    (T : ℕ) :
    let L : Ξ → ℝ := fun ξ => alg1ExpectedLoss Z (ctxPolicy ξ) T μ []
    let B : ℝ := 24 * psdTraceSqrt (rvCovMat Z μ)
    (rvCovMat Z μ).PosSemidef ∧
    (∀ ξ : Ξ, 0 ≤ L ξ ∧ L ξ ≤ B) ∧
    (∫⁻ ξ, ENNReal.ofReal (L ξ) ∂ν_ctx ≤ ENNReal.ofReal B) ∧
    (MeasureTheory.AEStronglyMeasurable L ν_ctx →
      MeasureTheory.Integrable L ν_ctx ∧
      0 ≤ (∫ ξ, L ξ ∂ν_ctx) ∧
      (∫ ξ, L ξ ∂ν_ctx) ≤ B) := by
  dsimp only
  have h_psd : (rvCovMat Z μ).PosSemidef := by
    let constCtx : List (SearchObs d) → (Fin d → ℝ) := fun _ => 0
    have h0 : ∀ hist : List (SearchObs d), vecL2Norm (constCtx hist) ≤ 1 := by
      intro _
      rw [vecL2Norm, Real.sqrt_le_one]
      simp [constCtx]
    exact (thm_bayesian_contextual_search μ Z hZ constCtx h0 0).1
  have h_pw : ∀ ξ : Ξ,
      0 ≤ alg1ExpectedLoss Z (ctxPolicy ξ) T μ [] ∧
      alg1ExpectedLoss Z (ctxPolicy ξ) T μ [] ≤ 24 * psdTraceSqrt (rvCovMat Z μ) := by
    intro ξ
    have h := thm_bayesian_contextual_search μ Z hZ (ctxPolicy ξ) (hCtx ξ) T
    exact ⟨h.2.1, h.2.2.1⟩
  have h_exp := prob_expectation_le_of_pointwise ν_ctx _ (24 * psdTraceSqrt (rvCovMat Z μ)) h_pw
  exact ⟨h_psd, h_pw, h_exp.1, h_exp.2⟩

end TraceSqrt
