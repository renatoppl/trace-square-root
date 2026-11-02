import TraceSqrt.Defs
import TraceSqrt.Potential.GapEnvelope

set_option maxHeartbeats 4000000

/-!
# Lemma 1.2 & Equation (6): Potential Decrease Lemma and Quadratic Variational Duality

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 1.2.2, Equations (2)–(6) and Lemma 1.2 `lem:directional-sd-decrease`).

## Main Results
- `measurable_psdTraceSqrt`: Borel measurability of `A ↦ psdTraceSqrt (Matrix.of A)` via upper
  semicontinuity on the closed positive-semidefinite cone from the affine infimum in Lemma B.1.
- `quad_potential_variational`: Equation (6) (`2 Ψ(Σ) = inf_{m ∈ ℝ^d, R ≻ 0} E[Φ(m, R, Z)]`).
- `lem_directional_sd_decrease_family`: Equations (3) and (5) for any integrable family of PSD
  matrices `Σ_Y` dominated in Loewner order (`Σ ⪰ E[Σ_Y]`).
- `condCovMat` & `condDirStdDev`: Regular conditional covariance `Σ_Y = Cov(Z | Y)` and directional
  conditional standard deviation `√(xᵀ Σ_Y x)` for an arbitrary measurable space `β`.
- `lem_directional_sd_decrease`: **Lemma 1.2 (`lem:directional-sd-decrease`)** in unrestricted
  generality for any random vector `Z : Ω → ℝ^d` with finite second moments and any jointly defined
  a.e.-measurable signal `Y : Ω → β`, establishing Eqs. (2), (3), and (5).
- `lem_directional_sd_decrease_binary`: Specialization of Lemma 1.2 to binary conditioning on a
  null-measurable event `E` and its complement `Eᶜ`.
-/

namespace TraceSqrt

private lemma psdTraceSqrt_eq_trace_sqrt {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) :
    psdTraceSqrt A = Matrix.trace hA.sqrt := by
  unfold psdTraceSqrt
  rw [dif_pos hA]
  congr 1
  have h_dec : (fun a b : Fin d => Classical.propDecidable (a = b)) = instDecidableEqFin d :=
    Subsingleton.elim _ _
  rw [h_dec]

private lemma sqrt_posSemidef {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) : hA.sqrt.PosSemidef := by
  unfold Matrix.PosSemidef.sqrt
  let f : Fin d → ℝ := RCLike.ofReal ∘ (fun x : ℝ => √x) ∘ hA.isHermitian.eigenvalues
  have hdiag : (Matrix.diagonal f).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun i => by simp [f, Real.sqrt_nonneg]
  simpa only [Matrix.star_eq_conjTranspose] using
    hdiag.mul_mul_conjTranspose_same hA.isHermitian.eigenvectorUnitary.val

private lemma sqrt_mul_self {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) : hA.sqrt * hA.sqrt = A := by
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
            rw [hstarU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h_assoc, Matrix.diagonal_mul_diagonal]
  have h_diag_eq :
      (Matrix.diagonal fun i => f i * f i) =
        Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) := by
    congr 1; ext i
    have h_ev : 0 ≤ hA.isHermitian.eigenvalues i := hA.eigenvalues_nonneg i
    simp [f, RCLike.ofReal_real_eq_id, ← sq, Real.sq_sqrt h_ev]
  rw [h_diag_eq]
  simpa [Unitary.conjStarAlgAut_apply, U] using (hA.isHermitian.spectral_theorem).symm

private lemma trace_mul_nonneg_of_posSemidef {d : ℕ}
    {H N : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosSemidef) (hN : N.PosSemidef) :
    0 ≤ Matrix.trace (H * N) := by
  let K := hH.sqrt
  have hK_psd : K.PosSemidef := sqrt_posSemidef hH
  have hK_sq : K * K = H := sqrt_mul_self hH
  have hK_herm : K.conjTranspose = K := hK_psd.isHermitian.eq
  have h_eq : Matrix.trace (H * N) = Matrix.trace (K * N * K.conjTranspose) := by
    calc Matrix.trace (H * N)
        = Matrix.trace ((K * K) * N) := by rw [hK_sq]
      _ = Matrix.trace (K * (K * N)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((K * N) * K) := Matrix.trace_mul_comm K (K * N)
      _ = Matrix.trace (K * N * K.conjTranspose) := by rw [hK_herm]
  rw [h_eq]
  exact (hN.mul_mul_conjTranspose_same K).trace_nonneg

/-- Borel measurability of the total trace-square-root potential `A ↦ psdTraceSqrt (Matrix.of A)`. -/
lemma measurable_psdTraceSqrt (d : ℕ) :
    Measurable (fun A : Fin d → Fin d → ℝ => psdTraceSqrt (Matrix.of A)) := by
  let C : Set (Fin d → Fin d → ℝ) := {A | (Matrix.of A).PosSemidef}
  have hC_eq : C =
      (⋂ i : Fin d, ⋂ j : Fin d, {A : Fin d → Fin d → ℝ | A j i = A i j}) ∩
      (⋂ v : Fin d → ℝ, {A : Fin d → Fin d → ℝ |
        0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * (A i j * v j)}) := by
    ext A
    simp only [C, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro hA
      refine ⟨fun i j => ?_, fun v => ?_⟩
      · have := congr_fun (congr_fun hA.isHermitian.eq i) j
        simpa [Matrix.conjTranspose_apply] using this
      · have hv := hA.dotProduct_mulVec_nonneg v
        simpa [dotProduct, Matrix.mulVec, Finset.mul_sum] using hv
    · rintro ⟨hsym, hquad⟩
      have hHerm : (Matrix.of A).IsHermitian := by
        ext i j
        simpa [Matrix.conjTranspose_apply] using hsym i j
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v => ?_
      simpa [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] using hquad v
  have hC_closed : IsClosed C := by
    rw [hC_eq]
    refine IsClosed.inter ?_ ?_
    · refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_eq ((continuous_apply i).comp (continuous_apply j))
        ((continuous_apply j).comp (continuous_apply i))
    · refine isClosed_iInter fun v => isClosed_le continuous_const ?_
      refine continuous_finset_sum Finset.univ fun i _ =>
        continuous_finset_sum Finset.univ fun j _ => ?_
      exact continuous_const.mul
        (((continuous_apply j).comp (continuous_apply i)).mul continuous_const)
  have hC_meas : MeasurableSet C := hC_closed.measurableSet
  let f₀ : Subtype C → ℝ := fun A => psdTraceSqrt (Matrix.of A.1)
  have h0_norm : vecL2Norm (0 : Fin d → ℝ) ≤ 1 := by simp [vecL2Norm]
  have h_env0 := (lem_envelope (0 : Fin d → ℝ) h0_norm).2.1
  have hf₀_usc : UpperSemicontinuous f₀ := by
    rw [upperSemicontinuous_iff_isOpen_preimage]
    intro c
    have h_pre : f₀ ⁻¹' Set.Iio c =
        ⋃ (R : Matrix (Fin d) (Fin d) ℝ) (_ : R.PosDef),
          {A : Subtype C | envelopeObjective 0 R (Matrix.of A.1) < 2 * c} := by
      ext A
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq]
      obtain ⟨hGLB, hsInf⟩ := h_env0 (Matrix.of A.1) A.2
      have hgap0 : gapPotential 0 (Matrix.of A.1) A.2 = f₀ A := by
        simp [f₀, gapPotential, psdTraceSqrt_eq_trace_sqrt A.2]
      rw [hgap0] at hGLB hsInf
      have hne : {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ,
          R.PosDef ∧ v = envelopeObjective 0 R (Matrix.of A.1)}.Nonempty :=
        ⟨envelopeObjective 0 1 (Matrix.of A.1), 1, Matrix.PosDef.one, rfl⟩
      have hbdd : BddBelow {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ,
          R.PosDef ∧ v = envelopeObjective 0 R (Matrix.of A.1)} := ⟨2 * f₀ A, hGLB.1⟩
      constructor
      · intro hlt
        have hlt2 : sInf {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ,
            R.PosDef ∧ v = envelopeObjective 0 R (Matrix.of A.1)} < 2 * c := by
          linarith [hsInf]
        obtain ⟨v, ⟨R, hR, rfl⟩, hv⟩ := (csInf_lt_iff hbdd hne).mp hlt2
        exact ⟨R, hR, hv⟩
      · rintro ⟨R, hR, hlt⟩
        have hle : 2 * f₀ A ≤ envelopeObjective 0 R (Matrix.of A.1) := hGLB.1 ⟨R, hR, rfl⟩
        linarith
    rw [h_pre]
    refine isOpen_biUnion fun R _ => isOpen_lt ?_ continuous_const
    have h_cont_obj : Continuous (fun A : Subtype C => envelopeObjective 0 R (Matrix.of A.1)) := by
      have h_eq : (fun A : Subtype C => envelopeObjective 0 R (Matrix.of A.1)) =
          fun A => Matrix.trace R - vecL2Norm (R.mulVec 0) +
            ∑ i : Fin d, ∑ j : Fin d, envelopeSlope 0 R i j * A.1 j i := by
        ext A
        simp [envelopeObjective, Matrix.trace, Matrix.diag, Matrix.mul_apply]
      rw [h_eq]
      refine continuous_const.add ?_
      refine continuous_finset_sum Finset.univ fun i _ =>
        continuous_finset_sum Finset.univ fun j _ => ?_
      exact continuous_const.mul
        ((continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val))
    exact h_cont_obj
  have hf₀_meas : Measurable f₀ := hf₀_usc.measurable
  intro s hs
  classical
  have h_decomp : (fun A : Fin d → Fin d → ℝ => psdTraceSqrt (Matrix.of A)) ⁻¹' s =
      ((↑) '' (f₀ ⁻¹' s)) ∪ (if (0 : ℝ) ∈ s then Cᶜ else ∅) := by
    ext A
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_image]
    by_cases hA : A ∈ C
    · constructor
      · intro hAs
        exact Or.inl ⟨⟨A, hA⟩, hAs, rfl⟩
      · rintro (⟨⟨B, hB⟩, hBs, hBA⟩ | h_alt)
        · subst hBA; exact hBs
        · split_ifs at h_alt with h0
          · exact False.elim (h_alt hA)
          · exact False.elim h_alt
    · have h_zero : psdTraceSqrt (Matrix.of A) = 0 := by
        unfold psdTraceSqrt
        exact dif_neg hA
      rw [h_zero]
      constructor
      · intro h0s
        right; rw [if_pos h0s]; exact hA
      · rintro (⟨⟨B, hB⟩, _, hBA⟩ | h_alt)
        · subst hBA; exact False.elim (hA hB)
        · split_ifs at h_alt with h0s
          · exact h0s
          · exact False.elim h_alt
  rw [h_decomp]
  refine ((MeasurableEmbedding.subtype_coe hC_meas).measurableSet_image.mpr (hf₀_meas hs)).union ?_
  split_ifs
  · exact hC_meas.compl
  · exact MeasurableSet.empty

private lemma cov_basic_props {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
    (Z : Ω → (Fin d → ℝ))
    (hZ : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 ν) :
    (rvCovMat Z ν).PosSemidef ∧
    0 ≤ psdTraceSqrt (rvCovMat Z ν) ∧
    ∀ v : Fin d → ℝ,
      MeasureTheory.MemLp (fun ω => dotProduct v (Z ω)) 2 ν ∧
      dotProduct v ((rvCovMat Z ν).mulVec v) =
        ProbabilityTheory.variance (fun ω => dotProduct v (Z ω)) ν ∧
      Real.sqrt (dotProduct v ((rvCovMat Z ν).mulVec v)) =
        rvStdDev (fun ω => dotProduct v (Z ω)) ν := by
  let mu : Fin d → ℝ := rvMeanVec Z ν
  let D : Fin d → Ω → ℝ := fun i ω => Z ω i - mu i
  have hD_lp : ∀ i : Fin d, MeasureTheory.MemLp (D i) 2 ν :=
    fun i => (hZ i).sub (MeasureTheory.memLp_const (mu i))
  have hD_mul_int : ∀ i j : Fin d, MeasureTheory.Integrable (fun ω => D i ω * D j ω) ν :=
    fun i j => by simpa using (hD_lp i).integrable_mul (hD_lp j)
  have hZ_int : ∀ i : Fin d, MeasureTheory.Integrable (fun ω => Z ω i) ν :=
    fun i => (hZ i).integrable one_le_two
  have h_proj : ∀ v : Fin d → ℝ,
      MeasureTheory.MemLp (fun ω => dotProduct v (Z ω)) 2 ν ∧
      dotProduct v ((rvCovMat Z ν).mulVec v) =
        ProbabilityTheory.variance (fun ω => dotProduct v (Z ω)) ν ∧
      Real.sqrt (dotProduct v ((rvCovMat Z ν).mulVec v)) =
        rvStdDev (fun ω => dotProduct v (Z ω)) ν := by
    intro v
    have hU_lp : MeasureTheory.MemLp (fun ω => dotProduct v (Z ω)) 2 ν := by
      simpa only [dotProduct] using
        MeasureTheory.memLp_finset_sum Finset.univ (fun i _ => (hZ i).const_mul (v i))
    have h_mean : dotProduct v (rvMeanVec Z ν) = ∫ ω, dotProduct v (Z ω) ∂ν := by
      calc dotProduct v (rvMeanVec Z ν)
          = ∑ i : Fin d, v i * (∫ ω, Z ω i ∂ν) := rfl
        _ = ∑ i : Fin d, ∫ ω, v i * Z ω i ∂ν := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [MeasureTheory.integral_const_mul]
        _ = ∫ ω, ∑ i : Fin d, v i * Z ω i ∂ν := by
              rw [← MeasureTheory.integral_finset_sum Finset.univ
                (fun i _ => (hZ_int i).const_mul (v i))]
        _ = ∫ ω, dotProduct v (Z ω) ∂ν := rfl
    have h_var : dotProduct v ((rvCovMat Z ν).mulVec v) =
        ProbabilityTheory.variance (fun ω => dotProduct v (Z ω)) ν := by
      have h_term_int : ∀ i j : Fin d,
          MeasureTheory.Integrable (fun ω => (v i * v j) * (D i ω * D j ω)) ν :=
        fun i j => (hD_mul_int i j).const_mul (v i * v j)
      have h_inner_int : ∀ i : Fin d,
          MeasureTheory.Integrable (fun ω => ∑ j : Fin d, (v i * v j) * (D i ω * D j ω)) ν :=
        fun i => MeasureTheory.integrable_finset_sum Finset.univ (fun j _ => h_term_int i j)
      calc dotProduct v ((rvCovMat Z ν).mulVec v)
          = ∑ i : Fin d, ∑ j : Fin d, (v i * v j) * (∫ ω, D i ω * D j ω ∂ν) := by
              simp only [dotProduct, Matrix.mulVec, rvCovMat, Matrix.of_apply, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              dsimp [D, mu]; ring
        _ = ∑ i : Fin d, ∑ j : Fin d, ∫ ω, (v i * v j) * (D i ω * D j ω) ∂ν := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [MeasureTheory.integral_const_mul]
        _ = ∑ i : Fin d, ∫ ω, (∑ j : Fin d, (v i * v j) * (D i ω * D j ω)) ∂ν := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← MeasureTheory.integral_finset_sum Finset.univ (fun j _ => h_term_int i j)]
        _ = ∫ ω, (∑ i : Fin d, ∑ j : Fin d, (v i * v j) * (D i ω * D j ω)) ∂ν := by
              rw [← MeasureTheory.integral_finset_sum Finset.univ (fun i _ => h_inner_int i)]
        _ = ∫ ω, (dotProduct v (Z ω) - ∫ ω', dotProduct v (Z ω') ∂ν) ^ 2 ∂ν := by
              congr 1; ext ω
              rw [← h_mean]
              have h_lin : ∑ i : Fin d, v i * D i ω =
                  dotProduct v (Z ω) - dotProduct v (rvMeanVec Z ν) := by
                simp only [dotProduct, D, mu, mul_sub, Finset.sum_sub_distrib]
              calc ∑ i : Fin d, ∑ j : Fin d, (v i * v j) * (D i ω * D j ω)
                  = ∑ i : Fin d, (v i * D i ω) * (∑ j : Fin d, v j * D j ω) := by
                      refine Finset.sum_congr rfl fun i _ => ?_
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl fun j _ => ?_; ring
                _ = (∑ i : Fin d, v i * D i ω) * (∑ j : Fin d, v j * D j ω) := by
                      rw [← Finset.sum_mul]
                _ = (dotProduct v (Z ω) - dotProduct v (rvMeanVec Z ν)) ^ 2 := by
                      rw [h_lin, sq]
        _ = ProbabilityTheory.variance (fun ω => dotProduct v (Z ω)) ν :=
              (ProbabilityTheory.variance_eq_integral hU_lp.aemeasurable).symm
    exact ⟨hU_lp, h_var, by unfold rvStdDev; rw [h_var]⟩
  have hS_herm : (rvCovMat Z ν).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, rvCovMat, Matrix.of_apply]
    congr 1; ext ω; ring
  have hS_psd : (rvCovMat Z ν).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hS_herm fun v => ?_
    simp only [star_trivial]
    rw [(h_proj v).2.1]
    exact ProbabilityTheory.variance_nonneg _ ν
  have h_tr_nn : 0 ≤ psdTraceSqrt (rvCovMat Z ν) := by
    rw [psdTraceSqrt_eq_trace_sqrt hS_psd]
    exact (sqrt_posSemidef hS_psd).trace_nonneg
  exact ⟨hS_psd, h_tr_nn, h_proj⟩

/-- **Equation (6) (Quadratic Variational Duality, `eq:variational-quadratic-Phi`)**:
For any random vector `Z : Ω → ℝ^d` with finite second moments, covariance `Σ = rvCovMat Z μ`,
and mean `μ_Z = rvMeanVec Z μ`:
1. For every `m ∈ ℝ^d` and `R ≻ 0`, `Φ(m, R, Z)` is integrable,
   `E[Φ(m, R, Z)] = Tr R + Tr(R⁻¹ Σ) + (μ_Z - m)ᵀ R⁻¹ (μ_Z - m) ≥ 2 Ψ(Σ)`.
2. `2 Ψ(Σ) = inf_{m ∈ ℝ^d, R ≻ 0} E[Φ(m, R, Z)]` (both as `IsGLB` and `sInf`).
3. When `Σ ≻ 0`, the infimum is attained at `m = μ_Z` and `R = Σ^{1/2} ≻ 0`. -/
theorem quad_potential_variational {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Ω → (Fin d → ℝ))
    (hZ : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 μ) :
    let S := rvCovMat Z μ
    let muZ := rvMeanVec Z μ
    (∀ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef →
      MeasureTheory.Integrable (fun ω => quadPotential m R (Z ω)) μ ∧
      (∫ ω, quadPotential m R (Z ω) ∂μ) =
        Matrix.trace R + Matrix.trace (R⁻¹ * S) + dotProduct (muZ - m) (R⁻¹.mulVec (muZ - m)) ∧
      2 * psdTraceSqrt S ≤ ∫ ω, quadPotential m R (Z ω) ∂μ) ∧
    IsGLB {v : ℝ | ∃ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ),
        R.PosDef ∧ v = ∫ ω, quadPotential m R (Z ω) ∂μ}
      (2 * psdTraceSqrt S) ∧
    sInf {v : ℝ | ∃ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ),
        R.PosDef ∧ v = ∫ ω, quadPotential m R (Z ω) ∂μ} =
      2 * psdTraceSqrt S ∧
    (∀ (hS : S.PosSemidef), S.PosDef →
      hS.sqrt.PosDef ∧
      (∫ ω, quadPotential muZ hS.sqrt (Z ω) ∂μ) = 2 * psdTraceSqrt S) := by
  set S := rvCovMat Z μ
  set muZ := rvMeanVec Z μ
  obtain ⟨hS_psd, _, _⟩ := cov_basic_props μ Z hZ
  have h0_norm : vecL2Norm (0 : Fin d → ℝ) ≤ 1 := by simp [vecL2Norm]
  have h_env := lem_envelope (0 : Fin d → ℝ) h0_norm
  have hgap0 : gapPotential 0 S hS_psd = psdTraceSqrt S := by
    simp only [gapPotential, Matrix.mulVec_zero, dotProduct_zero, Real.sqrt_zero, sub_zero]
    exact (psdTraceSqrt_eq_trace_sqrt hS_psd).symm
  have hobj0 : ∀ R : Matrix (Fin d) (Fin d) ℝ,
      envelopeObjective 0 R S = Matrix.trace R + Matrix.trace (R⁻¹ * S) := by
    intro R
    simp [envelopeObjective, envelopeSlope, vecL2Norm]
  have hS_symm : ∀ i j : Fin d, S j i = S i j := fun i j => by
    have := congr_fun (congr_fun hS_psd.isHermitian.eq i) j
    simpa [Matrix.conjTranspose_apply] using this

  have h_eval : ∀ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef →
      MeasureTheory.Integrable (fun ω => quadPotential m R (Z ω)) μ ∧
      (∫ ω, quadPotential m R (Z ω) ∂μ) =
        Matrix.trace R + Matrix.trace (R⁻¹ * S) + dotProduct (muZ - m) (R⁻¹.mulVec (muZ - m)) ∧
      2 * psdTraceSqrt S ≤ ∫ ω, quadPotential m R (Z ω) ∂μ := by
    intro m R hR
    let A := R⁻¹
    have hA_psd : A.PosSemidef := hR.inv.posSemidef
    have hA_symm : ∀ i j : Fin d, A j i = A i j := fun i j => by
      have := congr_fun (congr_fun hA_psd.isHermitian.eq i) j
      simpa [Matrix.conjTranspose_apply] using this
    let U : Fin d → Ω → ℝ := fun i ω => Z ω i - muZ i
    let δ : Fin d → ℝ := muZ - m
    have hU_lp : ∀ i : Fin d, MeasureTheory.MemLp (U i) 2 μ :=
      fun i => (hZ i).sub (MeasureTheory.memLp_const (muZ i))
    have hU_int : ∀ i : Fin d, MeasureTheory.Integrable (U i) μ :=
      fun i => (hU_lp i).integrable one_le_two
    have hUU_int : ∀ i j : Fin d, MeasureTheory.Integrable (fun ω => U i ω * U j ω) μ :=
      fun i j => by simpa using (hU_lp i).integrable_mul (hU_lp j)
    have hU_zero : ∀ i : Fin d, (∫ ω, U i ω ∂μ) = 0 := by
      intro i
      dsimp [U]
      rw [MeasureTheory.integral_sub ((hZ i).integrable one_le_two)
          (MeasureTheory.integrable_const (muZ i)),
        MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
      change (∫ ω, Z ω i ∂μ) - (∫ ω, Z ω i ∂μ) = 0
      ring
    have h_quad_expand : ∀ ω : Ω,
        quadPotential m R (Z ω) =
          (Matrix.trace R + dotProduct δ (A.mulVec δ)) +
          (∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * U j ω)) +
          (∑ i : Fin d, ∑ j : Fin d, (2 * A i j * δ j) * U i ω) := by
      intro ω
      have h_zm : ∀ i : Fin d, (Z ω - m) i = U i ω + δ i := fun i => by
        simp [U, δ]
      have h_dot : dotProduct (Z ω - m) (A.mulVec (Z ω - m)) =
          (∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * U j ω)) +
          ((∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * δ j)) +
           (∑ i : Fin d, ∑ j : Fin d, A i j * (δ i * U j ω))) +
          dotProduct δ (A.mulVec δ) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, h_zm]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      have h_cross_symm :
          (∑ i : Fin d, ∑ j : Fin d, A i j * (δ i * U j ω)) =
            ∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * δ j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hA_symm i j]
        ring
      have h_cross2 :
          (∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * δ j)) +
          (∑ i : Fin d, ∑ j : Fin d, A i j * (δ i * U j ω)) =
            ∑ i : Fin d, ∑ j : Fin d, (2 * A i j * δ j) * U i ω := by
        rw [h_cross_symm, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      unfold quadPotential
      change Matrix.trace R + dotProduct (Z ω - m) (A.mulVec (Z ω - m)) = _
      rw [h_dot, h_cross2]
      ring
    have h_int1 : MeasureTheory.Integrable
        (fun _ : Ω => Matrix.trace R + dotProduct δ (A.mulVec δ)) μ :=
      MeasureTheory.integrable_const _
    have h_int2 : MeasureTheory.Integrable
        (fun ω : Ω => ∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * U j ω)) μ :=
      MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
        MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
          (hUU_int i j).const_mul (A i j)
    have h_int3 : MeasureTheory.Integrable
        (fun ω : Ω => ∑ i : Fin d, ∑ j : Fin d, (2 * A i j * δ j) * U i ω) μ :=
      MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
        MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
          (hU_int i).const_mul (2 * A i j * δ j)
    have h_int_quad : MeasureTheory.Integrable (fun ω => quadPotential m R (Z ω)) μ := by
      have h_eq_fn : (fun ω => quadPotential m R (Z ω)) =
          fun ω => ((Matrix.trace R + dotProduct δ (A.mulVec δ)) +
            (∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * U j ω))) +
            (∑ i : Fin d, ∑ j : Fin d, (2 * A i j * δ j) * U i ω) :=
        funext h_quad_expand
      rw [h_eq_fn]
      exact (h_int1.add h_int2).add h_int3
    have h_val2 : (∫ ω, (∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * U j ω)) ∂μ) =
        Matrix.trace (A * S) := by
      rw [MeasureTheory.integral_finset_sum Finset.univ
        (fun i _ => MeasureTheory.integrable_finset_sum Finset.univ
          fun j _ => (hUU_int i j).const_mul (A i j))]
      calc ∑ i : Fin d, ∫ ω, (∑ j : Fin d, A i j * (U i ω * U j ω)) ∂μ
          = ∑ i : Fin d, ∑ j : Fin d, A i j * (∫ ω, U i ω * U j ω ∂μ) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [MeasureTheory.integral_finset_sum Finset.univ
                (fun j _ => (hUU_int i j).const_mul (A i j))]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [MeasureTheory.integral_const_mul]
        _ = ∑ i : Fin d, ∑ j : Fin d, A i j * S j i := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [hS_symm i j]; rfl
        _ = Matrix.trace (A * S) := by
              simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    have h_val3 : (∫ ω, (∑ i : Fin d, ∑ j : Fin d, (2 * A i j * δ j) * U i ω) ∂μ) = 0 := by
      rw [MeasureTheory.integral_finset_sum Finset.univ
        (fun i _ => MeasureTheory.integrable_finset_sum Finset.univ
          fun j _ => (hU_int i).const_mul (2 * A i j * δ j))]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [MeasureTheory.integral_finset_sum Finset.univ
        (fun j _ => (hU_int i).const_mul (2 * A i j * δ j))]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [MeasureTheory.integral_const_mul, hU_zero i, mul_zero]
    have h_int_eq : (∫ ω, quadPotential m R (Z ω) ∂μ) =
        Matrix.trace R + Matrix.trace (A * S) + dotProduct δ (A.mulVec δ) := by
      have h_int12 : MeasureTheory.Integrable
          (fun ω : Ω => (Matrix.trace R + dotProduct δ (A.mulVec δ)) +
            (∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * U j ω))) μ :=
        h_int1.add h_int2
      have h_eq_fn : (fun ω => quadPotential m R (Z ω)) =
          fun ω => ((Matrix.trace R + dotProduct δ (A.mulVec δ)) +
            (∑ i : Fin d, ∑ j : Fin d, A i j * (U i ω * U j ω))) +
            (∑ i : Fin d, ∑ j : Fin d, (2 * A i j * δ j) * U i ω) :=
        funext h_quad_expand
      rw [h_eq_fn, MeasureTheory.integral_add h_int12 h_int3,
        MeasureTheory.integral_add h_int1 h_int2,
        MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul,
        h_val2, h_val3]
      ring
    have h_lb_env : 2 * psdTraceSqrt S ≤ Matrix.trace R + Matrix.trace (A * S) := by
      have h1 := (h_env.2.1 S hS_psd).1.1 ⟨R, hR, rfl⟩
      rwa [hgap0, hobj0 R] at h1
    have h_δ_nn : 0 ≤ dotProduct δ (A.mulVec δ) := by
      simpa using hA_psd.dotProduct_mulVec_nonneg δ
    refine ⟨h_int_quad, h_int_eq, ?_⟩
    linarith

  obtain ⟨hGLB0, _⟩ := h_env.2.1 S hS_psd
  rw [hgap0] at hGLB0
  set W_set : Set ℝ := {v : ℝ | ∃ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ),
      R.PosDef ∧ v = ∫ ω, quadPotential m R (Z ω) ∂μ}
  have hGLB : IsGLB W_set (2 * psdTraceSqrt S) := by
    refine ⟨?_, ?_⟩
    · rintro v ⟨m, R, hR, rfl⟩
      exact (h_eval m R hR).2.2
    · intro b hb
      refine hGLB0.2 ?_
      rintro v ⟨R, hR, rfl⟩
      rw [hobj0 R]
      have h_at_mu := (h_eval muZ R hR).2.1
      simp only [sub_self, zero_dotProduct, add_zero] at h_at_mu
      rw [← h_at_mu]
      exact hb ⟨muZ, R, hR, rfl⟩
  have hne : W_set.Nonempty := ⟨_, 0, 1, Matrix.PosDef.one, rfl⟩
  refine ⟨h_eval, hGLB, hGLB.csInf_eq hne, ?_⟩
  intro hS hS_pd
  obtain ⟨hT_pd, hT_eq⟩ := h_env.2.2.1 S hS hS_pd
  have hgap0' : gapPotential 0 S hS = psdTraceSqrt S := by
    simp only [gapPotential, Matrix.mulVec_zero, dotProduct_zero, Real.sqrt_zero, sub_zero]
    exact (psdTraceSqrt_eq_trace_sqrt hS).symm
  rw [hgap0', hobj0 hS.sqrt] at hT_eq
  refine ⟨hT_pd, ?_⟩
  have h_at_mu := (h_eval muZ hS.sqrt hT_pd).2.1
  simp only [sub_self, zero_dotProduct, add_zero] at h_at_mu
  linarith

/-- **Equations (3) & (5) for PSD Matrix Families**:
For any PSD matrix `S ⪰ 0`, any integrable a.e.-PSD matrix family `SY : Ω → Matrix (Fin d) (Fin d) ℝ`
satisfying `S ⪰ E[SY]`, and any unit-norm direction `x ∈ ℝ^d` (`‖x‖₂ ≤ 1`):
1. `psdTraceSqrt ∘ SY` and `ω ↦ √(xᵀ SY(ω) x)` are integrable under `μ`,
2. **Eq. (3)**: `∫ ω, psdTraceSqrt (SY ω) ∂μ ≤ psdTraceSqrt S`, and
3. **Eq. (5)**: `√(xᵀ S x) - ∫ ω, √(xᵀ SY(ω) x) ∂μ ≤ psdTraceSqrt S - ∫ ω, psdTraceSqrt (SY ω) ∂μ`. -/
theorem lem_directional_sd_decrease_family {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (SY : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hSY_psd : ∀ᵐ ω ∂μ, (SY ω).PosSemidef)
    (hSY_int : ∀ i j : Fin d, MeasureTheory.Integrable (fun ω => SY ω i j) μ)
    (hDom : (S - Matrix.of (fun i j => ∫ ω, SY ω i j ∂μ)).PosSemidef)
    (x : Fin d → ℝ) (hx : vecL2Norm x ≤ 1) :
    MeasureTheory.Integrable (fun ω => psdTraceSqrt (SY ω)) μ ∧
    MeasureTheory.Integrable (fun ω => Real.sqrt (dotProduct x ((SY ω).mulVec x))) μ ∧
    (∫ ω, psdTraceSqrt (SY ω) ∂μ) ≤ psdTraceSqrt S ∧
    Real.sqrt (dotProduct x (S.mulVec x)) -
      (∫ ω, Real.sqrt (dotProduct x ((SY ω).mulVec x)) ∂μ) ≤
      psdTraceSqrt S - (∫ ω, psdTraceSqrt (SY ω) ∂μ) := by
  have h_raw_aem : AEMeasurable (fun ω : Ω => fun i j : Fin d => SY ω i j) μ :=
    aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j => (hSY_int i j).aemeasurable
  have h_tr_aem : AEMeasurable (fun ω => psdTraceSqrt (SY ω)) μ := by
    have : (fun ω => psdTraceSqrt (SY ω)) =
        (fun A : Fin d → Fin d → ℝ => psdTraceSqrt (Matrix.of A)) ∘
          (fun ω i j => SY ω i j) := rfl
    rw [this]
    exact (measurable_psdTraceSqrt d).comp_aemeasurable h_raw_aem
  have h0_norm : vecL2Norm (0 : Fin d → ℝ) ≤ 1 := by simp [vecL2Norm]
  have h_env0 := lem_envelope (0 : Fin d → ℝ) h0_norm
  have h_tr_int : MeasureTheory.Integrable (fun ω => psdTraceSqrt (SY ω)) μ := by
    let ub : Ω → ℝ := fun ω => ((d : ℝ) + ∑ i : Fin d, SY ω i i) / 2
    have hub_int : MeasureTheory.Integrable ub μ :=
      ((MeasureTheory.integrable_const (d : ℝ)).add
        (MeasureTheory.integrable_finset_sum Finset.univ fun i _ => hSY_int i i)).div_const 2
    refine MeasureTheory.Integrable.mono' hub_int h_tr_aem.aestronglyMeasurable ?_
    filter_upwards [hSY_psd] with ω hω
    have h_nn : 0 ≤ psdTraceSqrt (SY ω) := by
      rw [psdTraceSqrt_eq_trace_sqrt hω]
      exact (sqrt_posSemidef hω).trace_nonneg
    rw [Real.norm_of_nonneg h_nn]
    have h1 := (h_env0.2.1 (SY ω) hω).1.1 ⟨1, Matrix.PosDef.one, rfl⟩
    have hgap0 : gapPotential 0 (SY ω) hω = psdTraceSqrt (SY ω) := by
      simp [gapPotential, psdTraceSqrt_eq_trace_sqrt hω]
    have hobj1 : envelopeObjective 0 1 (SY ω) = (d : ℝ) + ∑ i : Fin d, SY ω i i := by
      simp [envelopeObjective, envelopeSlope, vecL2Norm, Matrix.trace, Matrix.diag]
    rw [hgap0, hobj1] at h1
    dsimp [ub]
    linarith

  have h_quad_int : MeasureTheory.Integrable (fun ω => dotProduct x ((SY ω).mulVec x)) μ := by
    have h_eq : (fun ω => dotProduct x ((SY ω).mulVec x)) =
        fun ω => ∑ i : Fin d, ∑ j : Fin d, (x i * x j) * SY ω i j := by
      ext ω
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h_eq]
    exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
      MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
        (hSY_int i j).const_mul (x i * x j)

  have h_dir_int :
      MeasureTheory.Integrable (fun ω => Real.sqrt (dotProduct x ((SY ω).mulVec x))) μ := by
    have h_aem : AEMeasurable (fun ω => Real.sqrt (dotProduct x ((SY ω).mulVec x))) μ :=
      Real.continuous_sqrt.measurable.comp_aemeasurable h_quad_int.aemeasurable
    let ub : Ω → ℝ := fun ω => (1 + dotProduct x ((SY ω).mulVec x)) / 2
    have hub_int : MeasureTheory.Integrable ub μ :=
      ((MeasureTheory.integrable_const (1 : ℝ)).add h_quad_int).div_const 2
    refine MeasureTheory.Integrable.mono' hub_int h_aem.aestronglyMeasurable ?_
    filter_upwards [hSY_psd] with ω hω
    set u := dotProduct x ((SY ω).mulVec x)
    have hu_nn : 0 ≤ u := by simpa [u] using hω.dotProduct_mulVec_nonneg x
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg u)]
    have hsq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu_nn
    dsimp [ub]
    nlinarith [sq_nonneg (Real.sqrt u - 1), hsq]

  have h_main_ineq : ∀ (y : Fin d → ℝ), vecL2Norm y ≤ 1 →
      MeasureTheory.Integrable (fun ω => Real.sqrt (dotProduct y ((SY ω).mulVec y))) μ →
      Real.sqrt (dotProduct y (S.mulVec y)) -
        (∫ ω, Real.sqrt (dotProduct y ((SY ω).mulVec y)) ∂μ) ≤
        psdTraceSqrt S - (∫ ω, psdTraceSqrt (SY ω) ∂μ) := by
    intro y hy h_y_int
    have h_env_y := lem_envelope y hy
    obtain ⟨hGLB_S, _⟩ := h_env_y.2.1 S hS
    set ESY : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => ∫ ω, SY ω i j ∂μ
    let g_fn : Ω → ℝ := fun ω =>
      psdTraceSqrt (SY ω) - Real.sqrt (dotProduct y ((SY ω).mulVec y))
    have hg_int : MeasureTheory.Integrable g_fn μ := h_tr_int.sub h_y_int
    have h_lb : 2 * (∫ ω, g_fn ω ∂μ) ∈
        lowerBounds {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ,
          R.PosDef ∧ v = envelopeObjective y R S} := by
      rintro v ⟨R, hR, rfl⟩
      let H := envelopeSlope y R
      have hH_psd : H.PosSemidef := h_env_y.1 R hR
      have h_obj_int : MeasureTheory.Integrable (fun ω => envelopeObjective y R (SY ω)) μ := by
        have h_eq : (fun ω => envelopeObjective y R (SY ω)) =
            fun ω => (Matrix.trace R - vecL2Norm (R.mulVec y)) +
              ∑ i : Fin d, ∑ j : Fin d, H i j * SY ω j i := by
          ext ω
          simp [envelopeObjective, H, Matrix.trace, Matrix.diag, Matrix.mul_apply]
        rw [h_eq]
        exact (MeasureTheory.integrable_const _).add
          (MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
            MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
              (hSY_int j i).const_mul (H i j))
      have h_ae_le : ∀ᵐ ω ∂μ, 2 * g_fn ω ≤ envelopeObjective y R (SY ω) := by
        filter_upwards [hSY_psd] with ω hω
        have h_pt := (h_env_y.2.1 (SY ω) hω).1.1 ⟨R, hR, rfl⟩
        have h_g_eq : gapPotential y (SY ω) hω = g_fn ω := by
          simp [g_fn, gapPotential, psdTraceSqrt_eq_trace_sqrt hω]
        rwa [h_g_eq] at h_pt
      have h_int_le : 2 * (∫ ω, g_fn ω ∂μ) ≤ ∫ ω, envelopeObjective y R (SY ω) ∂μ := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_mono_ae (hg_int.const_mul 2) h_obj_int h_ae_le
      have h_int_obj : (∫ ω, envelopeObjective y R (SY ω) ∂μ) = envelopeObjective y R ESY := by
        have h_eq : (fun ω => envelopeObjective y R (SY ω)) =
            fun ω => (Matrix.trace R - vecL2Norm (R.mulVec y)) +
              ∑ i : Fin d, ∑ j : Fin d, H i j * SY ω j i := by
          ext ω
          simp [envelopeObjective, H, Matrix.trace, Matrix.diag, Matrix.mul_apply]
        rw [h_eq, MeasureTheory.integral_add (MeasureTheory.integrable_const _)
            (MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
              MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
                (hSY_int j i).const_mul (H i j)),
          MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul,
          MeasureTheory.integral_finset_sum Finset.univ (fun i _ =>
            MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
              (hSY_int j i).const_mul (H i j))]
        have h_sum_eq :
            (∑ i : Fin d, ∫ ω, (∑ j : Fin d, H i j * SY ω j i) ∂μ) =
              Matrix.trace (H * ESY) := by
          calc ∑ i : Fin d, ∫ ω, (∑ j : Fin d, H i j * SY ω j i) ∂μ
              = ∑ i : Fin d, ∑ j : Fin d, H i j * (∫ ω, SY ω j i ∂μ) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [MeasureTheory.integral_finset_sum Finset.univ
                    (fun j _ => (hSY_int j i).const_mul (H i j))]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [MeasureTheory.integral_const_mul]
            _ = Matrix.trace (H * ESY) := by
                  simp [ESY, Matrix.trace, Matrix.diag, Matrix.mul_apply]
        rw [h_sum_eq]
        rfl
      have h_dom_tr : 0 ≤ Matrix.trace (H * (S - ESY)) :=
        trace_mul_nonneg_of_posSemidef hH_psd hDom
      have h_obj_diff : envelopeObjective y R S - envelopeObjective y R ESY =
          Matrix.trace (H * (S - ESY)) := by
        simp only [envelopeObjective, H, mul_sub, Matrix.trace_sub]
        ring
      linarith
    have h_glb_le : 2 * (∫ ω, g_fn ω ∂μ) ≤ 2 * gapPotential y S hS := hGLB_S.2 h_lb
    rw [MeasureTheory.integral_sub h_tr_int h_y_int] at h_glb_le
    unfold gapPotential at h_glb_le
    rw [← psdTraceSqrt_eq_trace_sqrt hS] at h_glb_le
    linarith

  have h_eq5 := h_main_ineq x hx h_dir_int
  have h_zero_int :
      MeasureTheory.Integrable (fun ω => Real.sqrt (dotProduct 0 ((SY ω).mulVec 0))) μ := by
    simp
  have h_eq3_raw := h_main_ineq 0 h0_norm h_zero_int
  simp only [Matrix.mulVec_zero, dotProduct_zero, Real.sqrt_zero,
    MeasureTheory.integral_zero, sub_zero] at h_eq3_raw
  exact ⟨h_tr_int, h_dir_int, by linarith, h_eq5⟩

/-- Regular conditional covariance matrix `Σ_Y(ω) = Cov(Z | Y = Y(ω))` defined via
`ProbabilityTheory.condDistrib Z Y μ` (Section 1.2.2, Eqs. (2)–(5)). -/
noncomputable def condCovMat {d : ℕ} {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (Z : Ω → (Fin d → ℝ)) (Y : Ω → β) (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure μ] (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  rvCovMat id (ProbabilityTheory.condDistrib Z Y μ (Y ω))

/-- Conditional directional standard deviation `sd_x(Z | Y)(ω) = √(xᵀ Σ_Y(ω) x)`
(Section 1.2.2, Eq. (5)). -/
noncomputable def condDirStdDev {d : ℕ} {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (x : Fin d → ℝ) (Z : Ω → (Fin d → ℝ)) (Y : Ω → β) (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure μ] (ω : Ω) : ℝ :=
  Real.sqrt (dotProduct x ((condCovMat Z Y μ ω).mulVec x))

/-- **Lemma 1.2 (Potential Decrease Lemma, `lem:directional-sd-decrease`)**:
Let `Z : Ω → ℝ^d` be a random vector with finite second moments (`Σ = rvCovMat Z μ ⪰ 0`),
let `Y : Ω → β` be any jointly defined a.e.-measurable random variable taking values in an
arbitrary measurable space `β`, and let `x ∈ ℝ^d` satisfy `‖x‖₂ ≤ 1`. Writing
`Σ_Y = condCovMat Z Y μ` for the posterior covariance matrix `Cov(Z | Y)`:
1. Almost surely `Σ_Y ⪰ 0`, every entry of `Σ_Y` is integrable, and **Eq. (2)** holds:
   `Cov(Z) ⪰ E[Cov(Z | Y)]`, i.e. `(Σ - E[Σ_Y]).PosSemidef`.
2. Both `Ψ(Σ_Y) = Tr(√Σ_Y)` and `√(xᵀ Σ_Y x)` are integrable under `μ`.
3. **Eq. (3)**: `E[Ψ(Σ_Y)] ≤ Ψ(Σ)`.
4. **Eq. (5)**: `Tr(√Σ) - E[Tr(√Σ_Y)] ≥ √(xᵀ Σ x) - E[√(xᵀ Σ_Y x)]`. -/
theorem lem_directional_sd_decrease {d : ℕ} {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Ω → (Fin d → ℝ))
    (hZ : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 μ)
    (Y : Ω → β) (hY : AEMeasurable Y μ)
    (x : Fin d → ℝ) (hx : vecL2Norm x ≤ 1) :
    let S := rvCovMat Z μ
    let SY := condCovMat Z Y μ
    S.PosSemidef ∧
    (∀ᵐ ω ∂μ, (SY ω).PosSemidef) ∧
    (∀ i j : Fin d, MeasureTheory.Integrable (fun ω => SY ω i j) μ) ∧
    (S - Matrix.of (fun i j => ∫ ω, SY ω i j ∂μ)).PosSemidef ∧
    MeasureTheory.Integrable (fun ω => psdTraceSqrt (SY ω)) μ ∧
    MeasureTheory.Integrable (condDirStdDev x Z Y μ) μ ∧
    (∫ ω, psdTraceSqrt (SY ω) ∂μ) ≤ psdTraceSqrt S ∧
    Real.sqrt (dotProduct x (S.mulVec x)) - (∫ ω, condDirStdDev x Z Y μ ω ∂μ) ≤
      psdTraceSqrt S - (∫ ω, psdTraceSqrt (SY ω) ∂μ) := by
  set S := rvCovMat Z μ
  set SY := condCovMat Z Y μ
  obtain ⟨hS_psd, _, h_proj_μ⟩ := cov_basic_props μ Z hZ
  have hZ_aem : AEMeasurable Z μ :=
    aemeasurable_pi_iff.mpr fun i => (hZ i).aemeasurable
  let κ := ProbabilityTheory.condDistrib Z Y μ

  -- Step 1: Entrywise a.e.-measurability of SY via StronglyMeasurable.integral_condDistrib
  let m_κ : β → Fin d → ℝ := fun b i => ∫ z, z i ∂(κ b)
  have hm_κ_sm : ∀ i : Fin d, MeasureTheory.StronglyMeasurable (fun b => m_κ b i) := by
    intro i
    have hf : MeasureTheory.StronglyMeasurable (fun p : β × (Fin d → ℝ) => p.2 i) :=
      ((measurable_pi_apply i).comp measurable_snd).stronglyMeasurable
    exact hf.integral_condDistrib
  let c_κ : β → Fin d → Fin d → ℝ := fun b i j =>
    ∫ z, (z i - m_κ b i) * (z j - m_κ b j) ∂(κ b)
  have hc_κ_meas : ∀ i j : Fin d, Measurable (fun b => c_κ b i j) := by
    intro i j
    have hg : MeasureTheory.StronglyMeasurable
        (fun p : β × (Fin d → ℝ) => (p.2 i - m_κ p.1 i) * (p.2 j - m_κ p.1 j)) := by
      have h1 : MeasureTheory.StronglyMeasurable (fun p : β × (Fin d → ℝ) => p.2 i) :=
        ((measurable_pi_apply i).comp measurable_snd).stronglyMeasurable
      have h2 : MeasureTheory.StronglyMeasurable (fun p : β × (Fin d → ℝ) => m_κ p.1 i) :=
        (hm_κ_sm i).comp_measurable measurable_fst
      have h3 : MeasureTheory.StronglyMeasurable (fun p : β × (Fin d → ℝ) => p.2 j) :=
        ((measurable_pi_apply j).comp measurable_snd).stronglyMeasurable
      have h4 : MeasureTheory.StronglyMeasurable (fun p : β × (Fin d → ℝ) => m_κ p.1 j) :=
        (hm_κ_sm j).comp_measurable measurable_fst
      exact (h1.sub h2).mul (h3.sub h4)
    exact hg.integral_condDistrib.measurable
  have hSY_aem : ∀ i j : Fin d, AEMeasurable (fun ω => SY ω i j) μ := by
    intro i j
    have h_eq : (fun ω => SY ω i j) = (fun b => c_κ b i j) ∘ Y := rfl
    rw [h_eq]
    exact (hc_κ_meas i j).comp_aemeasurable hY

  -- Step 2: Almost surely under μ, every coordinate is in L²(κ (Y ω))
  have h_ae_lp : ∀ᵐ ω ∂μ, ∀ i : Fin d, MeasureTheory.MemLp (fun z : Fin d → ℝ => z i) 2 (κ (Y ω)) := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    let f_sq : β × (Fin d → ℝ) → ℝ := fun p => (p.2 i) ^ 2
    have hf_sq_sm : MeasureTheory.StronglyMeasurable f_sq :=
      (((measurable_pi_apply i).comp measurable_snd).pow_const 2).stronglyMeasurable
    have hf_sq_map : MeasureTheory.Integrable f_sq (μ.map fun ω => (Y ω, Z ω)) := by
      rw [MeasureTheory.integrable_map_measure hf_sq_sm.aestronglyMeasurable (hY.prodMk hZ_aem)]
      exact (hZ i).integrable_sq
    filter_upwards [hf_sq_map.condDistrib_ae hY hZ_aem] with ω hω_sq
    exact (MeasureTheory.memLp_two_iff_integrable_sq
      (continuous_apply i).stronglyMeasurable.aestronglyMeasurable).mpr hω_sq

  have hSY_psd : ∀ᵐ ω ∂μ, (SY ω).PosSemidef := by
    filter_upwards [h_ae_lp] with ω hω
    exact (cov_basic_props (κ (Y ω)) id hω).1

  -- Step 3: Tower law for quadratic forms via compProd_map_condDistrib
  have h_tower_quad : ∀ v : Fin d → ℝ,
      let mv := ∫ ω, dotProduct v (Z ω) ∂μ
      (∀ᵐ ω ∂μ,
        0 ≤ dotProduct v ((SY ω).mulVec v) ∧
        dotProduct v ((SY ω).mulVec v) ≤ ∫ z, (dotProduct v z - mv) ^ 2 ∂(κ (Y ω))) ∧
      MeasureTheory.Integrable (fun ω => ∫ z, (dotProduct v z - mv) ^ 2 ∂(κ (Y ω))) μ ∧
      (∫ ω, (∫ z, (dotProduct v z - mv) ^ 2 ∂(κ (Y ω))) ∂μ) = dotProduct v (S.mulVec v) := by
    intro v mv
    let q : (Fin d → ℝ) → ℝ := fun z => (dotProduct v z - mv) ^ 2
    have hq_cont : Continuous q := by
      have h_dp : Continuous (fun z : Fin d → ℝ => dotProduct v z) :=
        continuous_finset_sum Finset.univ fun i _ => continuous_const.mul (continuous_apply i)
      exact (h_dp.sub continuous_const).pow 2
    let fq : β × (Fin d → ℝ) → ℝ := fun p => q p.2
    have hfq_sm : MeasureTheory.StronglyMeasurable fq :=
      (hq_cont.measurable.comp measurable_snd).stronglyMeasurable
    have hU_lp : MeasureTheory.MemLp (fun ω => dotProduct v (Z ω)) 2 μ := (h_proj_μ v).1
    have hqZ_int : MeasureTheory.Integrable (fun ω => q (Z ω)) μ :=
      (hU_lp.sub (MeasureTheory.memLp_const mv)).integrable_sq
    have hfq_map : MeasureTheory.Integrable fq (μ.map fun ω => (Y ω, Z ω)) := by
      rwa [MeasureTheory.integrable_map_measure hfq_sm.aestronglyMeasurable (hY.prodMk hZ_aem)]
    have h_int_cond : MeasureTheory.Integrable (fun ω => ∫ z, q z ∂(κ (Y ω))) μ :=
      hfq_map.integral_condDistrib hY hZ_aem
    have h_comp_eq : (μ.map Y).compProd κ = μ.map (fun ω => (Y ω, Z ω)) :=
      ProbabilityTheory.compProd_map_condDistrib hZ_aem
    have hfq_cp : MeasureTheory.Integrable fq ((μ.map Y).compProd κ) := by
      rwa [h_comp_eq]
    have h_tower_eq : (∫ ω, (∫ z, q z ∂(κ (Y ω))) ∂μ) = dotProduct v (S.mulVec v) := by
      have h1 : (∫ p, fq p ∂((μ.map Y).compProd κ)) = ∫ b, (∫ z, q z ∂(κ b)) ∂(μ.map Y) :=
        MeasureTheory.Measure.integral_compProd hfq_cp
      have h2 : (∫ b, (∫ z, q z ∂(κ b)) ∂(μ.map Y)) = ∫ ω, (∫ z, q z ∂(κ (Y ω))) ∂μ := by
        have h_sm_b : MeasureTheory.StronglyMeasurable (fun b => ∫ z, q z ∂(κ b)) :=
          hfq_sm.integral_condDistrib
        exact MeasureTheory.integral_map hY h_sm_b.aestronglyMeasurable
      have h3 : (∫ p, fq p ∂((μ.map Y).compProd κ)) = ∫ ω, q (Z ω) ∂μ := by
        rw [h_comp_eq]
        exact MeasureTheory.integral_map (hY.prodMk hZ_aem) hfq_sm.aestronglyMeasurable
      have h4 : (∫ ω, q (Z ω) ∂μ) = dotProduct v (S.mulVec v) := by
        dsimp [q, mv]
        rw [← ProbabilityTheory.variance_eq_integral hU_lp.aemeasurable]
        exact ((h_proj_μ v).2.1).symm
      linarith
    have h_ae_ineq : ∀ᵐ ω ∂μ,
        0 ≤ dotProduct v ((SY ω).mulVec v) ∧
        dotProduct v ((SY ω).mulVec v) ≤ ∫ z, q z ∂(κ (Y ω)) := by
      filter_upwards [h_ae_lp] with ω hω
      obtain ⟨h_psd_ω, _, h_proj_ω⟩ := cov_basic_props (κ (Y ω)) id hω
      have h_nn : 0 ≤ dotProduct v ((SY ω).mulVec v) := by
        simpa using h_psd_ω.dotProduct_mulVec_nonneg v
      obtain ⟨hV_lp, hV_var, _⟩ := h_proj_ω v
      have h_sub_lp : MeasureTheory.MemLp (fun z : Fin d → ℝ => dotProduct v z - mv) 2 (κ (Y ω)) :=
        hV_lp.sub (MeasureTheory.memLp_const mv)
      have h_le : dotProduct v ((SY ω).mulVec v) ≤ ∫ z, q z ∂(κ (Y ω)) := by
        change dotProduct v ((rvCovMat id (κ (Y ω))).mulVec v) ≤ ∫ z, q z ∂(κ (Y ω))
        rw [hV_var, ← ProbabilityTheory.variance_sub_const hV_lp.aestronglyMeasurable mv]
        exact ProbabilityTheory.variance_le_expectation_sq h_sub_lp.aestronglyMeasurable
      exact ⟨h_nn, h_le⟩
    exact ⟨h_ae_ineq, h_int_cond, h_tower_eq⟩

  -- Step 4: Integrability of all entries of SY
  have hSY_diag_int : ∀ i : Fin d, MeasureTheory.Integrable (fun ω => SY ω i i) μ := by
    intro i
    let e_i : Fin d → ℝ := Pi.single i 1
    obtain ⟨h_ae_i, h_int_i, _⟩ := h_tower_quad e_i
    refine MeasureTheory.Integrable.mono' h_int_i (hSY_aem i i).aestronglyMeasurable ?_
    filter_upwards [h_ae_i] with ω ⟨h_nn, h_le⟩
    have h_diag : dotProduct e_i ((SY ω).mulVec e_i) = SY ω i i := by
      simp [e_i, Matrix.mulVec_single]
    rw [h_diag] at h_nn h_le
    rw [Real.norm_of_nonneg h_nn]
    exact h_le

  have hSY_int : ∀ i j : Fin d, MeasureTheory.Integrable (fun ω => SY ω i j) μ := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact hSY_diag_int i
    · let ub : Ω → ℝ := fun ω => (SY ω i i + SY ω j j) / 2
      have hub_int : MeasureTheory.Integrable ub μ :=
        ((hSY_diag_int i).add (hSY_diag_int j)).div_const 2
      refine MeasureTheory.Integrable.mono' hub_int (hSY_aem i j).aestronglyMeasurable ?_
      filter_upwards [hSY_psd] with ω hω
      have hsym : SY ω j i = SY ω i j := by
        have := congr_fun (congr_fun hω.isHermitian.eq i) j
        simpa [Matrix.conjTranspose_apply] using this
      let v_pos : Fin d → ℝ := Pi.single i 1 + Pi.single j 1
      let v_neg : Fin d → ℝ := Pi.single i 1 - Pi.single j 1
      have hp : 0 ≤ dotProduct v_pos ((SY ω).mulVec v_pos) := by
        simpa using hω.dotProduct_mulVec_nonneg v_pos
      have hn : 0 ≤ dotProduct v_neg ((SY ω).mulVec v_neg) := by
        simpa using hω.dotProduct_mulVec_nonneg v_neg
      have hp_eq : dotProduct v_pos ((SY ω).mulVec v_pos) =
          SY ω i i + SY ω j j + 2 * SY ω i j := by
        dsimp only [v_pos]
        rw [add_dotProduct, Matrix.mulVec_add, Matrix.mulVec_single, Matrix.mulVec_single]
        simp [hij, Ne.symm hij, hsym]
        ring
      have hn_eq : dotProduct v_neg ((SY ω).mulVec v_neg) =
          SY ω i i + SY ω j j - 2 * SY ω i j := by
        dsimp only [v_neg]
        rw [sub_dotProduct, Matrix.mulVec_sub, Matrix.mulVec_single, Matrix.mulVec_single]
        simp [hij, Ne.symm hij, hsym]
        ring
      rw [Real.norm_eq_abs]
      dsimp [ub]
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩

  -- Step 5: Loewner dominance S ⪰ E[SY] (Eq. (2))
  set ESY : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => ∫ ω, SY ω i j ∂μ
  have hESY_herm : ESY.IsHermitian := by
    ext i j
    simp only [ESY, Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
    have h_sym_pt : ∀ ω : Ω, SY ω i j = SY ω j i := fun ω => by
      simp only [SY, condCovMat, rvCovMat, Matrix.of_apply]
      congr 1; ext z; ring
    simp_rw [h_sym_pt]
  have hDom : (S - ESY).PosSemidef := by
    have hDiff_herm : (S - ESY).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hS_psd.isHermitian.eq, hESY_herm.eq]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hDiff_herm fun v => ?_
    simp only [star_trivial]
    obtain ⟨h_ae_v, h_int_v, h_eq_v⟩ := h_tower_quad v
    have h_quad_SY_int : MeasureTheory.Integrable (fun ω => dotProduct v ((SY ω).mulVec v)) μ := by
      have h_eq : (fun ω => dotProduct v ((SY ω).mulVec v)) =
          fun ω => ∑ i : Fin d, ∑ j : Fin d, (v i * v j) * SY ω i j := by
        ext ω
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [h_eq]
      exact MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
        MeasureTheory.integrable_finset_sum Finset.univ fun j _ =>
          (hSY_int i j).const_mul (v i * v j)
    have h_quad_ESY : dotProduct v (ESY.mulVec v) =
        ∫ ω, dotProduct v ((SY ω).mulVec v) ∂μ := by
      have h_eq : (fun ω => dotProduct v ((SY ω).mulVec v)) =
          fun ω => ∑ i : Fin d, ∑ j : Fin d, (v i * v j) * SY ω i j := by
        ext ω
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [h_eq, MeasureTheory.integral_finset_sum Finset.univ
        (fun i _ => MeasureTheory.integrable_finset_sum Finset.univ
          fun j _ => (hSY_int i j).const_mul (v i * v j))]
      calc dotProduct v (ESY.mulVec v)
          = ∑ i : Fin d, ∑ j : Fin d, (v i * v j) * (∫ ω, SY ω i j ∂μ) := by
              simp only [ESY, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              ring
        _ = ∑ i : Fin d, ∫ ω, (∑ j : Fin d, (v i * v j) * SY ω i j) ∂μ := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [MeasureTheory.integral_finset_sum Finset.univ
                (fun j _ => (hSY_int i j).const_mul (v i * v j))]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [MeasureTheory.integral_const_mul]
    have h_mono := MeasureTheory.integral_mono_ae h_quad_SY_int h_int_v
      (h_ae_v.mono fun _ h => h.2)
    have h_sub_expand : dotProduct v ((S - ESY).mulVec v) =
        dotProduct v (S.mulVec v) - dotProduct v (ESY.mulVec v) := by
      simp [Matrix.sub_mulVec, dotProduct_sub]
    rw [h_sub_expand, h_quad_ESY]
    linarith

  -- Step 6: Apply lem_directional_sd_decrease_family
  obtain ⟨h_tr_int, h_dir_int, h_eq3, h_eq5⟩ :=
    lem_directional_sd_decrease_family μ S hS_psd SY hSY_psd hSY_int hDom x hx
  exact ⟨hS_psd, hSY_psd, hSY_int, hDom, h_tr_int, h_dir_int, h_eq3, h_eq5⟩

/-- **Binary Conditioning Form of Lemma 1.2**:
For any random vector `Z : Ω → ℝ^d` with finite second moments, any null-measurable event `E`,
and any `x ∈ ℝ^d` with `‖x‖₂ ≤ 1`:
`sd(xᵀ Z) - (P(E) sd(xᵀ Z | E) + P(Eᶜ) sd(xᵀ Z | Eᶜ)) ≤ Ψ(Cov(Z)) - (P(E) Ψ(Cov(Z|E)) + P(Eᶜ) Ψ(Cov(Z|Eᶜ)))`. -/
theorem lem_directional_sd_decrease_binary {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Ω → (Fin d → ℝ))
    (hZ : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 μ)
    (E : Set Ω) (hE : MeasureTheory.NullMeasurableSet E μ)
    (x : Fin d → ℝ) (hx : vecL2Norm x ≤ 1) :
    let S := rvCovMat Z μ
    let S_pos := rvCovMat Z (ProbabilityTheory.cond μ E)
    let S_neg := rvCovMat Z (ProbabilityTheory.cond μ Eᶜ)
    let p_pos := μ.real E
    let p_neg := μ.real Eᶜ
    (S - (p_pos • S_pos + p_neg • S_neg)).PosSemidef ∧
    p_pos * psdTraceSqrt S_pos + p_neg * psdTraceSqrt S_neg ≤ psdTraceSqrt S ∧
    rvStdDev (fun ω => dotProduct x (Z ω)) μ -
      (p_pos * condStdDev (fun ω => dotProduct x (Z ω)) μ E +
       p_neg * condStdDev (fun ω => dotProduct x (Z ω)) μ Eᶜ) ≤
      psdTraceSqrt S - (p_pos * psdTraceSqrt S_pos + p_neg * psdTraceSqrt S_neg) := by
  set S := rvCovMat Z μ
  set ν_pos := ProbabilityTheory.cond μ E
  set ν_neg := ProbabilityTheory.cond μ Eᶜ
  set S_pos := rvCovMat Z ν_pos
  set S_neg := rvCovMat Z ν_neg
  set p_pos := μ.real E
  set p_neg := μ.real Eᶜ
  obtain ⟨hS_psd, _, h_proj_μ⟩ := cov_basic_props μ Z hZ
  have hp_pos_nn : 0 ≤ p_pos := MeasureTheory.measureReal_nonneg
  have hp_neg_nn : 0 ≤ p_neg := MeasureTheory.measureReal_nonneg
  have hp_sum : p_pos + p_neg = 1 := by
    have hc : p_neg = 1 - p_pos := by
      dsimp [p_pos, p_neg]
      rw [MeasureTheory.measureReal_compl₀ hE, MeasureTheory.probReal_univ]
    linarith
  have h_cov_zero : rvCovMat Z (0 : MeasureTheory.Measure Ω) = 0 := by
    ext i j; simp [rvCovMat, MeasureTheory.integral_zero_measure]
  have h_cond_null : ∀ G : Set Ω, μ G = 0 →
      ProbabilityTheory.cond μ G = 0 ∧ ProbabilityTheory.cond μ Gᶜ = μ := by
    intro G hG0
    have h1 : ProbabilityTheory.cond μ G = 0 :=
      ProbabilityTheory.cond_eq_zero.mpr (Or.inr hG0)
    have hae : ∀ᵐ ω ∂μ, ω ∈ Gᶜ := by
      rw [MeasureTheory.ae_iff]
      have hset : {ω : Ω | ¬(ω ∈ Gᶜ)} = G := by ext ω; simp
      rw [hset]; exact hG0
    have hrest : μ.restrict Gᶜ = μ := MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae
    have hGc1 : μ Gᶜ = 1 := by
      calc μ Gᶜ = (μ.restrict Gᶜ) Set.univ := (MeasureTheory.Measure.restrict_apply_univ Gᶜ).symm
        _ = μ Set.univ := by rw [hrest]
        _ = 1 := MeasureTheory.measure_univ
    have h2 : ProbabilityTheory.cond μ Gᶜ = μ := by
      change (μ Gᶜ)⁻¹ • μ.restrict Gᶜ = μ
      rw [hGc1, hrest, inv_one, one_smul]
    exact ⟨h1, h2⟩

  have h_core :
      S_pos.PosSemidef ∧ S_neg.PosSemidef ∧
      (S - (p_pos • S_pos + p_neg • S_neg)).PosSemidef ∧
      p_pos * Real.sqrt (dotProduct x (S_pos.mulVec x)) =
        p_pos * condStdDev (fun ω => dotProduct x (Z ω)) μ E ∧
      p_neg * Real.sqrt (dotProduct x (S_neg.mulVec x)) =
        p_neg * condStdDev (fun ω => dotProduct x (Z ω)) μ Eᶜ := by
    by_cases hE0 : μ E = 0
    · obtain ⟨hc0, hc1⟩ := h_cond_null E hE0
      have hp0 : p_pos = 0 := by simp [p_pos, MeasureTheory.measureReal_def, hE0]
      have hp1 : p_neg = 1 := by linarith
      have hSp0 : S_pos = 0 := by dsimp [S_pos, ν_pos]; rw [hc0, h_cov_zero]
      have hSnS : S_neg = S := by dsimp [S_neg, ν_neg, S]; rw [hc1]
      have h_dom0 : S - (p_pos • S_pos + p_neg • S_neg) = 0 := by
        rw [hp0, hp1, hSp0, hSnS]; simp
      refine ⟨by rw [hSp0]; exact Matrix.PosSemidef.zero,
              by rw [hSnS]; exact hS_psd,
              by rw [h_dom0]; exact Matrix.PosSemidef.zero,
              by rw [hp0]; simp, ?_⟩
      rw [hSnS, (h_proj_μ x).2.2]
      unfold condStdDev; rw [hc1]
    · by_cases hEc0 : μ Eᶜ = 0
      · obtain ⟨hc0, hc1⟩ := h_cond_null Eᶜ hEc0
        have hc1' : ProbabilityTheory.cond μ E = μ := by simpa [compl_compl] using hc1
        have hp0 : p_neg = 0 := by simp [p_neg, MeasureTheory.measureReal_def, hEc0]
        have hp1 : p_pos = 1 := by linarith
        have hSn0 : S_neg = 0 := by dsimp [S_neg, ν_neg]; rw [hc0, h_cov_zero]
        have hSpS : S_pos = S := by dsimp [S_pos, ν_pos, S]; rw [hc1']
        have h_dom0 : S - (p_pos • S_pos + p_neg • S_neg) = 0 := by
          rw [hp0, hp1, hSn0, hSpS]; simp
        refine ⟨by rw [hSpS]; exact hS_psd,
                by rw [hSn0]; exact Matrix.PosSemidef.zero,
                by rw [h_dom0]; exact Matrix.PosSemidef.zero,
                ?_, by rw [hp0]; simp⟩
        rw [hSpS, (h_proj_μ x).2.2]
        unfold condStdDev; rw [hc1']
      · haveI : MeasureTheory.IsProbabilityMeasure ν_pos :=
          ProbabilityTheory.cond_isProbabilityMeasure hE0
        haveI : MeasureTheory.IsProbabilityMeasure ν_neg :=
          ProbabilityTheory.cond_isProbabilityMeasure hEc0
        have hZ_pos : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 ν_pos :=
          fun i => ((hZ i).restrict E).smul_measure (ENNReal.inv_ne_top.mpr hE0)
        have hZ_neg : ∀ i : Fin d, MeasureTheory.MemLp (fun ω => Z ω i) 2 ν_neg :=
          fun i => ((hZ i).restrict Eᶜ).smul_measure (ENNReal.inv_ne_top.mpr hEc0)
        obtain ⟨hSp_psd, _, h_proj_pos⟩ := cov_basic_props ν_pos Z hZ_pos
        obtain ⟨hSn_psd, _, h_proj_neg⟩ := cov_basic_props ν_neg Z hZ_neg
        have hD_herm : (S - (p_pos • S_pos + p_neg • S_neg)).IsHermitian := by
          rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
              Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
              hS_psd.isHermitian.eq, hSp_psd.isHermitian.eq, hSn_psd.isHermitian.eq]
          simp only [star_trivial]; rfl
        have h_branch_var : ∀ (F : Set Ω), μ F ≠ 0 → ∀ v : Fin d → ℝ,
            let m := ∫ ω, dotProduct v (Z ω) ∂μ
            μ.real F * ProbabilityTheory.variance (fun ω => dotProduct v (Z ω))
              (ProbabilityTheory.cond μ F) ≤
              ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂μ := by
          intro F hF0 v m
          haveI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond μ F) :=
            ProbabilityTheory.cond_isProbabilityMeasure hF0
          have hU_μ : MeasureTheory.MemLp (fun ω => dotProduct v (Z ω)) 2 μ := (h_proj_μ v).1
          have hU_F : MeasureTheory.MemLp (fun ω => dotProduct v (Z ω)) 2
              (ProbabilityTheory.cond μ F) :=
            (hU_μ.restrict F).smul_measure (ENNReal.inv_ne_top.mpr hF0)
          have hU_sub : MeasureTheory.MemLp (fun ω => dotProduct v (Z ω) - m) 2
              (ProbabilityTheory.cond μ F) :=
            hU_F.sub (MeasureTheory.memLp_const m)
          have hpF_pos : 0 < μ.real F :=
            ENNReal.toReal_pos hF0 (MeasureTheory.measure_ne_top μ F)
          have hpF_ne : μ.real F ≠ 0 := hpF_pos.ne'
          have hv1 : ProbabilityTheory.variance (fun ω => dotProduct v (Z ω))
              (ProbabilityTheory.cond μ F) =
              ProbabilityTheory.variance (fun ω => dotProduct v (Z ω) - m)
                (ProbabilityTheory.cond μ F) :=
            (ProbabilityTheory.variance_sub_const hU_F.1 m).symm
          have hv2 : ProbabilityTheory.variance (fun ω => dotProduct v (Z ω) - m)
              (ProbabilityTheory.cond μ F) ≤
              ∫ ω, (dotProduct v (Z ω) - m) ^ 2 ∂(ProbabilityTheory.cond μ F) :=
            ProbabilityTheory.variance_le_expectation_sq hU_sub.1
          have hv3 : (∫ ω, (dotProduct v (Z ω) - m) ^ 2 ∂(ProbabilityTheory.cond μ F)) =
              (μ.real F)⁻¹ * ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂μ := by
            change (∫ ω, (dotProduct v (Z ω) - m) ^ 2 ∂((μ F)⁻¹ • μ.restrict F)) = _
            rw [MeasureTheory.integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
              ← MeasureTheory.measureReal_def]
          have h_le : ProbabilityTheory.variance (fun ω => dotProduct v (Z ω))
              (ProbabilityTheory.cond μ F) ≤
              (μ.real F)⁻¹ * ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂μ := by linarith
          have hmul := mul_le_mul_of_nonneg_left h_le hpF_pos.le
          have hcancel : μ.real F * ((μ.real F)⁻¹ * ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂μ) =
              ∫ ω in F, (dotProduct v (Z ω) - m) ^ 2 ∂μ := by field_simp
          linarith
        have h_dom : (S - (p_pos • S_pos + p_neg • S_neg)).PosSemidef := by
          refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hD_herm fun v => ?_
          simp only [star_trivial]
          let U : Ω → ℝ := fun ω => dotProduct v (Z ω)
          let m : ℝ := ∫ ω, U ω ∂μ
          have hU_lp : MeasureTheory.MemLp U 2 μ := (h_proj_μ v).1
          have h_sq_int : MeasureTheory.Integrable (fun ω => (U ω - m) ^ 2) μ :=
            (hU_lp.sub (MeasureTheory.memLp_const m)).integrable_sq
          have hb_pos := h_branch_var E hE0 v
          have hb_neg := h_branch_var Eᶜ hEc0 v
          have h_sum_int : (∫ ω in E, (U ω - m) ^ 2 ∂μ) + (∫ ω in Eᶜ, (U ω - m) ^ 2 ∂μ) =
              ∫ ω, (U ω - m) ^ 2 ∂μ :=
            MeasureTheory.integral_add_compl₀ hE h_sq_int
          have h_tot_var : (∫ ω, (U ω - m) ^ 2 ∂μ) = dotProduct v (S.mulVec v) := by
            rw [← ProbabilityTheory.variance_eq_integral hU_lp.aemeasurable]
            exact ((h_proj_μ v).2.1).symm
          have h_quad_expand :
              dotProduct v ((S - (p_pos • S_pos + p_neg • S_neg)).mulVec v) =
                dotProduct v (S.mulVec v) -
                  (p_pos * ProbabilityTheory.variance U ν_pos +
                   p_neg * ProbabilityTheory.variance U ν_neg) := by
            simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
              dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
            rw [(h_proj_pos v).2.1, (h_proj_neg v).2.1]
          rw [h_quad_expand]
          dsimp [U, m, p_pos, p_neg, ν_pos, ν_neg] at *
          linarith
        exact ⟨hSp_psd, hSn_psd, h_dom,
          by rw [(h_proj_pos x).2.2]; rfl,
          by rw [(h_proj_neg x).2.2]; rfl⟩

  obtain ⟨hSp_psd, hSn_psd, hDom, h_sd_pos, h_sd_neg⟩ := h_core
  have hComb : (p_pos • S_pos + p_neg • S_neg).PosSemidef :=
    (hSp_psd.smul hp_pos_nn).add (hSn_psd.smul hp_neg_nn)
  have h_gap := lem_gap_function x hx
  have h_conc := h_gap.2 S_pos S_neg hSp_psd hSn_psd p_pos p_neg hp_pos_nn hp_neg_nn hp_sum hComb
  have h_mono := h_gap.1 (p_pos • S_pos + p_neg • S_neg) S hComb hS_psd hDom
  unfold gapPotential at h_conc h_mono
  rw [← psdTraceSqrt_eq_trace_sqrt hSp_psd,
      ← psdTraceSqrt_eq_trace_sqrt hSn_psd] at h_conc
  rw [← psdTraceSqrt_eq_trace_sqrt hS_psd] at h_mono
  have h0_norm : vecL2Norm (0 : Fin d → ℝ) ≤ 1 := by simp [vecL2Norm]
  have h_gap0 := lem_gap_function (0 : Fin d → ℝ) h0_norm
  have h_conc0 := h_gap0.2 S_pos S_neg hSp_psd hSn_psd p_pos p_neg hp_pos_nn hp_neg_nn hp_sum hComb
  have h_mono0 := h_gap0.1 (p_pos • S_pos + p_neg • S_neg) S hComb hS_psd hDom
  unfold gapPotential at h_conc0 h_mono0
  simp only [Matrix.mulVec_zero, dotProduct_zero, Real.sqrt_zero, sub_zero,
    ← psdTraceSqrt_eq_trace_sqrt hSp_psd,
    ← psdTraceSqrt_eq_trace_sqrt hSn_psd] at h_conc0
  simp only [Matrix.mulVec_zero, dotProduct_zero, Real.sqrt_zero, sub_zero,
    ← psdTraceSqrt_eq_trace_sqrt hS_psd] at h_mono0
  have h_sd_S := (h_proj_μ x).2.2
  refine ⟨hDom, by linarith, ?_⟩
  linarith

end TraceSqrt
