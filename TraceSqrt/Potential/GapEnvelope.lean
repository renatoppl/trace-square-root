import TraceSqrt.Defs

set_option maxHeartbeats 4000000

/-!
# Lemma 1.1 & Lemma B.1: Gap Function Concavity and Variational Envelope (`lem:envelope`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 1.2.2 Lemma 1.1 and Appendix B Lemma B.1).
-/

namespace TraceSqrt

/-- **Lemma B.1 (Gap representation and directional comparison, `lem:envelope`)**:
For every `x ∈ ℝ^d` with `‖x‖₂ ≤ 1`:
1. For every `R ≻ 0`, the affine slope `H_R(x) = R⁻¹ - x xᵀ / ‖R x‖₂` is positive semidefinite.
2. For every `Σ ⪰ 0`, `2 g_x(Σ)` is the greatest lower bound (and `sInf`) of
   `envelopeObjective x R Σ` over `R ≻ 0` (Eq. (4) & Eq. (24)).
3. Whenever `Σ ≻ 0`, `Σ^{1/2} ≻ 0` and `R = Σ^{1/2}` attains the infimum `2 g_x(Σ)`.
4. `g_x` is monotone with respect to the Loewner PSD order (`0 ⪯ Σ₁ ⪯ Σ₂ → g_x(Σ₁) ≤ g_x(Σ₂)`).
5. `g_x` is concave on the positive-semidefinite cone. -/
theorem lem_envelope {d : ℕ} (x : Fin d → ℝ) (hx : vecL2Norm x ≤ 1) :
    (∀ R : Matrix (Fin d) (Fin d) ℝ, R.PosDef → (envelopeSlope x R).PosSemidef) ∧
    (∀ (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef),
      IsGLB {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ, R.PosDef ∧ v = envelopeObjective x R S}
        (2 * gapPotential x S hS) ∧
      sInf {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ, R.PosDef ∧ v = envelopeObjective x R S} =
        2 * gapPotential x S hS) ∧
    (∀ (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef), S.PosDef →
      (hS.sqrt).PosDef ∧ envelopeObjective x hS.sqrt S = 2 * gapPotential x S hS) ∧
    (∀ (S₁ S₂ : Matrix (Fin d) (Fin d) ℝ) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef),
      (S₂ - S₁).PosSemidef → gapPotential x S₁ hS₁ ≤ gapPotential x S₂ hS₂) ∧
    (∀ (S₁ S₂ : Matrix (Fin d) (Fin d) ℝ) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
      (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hab : a + b = 1)
      (hComb : (a • S₁ + b • S₂).PosSemidef),
      a * gapPotential x S₁ hS₁ + b * gapPotential x S₂ hS₂ ≤
        gapPotential x (a • S₁ + b • S₂) hComb) :=
by
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
      congr 1
      ext i
      have h_ev : 0 ≤ hA.isHermitian.eigenvalues i := hA.eigenvalues_nonneg i
      simp [f, RCLike.ofReal_real_eq_id, ← sq, Real.sq_sqrt h_ev]
    rw [h_diag_eq]
    simpa [Unitary.conjStarAlgAut_apply, U] using (hA.isHermitian.spectral_theorem).symm
  have h_sqrt_pd :
      ∀ {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef), A.PosDef → hA.sqrt.PosDef := by
    intro A hA hApd
    unfold Matrix.PosSemidef.sqrt
    let U : Matrix (Fin d) (Fin d) ℝ := hA.isHermitian.eigenvectorUnitary.val
    have hU_mem : U ∈ Matrix.unitaryGroup (Fin d) ℝ := hA.isHermitian.eigenvectorUnitary.prop
    have hUstar : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU_mem
    let f : Fin d → ℝ := RCLike.ofReal ∘ (fun x : ℝ => √x) ∘ hA.isHermitian.eigenvalues
    have hdiag : (Matrix.diagonal f).PosDef :=
      Matrix.posDef_diagonal_iff.mpr fun i => by
        simp [f, Real.sqrt_pos.mpr (hApd.eigenvalues_pos i)]
    have hinj : Function.Injective (fun v : Fin d → ℝ => Matrix.vecMul v U) := by
      intro v₁ v₂ hv
      have := congr_arg (fun w => Matrix.vecMul w (star U)) hv
      simpa [Matrix.vecMul_vecMul, hUstar] using this
    simpa only [Matrix.star_eq_conjTranspose] using hdiag.mul_mul_conjTranspose_same hinj

  have h_norm_nonneg : ∀ v : Fin d → ℝ, 0 ≤ vecL2Norm v :=
    fun v => Real.sqrt_nonneg _
  have h_norm_zero : vecL2Norm (0 : Fin d → ℝ) = 0 := by
    simp [vecL2Norm]
  have h_norm_sq : ∀ v : Fin d → ℝ, vecL2Norm v ^ 2 = ∑ i, (v i) ^ 2 :=
    fun v => Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))
  have h_cs : ∀ u v : Fin d → ℝ, dotProduct u v ≤ vecL2Norm u * vecL2Norm v :=
    fun u v => Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v
  have h_norm_pos_of_posDef :
      ∀ (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef → x ≠ 0 → 0 < vecL2Norm (R.mulVec x) := by
    intro R hR hx0
    have hpos : 0 < dotProduct x (R.mulVec x) := by
      simpa using hR.dotProduct_mulVec_pos hx0
    have hcs := h_cs x (R.mulVec x)
    have hnx := h_norm_nonneg x
    nlinarith
  have h_outer_herm : (Matrix.vecMulVec x x).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have h_outer_quad :
      ∀ y : Fin d → ℝ, dotProduct y ((Matrix.vecMulVec x x).mulVec y) = (dotProduct x y) ^ 2 := by
    intro y
    calc dotProduct y ((Matrix.vecMulVec x x).mulVec y)
        = ∑ i, (x i * y i) * (∑ j, x j * y j) := by
            simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = (∑ i, x i * y i) * (∑ j, x j * y j) := by rw [← Finset.sum_mul]
      _ = (dotProduct x y) ^ 2 := by simp [dotProduct, sq]
  have h_outer_trace :
      ∀ B : Matrix (Fin d) (Fin d) ℝ,
        Matrix.trace (Matrix.vecMulVec x x * B) = dotProduct x (B.mulVec x) := by
    intro B
    calc Matrix.trace (Matrix.vecMulVec x x * B)
        = ∑ i, ∑ j, (x i * x j) * B j i := by
            simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply]
      _ = ∑ j, ∑ i, (x i * x j) * B j i := Finset.sum_comm
      _ = ∑ j, x j * (∑ i, B j i * x i) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
      _ = dotProduct x (B.mulVec x) := rfl
  have h_herm_dot :
      ∀ (A : Matrix (Fin d) (Fin d) ℝ), A.IsHermitian →
        ∀ u v : Fin d → ℝ, dotProduct u (A.mulVec v) = dotProduct (A.mulVec u) v := by
    intro A hA u v
    have hA_symm : ∀ i j, A j i = A i j := fun i j => by
      have := congr_fun (congr_fun hA.eq i) j
      simpa [Matrix.conjTranspose_apply] using this
    calc dotProduct u (A.mulVec v)
        = ∑ i, ∑ j, u i * (A i j * v j) := by
            simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      _ = ∑ j, ∑ i, u i * (A i j * v j) := Finset.sum_comm
      _ = ∑ j, (∑ i, A j i * u i) * v j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hA_symm i j]
            ring
      _ = dotProduct (A.mulVec u) v := rfl
  have h_herm_sq_quad :
      ∀ (A : Matrix (Fin d) (Fin d) ℝ), A.IsHermitian →
        dotProduct x ((A * A).mulVec x) = ∑ i, (A.mulVec x i) ^ 2 := by
    intro A hA
    rw [← Matrix.mulVec_mulVec, h_herm_dot A hA x (A.mulVec x)]
    simp [dotProduct, sq]
  have h_gap_eq :
      ∀ (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef),
        dotProduct x (S.mulVec x) = vecL2Norm (hS.sqrt.mulVec x) ^ 2 ∧
        gapPotential x S hS = Matrix.trace hS.sqrt - vecL2Norm (hS.sqrt.mulVec x) := by
    intro S hS
    have hT_psd : hS.sqrt.PosSemidef := h_sqrt_psd hS
    have hquad : dotProduct x (S.mulVec x) = ∑ i, (hS.sqrt.mulVec x i) ^ 2 := by
      conv_lhs => rw [← h_sqrt_sq hS]
      exact h_herm_sq_quad hS.sqrt hT_psd.isHermitian
    refine ⟨?_, ?_⟩
    · rw [hquad, h_norm_sq]
    · simp only [gapPotential, vecL2Norm, hquad]

  have h_trace_psd :
      ∀ (H N : Matrix (Fin d) (Fin d) ℝ), H.PosSemidef → N.PosSemidef →
        0 ≤ Matrix.trace (H * N) := by
    intro H N hH hN
    let K := hH.sqrt
    have hK_psd : K.PosSemidef := h_sqrt_psd hH
    have hK_sq : K * K = H := h_sqrt_sq hH
    have hK_herm : K.conjTranspose = K := hK_psd.isHermitian.eq
    have h_eq : Matrix.trace (H * N) = Matrix.trace (K * N * K.conjTranspose) := by
      calc Matrix.trace (H * N)
          = Matrix.trace ((K * K) * N) := by rw [hK_sq]
        _ = Matrix.trace (K * (K * N)) := by rw [Matrix.mul_assoc]
        _ = Matrix.trace ((K * N) * K) := Matrix.trace_mul_comm K (K * N)
        _ = Matrix.trace (K * N * K.conjTranspose) := by rw [hK_herm]
    rw [h_eq]
    exact (hN.mul_mul_conjTranspose_same K).trace_nonneg

  have h_slope_psd :
      ∀ R : Matrix (Fin d) (Fin d) ℝ, R.PosDef → (envelopeSlope x R).PosSemidef := by
    intro R hR
    by_cases hx0 : x = 0
    · simp only [envelopeSlope, hx0, ↓reduceIte]
      exact hR.inv.posSemidef
    · simp only [envelopeSlope, hx0, ↓reduceIte]
      set u := R.mulVec x
      set r := vecL2Norm u
      set a := dotProduct x u
      have ha_pos : 0 < a := by simpa [a, u] using hR.dotProduct_mulVec_pos hx0
      have hcs : a ≤ vecL2Norm x * r := h_cs x u
      have hr_nonneg : 0 ≤ r := h_norm_nonneg u
      have ha_le_r : a ≤ r := by nlinarith [hx, h_norm_nonneg x]
      have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
      have hRRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hdet
      have hRinvR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hdet
      have hH_herm : (R⁻¹ - r⁻¹ • Matrix.vecMulVec x x).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
            star_trivial, hR.inv.isHermitian.eq, h_outer_herm.eq]
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH_herm fun y => ?_
      simp only [star_trivial]
      let c : ℝ := dotProduct x y / a
      let w : Fin d → ℝ := y - c • u
      have hw_nonneg : 0 ≤ dotProduct w (R⁻¹.mulVec w) := by
        simpa using hR.inv.posSemidef.dotProduct_mulVec_nonneg w
      have hRinv_u : R⁻¹.mulVec u = x := by
        simp [u, Matrix.mulVec_mulVec, hRinvR]
      have hu_Rinv_y : dotProduct u (R⁻¹.mulVec y) = dotProduct x y := by
        calc dotProduct (R.mulVec x) (R⁻¹.mulVec y)
            = dotProduct x (R.mulVec (R⁻¹.mulVec y)) :=
                (h_herm_dot R hR.isHermitian x (R⁻¹.mulVec y)).symm
          _ = dotProduct x y := by simp [Matrix.mulVec_mulVec, hRRinv]
      have hw_expand :
          dotProduct w (R⁻¹.mulVec w) =
            dotProduct y (R⁻¹.mulVec y) - (dotProduct x y) ^ 2 / a := by
        have h_rw : R⁻¹.mulVec w = R⁻¹.mulVec y - c • x := by
          simp [w, Matrix.mulVec_sub, Matrix.mulVec_smul, hRinv_u]
        have hu_x : dotProduct u x = a := dotProduct_comm u x
        have hc_mul_a : c * a = dotProduct x y := div_mul_cancel₀ (dotProduct x y) ha_pos.ne'
        rw [h_rw]
        simp only [w, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, hu_Rinv_y, dotProduct_comm y x, hu_x, hc_mul_a]
        dsimp only [c]
        ring
      have h_div_le : r⁻¹ * (dotProduct x y) ^ 2 ≤ dotProduct y (R⁻¹.mulVec y) := by
        calc r⁻¹ * (dotProduct x y) ^ 2
            = (dotProduct x y) ^ 2 / r := by ring
          _ ≤ (dotProduct x y) ^ 2 / a :=
              div_le_div_of_nonneg_left (sq_nonneg _) ha_pos ha_le_r
          _ ≤ dotProduct y (R⁻¹.mulVec y) := by linarith [hw_nonneg, hw_expand]
      have h_goal_expand :
          dotProduct y ((R⁻¹ - r⁻¹ • Matrix.vecMulVec x x).mulVec y) =
            dotProduct y (R⁻¹.mulVec y) - r⁻¹ * (dotProduct x y) ^ 2 := by
        simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
          smul_eq_mul, h_outer_quad y]
      linarith

  have h_trace_sq_id :
      ∀ (R S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef), R.PosDef →
        Matrix.trace (R⁻¹ * ((hS.sqrt - R) * (hS.sqrt - R))) =
          Matrix.trace (R⁻¹ * S) - 2 * Matrix.trace hS.sqrt + Matrix.trace R := by
    intro R S hS hR
    set T := hS.sqrt
    have hTT : T * T = S := h_sqrt_sq hS
    have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
    have hRRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hdet
    have hRinvR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hdet
    have hexp : R⁻¹ * ((T - R) * (T - R)) = R⁻¹ * S - R⁻¹ * T * R - T + R := by
      rw [mul_sub, sub_mul, sub_mul, hTT]
      simp only [mul_sub, ← Matrix.mul_assoc, hRinvR, Matrix.one_mul]
      abel
    have htr_cycle : Matrix.trace (R⁻¹ * T * R) = Matrix.trace T := by
      calc Matrix.trace (R⁻¹ * T * R)
          = Matrix.trace (R * (R⁻¹ * T)) := Matrix.trace_mul_comm (R⁻¹ * T) R
        _ = Matrix.trace ((R * R⁻¹) * T) := by rw [Matrix.mul_assoc]
        _ = Matrix.trace T := by rw [hRRinv, Matrix.one_mul]
    rw [hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, htr_cycle]
    ring

  have h_lower_bound :
      ∀ (R S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef), R.PosDef →
        2 * gapPotential x S hS ≤ envelopeObjective x R S := by
    intro R S hS hR
    set T := hS.sqrt
    set M := (T - R) * (T - R)
    have hT_psd : T.PosSemidef := h_sqrt_psd hS
    have hTR_herm : (T - R).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hT_psd.isHermitian.eq, hR.isHermitian.eq]
    have hM_psd : M.PosSemidef := by
      have : M = (T - R).conjTranspose * (T - R) := by rw [hTR_herm.eq]
      rw [this]
      exact Matrix.posSemidef_conjTranspose_mul_self (T - R)
    have htr_id := h_trace_sq_id R S hS hR
    obtain ⟨hS_quad, hgap_rw⟩ := h_gap_eq S hS
    set σ := vecL2Norm (T.mulVec x)
    set r := vecL2Norm (R.mulVec x)
    by_cases hx0 : x = 0
    · have hσ0 : σ = 0 := by simp [σ, hx0, h_norm_zero]
      have hr0 : r = 0 := by simp [r, hx0, h_norm_zero]
      have h_tr_nonneg : 0 ≤ Matrix.trace (R⁻¹ * M) :=
        h_trace_psd R⁻¹ M hR.inv.posSemidef hM_psd
      have hobj0 : envelopeObjective x R S = Matrix.trace R + Matrix.trace (R⁻¹ * S) := by
        simp [envelopeObjective, envelopeSlope, hx0, h_norm_zero]
      rw [hgap_rw, hobj0, hσ0]
      linarith [htr_id, h_tr_nonneg]
    · have hr_pos : 0 < r := h_norm_pos_of_posDef R hR hx0
      have hr_ne : r ≠ 0 := hr_pos.ne'
      have hSlope : (envelopeSlope x R).PosSemidef := h_slope_psd R hR
      have hRinv_decomp : R⁻¹ = envelopeSlope x R + r⁻¹ • Matrix.vecMulVec x x := by
        simp [envelopeSlope, hx0, r]
      have htr_decomp :
          Matrix.trace (R⁻¹ * M) =
            Matrix.trace (envelopeSlope x R * M) + r⁻¹ * Matrix.trace (Matrix.vecMulVec x x * M) := by
        conv_lhs => rw [hRinv_decomp]
        rw [add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
      have htr_HM_nonneg : 0 ≤ Matrix.trace (envelopeSlope x R * M) :=
        h_trace_psd (envelopeSlope x R) M hSlope hM_psd
      have htr_EM :
          (σ - r) ^ 2 ≤ Matrix.trace (Matrix.vecMulVec x x * M) := by
        rw [h_outer_trace M]
        have hM_quad : dotProduct x (M.mulVec x) = ∑ i, (T.mulVec x i - R.mulVec x i) ^ 2 := by
          dsimp [M]
          rw [h_herm_sq_quad (T - R) hTR_herm]
          simp [Matrix.sub_mulVec]
        rw [hM_quad]
        have hsum_expand :
            (∑ i, (T.mulVec x i - R.mulVec x i) ^ 2) =
              σ ^ 2 - 2 * dotProduct (T.mulVec x) (R.mulVec x) + r ^ 2 := by
          have hσ2 : σ ^ 2 = ∑ i, (T.mulVec x i) ^ 2 := h_norm_sq (T.mulVec x)
          have hr2 : r ^ 2 = ∑ i, (R.mulVec x i) ^ 2 := h_norm_sq (R.mulVec x)
          rw [hσ2, hr2]
          simp only [dotProduct, Finset.mul_sum]
          rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        have hcs_TR : dotProduct (T.mulVec x) (R.mulVec x) ≤ σ * r :=
          h_cs (T.mulVec x) (R.mulVec x)
        nlinarith
      have h_rinv_sq : r⁻¹ * (σ - r) ^ 2 ≤ Matrix.trace (R⁻¹ * M) := by
        have h1 : r⁻¹ * (σ - r) ^ 2 ≤ r⁻¹ * Matrix.trace (Matrix.vecMulVec x x * M) :=
          mul_le_mul_of_nonneg_left htr_EM (inv_nonneg.mpr hr_pos.le)
        linarith [htr_decomp, htr_HM_nonneg, h1]
      have h_alg : r⁻¹ * (σ - r) ^ 2 = r⁻¹ * σ ^ 2 - 2 * σ + r := by
        field_simp
        ring
      have hobj_eq :
          envelopeObjective x R S =
            Matrix.trace R - r + (Matrix.trace (R⁻¹ * S) - r⁻¹ * σ ^ 2) := by
        simp only [envelopeObjective, envelopeSlope, hx0, ↓reduceIte, sub_mul,
          Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
          h_outer_trace S, hS_quad]
        rfl
      rw [hgap_rw, hobj_eq]
      linarith [htr_id, h_rinv_sq, h_alg]

  have h_shifted_bound :
      ∀ (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (τ : ℝ), 0 < τ →
        (hS.sqrt + τ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef ∧
        envelopeObjective x (hS.sqrt + τ • (1 : Matrix (Fin d) (Fin d) ℝ)) S ≤
          2 * gapPotential x S hS + (d : ℝ) * τ := by
    intro S hS τ hτ
    set T := hS.sqrt
    set Rτ : Matrix (Fin d) (Fin d) ℝ := T + τ • 1
    have hT_psd : T.PosSemidef := h_sqrt_psd hS
    have hRτ_pd : Rτ.PosDef :=
      Matrix.PosDef.posSemidef_add hT_psd (Matrix.PosDef.one.smul hτ)
    refine ⟨hRτ_pd, ?_⟩
    have hτ_ne : τ ≠ 0 := hτ.ne'
    have hdet : IsUnit Rτ.det := (Matrix.isUnit_iff_isUnit_det Rτ).mp hRτ_pd.isUnit
    have hRRinv : Rτ * Rτ⁻¹ = 1 := Matrix.mul_nonsing_inv Rτ hdet
    have hRinvR : Rτ⁻¹ * Rτ = 1 := Matrix.nonsing_inv_mul Rτ hdet
    have htr_ray :
        Matrix.trace Rτ + Matrix.trace (Rτ⁻¹ * S) =
          2 * Matrix.trace T + τ ^ 2 * Matrix.trace (Rτ⁻¹) := by
      have h_id := h_trace_sq_id Rτ S hS hRτ_pd
      have h_diff : T - Rτ = -(τ • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
        dsimp [Rτ]
        abel
      have h_lhs :
          Matrix.trace (Rτ⁻¹ * ((T - Rτ) * (T - Rτ))) = τ ^ 2 * Matrix.trace (Rτ⁻¹) := by
        rw [h_diff]
        simp [sq, mul_assoc, Matrix.trace_smul]
      linarith [h_id, h_lhs]
    have htr_inv_bound : τ ^ 2 * Matrix.trace (Rτ⁻¹) ≤ (d : ℝ) * τ := by
      let P : Matrix (Fin d) (Fin d) ℝ := τ⁻¹ • S + T
      have hP_psd : P.PosSemidef :=
        (hS.smul (inv_nonneg.mpr hτ.le)).add hT_psd
      have hTT : T * T = S := h_sqrt_sq hS
      have hRτ_sq : Rτ * Rτ = S + (2 * τ) • T + (τ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
        dsimp [Rτ]
        rw [add_mul, mul_add, mul_add, hTT]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul]
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      have h_congr_eq : τ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rτ⁻¹ =
          Rτ⁻¹ * P * (Rτ⁻¹).conjTranspose := by
        have h_mid : Rτ * (τ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rτ⁻¹) * Rτ = P := by
          rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, hRRinv,
              Matrix.smul_mul, Matrix.one_mul, hRτ_sq]
          ext i j
          dsimp [P, Rτ]
          simp only [Matrix.one_apply]
          field_simp
          ring
        rw [hRτ_pd.inv.isHermitian.eq, ← h_mid]
        calc τ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rτ⁻¹
            = 1 * (τ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rτ⁻¹) * 1 := by
                rw [Matrix.one_mul, Matrix.mul_one]
          _ = (Rτ⁻¹ * Rτ) * (τ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rτ⁻¹) * (Rτ * Rτ⁻¹) := by
                rw [hRinvR, hRRinv]
          _ = Rτ⁻¹ * (Rτ * (τ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rτ⁻¹) * Rτ) * Rτ⁻¹ := by
                simp only [Matrix.mul_assoc]
      have h_diff_psd : (τ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rτ⁻¹).PosSemidef := by
        rw [h_congr_eq]
        exact hP_psd.mul_mul_conjTranspose_same Rτ⁻¹
      have h_tr_nonneg : 0 ≤ τ⁻¹ * (d : ℝ) - Matrix.trace (Rτ⁻¹) := by
        have h := h_diff_psd.trace_nonneg
        simpa [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] using h
      have hτ2_pos : 0 ≤ τ ^ 2 := sq_nonneg τ
      have h_mul := mul_le_mul_of_nonneg_left h_tr_nonneg hτ2_pos
      have h_simp : τ ^ 2 * (τ⁻¹ * (d : ℝ) - Matrix.trace (Rτ⁻¹)) =
          (d : ℝ) * τ - τ ^ 2 * Matrix.trace (Rτ⁻¹) := by
        field_simp
      linarith
    obtain ⟨hS_quad, hgap_rw⟩ := h_gap_eq S hS
    set σ := vecL2Norm (T.mulVec x)
    set rτ := vecL2Norm (Rτ.mulVec x)
    by_cases hx0 : x = 0
    · have hσ0 : σ = 0 := by simp [σ, hx0, h_norm_zero]
      have hobj0 : envelopeObjective x Rτ S = Matrix.trace Rτ + Matrix.trace (Rτ⁻¹ * S) := by
        simp [envelopeObjective, envelopeSlope, hx0, h_norm_zero]
      rw [hgap_rw, hobj0, hσ0]
      linarith [htr_ray, htr_inv_bound]
    · have hr_pos : 0 < rτ := h_norm_pos_of_posDef Rτ hRτ_pd hx0
      have hr_ne : rτ ≠ 0 := hr_pos.ne'
      have hobj_eq :
          envelopeObjective x Rτ S =
            Matrix.trace Rτ - rτ + (Matrix.trace (Rτ⁻¹ * S) - rτ⁻¹ * σ ^ 2) := by
        simp only [envelopeObjective, envelopeSlope, hx0, ↓reduceIte, sub_mul,
          Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
          h_outer_trace S, hS_quad]
        rfl
      have h_amgm : 2 * σ ≤ rτ + rτ⁻¹ * σ ^ 2 := by
        have hsq : 0 ≤ rτ⁻¹ * (rτ - σ) ^ 2 :=
          mul_nonneg (inv_nonneg.mpr hr_pos.le) (sq_nonneg _)
        have halg : rτ⁻¹ * (rτ - σ) ^ 2 = rτ - 2 * σ + rτ⁻¹ * σ ^ 2 := by
          field_simp
          ring
        linarith
      rw [hgap_rw, hobj_eq]
      linarith [htr_ray, htr_inv_bound, h_amgm]

  have h_conj2 :
      ∀ (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef),
        IsGLB {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ, R.PosDef ∧ v = envelopeObjective x R S}
          (2 * gapPotential x S hS) ∧
        sInf {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ, R.PosDef ∧ v = envelopeObjective x R S} =
          2 * gapPotential x S hS := by
    intro S hS
    set V : Set ℝ := {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ, R.PosDef ∧ v = envelopeObjective x R S}
    set g : ℝ := 2 * gapPotential x S hS
    have hGLB : IsGLB V g := by
      refine ⟨?_, ?_⟩
      · rintro v ⟨R, hR, rfl⟩
        exact h_lower_bound R S hS hR
      · intro b hb
        by_contra h_not_le
        push_neg at h_not_le
        have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
        let τ : ℝ := (b - g) / ((d : ℝ) + 1)
        have hτ_pos : 0 < τ := div_pos (sub_pos.mpr h_not_le) hd1_pos
        obtain ⟨hRτ_pd, hRτ_ub⟩ := h_shifted_bound S hS τ hτ_pos
        have hb_le : b ≤ envelopeObjective x (hS.sqrt + τ • 1) S :=
          hb ⟨hS.sqrt + τ • 1, hRτ_pd, rfl⟩
        have hb_le2 : b ≤ g + (d : ℝ) * τ := le_trans hb_le hRτ_ub
        have h_mul := mul_le_mul_of_nonneg_right hb_le2 hd1_pos.le
        have h_rhs : (g + (d : ℝ) * τ) * ((d : ℝ) + 1) = g + (d : ℝ) * b := by
          dsimp [τ]
          have hd1_ne : (d : ℝ) + 1 ≠ 0 := hd1_pos.ne'
          field_simp
          ring
        linarith
    have hne : V.Nonempty := ⟨envelopeObjective x 1 S, 1, Matrix.PosDef.one, rfl⟩
    exact ⟨hGLB, hGLB.csInf_eq hne⟩

  have h_conj3 :
      ∀ (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef), S.PosDef →
        (hS.sqrt).PosDef ∧ envelopeObjective x hS.sqrt S = 2 * gapPotential x S hS := by
    intro S hS hS_pd
    set T := hS.sqrt
    have hT_pd : T.PosDef := h_sqrt_pd hS hS_pd
    refine ⟨hT_pd, ?_⟩
    have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT_pd.isUnit
    have hTinvT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hdet
    have hTinvS : T⁻¹ * S = T := by
      calc T⁻¹ * S = T⁻¹ * (T * T) := by rw [h_sqrt_sq hS]
        _ = (T⁻¹ * T) * T := (Matrix.mul_assoc T⁻¹ T T).symm
        _ = T := by rw [hTinvT, Matrix.one_mul]
    obtain ⟨hS_quad, hgap_rw⟩ := h_gap_eq S hS
    set r := vecL2Norm (T.mulVec x)
    by_cases hx0 : x = 0
    · have hr0 : r = 0 := by simp [r, hx0, h_norm_zero]
      rw [hgap_rw, hr0]
      simp only [envelopeObjective, envelopeSlope, hx0, ↓reduceIte, Matrix.mulVec_zero,
        h_norm_zero, hTinvS]
      ring
    · have hr_pos : 0 < r := h_norm_pos_of_posDef T hT_pd hx0
      have hr_ne : r ≠ 0 := hr_pos.ne'
      have hobj_eq :
          envelopeObjective x T S =
            Matrix.trace T - r + (Matrix.trace T - r⁻¹ * r ^ 2) := by
        simp only [envelopeObjective, envelopeSlope, hx0, ↓reduceIte, sub_mul,
          Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
          h_outer_trace S, hS_quad, hTinvS]
        rfl
      rw [hobj_eq, hgap_rw]
      field_simp
      ring

  have h_conj4 :
      ∀ (S₁ S₂ : Matrix (Fin d) (Fin d) ℝ) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef),
        (S₂ - S₁).PosSemidef → gapPotential x S₁ hS₁ ≤ gapPotential x S₂ hS₂ := by
    intro S₁ S₂ hS₁ hS₂ hDiff
    have hGLB₂ := (h_conj2 S₂ hS₂).1
    have h_lb :
        2 * gapPotential x S₁ hS₁ ∈
          lowerBounds {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ, R.PosDef ∧ v = envelopeObjective x R S₂} := by
      rintro v ⟨R, hR, rfl⟩
      have h1 : 2 * gapPotential x S₁ hS₁ ≤ envelopeObjective x R S₁ :=
        h_lower_bound R S₁ hS₁ hR
      have hSlope : (envelopeSlope x R).PosSemidef := h_slope_psd R hR
      have h_tr_diff : 0 ≤ Matrix.trace (envelopeSlope x R * (S₂ - S₁)) :=
        h_trace_psd (envelopeSlope x R) (S₂ - S₁) hSlope hDiff
      have h_obj_diff :
          envelopeObjective x R S₂ - envelopeObjective x R S₁ =
            Matrix.trace (envelopeSlope x R * (S₂ - S₁)) := by
        simp only [envelopeObjective, mul_sub, Matrix.trace_sub]
        ring
      linarith
    have h2 : 2 * gapPotential x S₁ hS₁ ≤ 2 * gapPotential x S₂ hS₂ := hGLB₂.2 h_lb
    linarith

  have h_conj5 :
      ∀ (S₁ S₂ : Matrix (Fin d) (Fin d) ℝ) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
        (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hab : a + b = 1)
        (hComb : (a • S₁ + b • S₂).PosSemidef),
        a * gapPotential x S₁ hS₁ + b * gapPotential x S₂ hS₂ ≤
          gapPotential x (a • S₁ + b • S₂) hComb := by
    intro S₁ S₂ hS₁ hS₂ a b ha hb hab hComb
    set Sc := a • S₁ + b • S₂
    have hGLBc := (h_conj2 Sc hComb).1
    have h_lb :
        2 * (a * gapPotential x S₁ hS₁ + b * gapPotential x S₂ hS₂) ∈
          lowerBounds {v : ℝ | ∃ R : Matrix (Fin d) (Fin d) ℝ, R.PosDef ∧ v = envelopeObjective x R Sc} := by
      rintro v ⟨R, hR, rfl⟩
      have h1 : 2 * gapPotential x S₁ hS₁ ≤ envelopeObjective x R S₁ :=
        h_lower_bound R S₁ hS₁ hR
      have h2 : 2 * gapPotential x S₂ hS₂ ≤ envelopeObjective x R S₂ :=
        h_lower_bound R S₂ hS₂ hR
      have h_aff :
          envelopeObjective x R Sc =
            a * envelopeObjective x R S₁ + b * envelopeObjective x R S₂ := by
        have h_tr :
            Matrix.trace (envelopeSlope x R * Sc) =
              a * Matrix.trace (envelopeSlope x R * S₁) +
                b * Matrix.trace (envelopeSlope x R * S₂) := by
          dsimp [Sc]
          rw [mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
              Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
        simp only [envelopeObjective]
        rw [h_tr]
        calc Matrix.trace R - vecL2Norm (R.mulVec x) +
              (a * Matrix.trace (envelopeSlope x R * S₁) +
                b * Matrix.trace (envelopeSlope x R * S₂))
            = (a + b) * (Matrix.trace R - vecL2Norm (R.mulVec x)) +
              (a * Matrix.trace (envelopeSlope x R * S₁) +
                b * Matrix.trace (envelopeSlope x R * S₂)) := by rw [hab, one_mul]
          _ = a * (Matrix.trace R - vecL2Norm (R.mulVec x) +
                Matrix.trace (envelopeSlope x R * S₁)) +
              b * (Matrix.trace R - vecL2Norm (R.mulVec x) +
                Matrix.trace (envelopeSlope x R * S₂)) := by ring
      nlinarith
    have h_le : 2 * (a * gapPotential x S₁ hS₁ + b * gapPotential x S₂ hS₂) ≤
        2 * gapPotential x Sc hComb := hGLBc.2 h_lb
    linarith

  exact ⟨h_slope_psd, h_conj2, h_conj3, h_conj4, h_conj5⟩

/-- Alias for `lem_envelope`. -/
alias lem_gap_envelope := lem_envelope

/-- **Lemma 1.1 (Gap Function, Section 1.2.2)**:
For any vector `x ∈ ℝ^d` with `‖x‖₂ ≤ 1`, the gap function
`g_x(A) = Tr(√A) - √(xᵀ A x)` is monotone with respect to the Loewner positive-semidefinite
order and concave on the positive-semidefinite cone. -/
theorem lem_gap_function {d : ℕ} (x : Fin d → ℝ) (hx : vecL2Norm x ≤ 1) :
    (∀ (A₁ A₂ : Matrix (Fin d) (Fin d) ℝ) (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef),
      (A₂ - A₁).PosSemidef → gapPotential x A₁ hA₁ ≤ gapPotential x A₂ hA₂) ∧
    (∀ (A₁ A₂ : Matrix (Fin d) (Fin d) ℝ) (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
      (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hab : a + b = 1)
      (hComb : (a • A₁ + b • A₂).PosSemidef),
      a * gapPotential x A₁ hA₁ + b * gapPotential x A₂ hA₂ ≤
        gapPotential x (a • A₁ + b • A₂) hComb) := by
  have h := lem_envelope x hx
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

end TraceSqrt
