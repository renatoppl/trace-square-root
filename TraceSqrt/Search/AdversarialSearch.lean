import TraceSqrt.Defs
import TraceSqrt.Search.AdversarialDrift

set_option maxHeartbeats 4000000

/-!
# Theorem 2.4: Adversarial Contextual Search (`thm:main`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 2.2, Algorithm 2 and Theorem 2.4).
-/

namespace TraceSqrt

/-- **Theorem 2.4 (Adversarial Contextual Search, `thm:main`)**:
For every `d ≥ 1`, hidden target `zVec ∈ ℝ^d` with `‖zVec‖₂ ≤ 1`, full-history adaptive context
strategy `ctxPolicy` (`𝓕_{t-1}`) with `‖x_t‖₂ ≤ 1`, and horizon `T`:
`0 ≤ E[∑_{t=1}^T ℓ_t]`, `0 ≤ E[Φ_{T+1}]`,
`E[∑_{t=1}^T ℓ_t] + 6 E[Φ_{T+1}] ≤ 6 Φ₁ ≤ 12 √d`, and `E[∑_{t=1}^T ℓ_t] ≤ 12 √d` (Eq. (11)). -/
theorem thm_adversarial_contextual_search (d : ℕ) (hd : 0 < d)
    (zVec : Fin d → ℝ) (hz : vecL2Norm zVec ≤ 1)
    (ctxPolicy : List (SearchObs d) → (Fin d → ℝ))
    (hCtx : ∀ hist : List (SearchObs d), vecL2Norm (ctxPolicy hist) ≤ 1)
    (T : ℕ) :
    let out := alg2RunExpected zVec ctxPolicy T 0 (alg2InitScale d) []
    0 ≤ out.1 ∧
    0 ≤ out.2 ∧
    out.1 + 6 * out.2 ≤ 6 * quadPotential 0 (alg2InitScale d) zVec ∧
    6 * quadPotential 0 (alg2InitScale d) zVec ≤ 12 * Real.sqrt d ∧
    out.1 ≤ 12 * Real.sqrt d :=
by
  have h_norm_nonneg : ∀ v : Fin d → ℝ, 0 ≤ vecL2Norm v :=
    fun v => Real.sqrt_nonneg _
  have h_norm_sq : ∀ v : Fin d → ℝ, vecL2Norm v ^ 2 = ∑ i, (v i) ^ 2 :=
    fun v => Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))

  have h_init :
      (alg2InitScale d).PosDef ∧
      6 * quadPotential 0 (alg2InitScale d) zVec ≤ 12 * Real.sqrt d := by
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
    have hsqrt_ne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
    have hinv_pos : 0 < (Real.sqrt d)⁻¹ := inv_pos.mpr hsqrt_pos
    have hR_pd : (alg2InitScale d).PosDef := by
      unfold alg2InitScale
      exact Matrix.PosDef.one.smul hinv_pos
    have hR_inv : (alg2InitScale d)⁻¹ = Real.sqrt d • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      apply Matrix.inv_eq_right_inv
      unfold alg2InitScale
      rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, inv_mul_cancel₀ hsqrt_ne, one_smul]
    have h_trace : Matrix.trace (alg2InitScale d) = Real.sqrt d := by
      unfold alg2InitScale
      rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
      have hsq : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
      calc (Real.sqrt d)⁻¹ * (d : ℝ)
          = (Real.sqrt d)⁻¹ * (Real.sqrt d ^ 2) := by rw [hsq]
        _ = Real.sqrt d := by field_simp
    have h_quad :
        dotProduct (zVec - 0) ((alg2InitScale d)⁻¹.mulVec (zVec - 0)) ≤ Real.sqrt d := by
      rw [sub_zero, hR_inv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      have h_dot_eq : dotProduct zVec zVec = vecL2Norm zVec ^ 2 := by
        rw [h_norm_sq zVec]
        simp [dotProduct, sq]
      have hz_nn : 0 ≤ vecL2Norm zVec := h_norm_nonneg zVec
      have hz_sq : vecL2Norm zVec ^ 2 ≤ 1 := by nlinarith
      rw [h_dot_eq]
      nlinarith [hsqrt_pos]
    refine ⟨hR_pd, ?_⟩
    unfold quadPotential
    linarith [h_trace, h_quad]

  have h_quad_nonneg :
      ∀ (mVec : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ),
        R.PosDef → 0 ≤ quadPotential mVec R zVec := by
    intro mVec R hR
    unfold quadPotential
    have h1 : 0 ≤ Matrix.trace R := hR.posSemidef.trace_nonneg
    have h2 : 0 ≤ dotProduct (zVec - mVec) (R⁻¹.mulVec (zVec - mVec)) := by
      simpa using hR.inv.posSemidef.dotProduct_mulVec_nonneg (zVec - mVec)
    exact add_nonneg h1 h2

  have h_ind :
      ∀ (n : ℕ) (mVec : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ) (hist : List (SearchObs d)),
        R.PosDef →
        0 ≤ (alg2RunExpected zVec ctxPolicy n mVec R hist).1 ∧
        0 ≤ (alg2RunExpected zVec ctxPolicy n mVec R hist).2 ∧
        (alg2RunExpected zVec ctxPolicy n mVec R hist).1 +
          6 * (alg2RunExpected zVec ctxPolicy n mVec R hist).2 ≤
            6 * quadPotential mVec R zVec := by
    intro n
    induction n with
    | zero =>
      intro mVec R hist hR
      dsimp only [alg2RunExpected]
      refine ⟨le_rfl, h_quad_nonneg mVec R hR, by linarith⟩
    | succ n ih =>
      intro mVec R hist hR
      dsimp only [alg2RunExpected]
      set xVec := ctxPolicy hist
      have hx : vecL2Norm xVec ≤ 1 := hCtx hist
      set PNeg := alg2PostedPrice mVec R xVec (-1)
      set YNeg := paperSign (dotProduct xVec zVec - PNeg)
      set ellNeg := |dotProduct xVec zVec - PNeg|
      set mNeg := alg2NextCenter mVec R zVec xVec (-1)
      set RNeg := alg2NextScale mVec R zVec xVec (-1)
      set subNeg := alg2RunExpected zVec ctxPolicy n mNeg RNeg (hist ++ [⟨xVec, -1, PNeg, YNeg⟩])
      set PPos := alg2PostedPrice mVec R xVec 1
      set YPos := paperSign (dotProduct xVec zVec - PPos)
      set ellPos := |dotProduct xVec zVec - PPos|
      set mPos := alg2NextCenter mVec R zVec xVec 1
      set RPos := alg2NextScale mVec R zVec xVec 1
      set subPos := alg2RunExpected zVec ctxPolicy n mPos RPos (hist ++ [⟨xVec, 1, PPos, YPos⟩])
      have h_drift := lem_drift mVec zVec xVec hx R hR
      have hRNeg : RNeg.PosDef := (h_drift.1 (-1) (Or.inl rfl)).1
      have hRPos : RPos.PosDef := (h_drift.1 1 (Or.inr rfl)).1
      obtain ⟨h_subNeg_loss_nn, h_subNeg_nn, h_subNeg_bound⟩ :=
        ih mNeg RNeg (hist ++ [⟨xVec, -1, PNeg, YNeg⟩]) hRNeg
      obtain ⟨h_subPos_loss_nn, h_subPos_nn, h_subPos_bound⟩ :=
        ih mPos RPos (hist ++ [⟨xVec, 1, PPos, YPos⟩]) hRPos
      have h_ellNeg_nn : 0 ≤ ellNeg := abs_nonneg _
      have h_ellPos_nn : 0 ≤ ellPos := abs_nonneg _
      have h_step :
          (1 / 2 : ℝ) * (ellNeg + ellPos) ≤
            6 * (quadPotential mVec R zVec -
              (1 / 2 : ℝ) * (quadPotential mNeg RNeg zVec + quadPotential mPos RPos zVec)) := by
        simpa only [rademacherExpect] using h_drift.2.2
      refine ⟨?_, ?_, ?_⟩
      · linarith [h_ellNeg_nn, h_ellPos_nn, h_subNeg_loss_nn, h_subPos_loss_nn]
      · linarith [h_subNeg_nn, h_subPos_nn]
      · linarith [h_subNeg_bound, h_subPos_bound, h_step]

  dsimp only
  obtain ⟨hR_init, h_init_bound⟩ := h_init
  obtain ⟨h_loss_nn, h_run_nn, h_run_bound⟩ := h_ind T 0 (alg2InitScale d) [] hR_init
  refine ⟨h_loss_nn, h_run_nn, h_run_bound, h_init_bound, ?_⟩
  linarith

/-- **Theorem 2.4 for randomized adaptive context strategies**:
For any probability space `(Ξ, ν_ctx)` driving the context adversary's randomization and any
full-history context policy `ctxPolicy : Ξ → List (SearchObs d) → (Fin d → ℝ)` with
`‖ctxPolicy ξ hist‖₂ ≤ 1`, Algorithm 2 satisfies `E[∑_{t=1}^T ℓ_t] ≤ 12 √d` both as an
unconditional extended Lebesgue integral and (when `AEStronglyMeasurable`) as a Bochner integral. -/
theorem thm_adversarial_contextual_search_rand_ctx (d : ℕ) (hd : 0 < d)
    (zVec : Fin d → ℝ) (hz : vecL2Norm zVec ≤ 1)
    {Ξ : Type*} [MeasurableSpace Ξ]
    (ν_ctx : MeasureTheory.Measure Ξ) [MeasureTheory.IsProbabilityMeasure ν_ctx]
    (ctxPolicy : Ξ → List (SearchObs d) → (Fin d → ℝ))
    (hCtx : ∀ (ξ : Ξ) (hist : List (SearchObs d)), vecL2Norm (ctxPolicy ξ hist) ≤ 1)
    (T : ℕ) :
    let L : Ξ → ℝ := fun ξ => (alg2RunExpected zVec (ctxPolicy ξ) T 0 (alg2InitScale d) []).1
    (∀ ξ : Ξ, 0 ≤ L ξ ∧ L ξ ≤ 12 * Real.sqrt d) ∧
    (∫⁻ ξ, ENNReal.ofReal (L ξ) ∂ν_ctx ≤ ENNReal.ofReal (12 * Real.sqrt d)) ∧
    (MeasureTheory.AEStronglyMeasurable L ν_ctx →
      MeasureTheory.Integrable L ν_ctx ∧
      0 ≤ (∫ ξ, L ξ ∂ν_ctx) ∧
      (∫ ξ, L ξ ∂ν_ctx) ≤ 12 * Real.sqrt d) := by
  dsimp only
  have h_pw : ∀ ξ : Ξ,
      0 ≤ (alg2RunExpected zVec (ctxPolicy ξ) T 0 (alg2InitScale d) []).1 ∧
      (alg2RunExpected zVec (ctxPolicy ξ) T 0 (alg2InitScale d) []).1 ≤ 12 * Real.sqrt d := by
    intro ξ
    have h := thm_adversarial_contextual_search d hd zVec hz (ctxPolicy ξ) (hCtx ξ) T
    exact ⟨h.1, h.2.2.2.2⟩
  have h_exp := prob_expectation_le_of_pointwise ν_ctx _ (12 * Real.sqrt d) h_pw
  exact ⟨h_pw, h_exp.1, h_exp.2⟩

end TraceSqrt
