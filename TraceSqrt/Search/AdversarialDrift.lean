import TraceSqrt.Defs
import TraceSqrt.Search.ScalarPotential

set_option maxHeartbeats 4000000

/-!
# Remark 2.3 & Lemma 2.5: Adversarial Search PD Preservation and Drift (`rem:pd`, `lem:drift`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 2.2 Remark 2.3 and Lemma 2.5, proved in Appendix C.3).
-/

namespace TraceSqrt

/-- **Remark 2.3 (`R_t ≻ 0` throughout execution, `rem:pd`)**:
For any positive-definite matrix `R ≻ 0` and nonzero context `xVec ≠ 0`, setting `u = R xVec`
and `a = xVecᵀ R xVec > 0`:
1. `(vᵀ u)^2 ≤ (vᵀ R v) (xVecᵀ R xVec)` for all `v ∈ ℝ^d` (Cauchy–Schwarz in the `R`-inner product),
2. `R - (4 a)⁻¹ u uᵀ ⪰ (3 / 4) R ≻ 0`, and
3. Both coin realizations `ε ∈ {-1, 1}` of Algorithm 2 satisfy `R_{t+1} ⪰ (3 / 4) R ≻ 0`
   (including when `xVec = 0`). -/
theorem rem_pd {d : ℕ}
    (mVec zVec xVec : Fin d → ℝ)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosDef) :
    (xVec ≠ 0 →
      let u := R.mulVec xVec
      let a := dotProduct xVec u
      0 < a ∧
      (∀ v : Fin d → ℝ, (dotProduct v u) ^ 2 ≤ dotProduct v (R.mulVec v) * a) ∧
      (R - (4 * a)⁻¹ • Matrix.vecMulVec u u - (3 / 4 : ℝ) • R).PosSemidef ∧
      (R - (4 * a)⁻¹ • Matrix.vecMulVec u u).PosDef) ∧
    (∀ eps : ℝ, (eps = -1 ∨ eps = 1) →
      (alg2NextScale mVec R zVec xVec eps).PosDef ∧
      (alg2NextScale mVec R zVec xVec eps - (3 / 4 : ℝ) • R).PosSemidef) :=
by
  have h_outer_herm : ∀ v : Fin d → ℝ, (Matrix.vecMulVec v v).IsHermitian := by
    intro v
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have h_outer_quad :
      ∀ v y : Fin d → ℝ, dotProduct y ((Matrix.vecMulVec v v).mulVec y) = (dotProduct v y) ^ 2 := by
    intro v y
    calc dotProduct y ((Matrix.vecMulVec v v).mulVec y)
        = ∑ i, (v i * y i) * (∑ j, v j * y j) := by
            simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = (∑ i, v i * y i) * (∑ j, v j * y j) := by rw [← Finset.sum_mul]
      _ = (dotProduct v y) ^ 2 := by simp [dotProduct, sq]
  have h_herm_dot :
      ∀ (A : Matrix (Fin d) (Fin d) ℝ), A.IsHermitian →
        ∀ v₁ v₂ : Fin d → ℝ, dotProduct v₁ (A.mulVec v₂) = dotProduct (A.mulVec v₁) v₂ := by
    intro A hA v₁ v₂
    have hA_symm : ∀ i j, A j i = A i j := fun i j => by
      have := congr_fun (congr_fun hA.eq i) j
      simpa [Matrix.conjTranspose_apply] using this
    calc dotProduct v₁ (A.mulVec v₂)
        = ∑ i, ∑ j, v₁ i * (A i j * v₂ j) := by
            simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      _ = ∑ j, ∑ i, v₁ i * (A i j * v₂ j) := Finset.sum_comm
      _ = ∑ j, (∑ i, A j i * v₁ i) * v₂ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hA_symm i j]
            ring
      _ = dotProduct (A.mulVec v₁) v₂ := rfl

  have h_cs_R : ∀ (hx0 : xVec ≠ 0) (y : Fin d → ℝ),
      let u := R.mulVec xVec
      let a := dotProduct xVec u
      (dotProduct y u) ^ 2 ≤ dotProduct y (R.mulVec y) * a := by
    intro hx0 y u a
    have ha_pos : 0 < a := by simpa [a, u] using hR.dotProduct_mulVec_pos hx0
    have ha_ne : a ≠ 0 := ha_pos.ne'
    let c : ℝ := dotProduct u y / a
    let w : Fin d → ℝ := y - c • xVec
    have hw_nonneg : 0 ≤ dotProduct w (R.mulVec w) := by
      simpa using hR.posSemidef.dotProduct_mulVec_nonneg w
    have hx_Ry : dotProduct xVec (R.mulVec y) = dotProduct u y :=
      h_herm_dot R hR.isHermitian xVec y
    have hw_expand :
        dotProduct w (R.mulVec w) = dotProduct y (R.mulVec y) - (dotProduct u y) ^ 2 / a := by
      have hRw : R.mulVec w = R.mulVec y - c • u := by
        simp [w, u, Matrix.mulVec_sub, Matrix.mulVec_smul]
      have hc_mul_a : c * a = dotProduct u y := div_mul_cancel₀ (dotProduct u y) ha_ne
      rw [hRw]
      simp only [w, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, hx_Ry, dotProduct_comm y u, show dotProduct xVec u = a from rfl, hc_mul_a]
      dsimp only [c]
      ring
    have h_div : (dotProduct u y) ^ 2 / a ≤ dotProduct y (R.mulVec y) := by
      linarith [hw_nonneg, hw_expand]
    have h_mul := mul_le_mul_of_nonneg_right h_div ha_pos.le
    have h_cancel : ((dotProduct u y) ^ 2 / a) * a = (dotProduct y u) ^ 2 := by
      rw [div_mul_cancel₀ _ ha_ne, dotProduct_comm u y]
    linarith

  have h_part1 : xVec ≠ 0 →
      let u := R.mulVec xVec
      let a := dotProduct xVec u
      0 < a ∧
      (∀ v : Fin d → ℝ, (dotProduct v u) ^ 2 ≤ dotProduct v (R.mulVec v) * a) ∧
      (R - (4 * a)⁻¹ • Matrix.vecMulVec u u - (3 / 4 : ℝ) • R).PosSemidef ∧
      (R - (4 * a)⁻¹ • Matrix.vecMulVec u u).PosDef := by
    intro hx0 u a
    have ha_pos : 0 < a := by simpa [a, u] using hR.dotProduct_mulVec_pos hx0
    have ha_ne : a ≠ 0 := ha_pos.ne'
    set D := R - (4 * a)⁻¹ • Matrix.vecMulVec u u - (3 / 4 : ℝ) • R
    have hD_eq : D = (1 / 4 : ℝ) • R - (4 * a)⁻¹ • Matrix.vecMulVec u u := by
      ext i j
      dsimp only [D]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hD_herm : D.IsHermitian := by
      rw [hD_eq, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_smul, star_trivial, star_trivial,
          hR.isHermitian.eq, (h_outer_herm u).eq]
    have hD_psd : D.PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hD_herm fun y => ?_
      simp only [star_trivial]
      have hcs := h_cs_R hx0 y
      have h_div : (dotProduct y u) ^ 2 / a ≤ dotProduct y (R.mulVec y) :=
        (div_le_iff₀ ha_pos).mpr hcs
      have hD_quad :
          dotProduct y (D.mulVec y) =
            (1 / 4 : ℝ) * dotProduct y (R.mulVec y) - (1 / 4 : ℝ) * ((dotProduct y u) ^ 2 / a) := by
        rw [hD_eq]
        simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
          smul_eq_mul, h_outer_quad u y, dotProduct_comm u y]
        field_simp
      linarith
    have h_pd : (R - (4 * a)⁻¹ • Matrix.vecMulVec u u).PosDef := by
      have h_decomp : R - (4 * a)⁻¹ • Matrix.vecMulVec u u = D + (3 / 4 : ℝ) • R := by
        dsimp only [D]
        exact (sub_add_cancel _ _).symm
      rw [h_decomp]
      exact Matrix.PosDef.posSemidef_add hD_psd (hR.smul (by norm_num : (0 : ℝ) < 3 / 4))
    exact ⟨ha_pos, h_cs_R hx0, hD_psd, h_pd⟩

  have h_part2 : ∀ eps : ℝ, (eps = -1 ∨ eps = 1) →
      (alg2NextScale mVec R zVec xVec eps).PosDef ∧
      (alg2NextScale mVec R zVec xVec eps - (3 / 4 : ℝ) • R).PosSemidef := by
    intro eps heps
    by_cases hx0 : xVec = 0
    · simp only [alg2NextScale, hx0, ↓reduceIte]
      have h_sub_eq : R - (3 / 4 : ℝ) • R = (1 / 4 : ℝ) • R := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      refine ⟨hR, ?_⟩
      rw [h_sub_eq]
      exact hR.posSemidef.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)
    · obtain ⟨ha_pos, hcs, hD0_psd, _⟩ := h_part1 hx0
      simp only [alg2NextScale, hx0, ↓reduceIte]
      set u := R.mulVec xVec
      set a := dotProduct xVec u
      set P := alg2PostedPrice mVec R xVec eps
      set Y := paperSign (dotProduct xVec zVec - P)
      set s := eps * Y
      set α := s / (a * (3 - s))
      have hs : s = -1 ∨ s = 1 := by
        rcases heps with rfl | rfl <;>
        · by_cases hsign : 0 ≤ dotProduct xVec zVec - P <;>
            simp [s, Y, paperSign, hsign]
      have hα_lb : -((4 * a)⁻¹) ≤ α := by
        rcases hs with hs_neg | hs_pos
        · have h_eq : α = -((4 * a)⁻¹) := by
            dsimp only [α]
            rw [hs_neg]
            field_simp
            ring
          linarith
        · have h1 : (0 : ℝ) ≤ α := by
            dsimp only [α]
            rw [hs_pos]
            norm_num
            positivity
          have h2 : (0 : ℝ) ≤ (4 * a)⁻¹ := by positivity
          linarith
      set D := R + α • Matrix.vecMulVec u u - (3 / 4 : ℝ) • R
      have hD_diff : D = (R - (4 * a)⁻¹ • Matrix.vecMulVec u u - (3 / 4 : ℝ) • R) +
          (α + (4 * a)⁻¹) • Matrix.vecMulVec u u := by
        ext i j
        dsimp only [D]
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      have huu_psd : (Matrix.vecMulVec u u).PosSemidef := by
        refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (h_outer_herm u) fun y => ?_
        simp only [star_trivial, h_outer_quad u y]
        exact sq_nonneg _
      have hD_psd : D.PosSemidef := by
        rw [hD_diff]
        exact hD0_psd.add (huu_psd.smul (by linarith))
      have h_scale_pd : (R + α • Matrix.vecMulVec u u).PosDef := by
        have h_decomp : R + α • Matrix.vecMulVec u u = D + (3 / 4 : ℝ) • R := by
          dsimp only [D]
          exact (sub_add_cancel _ _).symm
        rw [h_decomp]
        exact Matrix.PosDef.posSemidef_add hD_psd (hR.smul (by norm_num : (0 : ℝ) < 3 / 4))
      exact ⟨h_scale_pd, hD_psd⟩

  exact ⟨h_part1, h_part2⟩

/-- **Lemma 2.5 (One-round potential decrease, `lem:drift`)**:
For any state `(mVec, R)` with `R ≻ 0`, hidden target `zVec ∈ ℝ^d`, and context `xVec` with
`‖xVec‖₂ ≤ 1`:
1. Both coin realizations `ε ∈ {-1, 1}` preserve `R_{t+1} ⪰ (3/4) R ≻ 0` (Remark 2.3),
2. `Φ(mVec, R, zVec) ≥ 0`, and
3. `E_ε |xVecᵀ zVec - P_t| ≤ 6 (Φ(mVec, R, zVec) - E_ε Φ(m_{t+1}, R_{t+1}, zVec))`. -/
theorem lem_drift {d : ℕ}
    (mVec zVec xVec : Fin d → ℝ) (hx : vecL2Norm xVec ≤ 1)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosDef) :
    (∀ eps : ℝ, (eps = -1 ∨ eps = 1) →
      (alg2NextScale mVec R zVec xVec eps).PosDef ∧
      (alg2NextScale mVec R zVec xVec eps - (3 / 4 : ℝ) • R).PosSemidef) ∧
    0 ≤ quadPotential mVec R zVec ∧
    rademacherExpect (fun eps => |dotProduct xVec zVec - alg2PostedPrice mVec R xVec eps|) ≤
      6 * (quadPotential mVec R zVec -
        rademacherExpect (fun eps =>
          quadPotential
            (alg2NextCenter mVec R zVec xVec eps)
            (alg2NextScale mVec R zVec xVec eps)
            zVec)) :=
by
  have h_norm_nonneg : ∀ v : Fin d → ℝ, 0 ≤ vecL2Norm v :=
    fun v => Real.sqrt_nonneg _
  have h_norm_sq : ∀ v : Fin d → ℝ, vecL2Norm v ^ 2 = ∑ i, (v i) ^ 2 :=
    fun v => Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))
  have h_cs : ∀ v₁ v₂ : Fin d → ℝ, dotProduct v₁ v₂ ≤ vecL2Norm v₁ * vecL2Norm v₂ :=
    fun v₁ v₂ => Real.sum_mul_le_sqrt_mul_sqrt Finset.univ v₁ v₂
  have h_outer_quad :
      ∀ v y : Fin d → ℝ, dotProduct y ((Matrix.vecMulVec v v).mulVec y) = (dotProduct v y) ^ 2 := by
    intro v y
    calc dotProduct y ((Matrix.vecMulVec v v).mulVec y)
        = ∑ i, (v i * y i) * (∑ j, v j * y j) := by
            simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = (∑ i, v i * y i) * (∑ j, v j * y j) := by rw [← Finset.sum_mul]
      _ = (dotProduct v y) ^ 2 := by simp [dotProduct, sq]
  have h_herm_dot :
      ∀ (A : Matrix (Fin d) (Fin d) ℝ), A.IsHermitian →
        ∀ v₁ v₂ : Fin d → ℝ, dotProduct v₁ (A.mulVec v₂) = dotProduct (A.mulVec v₁) v₂ := by
    intro A hA v₁ v₂
    have hA_symm : ∀ i j, A j i = A i j := fun i j => by
      have := congr_fun (congr_fun hA.eq i) j
      simpa [Matrix.conjTranspose_apply] using this
    calc dotProduct v₁ (A.mulVec v₂)
        = ∑ i, ∑ j, v₁ i * (A i j * v₂ j) := by
            simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      _ = ∑ j, ∑ i, v₁ i * (A i j * v₂ j) := Finset.sum_comm
      _ = ∑ j, (∑ i, A j i * v₁ i) * v₂ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hA_symm i j]
            ring
      _ = dotProduct (A.mulVec v₁) v₂ := rfl

  have h_conj1 := (rem_pd mVec zVec xVec R hR).2

  have h_conj2 : 0 ≤ quadPotential mVec R zVec := by
    unfold quadPotential
    have h1 : 0 ≤ Matrix.trace R := hR.posSemidef.trace_nonneg
    have h2 : 0 ≤ dotProduct (zVec - mVec) (R⁻¹.mulVec (zVec - mVec)) := by
      simpa using hR.inv.posSemidef.dotProduct_mulVec_nonneg (zVec - mVec)
    exact add_nonneg h1 h2

  have h_rank_one_diff :
      ∀ (hx0 : xVec ≠ 0) (eps : ℝ), (eps = -1 ∨ eps = 1) →
        let u := R.mulVec xVec
        let a := dotProduct xVec u
        let r := vecL2Norm u
        let m := dotProduct xVec mVec
        let z := dotProduct xVec zVec
        let P := m + (r / 2) * eps
        let Y := paperSign (z - P)
        let mNext := m + r * Y / (3 - eps * Y)
        let rNext := 3 * r / (3 - eps * Y)
        quadPotential (alg2NextCenter mVec R zVec xVec eps)
            (alg2NextScale mVec R zVec xVec eps) zVec -
          quadPotential mVec R zVec =
        (r / a) * ((rNext + (mNext - z) ^ 2 / rNext) - (r + (m - z) ^ 2 / r)) := by
    intro hx0 eps heps
    dsimp only
    set u := R.mulVec xVec
    set a := dotProduct xVec u
    set r := vecL2Norm u
    set m := dotProduct xVec mVec
    set z := dotProduct xVec zVec
    set P := m + (r / 2) * eps
    set Y := paperSign (z - P)
    set s := eps * Y
    set δ := r * Y / (3 - s)
    set mNext := m + δ
    set rNext := 3 * r / (3 - s)
    have ha_pos : 0 < a := by simpa [a, u] using hR.dotProduct_mulVec_pos hx0
    have ha_ne : a ≠ 0 := ha_pos.ne'
    have hr_pos : 0 < r := by
      have hcs : a ≤ vecL2Norm xVec * r := h_cs xVec u
      nlinarith [h_norm_nonneg xVec, h_norm_nonneg u]
    have hr_ne : r ≠ 0 := hr_pos.ne'
    have hs_cases : s = -1 ∨ s = 1 := by
      rcases heps with rfl | rfl <;>
      · by_cases hsign : 0 ≤ z - P <;>
          simp [s, Y, paperSign, hsign]
    have h3s_pos : 0 < 3 - s := by
      rcases hs_cases with hs1 | hs1 <;> linarith
    have h3s_ne : 3 - s ≠ 0 := h3s_pos.ne'
    have h3r_ne : 3 * r ≠ 0 := mul_ne_zero (by norm_num) hr_ne
    have hP_eq : alg2PostedPrice mVec R xVec eps = P := by
      simp [alg2PostedPrice, hx0, P, m, r, u]
    have h_center_eq : alg2NextCenter mVec R zVec xVec eps = mVec + (δ / a) • u := by
      simp only [alg2NextCenter, hx0, ↓reduceIte, hP_eq]
      congr 1
      congr 1
      change Y * r / (a * (3 - s)) = δ / a
      dsimp only [δ]
      field_simp
    set c₁ := s / (a * (3 - s))
    have h_scale_eq : alg2NextScale mVec R zVec xVec eps = R + c₁ • Matrix.vecMulVec u u := by
      simp only [alg2NextScale, hx0, ↓reduceIte, hP_eq]
      rfl
    have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
    have hRRinv : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hdet
    have hRinvR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hdet
    have hRinv_u : R⁻¹.mulVec u = xVec := by
      simp [u, Matrix.mulVec_mulVec, hRinvR]
    have hRinv_symm : ∀ i j, R⁻¹ i j = R⁻¹ j i := fun i j => by
      have := congr_fun (congr_fun hR.inv.isHermitian.eq j) i
      simpa [Matrix.conjTranspose_apply] using this
    have h_prod1 : R * Matrix.vecMulVec xVec xVec = Matrix.vecMulVec u xVec := by
      ext i j
      calc (R * Matrix.vecMulVec xVec xVec) i j
          = ∑ k, (R i k * xVec k) * xVec j := by
              simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
              refine Finset.sum_congr rfl fun k _ => by ring
        _ = (∑ k, R i k * xVec k) * xVec j := by rw [← Finset.sum_mul]
        _ = (Matrix.vecMulVec u xVec) i j := by
              simp [Matrix.vecMulVec_apply, u, Matrix.mulVec, dotProduct]
    have h_prod2 : Matrix.vecMulVec u u * R⁻¹ = Matrix.vecMulVec u xVec := by
      ext i j
      calc (Matrix.vecMulVec u u * R⁻¹) i j
          = ∑ k, u i * (R⁻¹ j k * u k) := by
              simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
              refine Finset.sum_congr rfl fun k _ => by
                rw [hRinv_symm k j]
                ring
        _ = u i * (∑ k, R⁻¹ j k * u k) := by rw [← Finset.mul_sum]
        _ = u i * (R⁻¹.mulVec u) j := rfl
        _ = (Matrix.vecMulVec u xVec) i j := by
              rw [hRinv_u]
              simp [Matrix.vecMulVec_apply]
    have h_prod3 :
        Matrix.vecMulVec u u * Matrix.vecMulVec xVec xVec = a • Matrix.vecMulVec u xVec := by
      ext i j
      calc (Matrix.vecMulVec u u * Matrix.vecMulVec xVec xVec) i j
          = ∑ k, (xVec k * u k) * (u i * xVec j) := by
              simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
              refine Finset.sum_congr rfl fun k _ => by ring
        _ = (∑ k, xVec k * u k) * (u i * xVec j) := by rw [← Finset.sum_mul]
        _ = (a • Matrix.vecMulVec u xVec) i j := by
              simp [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, a, dotProduct]
    set c₂ := s / (3 * a)
    set RNext := R + c₁ • Matrix.vecMulVec u u
    set B := R⁻¹ - c₂ • Matrix.vecMulVec xVec xVec
    have h_coeff_zero : -c₂ + c₁ - c₁ * c₂ * a = 0 := by
      dsimp only [c₁, c₂]
      field_simp
      ring
    have h_RNext_mul_B : RNext * B = 1 := by
      have hexp :
          RNext * B =
            1 - c₂ • Matrix.vecMulVec u xVec +
               (c₁ • Matrix.vecMulVec u xVec - c₁ • (c₂ • (a • Matrix.vecMulVec u xVec))) := by
        dsimp only [RNext, B]
        rw [add_mul, mul_sub, mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
            Matrix.mul_smul, hRRinv, h_prod1, h_prod2, h_prod3]
      rw [hexp]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      calc (1 : Matrix (Fin d) (Fin d) ℝ) i j - c₂ * Matrix.vecMulVec u xVec i j +
            (c₁ * Matrix.vecMulVec u xVec i j - c₁ * (c₂ * (a * Matrix.vecMulVec u xVec i j)))
          = (1 : Matrix (Fin d) (Fin d) ℝ) i j +
            (-c₂ + c₁ - c₁ * c₂ * a) * Matrix.vecMulVec u xVec i j := by ring
        _ = (1 : Matrix (Fin d) (Fin d) ℝ) i j := by rw [h_coeff_zero, zero_mul, add_zero]
    have h_RNext_inv : RNext⁻¹ = B := Matrix.inv_eq_right_inv h_RNext_mul_B
    have h_outer_u_trace : Matrix.trace (Matrix.vecMulVec u u) = r ^ 2 := by
      calc Matrix.trace (Matrix.vecMulVec u u)
          = ∑ i, (u i) ^ 2 := by
              simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, sq]
        _ = r ^ 2 := (h_norm_sq u).symm
    have h_trace_diff : Matrix.trace RNext - Matrix.trace R = (r / a) * (rNext - r) := by
      calc Matrix.trace RNext - Matrix.trace R
          = c₁ * r ^ 2 := by
              dsimp only [RNext]
              rw [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, h_outer_u_trace]
              ring
        _ = (r / a) * (rNext - r) := by
              dsimp only [c₁, rNext]
              field_simp
              ring
    set w := zVec - mVec
    set mVecNext := mVec + (δ / a) • u
    set wNext := zVec - mVecNext
    have hwNext_eq : wNext = w - (δ / a) • u := by
      ext i
      simp only [wNext, mVecNext, w, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h_xw : dotProduct xVec w = z - m := by
      simp [w, z, m, dotProduct_sub]
    have h_xwNext : dotProduct xVec wNext = z - m - δ := by
      rw [hwNext_eq]
      simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, h_xw,
        show dotProduct xVec u = a from rfl]
      have h_cancel : (δ / a) * a = δ := div_mul_cancel₀ δ ha_ne
      linarith
    have h_quad_B :
        dotProduct wNext (RNext⁻¹.mulVec wNext) =
          dotProduct wNext (R⁻¹.mulVec wNext) - c₂ * (z - m - δ) ^ 2 := by
      rw [h_RNext_inv]
      dsimp only [B]
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
        smul_eq_mul, h_outer_quad xVec wNext, h_xwNext]
    have h_u_Rinv_w : dotProduct u (R⁻¹.mulVec w) = z - m := by
      calc dotProduct u (R⁻¹.mulVec w)
          = dotProduct (R⁻¹.mulVec u) w := h_herm_dot R⁻¹ hR.inv.isHermitian u w
        _ = dotProduct xVec w := by rw [hRinv_u]
        _ = z - m := h_xw
    have h_quad_Rinv :
        dotProduct wNext (R⁻¹.mulVec wNext) =
          dotProduct w (R⁻¹.mulVec w) - 2 * (δ / a) * (z - m) + δ ^ 2 / a := by
      have hRinv_wNext : R⁻¹.mulVec wNext = R⁻¹.mulVec w - (δ / a) • xVec := by
        rw [hwNext_eq, Matrix.mulVec_sub, Matrix.mulVec_smul, hRinv_u]
      rw [hRinv_wNext, hwNext_eq]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        dotProduct_comm w xVec, h_xw, h_u_Rinv_w, dotProduct_comm u xVec,
        show dotProduct xVec u = a from rfl]
      field_simp
      ring
    have h_quad_diff :
        dotProduct wNext (RNext⁻¹.mulVec wNext) - dotProduct w (R⁻¹.mulVec w) =
          (r / a) * ((mNext - z) ^ 2 / rNext - (m - z) ^ 2 / r) := by
      have h_lhs :
          dotProduct wNext (RNext⁻¹.mulVec wNext) - dotProduct w (R⁻¹.mulVec w) =
            -2 * (δ / a) * (z - m) + δ ^ 2 / a - c₂ * (z - m - δ) ^ 2 := by
        linarith [h_quad_B, h_quad_Rinv]
      rw [h_lhs]
      dsimp only [c₂, mNext, rNext]
      field_simp
      ring
    unfold quadPotential
    rw [h_center_eq, h_scale_eq]
    change (Matrix.trace RNext + dotProduct wNext (RNext⁻¹.mulVec wNext)) -
        (Matrix.trace R + dotProduct w (R⁻¹.mulVec w)) =
      (r / a) * ((rNext + (mNext - z) ^ 2 / rNext) - (r + (m - z) ^ 2 / r))
    linarith [h_trace_diff, h_quad_diff]

  have h_scalar_drift :
      ∀ (m r z : ℝ), 0 < r →
        rademacherExpect (fun eps => |z - (m + (r / 2) * eps)|) ≤
          6 * ((r + (m - z) ^ 2 / r) -
            rademacherExpect (fun eps =>
              let P := m + (r / 2) * eps
              let Y := paperSign (z - P)
              let mNext := m + r * Y / (3 - eps * Y)
              let rNext := 3 * r / (3 - eps * Y)
              rNext + (mNext - z) ^ 2 / rNext)) := by
    intro m r z hr
    have h := (lem_scalar_potential m r z hr).2.1
    unfold rademacherExpect scalarPotential scalarUpdatedCenter
      scalarUpdatedScale scalarFeedback scalarPostedPrice at h
    unfold rademacherExpect
    dsimp only at h ⊢
    linarith

  have h_conj3 :
      rademacherExpect (fun eps => |dotProduct xVec zVec - alg2PostedPrice mVec R xVec eps|) ≤
        6 * (quadPotential mVec R zVec -
          rademacherExpect (fun eps =>
            quadPotential
              (alg2NextCenter mVec R zVec xVec eps)
              (alg2NextScale mVec R zVec xVec eps)
              zVec)) := by
    by_cases hx0 : xVec = 0
    · simp only [hx0, zero_dotProduct, alg2PostedPrice, alg2NextCenter, alg2NextScale,
        ↓reduceIte, rademacherExpect, sub_self, abs_zero]
      linarith
    · set u := R.mulVec xVec
      set a := dotProduct xVec u
      set r := vecL2Norm u
      set m := dotProduct xVec mVec
      set z := dotProduct xVec zVec
      have ha_pos : 0 < a := by simpa [a, u] using hR.dotProduct_mulVec_pos hx0
      have ha_le_r : a ≤ r := by
        have hcs : a ≤ vecL2Norm xVec * r := h_cs xVec u
        nlinarith [hx, h_norm_nonneg xVec, h_norm_nonneg u]
      have hr_pos : 0 < r := lt_of_lt_of_le ha_pos ha_le_r
      have h_lhs_eq :
          rademacherExpect (fun eps => |dotProduct xVec zVec - alg2PostedPrice mVec R xVec eps|) =
            rademacherExpect (fun eps => |z - (m + (r / 2) * eps)|) := by
        simp [alg2PostedPrice, hx0, m, z, r, u]
      have h_lhs_nonneg :
          0 ≤ rademacherExpect (fun eps => |z - (m + (r / 2) * eps)|) := by
        unfold rademacherExpect
        positivity
      let φ₀ : ℝ := r + (m - z) ^ 2 / r
      let φNext : ℝ → ℝ := fun eps =>
        let P := m + (r / 2) * eps
        let Y := paperSign (z - P)
        let mNext := m + r * Y / (3 - eps * Y)
        let rNext := 3 * r / (3 - eps * Y)
        rNext + (mNext - z) ^ 2 / rNext
      have h_diff_neg :
          quadPotential (alg2NextCenter mVec R zVec xVec (-1))
              (alg2NextScale mVec R zVec xVec (-1)) zVec -
            quadPotential mVec R zVec =
          (r / a) * (φNext (-1) - φ₀) :=
        h_rank_one_diff hx0 (-1) (Or.inl rfl)
      have h_diff_pos :
          quadPotential (alg2NextCenter mVec R zVec xVec 1)
              (alg2NextScale mVec R zVec xVec 1) zVec -
            quadPotential mVec R zVec =
          (r / a) * (φNext 1 - φ₀) :=
        h_rank_one_diff hx0 1 (Or.inr rfl)
      have h_expect_diff :
          quadPotential mVec R zVec -
            rademacherExpect (fun eps =>
              quadPotential
                (alg2NextCenter mVec R zVec xVec eps)
                (alg2NextScale mVec R zVec xVec eps)
                zVec) =
          (r / a) * (φ₀ - rademacherExpect φNext) := by
        unfold rademacherExpect
        dsimp only
        linarith [h_diff_neg, h_diff_pos]
      have h_1d :
          rademacherExpect (fun eps => |z - (m + (r / 2) * eps)|) ≤
            6 * (φ₀ - rademacherExpect φNext) :=
        h_scalar_drift m r z hr_pos
      have h_drop_nonneg : 0 ≤ φ₀ - rademacherExpect φNext := by
        linarith [h_lhs_nonneg, h_1d]
      have h_one_le_ra : 1 ≤ r / a := (one_le_div₀ ha_pos).mpr ha_le_r
      have h_amp :
          φ₀ - rademacherExpect φNext ≤ (r / a) * (φ₀ - rademacherExpect φNext) := by
        have h_mul := mul_le_mul_of_nonneg_right h_one_le_ra h_drop_nonneg
        linarith
      rw [h_lhs_eq, h_expect_diff]
      linarith

  exact ⟨h_conj1, h_conj2, h_conj3⟩

/-- Alias for `lem_drift`. -/
alias lem_adversarial_drift := lem_drift

end TraceSqrt
