import TraceSqrt.Defs

set_option maxHeartbeats 4000000

/-!
# Lemma 3.3: Existence of a Valid Grid-Priced Trade Lottery (`lem:trade-lottery`)
From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Section 3.2 Lemma 3.3 `lem:trade-lottery`, proved in Appendix D.2).
-/

namespace TraceSqrt

/-- Unnormalized finite weighted standard deviation `√((∑_A w_k)(∑_A w_k Z_k^2) - (∑_A w_k Z_k)^2)`. -/
noncomputable def finWeightedStdDev {K : ℕ}
    (w : Fin K → ℝ) (A : Finset (Fin K)) (Z : Fin K → ℝ) : ℝ :=
  Real.sqrt ((∑ k ∈ A, w k) * (∑ k ∈ A, w k * (Z k) ^ 2) - (∑ k ∈ A, w k * Z k) ^ 2)

theorem lem_scalar_trade_or_info {K : ℕ}
    (w : Fin K → ℝ) (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1)
    (S B : Fin K → ℝ) :
    ∃ p : ℝ,
      let E := Finset.univ.filter (fun k => S k ≤ p ∧ p ≤ B k)
      let Ec := Finset.univ \ E
      ∑ k ∈ Ec, w k * max (B k - S k) 0 ≤
        2048 * ((finWeightedStdDev w Finset.univ S -
                  finWeightedStdDev w E S -
                  finWeightedStdDev w Ec S) +
                (finWeightedStdDev w Finset.univ B -
                  finWeightedStdDev w E B -
                  finWeightedStdDev w Ec B)) :=
by
  
  have h_wsd_sq : ∀ (Z : Fin K → ℝ) (A : Finset (Fin K)),
      let μZ := ∑ k, w k * Z k
      (finWeightedStdDev w A Z) ^ 2 =
        (∑ k ∈ A, w k) * (∑ k ∈ A, w k * (Z k - μZ) ^ 2) -
          (∑ k ∈ A, w k * (Z k - μZ)) ^ 2 := by
    intro Z A μZ
    set qA : ℝ := ∑ k ∈ A, w k
    set mA : ℝ := ∑ k ∈ A, w k * (Z k - μZ)
    set vA : ℝ := ∑ k ∈ A, w k * (Z k - μZ) ^ 2
    have h_sum1 : ∑ k ∈ A, w k * Z k = mA + qA * μZ := by
      have h1 : ∀ k : Fin K, w k * Z k = w k * (Z k - μZ) + w k * μZ := fun _ => by ring
      simp_rw [h1, Finset.sum_add_distrib, ← Finset.sum_mul]
      rfl
    have h_sum2 : ∑ k ∈ A, w k * (Z k) ^ 2 = vA + 2 * μZ * mA + qA * μZ ^ 2 := by
      have h2 : ∀ k : Fin K, w k * (Z k) ^ 2 =
          (w k * (Z k - μZ) ^ 2 + 2 * μZ * (w k * (Z k - μZ))) + w k * μZ ^ 2 := fun _ => by ring
      simp_rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rfl
    have h_rad_eq : qA * (∑ k ∈ A, w k * (Z k) ^ 2) - (∑ k ∈ A, w k * Z k) ^ 2 =
        qA * vA - mA ^ 2 := by
      rw [h_sum1, h_sum2]
      ring
    have h_cs : mA ^ 2 ≤ qA * vA := by
      have h_ineq := Finset.sum_mul_sq_le_sq_mul_sq A
        (fun k => Real.sqrt (w k)) (fun k => Real.sqrt (w k) * (Z k - μZ))
      have h_lhs : (∑ k ∈ A, Real.sqrt (w k) * (Real.sqrt (w k) * (Z k - μZ))) = mA := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← mul_assoc, Real.mul_self_sqrt (hw_nn k)]
      have h_rhs1 : (∑ k ∈ A, (Real.sqrt (w k)) ^ 2) = qA :=
        Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (hw_nn k))
      have h_rhs2 : (∑ k ∈ A, (Real.sqrt (w k) * (Z k - μZ)) ^ 2) = vA := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [mul_pow, Real.sq_sqrt (hw_nn k)]
      rwa [h_lhs, h_rhs1, h_rhs2] at h_ineq
    unfold finWeightedStdDev
    change (Real.sqrt (qA * (∑ k ∈ A, w k * (Z k) ^ 2) - (∑ k ∈ A, w k * Z k) ^ 2)) ^ 2 =
      qA * vA - mA ^ 2
    rw [h_rad_eq]
    exact Real.sq_sqrt (sub_nonneg.mpr h_cs)

  have h_univ_sq : ∀ (Z : Fin K → ℝ),
      let μZ := ∑ k, w k * Z k
      (finWeightedStdDev w Finset.univ Z) ^ 2 = ∑ k, w k * (Z k - μZ) ^ 2 := by
    intro Z μZ
    have h1 := h_wsd_sq Z Finset.univ
    dsimp only at h1
    have hm0 : ∑ k, w k * (Z k - μZ) = 0 := by
      have h_sub : ∀ k : Fin K, w k * (Z k - μZ) = w k * Z k - w k * μZ := fun _ => by ring
      simp_rw [h_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum, one_mul]
      exact sub_self μZ
    rw [h1, hw_sum, one_mul, hm0]
    ring

  have h_l1_le : ∀ (Z : Fin K → ℝ),
      ∑ k, w k * |Z k - ∑ j, w j * Z j| ≤ finWeightedStdDev w Finset.univ Z := by
    intro Z
    set μZ : ℝ := ∑ j, w j * Z j
    set σZ : ℝ := finWeightedStdDev w Finset.univ Z
    set M1 : ℝ := ∑ k, w k * |Z k - μZ|
    have hM1_nn : 0 ≤ M1 := Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nn k) (abs_nonneg _))
    have hσZ_nn : 0 ≤ σZ := Real.sqrt_nonneg _
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k => Real.sqrt (w k)) (fun k => Real.sqrt (w k) * |Z k - μZ|)
    have h_lhs : (∑ k, Real.sqrt (w k) * (Real.sqrt (w k) * |Z k - μZ|)) = M1 := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← mul_assoc, Real.mul_self_sqrt (hw_nn k)]
    have h_rhs1 : (∑ k, (Real.sqrt (w k)) ^ 2) = 1 := by
      rw [← hw_sum]
      exact Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (hw_nn k))
    have h_rhs2 : (∑ k, (Real.sqrt (w k) * |Z k - μZ|) ^ 2) = σZ ^ 2 := by
      rw [h_univ_sq Z]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [mul_pow, Real.sq_sqrt (hw_nn k), sq_abs]
    rw [h_lhs, h_rhs1, h_rhs2, one_mul] at h_cs
    nlinarith

  have h_zero_const : ∀ (Z : Fin K → ℝ),
      finWeightedStdDev w Finset.univ Z = 0 → ∀ k, w k = 0 ∨ Z k = ∑ j, w j * Z j := by
    intro Z h0 k
    set μZ : ℝ := ∑ j, w j * Z j
    have h_sum0 : ∑ i, w i * (Z i - μZ) ^ 2 = 0 := by
      have hsq := h_univ_sq Z
      dsimp only at hsq
      rw [← hsq, h0]
      ring
    have h_term0 : w k * (Z k - μZ) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw_nn i) (sq_nonneg _))).mp
        h_sum0 k (Finset.mem_univ k)
    rcases mul_eq_zero.mp h_term0 with hwk | hzk
    · exact Or.inl hwk
    · exact Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp hzk))

  have h_drop : ∀ (Z : Fin K → ℝ) (E : Finset (Fin K)),
      let μZ := ∑ j, w j * Z j
      let σZ := finWeightedStdDev w Finset.univ Z
      let Ec := Finset.univ \ E
      let d := σZ - finWeightedStdDev w E Z - finWeightedStdDev w Ec Z
      (0 ≤ d ∧ d ≤ σZ) ∧
      (∑ k ∈ E, w k * (Z k - μZ)) ^ 2 ≤ 2 * (∑ k ∈ E, w k) * σZ * d ∧
      (Real.sqrt (∑ k ∈ E, w k) * σZ -
        Real.sqrt (∑ k ∈ E, w k * (Z k - μZ) ^ 2)) ^ 2 ≤ 2 * σZ * d := by
    intro Z E μZ σZ Ec d
    set q1 : ℝ := ∑ k ∈ E, w k
    set q0 : ℝ := ∑ k ∈ Ec, w k
    set m1 : ℝ := ∑ k ∈ E, w k * (Z k - μZ)
    set m0 : ℝ := ∑ k ∈ Ec, w k * (Z k - μZ)
    set v1 : ℝ := ∑ k ∈ E, w k * (Z k - μZ) ^ 2
    set v0 : ℝ := ∑ k ∈ Ec, w k * (Z k - μZ) ^ 2
    set s1 : ℝ := finWeightedStdDev w E Z
    set s0 : ℝ := finWeightedStdDev w Ec Z
    have hσZ_nn : 0 ≤ σZ := Real.sqrt_nonneg _
    have hq1_nn : 0 ≤ q1 := Finset.sum_nonneg (fun k _ => hw_nn k)
    have hq0_nn : 0 ≤ q0 := Finset.sum_nonneg (fun k _ => hw_nn k)
    have hv1_nn : 0 ≤ v1 := Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nn k) (sq_nonneg _))
    have hv0_nn : 0 ≤ v0 := Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nn k) (sq_nonneg _))
    have hs1_nn : 0 ≤ s1 := Real.sqrt_nonneg _
    have hs0_nn : 0 ≤ s0 := Real.sqrt_nonneg _
    have hq_sum : q0 + q1 = 1 := by
      dsimp only [q0, q1, Ec]
      rw [Finset.sum_sdiff (Finset.subset_univ E), hw_sum]
    have hv_sum : v0 + v1 = σZ ^ 2 := by
      dsimp only [v0, v1, Ec, σZ]
      rw [Finset.sum_sdiff (Finset.subset_univ E), ← h_univ_sq Z]
    have hs1_sq : s1 ^ 2 = q1 * v1 - m1 ^ 2 := h_wsd_sq Z E
    have hs0_sq : s0 ^ 2 = q0 * v0 - m0 ^ 2 := h_wsd_sq Z Ec
    set rq1 : ℝ := Real.sqrt q1
    set rv1 : ℝ := Real.sqrt v1
    set rq0 : ℝ := Real.sqrt q0
    set rv0 : ℝ := Real.sqrt v0
    have hrq1_nn : 0 ≤ rq1 := Real.sqrt_nonneg _
    have hrv1_nn : 0 ≤ rv1 := Real.sqrt_nonneg _
    have hrq0_nn : 0 ≤ rq0 := Real.sqrt_nonneg _
    have hrv0_nn : 0 ≤ rv0 := Real.sqrt_nonneg _
    have hrq1_sq : rq1 ^ 2 = q1 := Real.sq_sqrt hq1_nn
    have hrv1_sq : rv1 ^ 2 = v1 := Real.sq_sqrt hv1_nn
    have hrq0_sq : rq0 ^ 2 = q0 := Real.sq_sqrt hq0_nn
    have hrv0_sq : rv0 ^ 2 = v0 := Real.sq_sqrt hv0_nn
    have hs1_le : s1 ≤ rq1 * rv1 := by
      have h_sq : s1 ^ 2 ≤ (rq1 * rv1) ^ 2 := by
        calc s1 ^ 2 = q1 * v1 - m1 ^ 2 := hs1_sq
          _ ≤ q1 * v1 := by linarith [sq_nonneg m1]
          _ = rq1 ^ 2 * rv1 ^ 2 := by rw [hrq1_sq, hrv1_sq]
          _ = (rq1 * rv1) ^ 2 := by ring
      nlinarith [mul_nonneg hrq1_nn hrv1_nn]
    have hs0_le : s0 ≤ rq0 * rv0 := by
      have h_sq : s0 ^ 2 ≤ (rq0 * rv0) ^ 2 := by
        calc s0 ^ 2 = q0 * v0 - m0 ^ 2 := hs0_sq
          _ ≤ q0 * v0 := by linarith [sq_nonneg m0]
          _ = rq0 ^ 2 * rv0 ^ 2 := by rw [hrq0_sq, hrv0_sq]
          _ = (rq0 * rv0) ^ 2 := by ring
      nlinarith [mul_nonneg hrq0_nn hrv0_nn]
    have hd_le : d ≤ σZ := by
      change σZ - s1 - s0 ≤ σZ
      linarith
    have hd_nn : 0 ≤ d := by
      have h_lagrange : (rq1 * rv1 + rq0 * rv0) ^ 2 ≤ σZ ^ 2 := by
        have h_id : (rq1 * rv1 + rq0 * rv0) ^ 2 + (rq1 * rv0 - rq0 * rv1) ^ 2 =
            (rq1 ^ 2 + rq0 ^ 2) * (rv1 ^ 2 + rv0 ^ 2) := by ring
        rw [hrq1_sq, hrq0_sq, hrv1_sq, hrv0_sq] at h_id
        have h_prod : (q1 + q0) * (v1 + v0) = σZ ^ 2 := by
          rw [add_comm q1 q0, hq_sum, add_comm v1 v0, hv_sum, one_mul]
        linarith [sq_nonneg (rq1 * rv0 - rq0 * rv1)]
      have h_sum_nn : 0 ≤ rq1 * rv1 + rq0 * rv0 :=
        add_nonneg (mul_nonneg hrq1_nn hrv1_nn) (mul_nonneg hrq0_nn hrv0_nn)
      have h_sum_le : rq1 * rv1 + rq0 * rv0 ≤ σZ := by nlinarith
      change 0 ≤ σZ - s1 - s0
      linarith
    have h_master : q1 * σZ ^ 2 - 2 * σZ * s1 + v1 ≤ 2 * σZ * d := by
      have h_amgm0 : 2 * σZ * (rq0 * rv0) ≤ q0 * σZ ^ 2 + v0 := by
        have h_exp0 : (rq0 * σZ - rv0) ^ 2 =
            rq0 ^ 2 * σZ ^ 2 - 2 * σZ * (rq0 * rv0) + rv0 ^ 2 := by ring
        rw [hrq0_sq, hrv0_sq] at h_exp0
        linarith [sq_nonneg (rq0 * σZ - rv0)]
      have h_mul0 : 2 * σZ * s0 ≤ 2 * σZ * (rq0 * rv0) := by
        nlinarith [hσZ_nn, hs0_le]
      have h_2sd : 2 * σZ * d =
          (q0 + q1) * σZ ^ 2 + (v0 + v1) - 2 * σZ * s1 - 2 * σZ * s0 := by
        calc 2 * σZ * d
            = 1 * σZ ^ 2 + σZ ^ 2 - 2 * σZ * s1 - 2 * σZ * s0 := by
                change 2 * σZ * (σZ - s1 - s0) = _
                ring
          _ = (q0 + q1) * σZ ^ 2 + (v0 + v1) - 2 * σZ * s1 - 2 * σZ * s0 := by
                rw [hq_sum, hv_sum]
      linarith
    have h_rad : (rq1 * σZ - rv1) ^ 2 ≤ 2 * σZ * d := by
      have h_exp1 : (rq1 * σZ - rv1) ^ 2 = q1 * σZ ^ 2 - 2 * σZ * (rq1 * rv1) + v1 := by
        calc (rq1 * σZ - rv1) ^ 2
            = rq1 ^ 2 * σZ ^ 2 - 2 * σZ * (rq1 * rv1) + rv1 ^ 2 := by ring
          _ = q1 * σZ ^ 2 - 2 * σZ * (rq1 * rv1) + v1 := by rw [hrq1_sq, hrv1_sq]
      have h_mul1 : 2 * σZ * s1 ≤ 2 * σZ * (rq1 * rv1) := by
        nlinarith [hσZ_nn, hs1_le]
      linarith
    have h_mean : m1 ^ 2 ≤ 2 * q1 * σZ * d := by
      have h_mulq : q1 * (q1 * σZ ^ 2 - 2 * σZ * s1 + v1) ≤ q1 * (2 * σZ * d) :=
        mul_le_mul_of_nonneg_left h_master hq1_nn
      have h_id1 : q1 * (q1 * σZ ^ 2 - 2 * σZ * s1 + v1) =
          (q1 * σZ - s1) ^ 2 + m1 ^ 2 := by
        linear_combination -hs1_sq
      nlinarith [sq_nonneg (q1 * σZ - s1)]
    exact ⟨⟨hd_nn, hd_le⟩, h_mean, h_rad⟩

  
  have h_halfline : ∀ (U V : Fin K → ℝ) (σU D : ℝ),
      0 ≤ σU → 0 ≤ D →
      let μU := ∑ k, w k * U k
      let E : ℝ → Finset (Fin K) := fun p => Finset.univ.filter (fun k => U k ≤ p ∧ p ≤ V k)
      (σU = 0 → ∀ k, w k = 0 ∨ U k = μU) →
      (∀ p : ℝ, (∑ k ∈ E p, w k * (U k - μU)) ^ 2 ≤ 2 * (∑ k ∈ E p, w k) * σU * D) →
      (∀ p : ℝ, (Real.sqrt (∑ k ∈ E p, w k) * σU -
        Real.sqrt (∑ k ∈ E p, w k * (U k - μU) ^ 2)) ^ 2 ≤ 2 * σU * D) →
      ∑ k, w k * max (min (V k) (μU + σU / 3) - U k) 0 ≤ 81 * D := by
    intro U V σU D hσU_nn hD_nn μU E h_zero h_mean h_rad
    rcases eq_or_lt_of_le hσU_nn with hσ0 | hσ_pos
    · have hσU0 : σU = 0 := hσ0.symm
      rw [hσU0, zero_div, add_zero]
      have h_sum0 : ∑ k, w k * max (min (V k) μU - U k) 0 = 0 := by
        refine Finset.sum_eq_zero (fun k _ => ?_)
        rcases h_zero hσU0 k with hwk | huk
        · rw [hwk, zero_mul]
        · rw [huk, max_eq_right (sub_nonpos.mpr (min_le_right _ _)), mul_zero]
      rw [h_sum0]
      positivity
    · let α : ℝ → ℝ := fun p => ∑ k ∈ E p, w k
      let v : ℝ → ℝ := fun p => ∑ k ∈ E p, w k * (U k - μU) ^ 2
      have hα_nn : ∀ p : ℝ, 0 ≤ α p := fun p => Finset.sum_nonneg (fun k _ => hw_nn k)
      have hv_nn : ∀ p : ℝ, 0 ≤ v p :=
        fun p => Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nn k) (sq_nonneg _))
      have h_tail : ∀ p : ℝ, p < μU → α p * (μU - p) ^ 2 ≤ 2 * σU * D := by
        intro p hp
        rcases eq_or_lt_of_le (hα_nn p) with hα0 | hα_pos
        · rw [← hα0, zero_mul]
          positivity
        · have h_mono : ∑ k ∈ E p, w k * (U k - μU) ≤ α p * (p - μU) := by
            calc ∑ k ∈ E p, w k * (U k - μU)
                ≤ ∑ k ∈ E p, w k * (p - μU) := by
                    refine Finset.sum_le_sum (fun k hk => ?_)
                    have hUk : U k ≤ p := (Finset.mem_filter.mp hk).2.1
                    exact mul_le_mul_of_nonneg_left (by linarith) (hw_nn k)
              _ = α p * (p - μU) := (Finset.sum_mul _ _ _).symm
          have h_pos_prod : 0 ≤ α p * (μU - p) := mul_nonneg hα_pos.le (sub_pos.mpr hp).le
          have h_sq_le : (α p) ^ 2 * (μU - p) ^ 2 ≤ (∑ k ∈ E p, w k * (U k - μU)) ^ 2 := by
            nlinarith
          have h_comb : (α p) ^ 2 * (μU - p) ^ 2 ≤ 2 * α p * σU * D :=
            le_trans h_sq_le (h_mean p)
          nlinarith
      set η : ℝ := σU / 3
      have hη_pos : 0 < η := by positivity
      have h_central : ∀ p : ℝ, μU - η ≤ p → p ≤ μU + η → α p ≤ (225 / 2 : ℝ) * D / σU := by
        intro p hp_lo hp_hi
        set p' : ℝ := μU - η
        have hv_split : v p ≤ η ^ 2 * α p + v p' := by
          have hv_eq : v p = ∑ k : Fin K,
              if U k ≤ p ∧ p ≤ V k then w k * (U k - μU) ^ 2 else 0 :=
            Finset.sum_filter _ _
          have hα_eq : η ^ 2 * α p = ∑ k : Fin K,
              if U k ≤ p ∧ p ≤ V k then w k * η ^ 2 else 0 := by
            calc η ^ 2 * α p
                = ∑ k ∈ E p, η ^ 2 * w k := Finset.mul_sum _ _ _
              _ = ∑ k ∈ E p, w k * η ^ 2 := Finset.sum_congr rfl (fun k _ => mul_comm _ _)
              _ = ∑ k : Fin K, if U k ≤ p ∧ p ≤ V k then w k * η ^ 2 else 0 :=
                  Finset.sum_filter _ _
          have hv'_eq : v p' = ∑ k : Fin K,
              if U k ≤ p' ∧ p' ≤ V k then w k * (U k - μU) ^ 2 else 0 :=
            Finset.sum_filter _ _
          rw [hv_eq, hα_eq, hv'_eq, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum (fun k _ => ?_)
          by_cases hk : U k ≤ p ∧ p ≤ V k
          · rw [if_pos hk, if_pos hk]
            by_cases hk' : U k ≤ p'
            · have h_mem' : U k ≤ p' ∧ p' ≤ V k := ⟨hk', le_trans hp_lo hk.2⟩
              rw [if_pos h_mem']
              linarith [mul_nonneg (hw_nn k) (sq_nonneg η)]
            · push_neg at hk'
              have h_sq_le : (U k - μU) ^ 2 ≤ η ^ 2 := by
                have h1 : -η < U k - μU := by dsimp [p'] at hk'; linarith
                have h2 : U k - μU ≤ η := by linarith [hk.1, hp_hi]
                nlinarith
              have h_w_le : w k * (U k - μU) ^ 2 ≤ w k * η ^ 2 :=
                mul_le_mul_of_nonneg_left h_sq_le (hw_nn k)
              have h_ite_nn : 0 ≤ (if U k ≤ p' ∧ p' ≤ V k then w k * (U k - μU) ^ 2 else 0) := by
                split_ifs
                · exact mul_nonneg (hw_nn k) (sq_nonneg _)
                · exact le_rfl
              linarith
          · rw [if_neg hk, if_neg hk, zero_add]
            split_ifs
            · exact mul_nonneg (hw_nn k) (sq_nonneg _)
            · exact le_rfl
        set R : ℝ := Real.sqrt (2 * σU * D)
        have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
        have hR_sq : R ^ 2 = 2 * σU * D := Real.sq_sqrt (by positivity)
        have hq'_tail : α p' * (μU - p') ^ 2 ≤ 2 * σU * D :=
          h_tail p' (by dsimp [p']; linarith)
        have hq'_mul : α p' * σU ^ 2 ≤ 9 * R ^ 2 := by
          have h_denom : μU - p' = σU / 3 := by dsimp [p', η]; ring
          rw [h_denom] at hq'_tail
          nlinarith [hR_sq]
        have hrq'_sig : Real.sqrt (α p') * σU ≤ 3 * R := by
          have h_sq1 : (Real.sqrt (α p') * σU) ^ 2 = α p' * σU ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (hα_nn p')]
          have h_nn1 : 0 ≤ Real.sqrt (α p') * σU := mul_nonneg (Real.sqrt_nonneg _) hσ_pos.le
          nlinarith
        have hrv'_sub : Real.sqrt (v p') - Real.sqrt (α p') * σU ≤ R := by
          have hr' : (Real.sqrt (α p') * σU - Real.sqrt (v p')) ^ 2 ≤ R ^ 2 := by
            rw [hR_sq]
            exact h_rad p'
          nlinarith [hR_nn]
        have hv'_le : v p' ≤ 16 * R ^ 2 := by
          have hrv'_le : Real.sqrt (v p') ≤ 4 * R := by linarith
          have hrv'_nn : 0 ≤ Real.sqrt (v p') := Real.sqrt_nonneg _
          have hrv'_sq : (Real.sqrt (v p')) ^ 2 = v p' := Real.sq_sqrt (hv_nn p')
          nlinarith
        have hrv_le : Real.sqrt (v p) ≤ η * Real.sqrt (α p) + 4 * R := by
          have hrα_nn : 0 ≤ Real.sqrt (α p) := Real.sqrt_nonneg _
          have hrα_sq : (Real.sqrt (α p)) ^ 2 = α p := Real.sq_sqrt (hα_nn p)
          have hrv_nn : 0 ≤ Real.sqrt (v p) := Real.sqrt_nonneg _
          have hrv_sq : (Real.sqrt (v p)) ^ 2 = v p := Real.sq_sqrt (hv_nn p)
          have h_sum_sq : (Real.sqrt (v p)) ^ 2 ≤ (η * Real.sqrt (α p) + 4 * R) ^ 2 := by
            calc (Real.sqrt (v p)) ^ 2 = v p := hrv_sq
              _ ≤ η ^ 2 * α p + 16 * R ^ 2 := by linarith [hv_split, hv'_le]
              _ = η ^ 2 * (Real.sqrt (α p)) ^ 2 + 16 * R ^ 2 := by rw [hrα_sq]
              _ ≤ (η * Real.sqrt (α p) + 4 * R) ^ 2 := by
                  nlinarith [mul_nonneg hη_pos.le hrα_nn, hR_nn]
          have h_rhs_nn : 0 ≤ η * Real.sqrt (α p) + 4 * R := by positivity
          nlinarith
        have hrα_sub : Real.sqrt (α p) * σU - Real.sqrt (v p) ≤ R := by
          have hr : (Real.sqrt (α p) * σU - Real.sqrt (v p)) ^ 2 ≤ R ^ 2 := by
            rw [hR_sq]
            exact h_rad p
          nlinarith [hR_nn]
        have h_lin : (2 / 3 : ℝ) * σU * Real.sqrt (α p) ≤ 5 * R := by
          dsimp [η] at hrv_le
          linarith
        have h_sq_final : (4 / 9 : ℝ) * σU ^ 2 * α p ≤ 50 * σU * D := by
          have hrα_nn : 0 ≤ Real.sqrt (α p) := Real.sqrt_nonneg _
          have hrα_sq : (Real.sqrt (α p)) ^ 2 = α p := Real.sq_sqrt (hα_nn p)
          have h1 : ((2 / 3 : ℝ) * σU * Real.sqrt (α p)) ^ 2 ≤ (5 * R) ^ 2 := by
            nlinarith [mul_nonneg hσ_pos.le hrα_nn, hR_nn]
          nlinarith [hR_sq, hrα_sq]
        have h_canc : α p * σU ≤ (225 / 2 : ℝ) * D := by nlinarith
        exact (le_div_iff₀ hσ_pos).mpr h_canc
      
      refine le_of_forall_pos_lt_add (fun ε hε => ?_)
      set a : ℝ := μU - η
      set b : ℝ := μU + η
      obtain ⟨m, hm_gt⟩ := exists_nat_gt (η / ε)
      have hm_real_pos : 0 < (m : ℝ) := lt_trans (div_pos hη_pos hε) hm_gt
      have hm_pos : 0 < m := Nat.cast_pos.mp hm_real_pos
      have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
      set h : ℝ := η / (m : ℝ)
      have hh_pos : 0 < h := div_pos hη_pos hm_real_pos
      have hmh : (m : ℝ) * h = η := mul_div_cancel₀ η hm_real_pos.ne'
      have hh_lt_ε : h < ε := by
        rw [div_lt_iff₀ hm_real_pos]
        have h1 : η < (m : ℝ) * ε := (div_lt_iff₀ hε).mp hm_gt
        linarith
      set B_low : ℝ := ∑ i : Fin K, |U i|
      have hU_lb : ∀ k : Fin K, -B_low ≤ U k := by
        intro k
        have h1 : |U k| ≤ B_low :=
          Finset.single_le_sum (fun i _ => abs_nonneg (U i)) (Finset.mem_univ k)
        linarith [neg_abs_le (U k)]
      obtain ⟨N, hN_gt⟩ := exists_nat_gt (max 1 ((a + B_low) / h))
      have hN_gt1 : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN_gt
      have hN_pos : 0 < (N : ℝ) := by linarith
      have haB_lt : a + B_low < (N : ℝ) * h :=
        (div_lt_iff₀ hh_pos).mp (lt_of_le_of_lt (le_max_right _ _) hN_gt)
      set x0 : ℝ := a - (N : ℝ) * h
      let x : ℕ → ℝ := fun t => x0 + (t : ℝ) * h
      have hx0_lt_U : ∀ k : Fin K, x0 < U k := by
        intro k
        have hk := hU_lb k
        dsimp [x0]
        linarith
      have h_span : b - x0 = ((N + 2 * m : ℕ) : ℝ) * h := by
        push_cast
        dsimp [a, b, x0]
        linear_combination 2 * hmh.symm
      have h_pt_grid : ∀ k : Fin K,
          max (min (V k) b - U k) 0 - h ≤
            h * ∑ t ∈ Finset.range (N + 2 * m),
              (if U k ≤ x t ∧ x t ≤ V k then (1 : ℝ) else 0) := by
        intro k
        set u : ℝ := U k
        set vk : ℝ := min (V k) b
        by_cases huv : vk ≤ u
        · rw [max_eq_right (sub_nonpos.mpr huv), zero_sub]
          have h_rhs_nn : 0 ≤ h * ∑ t ∈ Finset.range (N + 2 * m),
              (if U k ≤ x t ∧ x t ≤ V k then (1 : ℝ) else 0) := by
            refine mul_nonneg hh_pos.le (Finset.sum_nonneg (fun t _ => ?_))
            split_ifs <;> norm_num
          linarith
        · push_neg at huv
          set t1 : ℕ := ⌈(u - x0) / h⌉₊
          set t2 : ℕ := ⌈(vk - x0) / h⌉₊
          have hu_div_pos : 0 < (u - x0) / h :=
            div_pos (sub_pos.mpr (hx0_lt_U k)) hh_pos
          have ht1_le_t2 : t1 ≤ t2 :=
            Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith : u - x0 ≤ vk - x0) hh_pos.le)
          have hvk_le_top : (vk - x0) / h ≤ ((N + 2 * m : ℕ) : ℝ) := by
            rw [div_le_iff₀ hh_pos, ← h_span]
            linarith [min_le_right (V k) b]
          have ht2_le_top : t2 ≤ N + 2 * m := Nat.ceil_le.mpr hvk_le_top
          have h_sub_Ico : Finset.Ico t1 t2 ⊆ Finset.range (N + 2 * m) := fun t ht =>
            Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp ht).2 ht2_le_top)
          have h_mem_ivl : ∀ t ∈ Finset.Ico t1 t2, U k ≤ x t ∧ x t ≤ V k := by
            intro t ht
            rcases Finset.mem_Ico.mp ht with ⟨ht1, ht2⟩
            constructor
            · have ht1_r : (t1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
              have h_le1 : (u - x0) / h ≤ (t : ℝ) := le_trans (Nat.le_ceil _) ht1_r
              have h_le2 : u - x0 ≤ (t : ℝ) * h := (div_le_iff₀ hh_pos).mp h_le1
              dsimp [x, u] at *
              linarith
            · have h_lt1 : (t : ℝ) < (vk - x0) / h := Nat.lt_ceil.mp ht2
              have h_lt2 : (t : ℝ) * h < vk - x0 := (lt_div_iff₀ hh_pos).mp h_lt1
              have hvk_V : vk ≤ V k := min_le_left _ _
              dsimp [x] at *
              linarith
          have h_count : ((t2 : ℝ) - (t1 : ℝ)) ≤
              ∑ t ∈ Finset.range (N + 2 * m),
                (if U k ≤ x t ∧ x t ≤ V k then (1 : ℝ) else 0) := by
            calc (t2 : ℝ) - (t1 : ℝ)
                = ((t2 - t1 : ℕ) : ℝ) := (Nat.cast_sub ht1_le_t2).symm
              _ = ((Finset.Ico t1 t2).card : ℝ) := by rw [Nat.card_Ico]
              _ = ∑ _t ∈ Finset.Ico t1 t2, (1 : ℝ) := by simp
              _ = ∑ t ∈ Finset.Ico t1 t2,
                    (if U k ≤ x t ∧ x t ≤ V k then (1 : ℝ) else 0) :=
                  Finset.sum_congr rfl (fun t ht => by rw [if_pos (h_mem_ivl t ht)])
              _ ≤ ∑ t ∈ Finset.range (N + 2 * m),
                    (if U k ≤ x t ∧ x t ≤ V k then (1 : ℝ) else 0) :=
                  Finset.sum_le_sum_of_subset_of_nonneg h_sub_Ico
                    (fun t _ _ => by split_ifs <;> norm_num)
          have ht2_ge : (vk - x0) / h ≤ (t2 : ℝ) := Nat.le_ceil _
          have ht1_lt : (t1 : ℝ) < (u - x0) / h + 1 := Nat.ceil_lt_add_one hu_div_pos.le
          have h_diff_div : (vk - u) / h - 1 ≤ (t2 : ℝ) - (t1 : ℝ) := by
            have h_alg : (vk - u) / h - 1 = (vk - x0) / h - ((u - x0) / h + 1) := by ring
            linarith
          have h_mul_h := mul_le_mul_of_nonneg_left (le_trans h_diff_div h_count) hh_pos.le
          have h_lhs_simp : h * ((vk - u) / h - 1) = vk - u - h := by
            field_simp [hh_pos.ne']
          rw [max_eq_left (by linarith : 0 ≤ vk - u)]
          linarith
      have h_grid_sum : ∑ k : Fin K, w k * max (min (V k) b - U k) 0 - h ≤
          (∑ t ∈ Finset.range N, h * α (x t)) +
            ∑ j ∈ Finset.range (2 * m), h * α (x (N + j)) := by
        have h_w_le : ∑ k : Fin K, w k * (max (min (V k) b - U k) 0 - h) ≤
            ∑ k : Fin K, w k * (h * ∑ t ∈ Finset.range (N + 2 * m),
              (if U k ≤ x t ∧ x t ≤ V k then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (h_pt_grid k) (hw_nn k))
        have h_lhs_eq : ∑ k : Fin K, w k * (max (min (V k) b - U k) 0 - h) =
            ∑ k : Fin K, w k * max (min (V k) b - U k) 0 - h := by
          have h1 : ∀ k : Fin K, w k * (max (min (V k) b - U k) 0 - h) =
              w k * max (min (V k) b - U k) 0 - w k * h := fun _ => by ring
          simp_rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum, one_mul]
        have h_rhs_eq : ∑ k : Fin K, w k * (h * ∑ t ∈ Finset.range (N + 2 * m),
              (if U k ≤ x t ∧ x t ≤ V k then (1 : ℝ) else 0)) =
            ∑ t ∈ Finset.range (N + 2 * m), h * α (x t) := by
          have h_in : ∀ k : Fin K, w k * (h * ∑ t ∈ Finset.range (N + 2 * m),
              (if U k ≤ x t ∧ x t ≤ V k then (1 : ℝ) else 0)) =
              ∑ t ∈ Finset.range (N + 2 * m),
                h * (if U k ≤ x t ∧ x t ≤ V k then w k else 0) := by
            intro k
            rw [← mul_assoc, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            split_ifs <;> ring
          simp_rw [h_in]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [← Finset.mul_sum, ← Finset.sum_filter]
        rw [h_lhs_eq, h_rhs_eq, Finset.sum_range_add (fun t => h * α (x t)) N (2 * m)] at h_w_le
        exact h_w_le
      
      have h_tail_sum : ∑ t ∈ Finset.range N, h * α (x t) ≤ 6 * D := by
        let r : ℕ → ℝ := fun t => (m : ℝ) + (N : ℝ) - (t : ℝ)
        let f : ℕ → ℝ := fun t => (r t)⁻¹
        have h_term_le : ∀ t ∈ Finset.range N,
            h * α (x t) ≤ (2 * σU * D / h) * (f (t + 1) - f t) := by
          intro t ht
          have ht_lt : t < N := Finset.mem_range.mp ht
          have ht_le : (t : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt ht_lt
          have hr1_ge1 : 1 ≤ r (t + 1) := by
            dsimp [r]
            push_cast
            linarith
          have hr1_pos : 0 < r (t + 1) := by linarith
          have hr_diff : r t - r (t + 1) = 1 := by
            dsimp [r]
            push_cast
            ring
          have hr_pos : 0 < r t := by linarith
          have h_mu_sub : μU - x t = r t * h := by
            dsimp [x, x0, a, r]
            linear_combination hmh.symm
          have hxt_lt : x t < μU := by
            have hpos : 0 < r t * h := mul_pos hr_pos hh_pos
            linarith
          have h_tb := h_tail (x t) hxt_lt
          rw [h_mu_sub] at h_tb
          have h_prod_pos : 0 < h * r (t + 1) * r t :=
            mul_pos (mul_pos hh_pos hr1_pos) hr_pos
          have h_f_id : (f (t + 1) - f t) * (h * r (t + 1) * r t) = h := by
            dsimp [f]
            field_simp [hr1_pos.ne', hr_pos.ne']
            linarith [hr_diff]
          have h_rr_le : r (t + 1) * r t ≤ (r t) ^ 2 := by
            nlinarith [hr_pos, hr_diff]
          have h_mul_bound :
              (h * α (x t)) * (h * r (t + 1) * r t) ≤
                ((2 * σU * D / h) * (f (t + 1) - f t)) * (h * r (t + 1) * r t) := by
            calc (h * α (x t)) * (h * r (t + 1) * r t)
                = (α (x t) * h ^ 2) * (r (t + 1) * r t) := by ring
              _ ≤ (α (x t) * h ^ 2) * (r t) ^ 2 :=
                  mul_le_mul_of_nonneg_left h_rr_le (mul_nonneg (hα_nn _) (sq_nonneg h))
              _ = α (x t) * (r t * h) ^ 2 := by ring
              _ ≤ 2 * σU * D := h_tb
              _ = (2 * σU * D / h) * h := by field_simp [hh_pos.ne']
              _ = (2 * σU * D / h) * ((f (t + 1) - f t) * (h * r (t + 1) * r t)) := by
                  rw [h_f_id]
              _ = ((2 * σU * D / h) * (f (t + 1) - f t)) * (h * r (t + 1) * r t) := by ring
          exact le_of_mul_le_mul_right h_mul_bound h_prod_pos
        have h_tele : ∑ t ∈ Finset.range N, h * α (x t) ≤ (2 * σU * D / h) * (f N - f 0) := by
          calc ∑ t ∈ Finset.range N, h * α (x t)
              ≤ ∑ t ∈ Finset.range N, (2 * σU * D / h) * (f (t + 1) - f t) :=
                Finset.sum_le_sum h_term_le
            _ = (2 * σU * D / h) * ∑ t ∈ Finset.range N, (f (t + 1) - f t) :=
                (Finset.mul_sum _ _ _).symm
            _ = (2 * σU * D / h) * (f N - f 0) := by rw [Finset.sum_range_sub f N]
        have hf0_nn : 0 ≤ f 0 := by
          dsimp [f, r]
          push_cast
          exact inv_nonneg.mpr (by linarith)
        have hfN_eq : f N = (m : ℝ)⁻¹ := by
          dsimp [f, r]
          ring_nf
        have h_coef_nn : 0 ≤ 2 * σU * D / h := by positivity
        calc ∑ t ∈ Finset.range N, h * α (x t)
            ≤ (2 * σU * D / h) * (f N - f 0) := h_tele
          _ ≤ (2 * σU * D / h) * f N :=
              mul_le_mul_of_nonneg_left (by linarith) h_coef_nn
          _ = (2 * σU * D) / ((m : ℝ) * h) := by
              rw [hfN_eq]
              ring
          _ = (2 * σU * D) / (σU / 3) := by rw [hmh]
          _ = 6 * D := by
              field_simp [hσ_pos.ne']
              ring
      
      have h_core_sum : ∑ j ∈ Finset.range (2 * m), h * α (x (N + j)) ≤ 75 * D := by
        have h_term_le : ∀ j ∈ Finset.range (2 * m),
            h * α (x (N + j)) ≤ h * ((225 / 2 : ℝ) * D / σU) := by
          intro j hj
          have hj_lt : j < 2 * m := Finset.mem_range.mp hj
          have hj_le : (j : ℝ) ≤ 2 * (m : ℝ) := by
            have h1 : j ≤ 2 * m := hj_lt.le
            exact_mod_cast h1
          have hj_nn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
          have hx_eq : x (N + j) = a + (j : ℝ) * h := by
            dsimp [x, x0]
            push_cast
            ring
          have hx_lo : μU - η ≤ x (N + j) := by
            rw [hx_eq]
            dsimp [a]
            nlinarith [hh_pos]
          have hx_hi : x (N + j) ≤ μU + η := by
            rw [hx_eq]
            dsimp [a]
            have h_jh : (j : ℝ) * h ≤ 2 * η := by
              calc (j : ℝ) * h ≤ (2 * (m : ℝ)) * h :=
                    mul_le_mul_of_nonneg_right hj_le hh_pos.le
                _ = 2 * ((m : ℝ) * h) := by ring
                _ = 2 * η := by rw [hmh]
            linarith
          exact mul_le_mul_of_nonneg_left (h_central (x (N + j)) hx_lo hx_hi) hh_pos.le
        calc ∑ j ∈ Finset.range (2 * m), h * α (x (N + j))
            ≤ ∑ _j ∈ Finset.range (2 * m), h * ((225 / 2 : ℝ) * D / σU) :=
              Finset.sum_le_sum h_term_le
          _ = ((2 * m : ℕ) : ℝ) * (h * ((225 / 2 : ℝ) * D / σU)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ = 2 * ((m : ℝ) * h) * ((225 / 2 : ℝ) * D / σU) := by
              push_cast
              ring
          _ = 2 * (σU / 3) * ((225 / 2 : ℝ) * D / σU) := by rw [hmh]
          _ = 75 * D := by
              field_simp [hσ_pos.ne']
              ring
      linarith

  
  set μS : ℝ := ∑ k, w k * S k
  set μB : ℝ := ∑ k, w k * B k
  set σS : ℝ := finWeightedStdDev w Finset.univ S
  set σB : ℝ := finWeightedStdDev w Finset.univ B
  set σ : ℝ := σS + σB
  set m : ℝ := μB - μS
  set G : ℝ := ∑ k, w k * max (B k - S k) 0
  let E_fn : ℝ → Finset (Fin K) := fun p => Finset.univ.filter (fun k => S k ≤ p ∧ p ≤ B k)
  let Ec_fn : ℝ → Finset (Fin K) := fun p => Finset.univ \ E_fn p
  let dS_fn : ℝ → ℝ := fun p => σS - finWeightedStdDev w (E_fn p) S - finWeightedStdDev w (Ec_fn p) S
  let dB_fn : ℝ → ℝ := fun p => σB - finWeightedStdDev w (E_fn p) B - finWeightedStdDev w (Ec_fn p) B
  let L_fn : ℝ → ℝ := fun p => ∑ k ∈ Ec_fn p, w k * max (B k - S k) 0

  have hσS_nn : 0 ≤ σS := Real.sqrt_nonneg _
  have hσB_nn : 0 ≤ σB := Real.sqrt_nonneg _
  have hσ_nn : 0 ≤ σ := add_nonneg hσS_nn hσB_nn
  have hdS_nn : ∀ p : ℝ, 0 ≤ dS_fn p := fun p => (h_drop S (E_fn p)).1.1
  have hdB_nn : ∀ p : ℝ, 0 ≤ dB_fn p := fun p => (h_drop B (E_fn p)).1.1
  have hL_le_G : ∀ p : ℝ, L_fn p ≤ G := fun p =>
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun k _ _ => mul_nonneg (hw_nn k) (le_max_right _ _))

  rcases eq_or_lt_of_le hσ_nn with hσ0 | hσ_pos
  · 
    have hσS0 : σS = 0 := by dsimp [σ] at hσ0; linarith
    have hσB0 : σB = 0 := by dsimp [σ] at hσ0; linarith
    have hS_const := h_zero_const S hσS0
    have hB_const := h_zero_const B hσB0
    refine ⟨μS, ?_⟩
    change L_fn μS ≤ 2048 * (dS_fn μS + dB_fn μS)
    have hL0 : L_fn μS = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      rcases hS_const k with hwk | hSk
      · rw [hwk, zero_mul]
      · rcases hB_const k with hwk | hBk
        · rw [hwk, zero_mul]
        · have hk_not : k ∉ E_fn μS := (Finset.mem_sdiff.mp hk).2
          have h_not_cond : ¬ (S k ≤ μS ∧ μS ≤ B k) := fun hc =>
            hk_not (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hc⟩)
          have h_lt : B k < S k := by
            change S k = μS at hSk
            change B k = μB at hBk
            rw [hSk, hBk] at h_not_cond ⊢
            push_neg at h_not_cond
            exact h_not_cond le_rfl
          rw [max_eq_right (by linarith : B k - S k ≤ 0), mul_zero]
    rw [hL0]
    have h1 := hdS_nn μS
    have h2 := hdB_nn μS
    linarith
  · by_cases hm : m < 3 * σ
    · 
      by_contra h_no
      have h_no' : ∀ p : ℝ, 2048 * (dS_fn p + dB_fn p) < L_fn p := by
        intro p
        by_contra h_le
        push_neg at h_le
        exact h_no ⟨p, h_le⟩
      have h_all_lt_G : ∀ p : ℝ, 2048 * (dS_fn p + dB_fn p) < G :=
        fun p => lt_of_lt_of_le (h_no' p) (hL_le_G p)
      have hG_pos : 0 < G := by
        have h0_nn : 0 ≤ 2048 * (dS_fn 0 + dB_fn 0) := by
          have := hdS_nn 0
          have := hdB_nn 0
          linarith
        exact lt_of_le_of_lt h0_nn (h_all_lt_G 0)
      set Dbar : ℝ := G / 2048
      have hDbar_nn : 0 ≤ Dbar := by positivity
      have hdS_le_Dbar : ∀ p : ℝ, dS_fn p ≤ Dbar := by
        intro p
        have hp := (h_all_lt_G p).le
        have := hdB_nn p
        dsimp [Dbar]
        linarith
      have hdB_le_Dbar : ∀ p : ℝ, dB_fn p ≤ Dbar := by
        intro p
        have hp := (h_all_lt_G p).le
        have := hdS_nn p
        dsimp [Dbar]
        linarith
      
      set a : ℝ := μS + σS / 3
      have h_left : ∑ k, w k * max (min (B k) a - S k) 0 ≤ 81 * Dbar := by
        refine h_halfline S B σS Dbar hσS_nn hDbar_nn (h_zero_const S) ?_ ?_
        · intro p
          have hm1 := (h_drop S (E_fn p)).2.1
          have h_q_nn : 0 ≤ 2 * (∑ k ∈ E_fn p, w k) * σS :=
            mul_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => hw_nn k)) hσS_nn
          exact le_trans hm1 (mul_le_mul_of_nonneg_left (hdS_le_Dbar p) h_q_nn)
        · intro p
          have hr1 := (h_drop S (E_fn p)).2.2
          have h_s_nn : 0 ≤ 2 * σS := mul_nonneg (by norm_num) hσS_nn
          exact le_trans hr1 (mul_le_mul_of_nonneg_left (hdS_le_Dbar p) h_s_nn)
      
      set c : ℝ := μB - σB / 3
      have h_right : ∑ k, w k * max (B k - max (S k) c) 0 ≤ 81 * Dbar := by
        let U' : Fin K → ℝ := fun k => -B k
        let V' : Fin K → ℝ := fun k => -S k
        have hμU' : ∑ k, w k * U' k = -μB := by
          dsimp [U', μB]
          simp_rw [mul_neg, Finset.sum_neg_distrib]
        let E' : ℝ → Finset (Fin K) := fun q => Finset.univ.filter (fun k => U' k ≤ q ∧ q ≤ V' k)
        have hE'_eq : ∀ q : ℝ, E' q = E_fn (-q) := by
          intro q
          refine Finset.filter_congr (fun k _ => ?_)
          dsimp [U', V']
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
        have h_raw := h_halfline U' V' σB Dbar hσB_nn hDbar_nn
          (fun h0 k => by
            rw [hμU']
            rcases h_zero_const B h0 k with hwk | hBk
            · exact Or.inl hwk
            · exact Or.inr (by dsimp [U']; linarith))
          (fun q => by
            change (∑ k ∈ E' q, w k * (U' k - ∑ j, w j * U' j)) ^ 2 ≤
              2 * (∑ k ∈ E' q, w k) * σB * Dbar
            rw [hμU', hE'_eq q]
            have h_sum_neg : ∑ k ∈ E_fn (-q), w k * (U' k - -μB) =
                -(∑ k ∈ E_fn (-q), w k * (B k - μB)) := by
              have h_pt_neg : ∀ k : Fin K, w k * (U' k - -μB) = -(w k * (B k - μB)) := fun k => by
                dsimp [U']
                ring
              simp_rw [h_pt_neg, Finset.sum_neg_distrib]
            rw [h_sum_neg, neg_sq]
            have hm1 := (h_drop B (E_fn (-q))).2.1
            have h_q_nn : 0 ≤ 2 * (∑ k ∈ E_fn (-q), w k) * σB :=
              mul_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => hw_nn k)) hσB_nn
            exact le_trans hm1 (mul_le_mul_of_nonneg_left (hdB_le_Dbar (-q)) h_q_nn))
          (fun q => by
            change (Real.sqrt (∑ k ∈ E' q, w k) * σB -
              Real.sqrt (∑ k ∈ E' q, w k * (U' k - ∑ j, w j * U' j) ^ 2)) ^ 2 ≤
              2 * σB * Dbar
            rw [hμU', hE'_eq q]
            have h_sq_eq : ∑ k ∈ E_fn (-q), w k * (U' k - -μB) ^ 2 =
                ∑ k ∈ E_fn (-q), w k * (B k - μB) ^ 2 := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              dsimp [U']
              ring
            rw [h_sq_eq]
            have hr1 := (h_drop B (E_fn (-q))).2.2
            have h_s_nn : 0 ≤ 2 * σB := mul_nonneg (by norm_num) hσB_nn
            exact le_trans hr1 (mul_le_mul_of_nonneg_left (hdB_le_Dbar (-q)) h_s_nn))
        have h_rew : ∑ k, w k * max (min (V' k) ((∑ j, w j * U' j) + σB / 3) - U' k) 0 =
            ∑ k, w k * max (B k - max (S k) c) 0 := by
          rw [hμU']
          refine Finset.sum_congr rfl (fun k _ => ?_)
          have h_inner : min (V' k) (-μB + σB / 3) - U' k = B k - max (S k) c := by
            dsimp [U', V', c]
            by_cases hsc : S k ≤ μB - σB / 3
            · rw [min_eq_right (by linarith), max_eq_right hsc]
              ring
            · push_neg at hsc
              rw [min_eq_left (by linarith), max_eq_left hsc.le]
              ring
          rw [h_inner]
        rwa [← h_rew]
      
      have hG_cover : G ≤ 162 * Dbar + max (c - a) 0 := by
        have h_pt : ∀ k : Fin K,
            w k * max (B k - S k) 0 ≤
              w k * max (min (B k) a - S k) 0 +
              w k * max (c - a) 0 +
              w k * max (B k - max (S k) c) 0 := by
          intro k
          have h_core : max (B k - S k) 0 ≤
              max (min (B k) a - S k) 0 + max (c - a) 0 + max (B k - max (S k) c) 0 := by
            refine max_le ?_ (by positivity)
            by_cases hba : B k ≤ a
            · rw [min_eq_left hba]
              linarith [le_max_left (B k - S k) 0, le_max_right (c - a) 0,
                        le_max_right (B k - max (S k) c) 0]
            · push_neg at hba
              by_cases hcs : c ≤ S k
              · rw [max_eq_left hcs]
                linarith [le_max_right (min (B k) a - S k) 0, le_max_right (c - a) 0,
                          le_max_left (B k - S k) 0]
              · push_neg at hcs
                rw [min_eq_right hba.le, max_eq_right hcs.le]
                linarith [le_max_left (a - S k) 0, le_max_left (c - a) 0,
                          le_max_left (B k - c) 0]
          have hw_mul := mul_le_mul_of_nonneg_left h_core (hw_nn k)
          linarith
        have h_sum_le := Finset.sum_le_sum (s := Finset.univ) (fun k _ => h_pt k)
        simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw_sum, one_mul] at h_sum_le
        change G ≤ _ at h_sum_le
        linarith [h_left, h_right]
      have hm_le_G : m ≤ G := by
        have h_sub : m = ∑ k, w k * (B k - S k) := by
          dsimp [m, μB, μS]
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [h_sub]
        exact Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (le_max_left _ _) (hw_nn k))
      have hca_le : max (c - a) 0 ≤ max (G - σ / 3) 0 := by
        refine max_le_max ?_ le_rfl
        dsimp [c, a, σ]
        linarith
      have h_min_le : min G (σ / 3) ≤ 162 * Dbar := by
        by_cases hGσ : G ≤ σ / 3
        · rw [min_eq_left hGσ]
          have h0 : max (G - σ / 3) 0 = 0 := max_eq_right (by linarith)
          linarith
        · push_neg at hGσ
          rw [min_eq_right hGσ.le]
          have h1 : max (G - σ / 3) 0 = G - σ / 3 := max_eq_left (by linarith)
          linarith
      have hG_le_4σ : G ≤ 4 * σ := by
        have h_pt : ∀ k : Fin K,
            w k * max (B k - S k) 0 ≤
              w k * max m 0 + w k * |B k - μB| + w k * |S k - μS| := by
          intro k
          have h_core : max (B k - S k) 0 ≤ max m 0 + |B k - μB| + |S k - μS| := by
            refine max_le ?_ (by positivity)
            have hm_m := le_max_left m 0
            have hB_abs := le_abs_self (B k - μB)
            have hS_abs := neg_le_abs (S k - μS)
            dsimp [m] at hm_m
            linarith
          have hw_mul := mul_le_mul_of_nonneg_left h_core (hw_nn k)
          linarith
        have h_sum_le := Finset.sum_le_sum (s := Finset.univ) (fun k _ => h_pt k)
        simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw_sum, one_mul] at h_sum_le
        change G ≤ max m 0 + (∑ k, w k * |B k - μB|) + (∑ k, w k * |S k - μS|) at h_sum_le
        have hlB := h_l1_le B
        have hlS := h_l1_le S
        have hm_max : max m 0 ≤ 3 * σ := max_le hm.le (by positivity)
        dsimp [σ] at *
        linarith
      have hG_le_12 : G ≤ 12 * min G (σ / 3) := by
        by_cases hGσ : G ≤ σ / 3
        · rw [min_eq_left hGσ]; linarith
        · push_neg at hGσ; rw [min_eq_right hGσ.le]; linarith
      dsimp [Dbar] at h_min_le
      linarith
    · 
      push_neg at hm
      set p_hat : ℝ := (μS + μB) / 2
      refine ⟨p_hat, ?_⟩
      change L_fn p_hat ≤ 2048 * (dS_fn p_hat + dB_fn p_hat)
      set E : Finset (Fin K) := E_fn p_hat
      set F : Finset (Fin K) := Ec_fn p_hat
      set β : ℝ := ∑ k ∈ F, w k
      have hβ_nn : 0 ≤ β := Finset.sum_nonneg (fun k _ => hw_nn k)
      rcases eq_or_lt_of_le hβ_nn with hβ0 | hβ_pos
      · have hwF0 : ∀ k ∈ F, w k = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hw_nn k)).mp hβ0.symm
        have hL0 : L_fn p_hat = 0 := by
          refine Finset.sum_eq_zero (fun k hk => ?_)
          rw [hwF0 k hk, zero_mul]
        rw [hL0]
        have := hdS_nn p_hat
        have := hdB_nn p_hat
        linarith
      · set rβ : ℝ := Real.sqrt β
        have hrβ_pos : 0 < rβ := Real.sqrt_pos.mpr hβ_pos
        have hrβ_nn : 0 ≤ rβ := hrβ_pos.le
        have hrβ_sq : rβ ^ 2 = β := Real.sq_sqrt hβ_nn
        set VS : ℝ := ∑ k ∈ F, w k * (S k - μS) ^ 2
        set VB : ℝ := ∑ k ∈ F, w k * (B k - μB) ^ 2
        have hVS_nn : 0 ≤ VS := Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nn k) (sq_nonneg _))
        have hVB_nn : 0 ≤ VB := Finset.sum_nonneg (fun k _ => mul_nonneg (hw_nn k) (sq_nonneg _))
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
        have h_pt_F : ∀ k ∈ F, (m / 2) ^ 2 ≤ (S k - μS) ^ 2 + (B k - μB) ^ 2 := by
          intro k hk
          have hk_not : k ∉ E := (Finset.mem_sdiff.mp hk).2
          have hnot : ¬ (S k ≤ p_hat ∧ p_hat ≤ B k) := fun hc =>
            hk_not (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hc⟩)
          by_cases hSp : S k ≤ p_hat
          · have hBp : B k < p_hat := by push_neg at hnot; exact hnot hSp
            have hdiff : m / 2 < μB - B k := by dsimp [p_hat, m] at *; linarith
            nlinarith [sq_nonneg (S k - μS)]
          · push_neg at hSp
            have hdiff : m / 2 < S k - μS := by dsimp [p_hat, m] at *; linarith
            nlinarith [sq_nonneg (B k - μB)]
        have h_W2_lb : β * (m / 2) ^ 2 ≤ W ^ 2 := by
          have h_sum_le : ∑ k ∈ F, w k * (m / 2) ^ 2 ≤
              ∑ k ∈ F, w k * ((S k - μS) ^ 2 + (B k - μB) ^ 2) :=
            Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (h_pt_F k hk) (hw_nn k))
          have h_lhs : ∑ k ∈ F, w k * (m / 2) ^ 2 = β * (m / 2) ^ 2 :=
            (Finset.sum_mul _ _ _).symm
          have h_rhs : ∑ k ∈ F, w k * ((S k - μS) ^ 2 + (B k - μB) ^ 2) = VS + VB := by
            have h1 : ∀ k : Fin K, w k * ((S k - μS) ^ 2 + (B k - μB) ^ 2) =
                w k * (S k - μS) ^ 2 + w k * (B k - μB) ^ 2 := fun _ => by ring
            simp_rw [h1, Finset.sum_add_distrib]
            rfl
          rw [h_lhs, h_rhs, ← hW_sq] at h_sum_le
          exact h_sum_le
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
        have h_pt_loss : ∀ k ∈ F,
            ν * max (B k - S k) 0 ≤ 2 * ((S k - μS) ^ 2 + (B k - μB) ^ 2) + 2 * ν ^ 2 := by
          intro k hk
          set u : ℝ := S k - μS
          set v : ℝ := B k - μB
          have huv : (m / 2) ^ 2 ≤ u ^ 2 + v ^ 2 := h_pt_F k hk
          have hBS_eq : B k - S k = m + v - u := by dsimp [u, v, m]; ring
          have h_sos : 2 * (u ^ 2 + v ^ 2) + 2 * ν ^ 2 - ν * (m + v - u) =
              (u ^ 2 + v ^ 2 - (m / 2) ^ 2) + (m / 2 - ν) ^ 2 +
              (u + ν / 2) ^ 2 + (v - ν / 2) ^ 2 + ν ^ 2 / 2 := by ring
          have h_lin : ν * (B k - S k) ≤ 2 * (u ^ 2 + v ^ 2) + 2 * ν ^ 2 := by
            rw [hBS_eq]
            nlinarith [h_sos, huv, sq_nonneg (m / 2 - ν),
                       sq_nonneg (u + ν / 2), sq_nonneg (v - ν / 2), sq_nonneg ν]
          by_cases hpos : 0 ≤ B k - S k
          · rwa [max_eq_left hpos]
          · push_neg at hpos
            rw [max_eq_right hpos.le, mul_zero]
            positivity
        have h_sum_loss : ν * L_fn p_hat ≤ 4 * β * ν ^ 2 := by
          have h_le : ∑ k ∈ F, w k * (ν * max (B k - S k) 0) ≤
              ∑ k ∈ F, w k * (2 * ((S k - μS) ^ 2 + (B k - μB) ^ 2) + 2 * ν ^ 2) :=
            Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (h_pt_loss k hk) (hw_nn k))
          have h_lhs : ∑ k ∈ F, w k * (ν * max (B k - S k) 0) = ν * L_fn p_hat := by
            change ∑ k ∈ F, w k * (ν * max (B k - S k) 0) =
              ν * ∑ k ∈ F, w k * max (B k - S k) 0
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun k _ => by ring)
          have h_rhs : ∑ k ∈ F, w k * (2 * ((S k - μS) ^ 2 + (B k - μB) ^ 2) + 2 * ν ^ 2) =
              2 * (VS + VB) + 2 * β * ν ^ 2 := by
            have h1 : ∀ k : Fin K,
                w k * (2 * ((S k - μS) ^ 2 + (B k - μB) ^ 2) + 2 * ν ^ 2) =
                (2 * (w k * (S k - μS) ^ 2) + 2 * (w k * (B k - μB) ^ 2)) +
                  w k * (2 * ν ^ 2) := fun _ => by ring
            simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
            ring
          rw [h_lhs, h_rhs] at h_le
          linarith [h_le, hβ_ν2]
        have hL_ub : L_fn p_hat ≤ 4 * rβ * W := by
          have h1 : L_fn p_hat ≤ 4 * β * ν := by nlinarith
          have h2 : 4 * β * ν = 4 * rβ * W := by
            calc 4 * β * ν = 4 * rβ * (rβ * ν) := by rw [← hrβ_sq]; ring
              _ = 4 * rβ * W := by rw [hrβ_ν]
          linarith
        have h_compl_F : Finset.univ \ F = E :=
          sdiff_sdiff_eq_self (Finset.subset_univ E)
        have h_radS_F : (rβ * σS - rS) ^ 2 ≤ 2 * σS * dS_fn p_hat := by
          have hr : (rβ * σS - rS) ^ 2 ≤
              2 * σS * (σS - finWeightedStdDev w F S - finWeightedStdDev w (Finset.univ \ F) S) :=
            (h_drop S F).2.2
          rw [h_compl_F] at hr
          have h_eq_d : σS - finWeightedStdDev w F S - finWeightedStdDev w E S = dS_fn p_hat := by
            change σS - finWeightedStdDev w F S - finWeightedStdDev w E S =
              σS - finWeightedStdDev w E S - finWeightedStdDev w F S
            ring
          rwa [h_eq_d] at hr
        have h_radB_F : (rβ * σB - rB) ^ 2 ≤ 2 * σB * dB_fn p_hat := by
          have hr : (rβ * σB - rB) ^ 2 ≤
              2 * σB * (σB - finWeightedStdDev w F B - finWeightedStdDev w (Finset.univ \ F) B) :=
            (h_drop B F).2.2
          rw [h_compl_F] at hr
          have h_eq_d : σB - finWeightedStdDev w F B - finWeightedStdDev w E B = dB_fn p_hat := by
            change σB - finWeightedStdDev w F B - finWeightedStdDev w E B =
              σB - finWeightedStdDev w E B - finWeightedStdDev w F B
            ring
          rwa [h_eq_d] at hr
        have h_sum_rad :
            (rS - rβ * σS) ^ 2 + (rB - rβ * σB) ^ 2 ≤
              2 * σ * (dS_fn p_hat + dB_fn p_hat) := by
          have hDS := hdS_nn p_hat
          have hDB := hdB_nn p_hat
          have h1 : 2 * σS * dS_fn p_hat ≤ 2 * σ * dS_fn p_hat := by dsimp [σ]; nlinarith
          have h2 : 2 * σB * dB_fn p_hat ≤ 2 * σ * dB_fn p_hat := by dsimp [σ]; nlinarith
          nlinarith
        have hrSrB_lb : W ≤ rS + rB := by
          have hsq : W ^ 2 ≤ (rS + rB) ^ 2 := by
            nlinarith [hW_sq, hrS_sq, hrB_sq, mul_nonneg hrS_nn hrB_nn]
          nlinarith [hrS_nn, hrB_nn]
        set devS : ℝ := rS - rβ * σS
        set devB : ℝ := rB - rβ * σB
        have hdev_lb : W / 3 ≤ devS + devB := by
          dsimp [devS, devB, σ] at *
          linarith
        have hdev_sq : W ^ 2 / 18 ≤ devS ^ 2 + devB ^ 2 := by
          have h1 : (W / 3) ^ 2 ≤ (devS + devB) ^ 2 := by nlinarith
          have h2 : (devS + devB) ^ 2 ≤ 2 * (devS ^ 2 + devB ^ 2) := by
            nlinarith [sq_nonneg (devS - devB)]
          linarith
        have hW2_prod : (rβ * W * σ) / 12 ≤ W ^ 2 / 18 := by
          have hmul : W * ((3 / 2 : ℝ) * rβ * σ) ≤ W * W :=
            mul_le_mul_of_nonneg_left hW_lb hW_nn
          linarith
        have hD_lb : rβ * W ≤ 24 * (dS_fn p_hat + dB_fn p_hat) := by
          have h_comb : (rβ * W * σ) / 12 ≤ 2 * σ * (dS_fn p_hat + dB_fn p_hat) :=
            le_trans hW2_prod (le_trans hdev_sq h_sum_rad)
          nlinarith
        have := hdS_nn p_hat
        have := hdB_nn p_hat
        linarith

theorem lem_directional_and_tangent_bounds {d K : ℕ}
    (w : Fin K → ℝ) (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1)
    (Z : Fin K → (Fin d → ℝ)) (hZ : ∀ k, vecL2Norm (Z k) ≤ 1)
    (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosDef)
    (x : Fin d → ℝ) (hx : vecL2Norm x ≤ 1)
    (E : Finset (Fin K))
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ (m1 m0 : Fin d → ℝ) (R1 R0 : Matrix (Fin d) (Fin d) ℝ),
      R1.PosDef ∧ R0.PosDef ∧
      vecL2Norm m1 ≤ 1 ∧ vecL2Norm m0 ≤ 1 ∧
      Matrix.trace R1 ≤ 2 * (d : ℝ) ∧ Matrix.trace R0 ≤ 2 * (d : ℝ) ∧
      (∀ u v : Fin d → ℝ, |dotProduct u (R1⁻¹.mulVec v)| ≤ τ⁻¹ * vecL2Norm u * vecL2Norm v) ∧
      (∀ u v : Fin d → ℝ, |dotProduct u (R0⁻¹.mulVec v)| ≤ τ⁻¹ * vecL2Norm u * vecL2Norm v) ∧
      2 * (finWeightedStdDev w Finset.univ (fun k => dotProduct x (Z k)) -
            finWeightedStdDev w E (fun k => dotProduct x (Z k)) -
            finWeightedStdDev w (Finset.univ \ E) (fun k => dotProduct x (Z k))) +
        (∑ k ∈ E, w k * agentQuadPotential m1 R1 (Z k)) +
        (∑ k ∈ Finset.univ \ E, w k * agentQuadPotential m0 R0 (Z k)) ≤
        (∑ k, w k * agentQuadPotential m R (Z k)) + (d : ℝ) * τ :=
by
  
  have h_sqrt_psd : ∀ {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef), hA.sqrt.PosSemidef := by
    intro A hA
    unfold Matrix.PosSemidef.sqrt
    let f : Fin d → ℝ := RCLike.ofReal ∘ (fun t : ℝ => √t) ∘ hA.isHermitian.eigenvalues
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
    let f : Fin d → ℝ := RCLike.ofReal ∘ (fun t : ℝ => √t) ∘ hA.isHermitian.eigenvalues
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

  have h_norm_nonneg : ∀ v : Fin d → ℝ, 0 ≤ vecL2Norm v :=
    fun _ => Real.sqrt_nonneg _
  have h_norm_zero : vecL2Norm (0 : Fin d → ℝ) = 0 := by
    simp [vecL2Norm]
  have h_norm_sq : ∀ v : Fin d → ℝ, vecL2Norm v ^ 2 = ∑ i, (v i) ^ 2 :=
    fun v => Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))
  have h_norm_sq_dot : ∀ v : Fin d → ℝ, dotProduct v v = vecL2Norm v ^ 2 := by
    intro v
    rw [h_norm_sq v]
    simp [dotProduct, sq]
  have h_cs : ∀ u v : Fin d → ℝ, dotProduct u v ≤ vecL2Norm u * vecL2Norm v :=
    fun u v => Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v
  have h_abs_cs : ∀ u v : Fin d → ℝ, |dotProduct u v| ≤ vecL2Norm u * vecL2Norm v := by
    intro u v
    have h_neg_norm : vecL2Norm (-u) = vecL2Norm u := by
      simp [vecL2Norm]
    refine abs_le.mpr ⟨?_, h_cs u v⟩
    have h1 := h_cs (-u) v
    rw [neg_dotProduct, h_neg_norm] at h1
    linarith

  have h_outer_herm : ∀ u : Fin d → ℝ, (Matrix.vecMulVec u u).IsHermitian := by
    intro u
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have h_outer_quad :
      ∀ u y : Fin d → ℝ, dotProduct y ((Matrix.vecMulVec u u).mulVec y) = (dotProduct u y) ^ 2 := by
    intro u y
    calc dotProduct y ((Matrix.vecMulVec u u).mulVec y)
        = ∑ i, (u i * y i) * (∑ j, u j * y j) := by
            simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = (∑ i, u i * y i) * (∑ j, u j * y j) := by rw [← Finset.sum_mul]
      _ = (dotProduct u y) ^ 2 := by simp [dotProduct, sq]
  have h_outer_psd : ∀ u : Fin d → ℝ, (Matrix.vecMulVec u u).PosSemidef := by
    intro u
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (h_outer_herm u) fun y => ?_
    simp only [star_trivial, h_outer_quad u y]
    exact sq_nonneg _
  have h_outer_trace_left :
      ∀ (u : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ),
        Matrix.trace (Matrix.vecMulVec u u * B) = dotProduct u (B.mulVec u) := by
    intro u B
    calc Matrix.trace (Matrix.vecMulVec u u * B)
        = ∑ i, ∑ j, (u i * u j) * B j i := by
            simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply]
      _ = ∑ j, ∑ i, (u i * u j) * B j i := Finset.sum_comm
      _ = ∑ j, u j * (∑ i, B j i * u i) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
      _ = dotProduct u (B.mulVec u) := rfl
  have h_outer_trace_right :
      ∀ (u : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ),
        Matrix.trace (B * Matrix.vecMulVec u u) = dotProduct u (B.mulVec u) := by
    intro u B
    rw [Matrix.trace_mul_comm B (Matrix.vecMulVec u u)]
    exact h_outer_trace_left u B
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
        ∀ y : Fin d → ℝ, dotProduct y ((A * A).mulVec y) = vecL2Norm (A.mulVec y) ^ 2 := by
    intro A hA y
    rw [← Matrix.mulVec_mulVec, h_herm_dot A hA y (A.mulVec y), h_norm_sq_dot]
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

  
  let p_fn : Finset (Fin K) → ℝ := fun A => ∑ k ∈ A, w k
  let m_fn : Finset (Fin K) → (Fin d → ℝ) := fun A => (p_fn A)⁻¹ • ∑ k ∈ A, w k • Z k
  let S_fn : Finset (Fin K) → Matrix (Fin d) (Fin d) ℝ :=
    fun A => (p_fn A)⁻¹ • ∑ k ∈ A, w k • Matrix.vecMulVec (Z k - m_fn A) (Z k - m_fn A)

  have hp_nn : ∀ A : Finset (Fin K), 0 ≤ p_fn A :=
    fun A => Finset.sum_nonneg fun k _ => hw_nn k
  have hp_zero_w : ∀ (A : Finset (Fin K)), p_fn A = 0 → ∀ k ∈ A, w k = 0 :=
    fun A hp0 => (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hw_nn k).mp hp0
  have hS_fn_psd : ∀ A : Finset (Fin K), (S_fn A).PosSemidef := by
    intro A
    have h_sum_psd :
        (∑ k ∈ A, w k • Matrix.vecMulVec (Z k - m_fn A) (Z k - m_fn A)).PosSemidef :=
      Matrix.posSemidef_sum A fun k _ => (h_outer_psd (Z k - m_fn A)).smul (hw_nn k)
    exact h_sum_psd.smul (inv_nonneg.mpr (hp_nn A))
  have h_pm_eq : ∀ A : Finset (Fin K), p_fn A • m_fn A = ∑ k ∈ A, w k • Z k := by
    intro A
    rcases eq_or_lt_of_le (hp_nn A) with hp0 | hp_pos
    · have hp0' : p_fn A = 0 := hp0.symm
      rw [hp0', zero_smul]
      symm
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [hp_zero_w A hp0' k hk, zero_smul]
    · dsimp [m_fn]
      rw [smul_smul, mul_inv_cancel₀ hp_pos.ne', one_smul]
  have h_pm_coord :
      ∀ (A : Finset (Fin K)) (i : Fin d), p_fn A * m_fn A i = ∑ k ∈ A, w k * Z k i := by
    intro A i
    have h := congr_fun (h_pm_eq A) i
    simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using h
  have h_pm_dot :
      ∀ (A : Finset (Fin K)) (y : Fin d → ℝ),
        p_fn A * dotProduct y (m_fn A) = ∑ k ∈ A, w k * dotProduct y (Z k) := by
    intro A y
    calc p_fn A * dotProduct y (m_fn A)
        = ∑ i : Fin d, y i * (p_fn A * m_fn A i) := by
            simp only [dotProduct, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i : Fin d, y i * (∑ k ∈ A, w k * Z k i) := by
            refine Finset.sum_congr rfl fun i _ => by rw [h_pm_coord A i]
      _ = ∑ i : Fin d, ∑ k ∈ A, y i * (w k * Z k i) := by
            refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ = ∑ k ∈ A, ∑ i : Fin d, y i * (w k * Z k i) := Finset.sum_comm
      _ = ∑ k ∈ A, w k * dotProduct y (Z k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [dotProduct, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
  have hm_fn_norm : ∀ A : Finset (Fin K), vecL2Norm (m_fn A) ≤ 1 := by
    intro A
    rcases eq_or_lt_of_le (hp_nn A) with hp0 | hp_pos
    · have hp0' : p_fn A = 0 := hp0.symm
      have hm0 : m_fn A = 0 := by simp [m_fn, hp0']
      rw [hm0, h_norm_zero]
      norm_num
    · set nm := vecL2Norm (m_fn A)
      have hnm_nn : 0 ≤ nm := h_norm_nonneg (m_fn A)
      have h_lhs : p_fn A * nm ^ 2 = ∑ k ∈ A, w k * dotProduct (m_fn A) (Z k) := by
        rw [← h_norm_sq_dot (m_fn A)]
        exact h_pm_dot A (m_fn A)
      have h_rhs : ∑ k ∈ A, w k * dotProduct (m_fn A) (Z k) ≤ p_fn A * nm := by
        calc ∑ k ∈ A, w k * dotProduct (m_fn A) (Z k)
            ≤ ∑ k ∈ A, w k * nm := by
                refine Finset.sum_le_sum fun k _ => ?_
                have h1 : dotProduct (m_fn A) (Z k) ≤ nm * vecL2Norm (Z k) := h_cs (m_fn A) (Z k)
                have h2 : nm * vecL2Norm (Z k) ≤ nm * 1 :=
                  mul_le_mul_of_nonneg_left (hZ k) hnm_nn
                exact mul_le_mul_of_nonneg_left (by linarith) (hw_nn k)
          _ = p_fn A * nm := by rw [← Finset.sum_mul]
      have h_sq_le : nm ^ 2 ≤ nm := by nlinarith
      nlinarith
  have h_master_outer :
      ∀ (A : Finset (Fin K)) (c : Fin d → ℝ),
        ∑ k ∈ A, w k • Matrix.vecMulVec (Z k - c) (Z k - c) =
          p_fn A • S_fn A + p_fn A • Matrix.vecMulVec (m_fn A - c) (m_fn A - c) := by
    intro A c
    rcases eq_or_lt_of_le (hp_nn A) with hp0 | hp_pos
    · have hp0' : p_fn A = 0 := hp0.symm
      rw [hp0', zero_smul, zero_smul, add_zero]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [hp_zero_w A hp0' k hk, zero_smul]
    · have hpS :
          p_fn A • S_fn A =
            ∑ k ∈ A, w k • Matrix.vecMulVec (Z k - m_fn A) (Z k - m_fn A) := by
        dsimp [S_fn]
        rw [smul_smul, mul_inv_cancel₀ hp_pos.ne', one_smul]
      have h_res_zero : ∀ i : Fin d, ∑ k ∈ A, w k * (Z k i - m_fn A i) = 0 := by
        intro i
        have h_sub :
            ∑ k ∈ A, w k * (Z k i - m_fn A i) =
              (∑ k ∈ A, w k * Z k i) - (∑ k ∈ A, w k) * m_fn A i := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [h_sub, ← h_pm_coord A i]
        ring
      rw [hpS]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
      have h_pt :
          ∀ k : Fin K,
            w k * ((Z k i - c i) * (Z k j - c j)) =
              (w k * ((Z k i - m_fn A i) * (Z k j - m_fn A j)) +
                (w k * (Z k i - m_fn A i)) * (m_fn A j - c j)) +
              ((m_fn A i - c i) * (w k * (Z k j - m_fn A j)) +
                w k * ((m_fn A i - c i) * (m_fn A j - c j))) := fun _ => by ring
      simp_rw [h_pt]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul,
          h_res_zero i, h_res_zero j]
      dsimp [p_fn]
      ring
  have h_master_quad :
      ∀ (A : Finset (Fin K)) (B : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ),
        ∑ k ∈ A, w k * dotProduct (Z k - c) (B.mulVec (Z k - c)) =
          p_fn A * Matrix.trace (B * S_fn A) +
            p_fn A * dotProduct (m_fn A - c) (B.mulVec (m_fn A - c)) := by
    intro A B c
    have h_congr := congr_arg (fun M => Matrix.trace (B * M)) (h_master_outer A c)
    have h_lhs :
        Matrix.trace (B * ∑ k ∈ A, w k • Matrix.vecMulVec (Z k - c) (Z k - c)) =
          ∑ k ∈ A, w k * dotProduct (Z k - c) (B.mulVec (Z k - c)) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, h_outer_trace_right (Z k - c) B]
    have h_rhs :
        Matrix.trace (B * (p_fn A • S_fn A + p_fn A • Matrix.vecMulVec (m_fn A - c) (m_fn A - c))) =
          p_fn A * Matrix.trace (B * S_fn A) +
            p_fn A * dotProduct (m_fn A - c) (B.mulVec (m_fn A - c)) := by
      have h1 : Matrix.trace (B * (p_fn A • S_fn A)) = p_fn A * Matrix.trace (B * S_fn A) := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      have h2 : Matrix.trace (B * (p_fn A • Matrix.vecMulVec (m_fn A - c) (m_fn A - c))) =
          p_fn A * dotProduct (m_fn A - c) (B.mulVec (m_fn A - c)) := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, h_outer_trace_right (m_fn A - c) B]
      rw [mul_add, Matrix.trace_add, h1, h2]
    linarith
  have hS_fn_tr : ∀ A : Finset (Fin K), Matrix.trace (S_fn A) ≤ 1 := by
    intro A
    rcases eq_or_lt_of_le (hp_nn A) with hp0 | hp_pos
    · have hp0' : p_fn A = 0 := hp0.symm
      have hS0 : S_fn A = 0 := by simp [S_fn, hp0']
      rw [hS0, Matrix.trace_zero]
      norm_num
    · have hq := h_master_quad A 1 0
      simp only [sub_zero, Matrix.one_mulVec, Matrix.one_mul, h_norm_sq_dot] at hq
      have h_lhs_le : ∑ k ∈ A, w k * vecL2Norm (Z k) ^ 2 ≤ p_fn A := by
        calc ∑ k ∈ A, w k * vecL2Norm (Z k) ^ 2
            ≤ ∑ k ∈ A, w k * 1 := by
                refine Finset.sum_le_sum fun k _ => ?_
                have hZk_sq : vecL2Norm (Z k) ^ 2 ≤ 1 := by
                  nlinarith [hZ k, h_norm_nonneg (Z k)]
                exact mul_le_mul_of_nonneg_left hZk_sq (hw_nn k)
          _ = p_fn A := by simp [p_fn]
      have h_m_nn : 0 ≤ p_fn A * vecL2Norm (m_fn A) ^ 2 :=
        mul_nonneg hp_pos.le (sq_nonneg _)
      have hp_tr : p_fn A * Matrix.trace (S_fn A) ≤ p_fn A * 1 := by linarith
      nlinarith
  have h_wsd_eq :
      ∀ A : Finset (Fin K),
        finWeightedStdDev w A (fun k => dotProduct x (Z k)) =
          p_fn A * Real.sqrt (dotProduct x ((S_fn A).mulVec x)) := by
    intro A
    have hq := h_master_quad A (Matrix.vecMulVec x x) 0
    simp only [sub_zero, h_outer_quad x, h_outer_trace_left x (S_fn A)] at hq
    have h_rad :
        (∑ k ∈ A, w k) * (∑ k ∈ A, w k * (dotProduct x (Z k)) ^ 2) -
          (∑ k ∈ A, w k * dotProduct x (Z k)) ^ 2 =
        (p_fn A) ^ 2 * dotProduct x ((S_fn A).mulVec x) := by
      rw [← h_pm_dot A x]
      change p_fn A * (∑ k ∈ A, w k * (dotProduct x (Z k)) ^ 2) -
        (p_fn A * dotProduct x (m_fn A)) ^ 2 = _
      linear_combination p_fn A * hq
    unfold finWeightedStdDev
    rw [h_rad, Real.sqrt_mul (sq_nonneg (p_fn A)), Real.sqrt_sq (hp_nn A)]
  have h_post_pot :
      ∀ (A : Finset (Fin K)) (Q : Matrix (Fin d) (Fin d) ℝ),
        ∑ k ∈ A, w k * agentQuadPotential (m_fn A) Q (Z k) =
          p_fn A * (Matrix.trace Q + Matrix.trace (Q⁻¹ * S_fn A)) := by
    intro A Q
    have hq := h_master_quad A Q⁻¹ (m_fn A)
    simp only [sub_self, Matrix.mulVec_zero, dotProduct_zero, mul_zero, add_zero] at hq
    have h_split :
        ∑ k ∈ A, w k * agentQuadPotential (m_fn A) Q (Z k) =
          (∑ k ∈ A, w k * Matrix.trace Q) +
            ∑ k ∈ A, w k * dotProduct (Z k - m_fn A) (Q⁻¹.mulVec (Z k - m_fn A)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by dsimp [agentQuadPotential]; ring
    rw [h_split, ← Finset.sum_mul, hq]
    dsimp [p_fn]
    ring

  let Ec : Finset (Fin K) := Finset.univ \ E
  let p1 : ℝ := p_fn E
  let p0 : ℝ := p_fn Ec
  let μ : Fin d → ℝ := m_fn Finset.univ
  let m1 : Fin d → ℝ := m_fn E
  let m0 : Fin d → ℝ := m_fn Ec
  let S : Matrix (Fin d) (Fin d) ℝ := S_fn Finset.univ
  let S1 : Matrix (Fin d) (Fin d) ℝ := S_fn E
  let S0 : Matrix (Fin d) (Fin d) ℝ := S_fn Ec
  have hS_psd : S.PosSemidef := hS_fn_psd Finset.univ
  have hS1_psd : S1.PosSemidef := hS_fn_psd E
  have hS0_psd : S0.PosSemidef := hS_fn_psd Ec
  have hp_univ : p_fn Finset.univ = 1 := hw_sum
  have hp1_nn : 0 ≤ p1 := hp_nn E
  have hp0_nn : 0 ≤ p0 := hp_nn Ec
  have hp_sum : p1 + p0 = 1 := by
    have h_sdiff : p0 + p1 = p_fn Finset.univ := Finset.sum_sdiff (Finset.subset_univ E)
    linarith [hp_univ]
  have h_prior_pot :
      Matrix.trace R + Matrix.trace (R⁻¹ * S) ≤
        ∑ k, w k * agentQuadPotential m R (Z k) := by
    have hq := h_master_quad Finset.univ R⁻¹ m
    rw [hp_univ, one_mul, one_mul] at hq
    have h_bias_nn : 0 ≤ dotProduct (μ - m) (R⁻¹.mulVec (μ - m)) := by
      simpa using hR.inv.posSemidef.dotProduct_mulVec_nonneg (μ - m)
    have h_split :
        ∑ k, w k * agentQuadPotential m R (Z k) =
          (∑ k, w k * Matrix.trace R) +
            ∑ k, w k * dotProduct (Z k - m) (R⁻¹.mulVec (Z k - m)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by dsimp [agentQuadPotential]; ring
    rw [h_split, ← Finset.sum_mul, hw_sum, one_mul]
    dsimp [S, μ] at *
    linarith
  have h_tot_cov : (S - (p1 • S1 + p0 • S0)).PosSemidef := by
    have h_u := h_master_outer Finset.univ μ
    have h_zero_outer : Matrix.vecMulVec (μ - μ) (μ - μ) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [hp_univ, one_smul, one_smul, h_zero_outer, add_zero] at h_u
    have h_part :
        (∑ k ∈ Ec, w k • Matrix.vecMulVec (Z k - μ) (Z k - μ)) +
          (∑ k ∈ E, w k • Matrix.vecMulVec (Z k - μ) (Z k - μ)) =
        ∑ k : Fin K, w k • Matrix.vecMulVec (Z k - μ) (Z k - μ) :=
      Finset.sum_sdiff (Finset.subset_univ E)
    rw [← h_part, h_master_outer Ec μ, h_master_outer E μ] at h_u
    have h_diff_eq :
        S - (p1 • S1 + p0 • S0) =
          p1 • Matrix.vecMulVec (m1 - μ) (m1 - μ) +
            p0 • Matrix.vecMulVec (m0 - μ) (m0 - μ) := by
      dsimp [S, S1, S0, p1, p0, m1, m0] at h_u ⊢
      rw [← h_u]
      abel
    rw [h_diff_eq]
    exact ((h_outer_psd (m1 - μ)).smul hp1_nn).add
      ((h_outer_psd (m0 - μ)).smul hp0_nn)

  
  have h_trace_sq_id :
      ∀ (Q A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef), Q.PosDef →
        Matrix.trace (Q⁻¹ * ((hA.sqrt - Q) * (hA.sqrt - Q))) =
          Matrix.trace (Q⁻¹ * A) - 2 * Matrix.trace hA.sqrt + Matrix.trace Q := by
    intro Q A hA hQ
    set T := hA.sqrt
    have hTT : T * T = A := h_sqrt_sq hA
    have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
    have hQQinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
    have hQinvQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdet
    have hexp : Q⁻¹ * ((T - Q) * (T - Q)) = Q⁻¹ * A - Q⁻¹ * T * Q - T + Q := by
      rw [mul_sub, sub_mul, sub_mul, hTT]
      simp only [mul_sub, ← Matrix.mul_assoc, hQinvQ, Matrix.one_mul]
      abel
    have htr_cycle : Matrix.trace (Q⁻¹ * T * Q) = Matrix.trace T := by
      calc Matrix.trace (Q⁻¹ * T * Q)
          = Matrix.trace (Q * (Q⁻¹ * T)) := Matrix.trace_mul_comm (Q⁻¹ * T) Q
        _ = Matrix.trace ((Q * Q⁻¹) * T) := by rw [Matrix.mul_assoc]
        _ = Matrix.trace T := by rw [hQQinv, Matrix.one_mul]
    rw [hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, htr_cycle]
    ring
  have h_tang_lb :
      ∀ (Q A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef), Q.PosDef →
        2 * Matrix.trace hA.sqrt ≤ Matrix.trace Q + Matrix.trace (Q⁻¹ * A) := by
    intro Q A hA hQ
    set T := hA.sqrt
    set M := (T - Q) * (T - Q)
    have hT_psd : T.PosSemidef := h_sqrt_psd hA
    have hTQ_herm : (T - Q).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hT_psd.isHermitian.eq, hQ.isHermitian.eq]
    have hM_psd : M.PosSemidef := by
      have : M = (T - Q).conjTranspose * (T - Q) := by rw [hTQ_herm.eq]
      rw [this]
      exact Matrix.posSemidef_conjTranspose_mul_self (T - Q)
    have h_tr_nn : 0 ≤ Matrix.trace (Q⁻¹ * M) :=
      h_trace_psd Q⁻¹ M hQ.inv.posSemidef hM_psd
    have h_id := h_trace_sq_id Q A hA hQ
    linarith
  have h_reg_base :
      ∀ (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) (η : ℝ), 0 < η →
        (hA.sqrt + η • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef ∧
        (η⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) -
          (hA.sqrt + η • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹).PosSemidef ∧
        Matrix.trace (hA.sqrt + η • (1 : Matrix (Fin d) (Fin d) ℝ)) +
          Matrix.trace ((hA.sqrt + η • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ * A) ≤
          2 * Matrix.trace hA.sqrt + (d : ℝ) * η := by
    intro A hA η hη
    set T := hA.sqrt
    set Rη : Matrix (Fin d) (Fin d) ℝ := T + η • 1
    have hT_psd : T.PosSemidef := h_sqrt_psd hA
    have hRη_pd : Rη.PosDef :=
      Matrix.PosDef.posSemidef_add hT_psd (Matrix.PosDef.one.smul hη)
    have hη_ne : η ≠ 0 := hη.ne'
    have hdet : IsUnit Rη.det := (Matrix.isUnit_iff_isUnit_det Rη).mp hRη_pd.isUnit
    have hRRinv : Rη * Rη⁻¹ = 1 := Matrix.mul_nonsing_inv Rη hdet
    have hRinvR : Rη⁻¹ * Rη = 1 := Matrix.nonsing_inv_mul Rη hdet
    let P : Matrix (Fin d) (Fin d) ℝ := η⁻¹ • A + T
    have hP_psd : P.PosSemidef := (hA.smul (inv_nonneg.mpr hη.le)).add hT_psd
    have hTT : T * T = A := h_sqrt_sq hA
    have hRη_sq : Rη * Rη = A + (2 * η) • T + (η ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      dsimp [Rη]
      rw [add_mul, mul_add, mul_add, hTT]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have h_congr_eq :
        η⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rη⁻¹ =
          Rη⁻¹ * P * (Rη⁻¹).conjTranspose := by
      have h_mid : Rη * (η⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rη⁻¹) * Rη = P := by
        rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, hRRinv,
            Matrix.smul_mul, Matrix.one_mul, hRη_sq]
        ext i j
        dsimp [P, Rη]
        simp only [Matrix.one_apply]
        field_simp
        ring
      rw [hRη_pd.inv.isHermitian.eq, ← h_mid]
      calc η⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rη⁻¹
          = 1 * (η⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rη⁻¹) * 1 := by
              rw [Matrix.one_mul, Matrix.mul_one]
        _ = (Rη⁻¹ * Rη) * (η⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rη⁻¹) * (Rη * Rη⁻¹) := by
              rw [hRinvR, hRRinv]
        _ = Rη⁻¹ * (Rη * (η⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rη⁻¹) * Rη) * Rη⁻¹ := by
              simp only [Matrix.mul_assoc]
    have h_diff_psd : (η⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rη⁻¹).PosSemidef := by
      rw [h_congr_eq]
      exact hP_psd.mul_mul_conjTranspose_same Rη⁻¹
    have htr_ray :
        Matrix.trace Rη + Matrix.trace (Rη⁻¹ * A) =
          2 * Matrix.trace T + η ^ 2 * Matrix.trace (Rη⁻¹) := by
      have h_id := h_trace_sq_id Rη A hA hRη_pd
      have h_diff : T - Rη = -(η • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
        dsimp [Rη]
        abel
      have h_lhs :
          Matrix.trace (Rη⁻¹ * ((T - Rη) * (T - Rη))) = η ^ 2 * Matrix.trace (Rη⁻¹) := by
        rw [h_diff]
        simp [sq, mul_assoc, Matrix.trace_smul]
      linarith [h_id, h_lhs]
    have htr_inv_bound : η ^ 2 * Matrix.trace (Rη⁻¹) ≤ (d : ℝ) * η := by
      have h_tr_nonneg : 0 ≤ η⁻¹ * (d : ℝ) - Matrix.trace (Rη⁻¹) := by
        simpa [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] using h_diff_psd.trace_nonneg
      have h_mul := mul_le_mul_of_nonneg_left h_tr_nonneg (sq_nonneg η)
      have h_simp : η ^ 2 * (η⁻¹ * (d : ℝ) - Matrix.trace (Rη⁻¹)) =
          (d : ℝ) * η - η ^ 2 * Matrix.trace (Rη⁻¹) := by
        field_simp
      linarith
    exact ⟨hRη_pd, h_diff_psd, by linarith⟩
  have h_reg_extra :
      ∀ (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef), Matrix.trace A ≤ 1 →
        Matrix.trace (hA.sqrt + τ • (1 : Matrix (Fin d) (Fin d) ℝ)) ≤ 2 * (d : ℝ) ∧
        (∀ u v : Fin d → ℝ,
          |dotProduct u ((hA.sqrt + τ • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹.mulVec v)| ≤
            τ⁻¹ * vecL2Norm u * vecL2Norm v) := by
    intro A hA hA_tr
    set Rτ : Matrix (Fin d) (Fin d) ℝ := hA.sqrt + τ • 1
    obtain ⟨hRτ_pd, h_diff_psd, _⟩ := h_reg_base A hA τ hτ0
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
      · have huniv_empty : (Finset.univ : Finset (Fin d)) = ∅ := by
          ext i
          have hi := i.isLt
          omega
        simp [Matrix.trace, huniv_empty, hd0]
      · have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd_pos
        have h1_inv : (1 : Matrix (Fin d) (Fin d) ℝ)⁻¹ = 1 := by
          have hdet1 : IsUnit (1 : Matrix (Fin d) (Fin d) ℝ).det := by simp
          have hm := Matrix.mul_nonsing_inv (1 : Matrix (Fin d) (Fin d) ℝ) hdet1
          rwa [Matrix.one_mul] at hm
        have h2T : 2 * Matrix.trace hA.sqrt ≤ (d : ℝ) + Matrix.trace A := by
          have hlb := h_tang_lb 1 A hA Matrix.PosDef.one
          simpa [Matrix.trace_one, h1_inv] using hlb
        have hT_le : Matrix.trace hA.sqrt ≤ (d : ℝ) := by linarith
        have hRτ_tr : Matrix.trace Rτ = Matrix.trace hA.sqrt + τ * (d : ℝ) := by
          simp [Rτ, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
        have hτd : τ * (d : ℝ) ≤ 1 * (d : ℝ) :=
          mul_le_mul_of_nonneg_right hτ1 (Nat.cast_nonneg d)
        linarith
    · intro u v
      have hInv_psd : (Rτ⁻¹).PosSemidef := hRτ_pd.inv.posSemidef
      let K := hInv_psd.sqrt
      have hK_psd : K.PosSemidef := h_sqrt_psd hInv_psd
      have hKK : K * K = Rτ⁻¹ := h_sqrt_sq hInv_psd
      have hKy_sq : ∀ y : Fin d → ℝ, vecL2Norm (K.mulVec y) ^ 2 ≤ τ⁻¹ * vecL2Norm y ^ 2 := by
        intro y
        have h_id : vecL2Norm (K.mulVec y) ^ 2 = dotProduct y (Rτ⁻¹.mulVec y) := by
          rw [← h_herm_sq_quad K hK_psd.isHermitian y, hKK]
        have h_nn : 0 ≤ dotProduct y ((τ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rτ⁻¹).mulVec y) := by
          simpa using h_diff_psd.dotProduct_mulVec_nonneg y
        have h_exp :
            dotProduct y ((τ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - Rτ⁻¹).mulVec y) =
              τ⁻¹ * vecL2Norm y ^ 2 - dotProduct y (Rτ⁻¹.mulVec y) := by
          simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
            smul_eq_mul, h_norm_sq_dot]
        linarith
      have h_dot_K : dotProduct u (Rτ⁻¹.mulVec v) = dotProduct (K.mulVec u) (K.mulVec v) := by
        rw [← hKK, ← Matrix.mulVec_mulVec, h_herm_dot K hK_psd.isHermitian u (K.mulVec v)]
      rw [h_dot_K]
      have h1 : |dotProduct (K.mulVec u) (K.mulVec v)| ≤
          vecL2Norm (K.mulVec u) * vecL2Norm (K.mulVec v) :=
        h_abs_cs (K.mulVec u) (K.mulVec v)
      set LHS := vecL2Norm (K.mulVec u) * vecL2Norm (K.mulVec v)
      set RHS := τ⁻¹ * vecL2Norm u * vecL2Norm v
      have hLHS_nn : 0 ≤ LHS := mul_nonneg (h_norm_nonneg _) (h_norm_nonneg _)
      have hRHS_nn : 0 ≤ RHS :=
        mul_nonneg (mul_nonneg (inv_nonneg.mpr hτ0.le) (h_norm_nonneg u)) (h_norm_nonneg v)
      have h_sq_le : LHS ^ 2 ≤ RHS ^ 2 := by
        have h_prod :
            vecL2Norm (K.mulVec u) ^ 2 * vecL2Norm (K.mulVec v) ^ 2 ≤
              (τ⁻¹ * vecL2Norm u ^ 2) * (τ⁻¹ * vecL2Norm v ^ 2) :=
          mul_le_mul (hKy_sq u) (hKy_sq v) (sq_nonneg _)
            (mul_nonneg (inv_nonneg.mpr hτ0.le) (sq_nonneg _))
        calc LHS ^ 2
            = vecL2Norm (K.mulVec u) ^ 2 * vecL2Norm (K.mulVec v) ^ 2 := by dsimp [LHS]; ring
          _ ≤ (τ⁻¹ * vecL2Norm u ^ 2) * (τ⁻¹ * vecL2Norm v ^ 2) := h_prod
          _ = RHS ^ 2 := by dsimp [RHS]; ring
      have h2 : LHS ≤ RHS := by nlinarith
      exact le_trans h1 h2

  
  let gapPot : ∀ (A : Matrix (Fin d) (Fin d) ℝ), A.PosSemidef → ℝ :=
    fun A hA => Matrix.trace hA.sqrt - Real.sqrt (dotProduct x (A.mulVec x))
  let envSlope : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ :=
    fun Q => if x = 0 then Q⁻¹ else Q⁻¹ - (vecL2Norm (Q.mulVec x))⁻¹ • Matrix.vecMulVec x x
  let envObj : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ → ℝ :=
    fun Q A => Matrix.trace Q - vecL2Norm (Q.mulVec x) + Matrix.trace (envSlope Q * A)

  have h_norm_pos_of_posDef :
      ∀ (Q : Matrix (Fin d) (Fin d) ℝ), Q.PosDef → x ≠ 0 → 0 < vecL2Norm (Q.mulVec x) := by
    intro Q hQ hx0
    have hpos : 0 < dotProduct x (Q.mulVec x) := by simpa using hQ.dotProduct_mulVec_pos hx0
    nlinarith [h_cs x (Q.mulVec x), h_norm_nonneg x]
  have h_gap_eq :
      ∀ (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef),
        dotProduct x (A.mulVec x) = vecL2Norm (hA.sqrt.mulVec x) ^ 2 ∧
        gapPot A hA = Matrix.trace hA.sqrt - vecL2Norm (hA.sqrt.mulVec x) := by
    intro A hA
    have hT_psd : hA.sqrt.PosSemidef := h_sqrt_psd hA
    have hquad : dotProduct x (A.mulVec x) = vecL2Norm (hA.sqrt.mulVec x) ^ 2 := by
      conv_lhs => rw [← h_sqrt_sq hA]
      exact h_herm_sq_quad hA.sqrt hT_psd.isHermitian x
    refine ⟨hquad, ?_⟩
    dsimp [gapPot]
    rw [hquad, Real.sqrt_sq (h_norm_nonneg _)]
  have h_slope_psd :
      ∀ Q : Matrix (Fin d) (Fin d) ℝ, Q.PosDef → (envSlope Q).PosSemidef := by
    intro Q hQ
    by_cases hx0 : x = 0
    · simp only [envSlope, hx0, ↓reduceIte]
      exact hQ.inv.posSemidef
    · simp only [envSlope, hx0, ↓reduceIte]
      set u := Q.mulVec x
      set r := vecL2Norm u
      set a := dotProduct x u
      have ha_pos : 0 < a := by simpa [a, u] using hQ.dotProduct_mulVec_pos hx0
      have ha_le_r : a ≤ r := by nlinarith [h_cs x u, hx, h_norm_nonneg x, h_norm_nonneg u]
      have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
      have hQQinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
      have hQinvQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdet
      have hH_herm : (Q⁻¹ - r⁻¹ • Matrix.vecMulVec x x).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
            star_trivial, hQ.inv.isHermitian.eq, (h_outer_herm x).eq]
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH_herm fun y => ?_
      simp only [star_trivial]
      let c : ℝ := dotProduct x y / a
      let z : Fin d → ℝ := y - c • u
      have hz_nonneg : 0 ≤ dotProduct z (Q⁻¹.mulVec z) := by
        simpa using hQ.inv.posSemidef.dotProduct_mulVec_nonneg z
      have hQinv_u : Q⁻¹.mulVec u = x := by simp [u, Matrix.mulVec_mulVec, hQinvQ]
      have hu_Qinv_y : dotProduct u (Q⁻¹.mulVec y) = dotProduct x y := by
        calc dotProduct (Q.mulVec x) (Q⁻¹.mulVec y)
            = dotProduct x (Q.mulVec (Q⁻¹.mulVec y)) :=
                (h_herm_dot Q hQ.isHermitian x (Q⁻¹.mulVec y)).symm
          _ = dotProduct x y := by simp [Matrix.mulVec_mulVec, hQQinv]
      have hz_expand :
          dotProduct z (Q⁻¹.mulVec z) =
            dotProduct y (Q⁻¹.mulVec y) - (dotProduct x y) ^ 2 / a := by
        have h_rw : Q⁻¹.mulVec z = Q⁻¹.mulVec y - c • x := by
          simp [z, Matrix.mulVec_sub, Matrix.mulVec_smul, hQinv_u]
        have hu_x : dotProduct u x = a := dotProduct_comm u x
        have hc_mul_a : c * a = dotProduct x y := div_mul_cancel₀ (dotProduct x y) ha_pos.ne'
        rw [h_rw]
        simp only [z, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, hu_Qinv_y, dotProduct_comm y x, hu_x, hc_mul_a]
        dsimp only [c]
        ring
      have h_div_le : r⁻¹ * (dotProduct x y) ^ 2 ≤ dotProduct y (Q⁻¹.mulVec y) := by
        calc r⁻¹ * (dotProduct x y) ^ 2
            = (dotProduct x y) ^ 2 / r := by ring
          _ ≤ (dotProduct x y) ^ 2 / a :=
              div_le_div_of_nonneg_left (sq_nonneg _) ha_pos ha_le_r
          _ ≤ dotProduct y (Q⁻¹.mulVec y) := by linarith [hz_nonneg, hz_expand]
      have h_goal_expand :
          dotProduct y ((Q⁻¹ - r⁻¹ • Matrix.vecMulVec x x).mulVec y) =
            dotProduct y (Q⁻¹.mulVec y) - r⁻¹ * (dotProduct x y) ^ 2 := by
        simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
          smul_eq_mul, h_outer_quad x y]
      linarith
  have h_env_lb :
      ∀ (Q A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef), Q.PosDef →
        2 * gapPot A hA ≤ envObj Q A := by
    intro Q A hA hQ
    set T := hA.sqrt
    set M := (T - Q) * (T - Q)
    have hT_psd : T.PosSemidef := h_sqrt_psd hA
    have hTQ_herm : (T - Q).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hT_psd.isHermitian.eq, hQ.isHermitian.eq]
    have hM_psd : M.PosSemidef := by
      have : M = (T - Q).conjTranspose * (T - Q) := by rw [hTQ_herm.eq]
      rw [this]
      exact Matrix.posSemidef_conjTranspose_mul_self (T - Q)
    have htr_id := h_trace_sq_id Q A hA hQ
    obtain ⟨hA_quad, hgap_rw⟩ := h_gap_eq A hA
    set σ := vecL2Norm (T.mulVec x)
    set r := vecL2Norm (Q.mulVec x)
    by_cases hx0 : x = 0
    · have hσ0 : σ = 0 := by simp [σ, hx0, h_norm_zero]
      have h_tr_nonneg : 0 ≤ Matrix.trace (Q⁻¹ * M) :=
        h_trace_psd Q⁻¹ M hQ.inv.posSemidef hM_psd
      have hobj0 : envObj Q A = Matrix.trace Q + Matrix.trace (Q⁻¹ * A) := by
        simp [envObj, envSlope, hx0, h_norm_zero]
      rw [hgap_rw, hobj0, hσ0]
      linarith [htr_id, h_tr_nonneg]
    · have hr_pos : 0 < r := h_norm_pos_of_posDef Q hQ hx0
      have hr_ne : r ≠ 0 := hr_pos.ne'
      have hSlope : (envSlope Q).PosSemidef := h_slope_psd Q hQ
      have hQinv_decomp : Q⁻¹ = envSlope Q + r⁻¹ • Matrix.vecMulVec x x := by
        simp [envSlope, hx0, r]
      have htr_decomp :
          Matrix.trace (Q⁻¹ * M) =
            Matrix.trace (envSlope Q * M) + r⁻¹ * Matrix.trace (Matrix.vecMulVec x x * M) := by
        conv_lhs => rw [hQinv_decomp]
        rw [add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
      have htr_HM_nonneg : 0 ≤ Matrix.trace (envSlope Q * M) :=
        h_trace_psd (envSlope Q) M hSlope hM_psd
      have htr_EM : (σ - r) ^ 2 ≤ Matrix.trace (Matrix.vecMulVec x x * M) := by
        rw [h_outer_trace_left x M]
        have hM_quad : dotProduct x (M.mulVec x) = ∑ i, (T.mulVec x i - Q.mulVec x i) ^ 2 := by
          dsimp [M]
          rw [h_herm_sq_quad (T - Q) hTQ_herm x, h_norm_sq]
          simp [Matrix.sub_mulVec]
        rw [hM_quad]
        have hsum_expand :
            (∑ i, (T.mulVec x i - Q.mulVec x i) ^ 2) =
              σ ^ 2 - 2 * dotProduct (T.mulVec x) (Q.mulVec x) + r ^ 2 := by
          rw [h_norm_sq (T.mulVec x), h_norm_sq (Q.mulVec x)]
          simp only [dotProduct, Finset.mul_sum]
          rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        nlinarith [h_cs (T.mulVec x) (Q.mulVec x)]
      have h_rinv_sq : r⁻¹ * (σ - r) ^ 2 ≤ Matrix.trace (Q⁻¹ * M) := by
        have h1 := mul_le_mul_of_nonneg_left htr_EM (inv_nonneg.mpr hr_pos.le)
        linarith [htr_decomp, htr_HM_nonneg, h1]
      have h_alg : r⁻¹ * (σ - r) ^ 2 = r⁻¹ * σ ^ 2 - 2 * σ + r := by field_simp; ring
      have hobj_eq :
          envObj Q A = Matrix.trace Q - r + (Matrix.trace (Q⁻¹ * A) - r⁻¹ * σ ^ 2) := by
        simp only [envObj, envSlope, hx0, ↓reduceIte, sub_mul,
          Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
          h_outer_trace_left x A, hA_quad]
        rfl
      rw [hgap_rw, hobj_eq]
      linarith [htr_id, h_rinv_sq, h_alg]
  have h_env_ub :
      ∀ (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) (η : ℝ), 0 < η →
        (hA.sqrt + η • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef ∧
        envObj (hA.sqrt + η • (1 : Matrix (Fin d) (Fin d) ℝ)) A ≤
          2 * gapPot A hA + (d : ℝ) * η := by
    intro A hA η hη
    set T := hA.sqrt
    set Rη : Matrix (Fin d) (Fin d) ℝ := T + η • 1
    obtain ⟨hRη_pd, _, htr_ub⟩ := h_reg_base A hA η hη
    refine ⟨hRη_pd, ?_⟩
    obtain ⟨hA_quad, hgap_rw⟩ := h_gap_eq A hA
    set σ := vecL2Norm (T.mulVec x)
    set rη := vecL2Norm (Rη.mulVec x)
    by_cases hx0 : x = 0
    · have hσ0 : σ = 0 := by simp [σ, hx0, h_norm_zero]
      have hobj0 : envObj Rη A = Matrix.trace Rη + Matrix.trace (Rη⁻¹ * A) := by
        simp [envObj, envSlope, hx0, h_norm_zero]
      rw [hgap_rw, hobj0, hσ0]
      linarith [htr_ub]
    · have hr_pos : 0 < rη := h_norm_pos_of_posDef Rη hRη_pd hx0
      have hr_ne : rη ≠ 0 := hr_pos.ne'
      have hobj_eq :
          envObj Rη A = Matrix.trace Rη - rη + (Matrix.trace (Rη⁻¹ * A) - rη⁻¹ * σ ^ 2) := by
        simp only [envObj, envSlope, hx0, ↓reduceIte, sub_mul,
          Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
          h_outer_trace_left x A, hA_quad]
        rfl
      have h_amgm : 2 * σ ≤ rη + rη⁻¹ * σ ^ 2 := by
        have hsq : 0 ≤ rη⁻¹ * (rη - σ) ^ 2 :=
          mul_nonneg (inv_nonneg.mpr hr_pos.le) (sq_nonneg _)
        have halg : rη⁻¹ * (rη - σ) ^ 2 = rη - 2 * σ + rη⁻¹ * σ ^ 2 := by field_simp; ring
        linarith
      rw [hgap_rw, hobj_eq]
      linarith [htr_ub, h_amgm]
  have h_glb_le :
      ∀ (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) (b : ℝ),
        (∀ Q : Matrix (Fin d) (Fin d) ℝ, Q.PosDef → b ≤ envObj Q A) →
          b ≤ 2 * gapPot A hA := by
    intro A hA b hb
    set g := 2 * gapPot A hA
    by_contra h_not_le
    push_neg at h_not_le
    have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    let η : ℝ := (b - g) / ((d : ℝ) + 1)
    have hη_pos : 0 < η := div_pos (sub_pos.mpr h_not_le) hd1_pos
    obtain ⟨hRη_pd, hRη_ub⟩ := h_env_ub A hA η hη_pos
    have hb_le : b ≤ g + (d : ℝ) * η := le_trans (hb _ hRη_pd) hRη_ub
    have h_mul := mul_le_mul_of_nonneg_right hb_le hd1_pos.le
    have h_rhs : (g + (d : ℝ) * η) * ((d : ℝ) + 1) = g + (d : ℝ) * b := by
      dsimp [η]
      have hd1_ne : (d : ℝ) + 1 ≠ 0 := hd1_pos.ne'
      field_simp
      ring
    linarith
  have h_gap_split :
      2 * (p1 * gapPot S1 hS1_psd + p0 * gapPot S0 hS0_psd) ≤ 2 * gapPot S hS_psd := by
    refine h_glb_le S hS_psd _ fun Q hQ => ?_
    have h1 : 2 * gapPot S1 hS1_psd ≤ envObj Q S1 := h_env_lb Q S1 hS1_psd hQ
    have h0 : 2 * gapPot S0 hS0_psd ≤ envObj Q S0 := h_env_lb Q S0 hS0_psd hQ
    have h_comb :
        2 * (p1 * gapPot S1 hS1_psd + p0 * gapPot S0 hS0_psd) ≤
          p1 * envObj Q S1 + p0 * envObj Q S0 := by nlinarith
    have h_diff_nn : 0 ≤ Matrix.trace (envSlope Q * (S - (p1 • S1 + p0 • S0))) :=
      h_trace_psd (envSlope Q) (S - (p1 • S1 + p0 • S0)) (h_slope_psd Q hQ) h_tot_cov
    have h_obj_diff :
        envObj Q S - (p1 * envObj Q S1 + p0 * envObj Q S0) =
          Matrix.trace (envSlope Q * (S - (p1 • S1 + p0 • S0))) := by
      have h_tr :
          Matrix.trace (envSlope Q * (S - (p1 • S1 + p0 • S0))) =
            Matrix.trace (envSlope Q * S) -
              (p1 * Matrix.trace (envSlope Q * S1) + p0 * Matrix.trace (envSlope Q * S0)) := by
        have ht1 : Matrix.trace (envSlope Q * (p1 • S1)) = p1 * Matrix.trace (envSlope Q * S1) := by
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        have ht0 : Matrix.trace (envSlope Q * (p0 • S0)) = p0 * Matrix.trace (envSlope Q * S0) := by
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        rw [mul_sub, mul_add, Matrix.trace_sub, Matrix.trace_add, ht1, ht0]
      rw [h_tr]
      dsimp only [envObj]
      calc Matrix.trace Q - vecL2Norm (Q.mulVec x) + Matrix.trace (envSlope Q * S) -
            (p1 * (Matrix.trace Q - vecL2Norm (Q.mulVec x) + Matrix.trace (envSlope Q * S1)) +
              p0 * (Matrix.trace Q - vecL2Norm (Q.mulVec x) + Matrix.trace (envSlope Q * S0)))
          = (1 - (p1 + p0)) * (Matrix.trace Q - vecL2Norm (Q.mulVec x)) +
            (Matrix.trace (envSlope Q * S) -
              (p1 * Matrix.trace (envSlope Q * S1) + p0 * Matrix.trace (envSlope Q * S0))) := by ring
        _ = Matrix.trace (envSlope Q * S) -
              (p1 * Matrix.trace (envSlope Q * S1) + p0 * Matrix.trace (envSlope Q * S0)) := by
              rw [hp_sum, sub_self, zero_mul, zero_add]
    linarith

  
  let R1 : Matrix (Fin d) (Fin d) ℝ := hS1_psd.sqrt + τ • 1
  let R0 : Matrix (Fin d) (Fin d) ℝ := hS0_psd.sqrt + τ • 1
  obtain ⟨hR1_pd, _, hR1_tang⟩ := h_reg_base S1 hS1_psd τ hτ0
  obtain ⟨hR0_pd, _, hR0_tang⟩ := h_reg_base S0 hS0_psd τ hτ0
  obtain ⟨hR1_tr, hR1_inv⟩ := h_reg_extra S1 hS1_psd (hS_fn_tr E)
  obtain ⟨hR0_tr, hR0_inv⟩ := h_reg_extra S0 hS0_psd (hS_fn_tr Ec)

  refine ⟨m1, m0, R1, R0, hR1_pd, hR0_pd, hm_fn_norm E, hm_fn_norm Ec,
    hR1_tr, hR0_tr, hR1_inv, hR0_inv, ?_⟩

  have h_wsd_univ :
      finWeightedStdDev w Finset.univ (fun k => dotProduct x (Z k)) =
        Real.sqrt (dotProduct x (S.mulVec x)) := by
    rw [h_wsd_eq Finset.univ, hp_univ, one_mul]
  have h_wsd_E :
      finWeightedStdDev w E (fun k => dotProduct x (Z k)) =
        p1 * Real.sqrt (dotProduct x (S1.mulVec x)) := h_wsd_eq E
  have h_wsd_Ec :
      finWeightedStdDev w Ec (fun k => dotProduct x (Z k)) =
        p0 * Real.sqrt (dotProduct x (S0.mulVec x)) := h_wsd_eq Ec
  have h_dir_bound :
      2 * (finWeightedStdDev w Finset.univ (fun k => dotProduct x (Z k)) -
            finWeightedStdDev w E (fun k => dotProduct x (Z k)) -
            finWeightedStdDev w Ec (fun k => dotProduct x (Z k))) ≤
        2 * Matrix.trace hS_psd.sqrt - 2 * p1 * Matrix.trace hS1_psd.sqrt -
          2 * p0 * Matrix.trace hS0_psd.sqrt := by
    rw [h_wsd_univ, h_wsd_E, h_wsd_Ec]
    dsimp only [gapPot] at h_gap_split
    linarith

  have h_post1 :
      ∑ k ∈ E, w k * agentQuadPotential m1 R1 (Z k) ≤
        p1 * (2 * Matrix.trace hS1_psd.sqrt + (d : ℝ) * τ) := by
    rw [h_post_pot E R1]
    exact mul_le_mul_of_nonneg_left hR1_tang hp1_nn
  have h_post0 :
      ∑ k ∈ Ec, w k * agentQuadPotential m0 R0 (Z k) ≤
        p0 * (2 * Matrix.trace hS0_psd.sqrt + (d : ℝ) * τ) := by
    rw [h_post_pot Ec R0]
    exact mul_le_mul_of_nonneg_left hR0_tang hp0_nn
  have h_post_sum :
      (∑ k ∈ E, w k * agentQuadPotential m1 R1 (Z k)) +
        (∑ k ∈ Ec, w k * agentQuadPotential m0 R0 (Z k)) ≤
      2 * p1 * Matrix.trace hS1_psd.sqrt + 2 * p0 * Matrix.trace hS0_psd.sqrt + (d : ℝ) * τ := by
    have h_tau_id : p1 * ((d : ℝ) * τ) + p0 * ((d : ℝ) * τ) = (d : ℝ) * τ := by
      calc p1 * ((d : ℝ) * τ) + p0 * ((d : ℝ) * τ)
          = (p1 + p0) * ((d : ℝ) * τ) := by ring
        _ = (d : ℝ) * τ := by rw [hp_sum, one_mul]
    linarith [h_post1, h_post0, h_tau_id]

  have h_prior_tang : 2 * Matrix.trace hS_psd.sqrt ≤ Matrix.trace R + Matrix.trace (R⁻¹ * S) :=
    h_tang_lb R S hS_psd hR

  dsimp only [Ec] at h_dir_bound h_post_sum
  linarith [h_dir_bound, h_post_sum, h_prior_tang, h_prior_pot]

theorem lem_initial_potential_jitter_and_lip {d : ℕ}
    (mS mB : Fin d → ℝ)
    (RS RB : Matrix (Fin d) (Fin d) ℝ) (hRS : RS.PosDef) (hRB : RB.PosDef)
    (x : Fin d → ℝ) (hx0 : x ≠ 0) (hx : vecL2Norm x ≤ 1) :
    let v : Fin d → ℝ := ((vecL2Norm x) ^ 2)⁻¹ • x
    ∃ (C0 L0 : ℝ), 0 < C0 ∧ 0 < L0 ∧
      (∀ ε u : ℝ, 0 < ε → ε ≤ 1 / 4 → |u| ≤ ε * vecL2Norm x →
        ∀ z : Fin d → ℝ, vecL2Norm z ≤ 1 →
          vecL2Norm ((1 - ε) • z + u • v) ≤ 1) ∧
      (∀ ε u : ℝ, 0 < ε → ε ≤ 1 / 4 → |u| ≤ ε * vecL2Norm x →
        ∀ s b : Fin d → ℝ, vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 →
          |(2 ^ 10 : ℝ) * ((1 - ε)⁻¹ * tradeQuadPotential mS mB RS RB
              ((1 - ε) • s + u • v) ((1 - ε) • b + u • v) -
            tradeQuadPotential mS mB RS RB s b)| ≤ C0 * ε) ∧
      (∀ δ : ℝ, 0 < δ →
        ∀ s b s' b' : Fin d → ℝ,
          vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 → vecL2Norm s' ≤ 1 → vecL2Norm b' ≤ 1 →
          vecL2Norm (s - s') ≤ δ → vecL2Norm (b - b') ≤ δ →
          |(2 ^ 10 : ℝ) * (tradeQuadPotential mS mB RS RB s b -
            tradeQuadPotential mS mB RS RB s' b')| ≤ L0 * δ) :=
by
  have _ : RS.PosDef ∧ RB.PosDef ∧ vecL2Norm x ≤ 1 := ⟨hRS, hRB, hx⟩
  intro v
  have h_norm_eq : ∀ w : Fin d → ℝ,
      vecL2Norm w = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d))‖ := by
    intro w
    rw [EuclideanSpace.norm_eq]
    simp [vecL2Norm, Real.norm_eq_abs, sq_abs]
  have h_norm_nn : ∀ w : Fin d → ℝ, 0 ≤ vecL2Norm w :=
    fun w => Real.sqrt_nonneg _
  have h_norm_smul : ∀ (c : ℝ) (w : Fin d → ℝ), vecL2Norm (c • w) = |c| * vecL2Norm w := by
    intro c w
    rw [h_norm_eq, h_norm_eq, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
  have h_norm_add : ∀ w₁ w₂ : Fin d → ℝ, vecL2Norm (w₁ + w₂) ≤ vecL2Norm w₁ + vecL2Norm w₂ := by
    intro w₁ w₂
    rw [h_norm_eq, h_norm_eq, h_norm_eq, WithLp.toLp_add]
    exact norm_add_le _ _
  have h_norm_sub : ∀ w₁ w₂ : Fin d → ℝ, vecL2Norm (w₁ - w₂) ≤ vecL2Norm w₁ + vecL2Norm w₂ := by
    intro w₁ w₂
    rw [h_norm_eq, h_norm_eq, h_norm_eq, WithLp.toLp_sub]
    exact norm_sub_le _ _
  have h_coord_le : ∀ (w : Fin d → ℝ) (i : Fin d), |w i| ≤ vecL2Norm w := by
    intro w i
    have h_le : (w i) ^ 2 ≤ ∑ k : Fin d, (w k) ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (w k)) (Finset.mem_univ i)
    calc |w i| = Real.sqrt ((w i) ^ 2) := (Real.sqrt_sq_eq_abs (w i)).symm
      _ ≤ Real.sqrt (∑ k : Fin d, (w k) ^ 2) := Real.sqrt_le_sqrt h_le
      _ = vecL2Norm w := rfl
  let nx : ℝ := vecL2Norm x
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx0
  have h_sq_pos : 0 < ∑ i : Fin d, (x i) ^ 2 := by
    have hi₀_sq : 0 < (x i₀) ^ 2 := sq_pos_of_ne_zero hi₀
    have h_le : (x i₀) ^ 2 ≤ ∑ i : Fin d, (x i) ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i₀)
    linarith
  have hnx_pos : 0 < nx := Real.sqrt_pos.mpr h_sq_pos
  have hnx_sq_inv_pos : 0 < (nx ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hnx_pos)
  have hv_norm : vecL2Norm v = nx⁻¹ := by
    change vecL2Norm ((nx ^ 2)⁻¹ • x) = nx⁻¹
    rw [h_norm_smul, abs_of_pos hnx_sq_inv_pos]
    change (nx ^ 2)⁻¹ * nx = nx⁻¹
    field_simp [ne_of_gt hnx_pos]
  have h_uv_le : ∀ ε u : ℝ, |u| ≤ ε * nx → vecL2Norm (u • v) ≤ ε := by
    intro ε u hu
    rw [h_norm_smul, hv_norm]
    calc |u| * nx⁻¹ ≤ (ε * nx) * nx⁻¹ :=
          mul_le_mul_of_nonneg_right hu (inv_nonneg.mpr (le_of_lt hnx_pos))
      _ = ε := by field_simp [ne_of_gt hnx_pos]
  have h_ball : ∀ ε u : ℝ, 0 < ε → ε ≤ 1 / 4 → |u| ≤ ε * nx →
      ∀ z : Fin d → ℝ, vecL2Norm z ≤ 1 → vecL2Norm ((1 - ε) • z + u • v) ≤ 1 := by
    intro ε u _ hε1 hu z hz
    have hc_pos : 0 < 1 - ε := by linarith
    have h1 : vecL2Norm ((1 - ε) • z) ≤ 1 - ε := by
      rw [h_norm_smul, abs_of_pos hc_pos]
      nlinarith [h_norm_nn z]
    have h2 : vecL2Norm (u • v) ≤ ε := h_uv_le ε u hu
    have h3 := h_norm_add ((1 - ε) • z) (u • v)
    linarith
  have h_disp : ∀ ε u : ℝ, 0 < ε → |u| ≤ ε * nx →
      ∀ z : Fin d → ℝ, vecL2Norm z ≤ 1 →
        vecL2Norm (((1 - ε) • z + u • v) - z) ≤ 2 * ε := by
    intro ε u hε0 hu z hz
    have h_eq : ((1 - ε) • z + u • v) - z = (-ε) • z + u • v := by
      ext i
      simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [h_eq]
    have h1 : vecL2Norm ((-ε) • z) ≤ ε := by
      rw [h_norm_smul, abs_neg, abs_of_pos hε0]
      nlinarith [h_norm_nn z]
    have h2 : vecL2Norm (u • v) ≤ ε := h_uv_le ε u hu
    have h3 := h_norm_add ((-ε) • z) (u • v)
    linarith
  let matEntrySum : Matrix (Fin d) (Fin d) ℝ → ℝ :=
    fun A => ∑ i : Fin d, ∑ j : Fin d, |A i j|
  have h_entry_nn : ∀ A : Matrix (Fin d) (Fin d) ℝ, 0 ≤ matEntrySum A :=
    fun A => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have h_bilin : ∀ (A : Matrix (Fin d) (Fin d) ℝ) (p q : Fin d → ℝ),
      |dotProduct p (A.mulVec q)| ≤ matEntrySum A * vecL2Norm p * vecL2Norm q := by
    intro A p q
    have h_expand : dotProduct p (A.mulVec q) =
        ∑ i : Fin d, ∑ j : Fin d, p i * (A i j * q j) := by
      dsimp [dotProduct, Matrix.mulVec]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
    rw [h_expand]
    have h_abs1 : |∑ i : Fin d, ∑ j : Fin d, p i * (A i j * q j)| ≤
        ∑ i : Fin d, ∑ j : Fin d, |p i * (A i j * q j)| := by
      calc |∑ i : Fin d, ∑ j : Fin d, p i * (A i j * q j)|
          ≤ ∑ i : Fin d, |∑ j : Fin d, p i * (A i j * q j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin d, ∑ j : Fin d, |p i * (A i j * q j)| :=
            Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    have h_term : ∀ (i j : Fin d),
        |p i * (A i j * q j)| ≤ |A i j| * (vecL2Norm p * vecL2Norm q) := by
      intro i j
      have hp : |p i| ≤ vecL2Norm p := h_coord_le p i
      have hq : |q j| ≤ vecL2Norm q := h_coord_le q j
      have hpq : |p i| * |q j| ≤ vecL2Norm p * vecL2Norm q :=
        mul_le_mul hp hq (abs_nonneg _) (h_norm_nn p)
      calc |p i * (A i j * q j)|
          = |p i| * (|A i j| * |q j|) := by rw [abs_mul, abs_mul]
        _ = |A i j| * (|p i| * |q j|) := by ring
        _ ≤ |A i j| * (vecL2Norm p * vecL2Norm q) :=
            mul_le_mul_of_nonneg_left hpq (abs_nonneg _)
    calc |∑ i : Fin d, ∑ j : Fin d, p i * (A i j * q j)|
        ≤ ∑ i : Fin d, ∑ j : Fin d, |p i * (A i j * q j)| := h_abs1
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| * (vecL2Norm p * vecL2Norm q) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h_term i j))
      _ = matEntrySum A * (vecL2Norm p * vecL2Norm q) := by
          dsimp [matEntrySum]
          simp_rw [← Finset.sum_mul]
      _ = matEntrySum A * vecL2Norm p * vecL2Norm q := by ring
  let L_ag : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ → ℝ :=
    fun m R => 2 * matEntrySum R⁻¹ * (1 + vecL2Norm m)
  let M_ag : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ → ℝ :=
    fun m R => |Matrix.trace R| + matEntrySum R⁻¹ * (1 + vecL2Norm m) ^ 2
  let C_ag : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ → ℝ :=
    fun m R => 4 * L_ag m R + 2 * M_ag m R
  have hL_ag_nn : ∀ m R, 0 ≤ L_ag m R := fun m R =>
    mul_nonneg (mul_nonneg (by norm_num) (h_entry_nn R⁻¹)) (by linarith [h_norm_nn m])
  have hM_ag_nn : ∀ m R, 0 ≤ M_ag m R := fun m R =>
    add_nonneg (abs_nonneg _) (mul_nonneg (h_entry_nn R⁻¹) (sq_nonneg _))
  have hC_ag_nn : ∀ m R, 0 ≤ C_ag m R := fun m R => by
    dsimp [C_ag]
    linarith [hL_ag_nn m R, hM_ag_nn m R]
  have h_ag_bound : ∀ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ),
      vecL2Norm z ≤ 1 → |agentQuadPotential m R z| ≤ M_ag m R := by
    intro m R z hz
    have hzm : vecL2Norm (z - m) ≤ 1 + vecL2Norm m := by
      have h1 := h_norm_sub z m
      linarith
    have hsq : vecL2Norm (z - m) * vecL2Norm (z - m) ≤ (1 + vecL2Norm m) ^ 2 := by
      have hnn := h_norm_nn (z - m)
      have hbm : 0 ≤ 1 + vecL2Norm m := by linarith [h_norm_nn m]
      calc vecL2Norm (z - m) * vecL2Norm (z - m)
          ≤ (1 + vecL2Norm m) * (1 + vecL2Norm m) := mul_le_mul hzm hzm hnn hbm
        _ = (1 + vecL2Norm m) ^ 2 := by ring
    have hbil := h_bilin R⁻¹ (z - m) (z - m)
    have hprod : matEntrySum R⁻¹ * vecL2Norm (z - m) * vecL2Norm (z - m) ≤
        matEntrySum R⁻¹ * (1 + vecL2Norm m) ^ 2 := by
      calc matEntrySum R⁻¹ * vecL2Norm (z - m) * vecL2Norm (z - m)
          = matEntrySum R⁻¹ * (vecL2Norm (z - m) * vecL2Norm (z - m)) := by ring
        _ ≤ matEntrySum R⁻¹ * (1 + vecL2Norm m) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (h_entry_nn R⁻¹)
    dsimp [agentQuadPotential, M_ag]
    have habs := abs_add_le (Matrix.trace R) (dotProduct (z - m) (R⁻¹.mulVec (z - m)))
    linarith
  have h_ag_lip : ∀ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ) (z z' : Fin d → ℝ),
      vecL2Norm z ≤ 1 → vecL2Norm z' ≤ 1 →
      |agentQuadPotential m R z - agentQuadPotential m R z'| ≤
        L_ag m R * vecL2Norm (z - z') := by
    intro m R z z' hz hz'
    let u₁ : Fin d → ℝ := z - m
    let u₂ : Fin d → ℝ := z' - m
    have hu_diff : u₁ - u₂ = z - z' := by
      ext i
      simp [u₁, u₂]
    have hu₁ : vecL2Norm u₁ ≤ 1 + vecL2Norm m := by
      have h1 := h_norm_sub z m
      linarith
    have hu₂ : vecL2Norm u₂ ≤ 1 + vecL2Norm m := by
      have h1 := h_norm_sub z' m
      linarith
    have h_diff_eq : agentQuadPotential m R z - agentQuadPotential m R z' =
        dotProduct (z - z') (R⁻¹.mulVec u₁) + dotProduct u₂ (R⁻¹.mulVec (z - z')) := by
      have h_pol : ∀ v₁ v₂ : Fin d → ℝ,
          dotProduct (v₁ - v₂) (R⁻¹.mulVec v₁) + dotProduct v₂ (R⁻¹.mulVec (v₁ - v₂)) =
          dotProduct v₁ (R⁻¹.mulVec v₁) - dotProduct v₂ (R⁻¹.mulVec v₂) := by
        intro v₁ v₂
        rw [sub_dotProduct, Matrix.mulVec_sub, dotProduct_sub]
        ring
      have h_u := h_pol u₁ u₂
      rw [hu_diff] at h_u
      dsimp [agentQuadPotential, u₁, u₂] at h_u ⊢
      linarith
    rw [h_diff_eq]
    have habs := abs_add_le (dotProduct (z - z') (R⁻¹.mulVec u₁))
      (dotProduct u₂ (R⁻¹.mulVec (z - z')))
    have hb1 := h_bilin R⁻¹ (z - z') u₁
    have hb2 := h_bilin R⁻¹ u₂ (z - z')
    have h_nonneg1 : 0 ≤ matEntrySum R⁻¹ * vecL2Norm (z - z') :=
      mul_nonneg (h_entry_nn R⁻¹) (h_norm_nn (z - z'))
    have h_t1 : matEntrySum R⁻¹ * vecL2Norm (z - z') * vecL2Norm u₁ ≤
        matEntrySum R⁻¹ * vecL2Norm (z - z') * (1 + vecL2Norm m) :=
      mul_le_mul_of_nonneg_left hu₁ h_nonneg1
    have h_t2 : matEntrySum R⁻¹ * vecL2Norm u₂ * vecL2Norm (z - z') ≤
        matEntrySum R⁻¹ * (1 + vecL2Norm m) * vecL2Norm (z - z') := by
      have h_inner : matEntrySum R⁻¹ * vecL2Norm u₂ ≤ matEntrySum R⁻¹ * (1 + vecL2Norm m) :=
        mul_le_mul_of_nonneg_left hu₂ (h_entry_nn R⁻¹)
      exact mul_le_mul_of_nonneg_right h_inner (h_norm_nn (z - z'))
    have h_sum_eq : matEntrySum R⁻¹ * vecL2Norm (z - z') * (1 + vecL2Norm m) +
        matEntrySum R⁻¹ * (1 + vecL2Norm m) * vecL2Norm (z - z') =
        L_ag m R * vecL2Norm (z - z') := by
      dsimp [L_ag]
      ring
    linarith
  have h_ag_drift : ∀ (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ)
      (ε u : ℝ), 0 < ε → ε ≤ 1 / 4 → |u| ≤ ε * nx →
      ∀ z : Fin d → ℝ, vecL2Norm z ≤ 1 →
        |(1 - ε)⁻¹ * agentQuadPotential m R ((1 - ε) • z + u • v) -
          agentQuadPotential m R z| ≤ C_ag m R * ε := by
    intro m R ε u hε0 hε1 hu z hz
    let c : ℝ := 1 - ε
    let z' : Fin d → ℝ := c • z + u • v
    have hc_pos : 0 < c := by dsimp [c]; linarith
    have hc_inv_pos : 0 < c⁻¹ := inv_pos.mpr hc_pos
    have hc_inv_le2 : c⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hc_pos (by norm_num : (0 : ℝ) < 2)]
      dsimp [c]
      linarith
    have hc_sub_eq : c⁻¹ - 1 = ε * c⁻¹ := by
      have hc_ne : c ≠ 0 := ne_of_gt hc_pos
      dsimp [c] at hc_ne ⊢
      field_simp [hc_ne]
      ring
    have hc_sub_nn : 0 ≤ c⁻¹ - 1 := by
      rw [hc_sub_eq]
      exact mul_nonneg (le_of_lt hε0) (le_of_lt hc_inv_pos)
    have hc_sub_le : c⁻¹ - 1 ≤ 2 * ε := by
      rw [hc_sub_eq]
      nlinarith
    have hz' : vecL2Norm z' ≤ 1 := h_ball ε u hε0 hε1 hu z hz
    have hdisp : vecL2Norm (z' - z) ≤ 2 * ε := h_disp ε u hε0 hu z hz
    have h_decomp : c⁻¹ * agentQuadPotential m R z' - agentQuadPotential m R z =
        c⁻¹ * (agentQuadPotential m R z' - agentQuadPotential m R z) +
        (c⁻¹ - 1) * agentQuadPotential m R z := by ring
    change |c⁻¹ * agentQuadPotential m R z' - agentQuadPotential m R z| ≤ C_ag m R * ε
    rw [h_decomp]
    have habs := abs_add_le (c⁻¹ * (agentQuadPotential m R z' - agentQuadPotential m R z))
      ((c⁻¹ - 1) * agentQuadPotential m R z)
    rw [abs_mul, abs_mul, abs_of_pos hc_inv_pos, abs_of_nonneg hc_sub_nn] at habs
    have hlip := h_ag_lip m R z' z hz' hz
    have hbd := h_ag_bound m R z hz
    have h_term1 : c⁻¹ * |agentQuadPotential m R z' - agentQuadPotential m R z| ≤
        4 * L_ag m R * ε := by
      have h1 : c⁻¹ * |agentQuadPotential m R z' - agentQuadPotential m R z| ≤
          2 * (L_ag m R * vecL2Norm (z' - z)) :=
        mul_le_mul hc_inv_le2 hlip (abs_nonneg _) (by norm_num)
      have h2 : L_ag m R * vecL2Norm (z' - z) ≤ L_ag m R * (2 * ε) :=
        mul_le_mul_of_nonneg_left hdisp (hL_ag_nn m R)
      linarith
    have h_term2 : (c⁻¹ - 1) * |agentQuadPotential m R z| ≤ 2 * M_ag m R * ε := by
      have h1 : (c⁻¹ - 1) * |agentQuadPotential m R z| ≤ (2 * ε) * M_ag m R :=
        mul_le_mul hc_sub_le hbd (abs_nonneg _) (by linarith)
      linarith
    dsimp [C_ag]
    linarith
  let C0 : ℝ := 1024 * (C_ag mS RS + C_ag mB RB) + 1
  let L0 : ℝ := 1024 * (L_ag mS RS + L_ag mB RB) + 1
  have h1024 : (2 ^ 10 : ℝ) = 1024 := by norm_num
  have hC0_pos : 0 < C0 := by
    dsimp [C0]
    linarith [hC_ag_nn mS RS, hC_ag_nn mB RB]
  have hL0_pos : 0 < L0 := by
    dsimp [L0]
    linarith [hL_ag_nn mS RS, hL_ag_nn mB RB]
  refine ⟨C0, L0, hC0_pos, hL0_pos, h_ball, ?_, ?_⟩
  · intro ε u hε0 hε1 hu s b hs hb
    have hS := h_ag_drift mS RS ε u hε0 hε1 hu s hs
    have hB := h_ag_drift mB RB ε u hε0 hε1 hu b hb
    have h_split : (2 ^ 10 : ℝ) * ((1 - ε)⁻¹ * tradeQuadPotential mS mB RS RB
          ((1 - ε) • s + u • v) ((1 - ε) • b + u • v) -
        tradeQuadPotential mS mB RS RB s b) =
        1024 * (((1 - ε)⁻¹ * agentQuadPotential mS RS ((1 - ε) • s + u • v) -
            agentQuadPotential mS RS s) +
          ((1 - ε)⁻¹ * agentQuadPotential mB RB ((1 - ε) • b + u • v) -
            agentQuadPotential mB RB b)) := by
      rw [h1024]
      dsimp [tradeQuadPotential]
      ring
    rw [h_split, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1024)]
    have habs := abs_add_le
      ((1 - ε)⁻¹ * agentQuadPotential mS RS ((1 - ε) • s + u • v) - agentQuadPotential mS RS s)
      ((1 - ε)⁻¹ * agentQuadPotential mB RB ((1 - ε) • b + u • v) - agentQuadPotential mB RB b)
    dsimp [C0]
    linarith
  · intro δ hδ0 s b s' b' hs hb hs' hb' hss' hbb'
    have hS : |agentQuadPotential mS RS s - agentQuadPotential mS RS s'| ≤ L_ag mS RS * δ := by
      calc |agentQuadPotential mS RS s - agentQuadPotential mS RS s'|
          ≤ L_ag mS RS * vecL2Norm (s - s') := h_ag_lip mS RS s s' hs hs'
        _ ≤ L_ag mS RS * δ := mul_le_mul_of_nonneg_left hss' (hL_ag_nn mS RS)
    have hB : |agentQuadPotential mB RB b - agentQuadPotential mB RB b'| ≤ L_ag mB RB * δ := by
      calc |agentQuadPotential mB RB b - agentQuadPotential mB RB b'|
          ≤ L_ag mB RB * vecL2Norm (b - b') := h_ag_lip mB RB b b' hb hb'
        _ ≤ L_ag mB RB * δ := mul_le_mul_of_nonneg_left hbb' (hL_ag_nn mB RB)
    have h_split : (2 ^ 10 : ℝ) * (tradeQuadPotential mS mB RS RB s b -
          tradeQuadPotential mS mB RS RB s' b') =
        1024 * ((agentQuadPotential mS RS s - agentQuadPotential mS RS s') +
          (agentQuadPotential mB RB b - agentQuadPotential mB RB b')) := by
      rw [h1024]
      dsimp [tradeQuadPotential]
      ring
    rw [h_split, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1024)]
    have habs := abs_add_le
      (agentQuadPotential mS RS s - agentQuadPotential mS RS s')
      (agentQuadPotential mB RB b - agentQuadPotential mB RB b')
    dsimp [L0]
    linarith

theorem lem_discrete_jitter_plan_approx {d : ℕ}
    (x : Fin d → ℝ) (hx0 : x ≠ 0) (hx : vecL2Norm x ≤ 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (M : ℕ) (hM : 0 < M)
    (gridDenom : ℕ) (hGrid : 0 < gridDenom)
    (hGridStep : (1 - ε) / (gridDenom : ℝ) < ε * vecL2Norm x / (M : ℝ))
    (pa : ℝ)
    (mS0 mB0 mS1 mB1 : Fin d → ℝ)
    (hmS0 : vecL2Norm mS0 ≤ 1) (hmB0 : vecL2Norm mB0 ≤ 1)
    (hmS1 : vecL2Norm mS1 ≤ 1) (hmB1 : vecL2Norm mB1 ≤ 1)
    (RS0 RB0 RS1 RB1 : Matrix (Fin d) (Fin d) ℝ)
    (hRS0_pd : RS0.PosDef) (hRB0_pd : RB0.PosDef)
    (hRS1_pd : RS1.PosDef) (hRB1_pd : RB1.PosDef)
    (hRS0_tr : Matrix.trace RS0 ≤ 2 * (d : ℝ)) (hRB0_tr : Matrix.trace RB0 ≤ 2 * (d : ℝ))
    (hRS1_tr : Matrix.trace RS1 ≤ 2 * (d : ℝ)) (hRB1_tr : Matrix.trace RB1 ≤ 2 * (d : ℝ))
    (hRS0_inv : ∀ u w : Fin d → ℝ, |dotProduct u (RS0⁻¹.mulVec w)| ≤ τ⁻¹ * vecL2Norm u * vecL2Norm w)
    (hRB0_inv : ∀ u w : Fin d → ℝ, |dotProduct u (RB0⁻¹.mulVec w)| ≤ τ⁻¹ * vecL2Norm u * vecL2Norm w)
    (hRS1_inv : ∀ u w : Fin d → ℝ, |dotProduct u (RS1⁻¹.mulVec w)| ≤ τ⁻¹ * vecL2Norm u * vecL2Norm w)
    (hRB1_inv : ∀ u w : Fin d → ℝ, |dotProduct u (RB1⁻¹.mulVec w)| ≤ τ⁻¹ * vecL2Norm u * vecL2Norm w) :
    let c : ℝ := 1 - ε
    let v : Fin d → ℝ := ((vecL2Norm x) ^ 2)⁻¹ • x
    let Δu : ℝ := ε * vecL2Norm x / (M : ℝ)
    let B_max : ℝ := 2 + 4096 * (d : ℝ) + 8192 * τ⁻¹
    ∃ L : List (ℝ × TradePlan d),
      (∀ wp ∈ L, 0 ≤ wp.1) ∧
      (L.map Prod.fst).sum = 1 ∧
      (∀ wp ∈ L, ∃ k : ℤ, (wp.2.price : ℝ) = (k : ℝ) / (gridDenom : ℝ)) ∧
      (∀ s b : Fin d → ℝ, vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 →
        (L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum ≤
          4 * B_max / (2 * (M : ℝ) + 1) +
          c⁻¹ * (2 * (M : ℝ) + 1)⁻¹ * ∑ k : Fin (2 * M + 1),
            (let u_k : ℝ := (((k : ℕ) : ℝ) - (M : ℝ)) * Δu
             let s_k : Fin d → ℝ := c • s + u_k • v
             let b_k : Fin d → ℝ := c • b + u_k • v
             if dotProduct x s_k ≤ pa ∧ pa ≤ dotProduct x b_k then
               (2 ^ 10 : ℝ) * tradeQuadPotential mS1 mB1 RS1 RB1 s_k b_k
             else
               max (dotProduct x b_k - dotProduct x s_k) 0 +
                 (2 ^ 10 : ℝ) * tradeQuadPotential mS0 mB0 RS0 RB0 s_k b_k)) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 → c * δ < Δu →
        ∀ s b s' b' : Fin d → ℝ,
          vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 → vecL2Norm s' ≤ 1 → vecL2Norm b' ≤ 1 →
          vecL2Norm (s - s') ≤ δ → vecL2Norm (b - b') ≤ δ →
          |(L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum -
           (L.map (fun wp => wp.1 * planRoundCost x wp.2 s' b')).sum| ≤
            12 * B_max / (2 * (M : ℝ) + 1) + (2 + 16384 * τ⁻¹) * δ) :=
by
  classical
  intro c v Δu B_max
  let _ := hτ1
  
  have hc_ge : 3 / 4 ≤ c := by
    change 3 / 4 ≤ 1 - ε
    linarith
  have hc_pos : 0 < c := by linarith
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hc_inv_pos : 0 < c⁻¹ := inv_pos.mpr hc_pos
  have hc_inv_le2 : c⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hc_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hτ_inv_pos : 0 < τ⁻¹ := inv_pos.mpr hτ0
  have hM_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hGrid_real : 0 < (gridDenom : ℝ) := Nat.cast_pos.mpr hGrid
  have hBmax_pos : 0 < B_max := by
    change 0 < 2 + 4096 * (d : ℝ) + 8192 * τ⁻¹
    positivity

  
  
  
  have h_norm_nonneg : ∀ w : Fin d → ℝ, 0 ≤ vecL2Norm w :=
    fun _ => Real.sqrt_nonneg _
  have h_norm_sq : ∀ w : Fin d → ℝ, vecL2Norm w ^ 2 = ∑ i, (w i) ^ 2 :=
    fun w => Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (w i))
  have h_cs : ∀ w₁ w₂ : Fin d → ℝ, dotProduct w₁ w₂ ≤ vecL2Norm w₁ * vecL2Norm w₂ :=
    fun w₁ w₂ => Real.sum_mul_le_sqrt_mul_sqrt Finset.univ w₁ w₂
  have h_norm_neg : ∀ w : Fin d → ℝ, vecL2Norm (-w) = vecL2Norm w := by
    intro w
    simp [vecL2Norm]
  have h_abs_dot : ∀ w₁ w₂ : Fin d → ℝ, |dotProduct w₁ w₂| ≤ vecL2Norm w₁ * vecL2Norm w₂ := by
    intro w₁ w₂
    refine abs_le.mpr ⟨?_, h_cs w₁ w₂⟩
    have hneg := h_cs w₁ (-w₂)
    simp only [dotProduct_neg, h_norm_neg] at hneg
    linarith
  have h_proj : ∀ w : Fin d → ℝ, |dotProduct x w| ≤ vecL2Norm w := by
    intro w
    calc |dotProduct x w|
        ≤ vecL2Norm x * vecL2Norm w := h_abs_dot x w
      _ ≤ 1 * vecL2Norm w := mul_le_mul_of_nonneg_right hx (h_norm_nonneg w)
      _ = vecL2Norm w := one_mul _
  have h_norm_smul : ∀ (a : ℝ) (w : Fin d → ℝ), vecL2Norm (a • w) = |a| * vecL2Norm w := by
    intro a w
    unfold vecL2Norm
    have hsum : ∑ i, (a • w) i ^ 2 = a ^ 2 * ∑ i, (w i) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
  have h_norm_add : ∀ w₁ w₂ : Fin d → ℝ, vecL2Norm (w₁ + w₂) ≤ vecL2Norm w₁ + vecL2Norm w₂ := by
    intro w₁ w₂
    have h_rhs_nn : 0 ≤ vecL2Norm w₁ + vecL2Norm w₂ :=
      add_nonneg (h_norm_nonneg w₁) (h_norm_nonneg w₂)
    have h_sq_le : ∑ i, (w₁ + w₂) i ^ 2 ≤ (vecL2Norm w₁ + vecL2Norm w₂) ^ 2 := by
      have h_exp : ∑ i, (w₁ + w₂) i ^ 2 =
          (∑ i, w₁ i ^ 2) + 2 * dotProduct w₁ w₂ + (∑ i, w₂ i ^ 2) := by
        have h1 : ∑ i, (w₁ + w₂) i ^ 2 = ∑ i, (w₁ i ^ 2 + 2 * (w₁ i * w₂ i) + w₂ i ^ 2) :=
          Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
        rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
      nlinarith [h_exp, h_norm_sq w₁, h_norm_sq w₂, h_cs w₁ w₂]
    calc vecL2Norm (w₁ + w₂)
        = Real.sqrt (∑ i, (w₁ + w₂) i ^ 2) := rfl
      _ ≤ Real.sqrt ((vecL2Norm w₁ + vecL2Norm w₂) ^ 2) := Real.sqrt_le_sqrt h_sq_le
      _ = vecL2Norm w₁ + vecL2Norm w₂ := Real.sqrt_sq h_rhs_nn
  have h_norm_sub : ∀ w₁ w₂ : Fin d → ℝ, vecL2Norm (w₁ - w₂) ≤ vecL2Norm w₁ + vecL2Norm w₂ := by
    intro w₁ w₂
    rw [sub_eq_add_neg]
    exact (h_norm_add w₁ (-w₂)).trans_eq (by rw [h_norm_neg])

  have hnx_pos : 0 < vecL2Norm x := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx0
    have h_sq_pos : 0 < ∑ i, (x i) ^ 2 :=
      lt_of_lt_of_le (sq_pos_of_ne_zero hi₀)
        (Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i₀))
    exact Real.sqrt_pos.mpr h_sq_pos
  have hnx_ne : vecL2Norm x ≠ 0 := hnx_pos.ne'

  have h_xv : dotProduct x v = 1 := by
    change dotProduct x (((vecL2Norm x) ^ 2)⁻¹ • x) = 1
    rw [dotProduct_smul, smul_eq_mul]
    have hxx : dotProduct x x = vecL2Norm x ^ 2 := by
      rw [h_norm_sq x]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hxx, inv_mul_cancel₀ (pow_ne_zero 2 hnx_ne)]

  have h_norm_v : vecL2Norm v = (vecL2Norm x)⁻¹ := by
    change vecL2Norm (((vecL2Norm x) ^ 2)⁻¹ • x) = (vecL2Norm x)⁻¹
    rw [h_norm_smul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hnx_pos))]
    field_simp [hnx_ne]

  have h_ball : ∀ (u : ℝ), |u| ≤ ε * vecL2Norm x →
      ∀ z : Fin d → ℝ, vecL2Norm z ≤ 1 → vecL2Norm (c • z + u • v) ≤ 1 := by
    intro u hu z hz
    calc vecL2Norm (c • z + u • v)
        ≤ vecL2Norm (c • z) + vecL2Norm (u • v) := h_norm_add _ _
      _ = c * vecL2Norm z + |u| * (vecL2Norm x)⁻¹ := by
          rw [h_norm_smul, h_norm_smul, abs_of_pos hc_pos, h_norm_v]
      _ ≤ c * 1 + (ε * vecL2Norm x) * (vecL2Norm x)⁻¹ :=
          add_le_add (mul_le_mul_of_nonneg_left hz hc_pos.le)
            (mul_le_mul_of_nonneg_right hu (inv_nonneg.mpr hnx_pos.le))
      _ = 1 := by
          change (1 - ε) * 1 + (ε * vecL2Norm x) * (vecL2Norm x)⁻¹ = 1
          field_simp [hnx_ne]
          ring

  have h_dot_shift : ∀ (u : ℝ) (z : Fin d → ℝ),
      dotProduct x (c • z + u • v) = c * dotProduct x z + u := by
    intro u z
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, h_xv, mul_one]

  have h_diff_shift : ∀ (u : ℝ) (z₁ z₂ : Fin d → ℝ),
      vecL2Norm ((c • z₁ + u • v) - (c • z₂ + u • v)) = c * vecL2Norm (z₁ - z₂) := by
    intro u z₁ z₂
    have h_eq : (c • z₁ + u • v) - (c • z₂ + u • v) = c • (z₁ - z₂) := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h_eq, h_norm_smul, abs_of_pos hc_pos]

  have h_pot_scale : ∀ (u : ℝ) (m z : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ),
      R.PosDef →
      agentQuadPotential (c⁻¹ • (m - u • v)) (c⁻¹ • R) z =
        c⁻¹ * agentQuadPotential m R (c • z + u • v) := by
    intro u m z R hR
    have hR_unit : IsUnit R.det := isUnit_iff_ne_zero.mpr hR.det_pos.ne'
    have h_inv : (c⁻¹ • R)⁻¹ = c • R⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc_ne, one_smul,
        Matrix.nonsing_inv_mul R hR_unit]
    let w : Fin d → ℝ := (c • z + u • v) - m
    have hw_eq : z - c⁻¹ • (m - u • v) = c⁻¹ • w := by
      ext i
      dsimp only [w]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hc_ne]
      ring
    unfold agentQuadPotential
    rw [Matrix.trace_smul, smul_eq_mul, hw_eq, h_inv, Matrix.smul_mulVec, Matrix.mulVec_smul,
      smul_smul, mul_inv_cancel₀ hc_ne, one_smul, smul_dotProduct, smul_eq_mul, mul_add]

  
  
  
  have h_herm_symm : ∀ (A : Matrix (Fin d) (Fin d) ℝ), A.IsHermitian →
      ∀ a b : Fin d → ℝ, dotProduct a (A.mulVec b) = dotProduct b (A.mulVec a) := by
    intro A hA a b
    have hA_ij : ∀ i j, A j i = A i j := fun i j => by
      simpa [Matrix.conjTranspose_apply] using congr_fun (congr_fun hA.eq i) j
    calc dotProduct a (A.mulVec b)
        = ∑ i, ∑ j, a i * (A i j * b j) := by
            simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      _ = ∑ j, ∑ i, a i * (A i j * b j) := Finset.sum_comm
      _ = ∑ j, b j * (∑ i, A j i * a i) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hA_ij i j]
            ring
      _ = dotProduct b (A.mulVec a) := rfl

  have h_pot_range : ∀ (m : Fin d → ℝ), vecL2Norm m ≤ 1 →
      ∀ (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef → Matrix.trace R ≤ 2 * (d : ℝ) →
        (∀ u w, |dotProduct u (R⁻¹.mulVec w)| ≤ τ⁻¹ * vecL2Norm u * vecL2Norm w) →
        ∀ z : Fin d → ℝ, vecL2Norm z ≤ 1 →
          0 ≤ agentQuadPotential m R z ∧ agentQuadPotential m R z ≤ 2 * (d : ℝ) + 4 * τ⁻¹ := by
    intro m hm R hR hR_tr hR_inv z hz
    constructor
    · unfold agentQuadPotential
      have h1 : 0 ≤ Matrix.trace R := hR.posSemidef.trace_nonneg
      have h2 : 0 ≤ dotProduct (z - m) (R⁻¹.mulVec (z - m)) := by
        simpa using hR.inv.posSemidef.dotProduct_mulVec_nonneg (z - m)
      exact add_nonneg h1 h2
    · have hzm_le : vecL2Norm (z - m) ≤ 2 := (h_norm_sub z m).trans (by linarith)
      have hzm_nn : 0 ≤ vecL2Norm (z - m) := h_norm_nonneg (z - m)
      have hsq : vecL2Norm (z - m) * vecL2Norm (z - m) ≤ 4 := by nlinarith [hzm_le, hzm_nn]
      have hquad : dotProduct (z - m) (R⁻¹.mulVec (z - m)) ≤ 4 * τ⁻¹ := by
        calc dotProduct (z - m) (R⁻¹.mulVec (z - m))
            ≤ |dotProduct (z - m) (R⁻¹.mulVec (z - m))| := le_abs_self _
          _ ≤ τ⁻¹ * vecL2Norm (z - m) * vecL2Norm (z - m) := hR_inv (z - m) (z - m)
          _ = τ⁻¹ * (vecL2Norm (z - m) * vecL2Norm (z - m)) := by ring
          _ ≤ τ⁻¹ * 4 := mul_le_mul_of_nonneg_left hsq hτ_inv_pos.le
          _ = 4 * τ⁻¹ := by ring
      unfold agentQuadPotential
      linarith

  have h_pot_lip : ∀ (m : Fin d → ℝ), vecL2Norm m ≤ 1 →
      ∀ (R : Matrix (Fin d) (Fin d) ℝ), R.PosDef →
        (∀ u w, |dotProduct u (R⁻¹.mulVec w)| ≤ τ⁻¹ * vecL2Norm u * vecL2Norm w) →
        ∀ z z' : Fin d → ℝ, vecL2Norm z ≤ 1 → vecL2Norm z' ≤ 1 →
          |agentQuadPotential m R z - agentQuadPotential m R z'| ≤
            4 * τ⁻¹ * vecL2Norm (z - z') := by
    intro m hm R hR hR_inv z z' hz hz'
    let u₁ : Fin d → ℝ := z - m
    let u₂ : Fin d → ℝ := z' - m
    have h_symm : dotProduct u₁ (R⁻¹.mulVec u₂) = dotProduct u₂ (R⁻¹.mulVec u₁) :=
      h_herm_symm R⁻¹ hR.inv.isHermitian u₁ u₂
    have h_quad_diff : dotProduct (u₁ - u₂) (R⁻¹.mulVec (u₁ + u₂)) =
        dotProduct u₁ (R⁻¹.mulVec u₁) - dotProduct u₂ (R⁻¹.mulVec u₂) := by
      rw [Matrix.mulVec_add, sub_dotProduct u₁ u₂, dotProduct_add u₁, dotProduct_add u₂, h_symm]
      ring
    have h_diff : agentQuadPotential m R z - agentQuadPotential m R z' =
        dotProduct (z - z') (R⁻¹.mulVec (u₁ + u₂)) := by
      have hu_sub : z - z' = u₁ - u₂ := by
        ext i
        simp [u₁, u₂]
      unfold agentQuadPotential
      change (Matrix.trace R + dotProduct u₁ (R⁻¹.mulVec u₁)) -
        (Matrix.trace R + dotProduct u₂ (R⁻¹.mulVec u₂)) =
        dotProduct (z - z') (R⁻¹.mulVec (u₁ + u₂))
      rw [hu_sub, h_quad_diff]
      ring
    have hu_sum_le : vecL2Norm (u₁ + u₂) ≤ 4 := by
      have h1 : vecL2Norm u₁ ≤ 2 := (h_norm_sub z m).trans (by linarith)
      have h2 : vecL2Norm u₂ ≤ 2 := (h_norm_sub z' m).trans (by linarith)
      exact (h_norm_add u₁ u₂).trans (by linarith)
    rw [h_diff]
    calc |dotProduct (z - z') (R⁻¹.mulVec (u₁ + u₂))|
        ≤ τ⁻¹ * vecL2Norm (z - z') * vecL2Norm (u₁ + u₂) := hR_inv (z - z') (u₁ + u₂)
      _ ≤ τ⁻¹ * vecL2Norm (z - z') * 4 :=
          mul_le_mul_of_nonneg_left hu_sum_le
            (mul_nonneg hτ_inv_pos.le (h_norm_nonneg (z - z')))
      _ = 4 * τ⁻¹ * vecL2Norm (z - z') := by ring

  
  
  
  let K : ℕ := 2 * M + 1
  have hK_eq : (K : ℝ) = 2 * (M : ℝ) + 1 := by
    dsimp only [K]
    push_cast
    ring
  have hK_pos : 0 < (K : ℝ) := by linarith
  have hΔu_pos : 0 < Δu := div_pos (mul_pos hε0 hnx_pos) hM_real
  let Δq : ℝ := Δu / c
  have hΔq_pos : 0 < Δq := div_pos hΔu_pos hc_pos

  let u_fn : Fin K → ℝ := fun k => (((k : ℕ) : ℝ) - (M : ℝ)) * Δu
  let q_fn : Fin K → ℝ := fun k => (pa - u_fn k) / c

  have hu_bound : ∀ k : Fin K, |u_fn k| ≤ ε * vecL2Norm x := by
    intro k
    have hk_le : (k : ℕ) ≤ 2 * M := Nat.lt_succ_iff.mp k.isLt
    have hk_real_le : ((k : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hk_le
    have hk_real_nn : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
    have habs : |((k : ℕ) : ℝ) - (M : ℝ)| ≤ (M : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |u_fn k|
        = |((k : ℕ) : ℝ) - (M : ℝ)| * |Δu| := abs_mul _ _
      _ = |((k : ℕ) : ℝ) - (M : ℝ)| * Δu := by rw [abs_of_pos hΔu_pos]
      _ ≤ (M : ℝ) * Δu := mul_le_mul_of_nonneg_right habs hΔu_pos.le
      _ = ε * vecL2Norm x := by
          change (M : ℝ) * (ε * vecL2Norm x / (M : ℝ)) = ε * vecL2Norm x
          field_simp [hM_real.ne']

  have hq_sep : ∀ k₁ k₂ : Fin K, k₁ ≠ k₂ → Δq ≤ |q_fn k₁ - q_fn k₂| := by
    intro k₁ k₂ hne
    have hnat_ne : (k₁ : ℕ) ≠ (k₂ : ℕ) := fun h => hne (Fin.ext h)
    have hint_ne : ((k₂ : ℕ) : ℤ) - ((k₁ : ℕ) : ℤ) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hnat_ne (Int.ofNat.inj h.symm))
    have hint_abs : (1 : ℤ) ≤ |((k₂ : ℕ) : ℤ) - ((k₁ : ℕ) : ℤ)| := Int.one_le_abs hint_ne
    have hreal_abs : (1 : ℝ) ≤ |((k₂ : ℕ) : ℝ) - ((k₁ : ℕ) : ℝ)| := by
      have hcast : ((|((k₂ : ℕ) : ℤ) - ((k₁ : ℕ) : ℤ)| : ℤ) : ℝ) =
          |((k₂ : ℕ) : ℝ) - ((k₁ : ℕ) : ℝ)| := by push_cast; rfl
      rw [← hcast]
      exact_mod_cast hint_abs
    have hdiff : q_fn k₁ - q_fn k₂ = (((k₂ : ℕ) : ℝ) - ((k₁ : ℕ) : ℝ)) * Δq := by
      dsimp only [q_fn, u_fn, Δq]
      field_simp [hc_ne]
      ring
    rw [hdiff, abs_mul, abs_of_pos hΔq_pos]
    calc Δq = 1 * Δq := (one_mul _).symm
      _ ≤ |((k₂ : ℕ) : ℝ) - ((k₁ : ℕ) : ℝ)| * Δq :=
          mul_le_mul_of_nonneg_right hreal_abs hΔq_pos.le

  
  let I_set : ℝ → Finset (Fin K) :=
    fun a => Finset.univ.filter (fun k : Fin K => a ≤ q_fn k ∧ q_fn k < a + Δq)
  have hI_card : ∀ a : ℝ, (I_set a).card ≤ 1 := by
    intro a
    rw [Finset.card_le_one_iff]
    intro k₁ k₂ hk₁ hk₂
    have h1 : a ≤ q_fn k₁ ∧ q_fn k₁ < a + Δq := (Finset.mem_filter.mp hk₁).2
    have h2 : a ≤ q_fn k₂ ∧ q_fn k₂ < a + Δq := (Finset.mem_filter.mp hk₂).2
    have habs_lt : |q_fn k₁ - q_fn k₂| < Δq := abs_lt.mpr ⟨by linarith, by linarith⟩
    by_contra hne
    linarith [hq_sep k₁ k₂ hne]

  have h_two_int_card : ∀ (a₁ a₂ : ℝ) (F : Finset (Fin K)),
      F ⊆ I_set a₁ ∪ I_set a₂ → F.card ≤ 2 := by
    intro a₁ a₂ F hsub
    calc F.card
        ≤ (I_set a₁ ∪ I_set a₂).card := Finset.card_le_card hsub
      _ ≤ (I_set a₁).card + (I_set a₂).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := add_le_add (hI_card a₁) (hI_card a₂)

  have h_abs_box : ∀ {u w M_cap : ℝ}, (0 ≤ u ∧ u ≤ M_cap) → (0 ≤ w ∧ w ≤ M_cap) →
      |u - w| ≤ M_cap := by
    intro u w M_cap hu hw
    exact abs_le.mpr ⟨by linarith, by linarith⟩

  
  have h_s6_round : ∀ (p_tilde Y₁ Y₀ : Fin K → ℝ) (M_cap S B : ℝ),
      0 ≤ M_cap →
      (∀ k, q_fn k - Δq < p_tilde k ∧ p_tilde k ≤ q_fn k) →
      (∀ k, 0 ≤ Y₁ k ∧ Y₁ k ≤ M_cap) →
      (∀ k, 0 ≤ Y₀ k ∧ Y₀ k ≤ M_cap) →
      |(∑ k : Fin K, if S ≤ p_tilde k ∧ p_tilde k ≤ B then Y₁ k else Y₀ k) -
       (∑ k : Fin K, if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k)| ≤ 2 * M_cap := by
    intro p_tilde Y₁ Y₀ M_cap S B hMcap hp hY₁ hY₀
    let F_round : Finset (Fin K) :=
      Finset.univ.filter (fun k : Fin K =>
        ¬ ((S ≤ p_tilde k ∧ p_tilde k ≤ B) ↔ (S ≤ q_fn k ∧ q_fn k ≤ B)))
    have hF_sub : F_round ⊆ I_set S ∪ I_set B := by
      intro k hk
      have hk_neg : ¬ ((S ≤ p_tilde k ∧ p_tilde k ≤ B) ↔ (S ≤ q_fn k ∧ q_fn k ≤ B)) :=
        (Finset.mem_filter.mp hk).2
      by_contra hk_not_mem
      have hk_not_S : ¬ (S ≤ q_fn k ∧ q_fn k < S + Δq) := by
        intro hS_in
        exact hk_not_mem (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hS_in⟩))
      have hk_not_B : ¬ (B ≤ q_fn k ∧ q_fn k < B + Δq) := by
        intro hB_in
        exact hk_not_mem (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hB_in⟩))
      have hp_k := hp k
      have h_eqv_S : S ≤ p_tilde k ↔ S ≤ q_fn k := by
        constructor
        · intro h; linarith [hp_k.2]
        · intro h
          have h_ge : S + Δq ≤ q_fn k := by
            by_contra hlt
            exact hk_not_S ⟨h, lt_of_not_ge hlt⟩
          linarith [hp_k.1]
      have h_eqv_B : p_tilde k ≤ B ↔ q_fn k ≤ B := by
        constructor
        · intro h
          by_contra hgt
          have hB_le : B ≤ q_fn k := le_of_lt (lt_of_not_ge hgt)
          have h_ge : B + Δq ≤ q_fn k := by
            by_contra hlt
            exact hk_not_B ⟨hB_le, lt_of_not_ge hlt⟩
          linarith [hp_k.1]
        · intro h; linarith [hp_k.2]
      exact hk_neg (and_congr h_eqv_S h_eqv_B)
    have hF_card_real : (F_round.card : ℝ) ≤ 2 := by exact_mod_cast h_two_int_card S B F_round hF_sub
    have h_term : ∀ k : Fin K,
        |(if S ≤ p_tilde k ∧ p_tilde k ≤ B then Y₁ k else Y₀ k) -
         (if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k)| ≤
        if k ∈ F_round then M_cap else 0 := by
      intro k
      by_cases hk : k ∈ F_round
      · rw [if_pos hk]
        have hb1 : 0 ≤ (if S ≤ p_tilde k ∧ p_tilde k ≤ B then Y₁ k else Y₀ k) ∧
            (if S ≤ p_tilde k ∧ p_tilde k ≤ B then Y₁ k else Y₀ k) ≤ M_cap := by
          split_ifs <;> [exact hY₁ k; exact hY₀ k]
        have hb2 : 0 ≤ (if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k) ∧
            (if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k) ≤ M_cap := by
          split_ifs <;> [exact hY₁ k; exact hY₀ k]
        exact h_abs_box hb1 hb2
      · rw [if_neg hk]
        have h_iff : (S ≤ p_tilde k ∧ p_tilde k ≤ B) ↔ (S ≤ q_fn k ∧ q_fn k ≤ B) := by
          by_contra hneg
          exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hneg⟩)
        have h_eq : (if S ≤ p_tilde k ∧ p_tilde k ≤ B then Y₁ k else Y₀ k) =
            (if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k) := by
          by_cases hP : S ≤ p_tilde k ∧ p_tilde k ≤ B
          · rw [if_pos hP, if_pos (h_iff.mp hP)]
          · rw [if_neg hP, if_neg (fun hQ => hP (h_iff.mpr hQ))]
        rw [h_eq, sub_self, abs_zero]
    rw [← Finset.sum_sub_distrib]
    calc |∑ k : Fin K, ((if S ≤ p_tilde k ∧ p_tilde k ≤ B then Y₁ k else Y₀ k) -
            (if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k))|
        ≤ ∑ k : Fin K, |(if S ≤ p_tilde k ∧ p_tilde k ≤ B then Y₁ k else Y₀ k) -
            (if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin K, (if k ∈ F_round then M_cap else 0) :=
          Finset.sum_le_sum fun k _ => h_term k
      _ = (F_round.card : ℝ) * M_cap := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * M_cap := mul_le_mul_of_nonneg_right hF_card_real hMcap

  
  have h_s6_pert : ∀ (Y₁ Y₀ Y₁' Y₀' : Fin K → ℝ) (M_cap L_step S B S' B' : ℝ),
      0 ≤ M_cap → 0 ≤ L_step →
      |S - S'| < Δq → |B - B'| < Δq →
      (∀ k, 0 ≤ Y₁ k ∧ Y₁ k ≤ M_cap) →
      (∀ k, 0 ≤ Y₀ k ∧ Y₀ k ≤ M_cap) →
      (∀ k, 0 ≤ Y₁' k ∧ Y₁' k ≤ M_cap) →
      (∀ k, 0 ≤ Y₀' k ∧ Y₀' k ≤ M_cap) →
      (∀ k, |Y₁ k - Y₁' k| ≤ L_step) →
      (∀ k, |Y₀ k - Y₀' k| ≤ L_step) →
      |(∑ k : Fin K, if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k) -
       (∑ k : Fin K, if S' ≤ q_fn k ∧ q_fn k ≤ B' then Y₁' k else Y₀' k)| ≤
        2 * M_cap + (K : ℝ) * L_step := by
    intro Y₁ Y₀ Y₁' Y₀' M_cap L_step S B S' B' hMcap hLstep hSS' hBB' hY₁ hY₀ hY₁' hY₀' hLip₁ hLip₀
    let aS : ℝ := min S S'
    let aB : ℝ := min B B'
    have hS_lt := abs_lt.mp hSS'
    have hB_lt := abs_lt.mp hBB'
    have haS_S : aS ≤ S ∧ S < aS + Δq :=
      ⟨min_le_left _ _, by dsimp only [aS]; rcases min_cases S S' with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith⟩
    have haS_S' : aS ≤ S' ∧ S' < aS + Δq :=
      ⟨min_le_right _ _, by dsimp only [aS]; rcases min_cases S S' with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith⟩
    have haB_B : aB ≤ B ∧ B < aB + Δq :=
      ⟨min_le_left _ _, by dsimp only [aB]; rcases min_cases B B' with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith⟩
    have haB_B' : aB ≤ B' ∧ B' < aB + Δq :=
      ⟨min_le_right _ _, by dsimp only [aB]; rcases min_cases B B' with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith⟩
    let F_pert : Finset (Fin K) :=
      Finset.univ.filter (fun k : Fin K =>
        ¬ ((S ≤ q_fn k ∧ q_fn k ≤ B) ↔ (S' ≤ q_fn k ∧ q_fn k ≤ B')))
    have hF_sub : F_pert ⊆ I_set aS ∪ I_set aB := by
      intro k hk
      have hk_neg : ¬ ((S ≤ q_fn k ∧ q_fn k ≤ B) ↔ (S' ≤ q_fn k ∧ q_fn k ≤ B')) :=
        (Finset.mem_filter.mp hk).2
      by_contra hk_not_mem
      have hk_not_S : ¬ (aS ≤ q_fn k ∧ q_fn k < aS + Δq) := by
        intro hS_in
        exact hk_not_mem (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hS_in⟩))
      have hk_not_B : ¬ (aB ≤ q_fn k ∧ q_fn k < aB + Δq) := by
        intro hB_in
        exact hk_not_mem (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hB_in⟩))
      have h_eqv_S : S ≤ q_fn k ↔ S' ≤ q_fn k := by
        constructor
        · intro h
          have h_ge : aS + Δq ≤ q_fn k := by
            by_contra hlt
            exact hk_not_S ⟨le_trans haS_S.1 h, lt_of_not_ge hlt⟩
          linarith [haS_S'.2]
        · intro h
          have h_ge : aS + Δq ≤ q_fn k := by
            by_contra hlt
            exact hk_not_S ⟨le_trans haS_S'.1 h, lt_of_not_ge hlt⟩
          linarith [haS_S.2]
      have h_eqv_B : q_fn k ≤ B ↔ q_fn k ≤ B' := by
        constructor
        · intro h
          have h_lt : q_fn k < aB := by
            by_contra hge
            exact hk_not_B ⟨le_of_not_gt hge, lt_of_le_of_lt h haB_B.2⟩
          linarith [haB_B'.1]
        · intro h
          have h_lt : q_fn k < aB := by
            by_contra hge
            exact hk_not_B ⟨le_of_not_gt hge, lt_of_le_of_lt h haB_B'.2⟩
          linarith [haB_B.1]
      exact hk_neg (and_congr h_eqv_S h_eqv_B)
    have hF_card_real : (F_pert.card : ℝ) ≤ 2 := by
      exact_mod_cast h_two_int_card aS aB F_pert hF_sub
    have h_term : ∀ k : Fin K,
        |(if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k) -
         (if S' ≤ q_fn k ∧ q_fn k ≤ B' then Y₁' k else Y₀' k)| ≤
        (if k ∈ F_pert then M_cap else 0) + L_step := by
      intro k
      by_cases hk : k ∈ F_pert
      · rw [if_pos hk]
        have hb1 : 0 ≤ (if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k) ∧
            (if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k) ≤ M_cap := by
          split_ifs <;> [exact hY₁ k; exact hY₀ k]
        have hb2 : 0 ≤ (if S' ≤ q_fn k ∧ q_fn k ≤ B' then Y₁' k else Y₀' k) ∧
            (if S' ≤ q_fn k ∧ q_fn k ≤ B' then Y₁' k else Y₀' k) ≤ M_cap := by
          split_ifs <;> [exact hY₁' k; exact hY₀' k]
        linarith [h_abs_box hb1 hb2, hLstep]
      · rw [if_neg hk, zero_add]
        have h_iff : (S ≤ q_fn k ∧ q_fn k ≤ B) ↔ (S' ≤ q_fn k ∧ q_fn k ≤ B') := by
          by_contra hneg
          exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hneg⟩)
        by_cases hQ : S ≤ q_fn k ∧ q_fn k ≤ B
        · rw [if_pos hQ, if_pos (h_iff.mp hQ)]
          exact hLip₁ k
        · rw [if_neg hQ, if_neg (fun hQ' => hQ (h_iff.mpr hQ'))]
          exact hLip₀ k
    rw [← Finset.sum_sub_distrib]
    calc |∑ k : Fin K, ((if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k) -
            (if S' ≤ q_fn k ∧ q_fn k ≤ B' then Y₁' k else Y₀' k))|
        ≤ ∑ k : Fin K, |(if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁ k else Y₀ k) -
            (if S' ≤ q_fn k ∧ q_fn k ≤ B' then Y₁' k else Y₀' k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin K, ((if k ∈ F_pert then M_cap else 0) + L_step) :=
          Finset.sum_le_sum fun k _ => h_term k
      _ = (F_pert.card : ℝ) * M_cap + (K : ℝ) * L_step := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
            Finset.sum_const, nsmul_eq_mul, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ 2 * M_cap + (K : ℝ) * L_step := by
          linarith [mul_le_mul_of_nonneg_right hF_card_real hMcap]

  
  
  
  have hGrid_lt_Δq : (gridDenom : ℝ)⁻¹ < Δq := by
    have h1 : c / (gridDenom : ℝ) < Δu := hGridStep
    rw [show Δq = Δu / c from rfl, lt_div_iff₀ hc_pos, inv_mul_eq_div]
    exact h1

  let n_fn : Fin K → ℤ := fun k => ⌊(gridDenom : ℝ) * q_fn k⌋
  let p_rat : Fin K → ℚ := fun k => (n_fn k : ℚ) / (gridDenom : ℚ)
  let p_tilde : Fin K → ℝ := fun k => (p_rat k : ℝ)

  have hp_tilde_eq : ∀ k : Fin K, p_tilde k = (n_fn k : ℝ) / (gridDenom : ℝ) := by
    intro k
    dsimp only [p_tilde, p_rat]
    push_cast
    rfl

  have hp_window : ∀ k : Fin K, q_fn k - Δq < p_tilde k ∧ p_tilde k ≤ q_fn k := by
    intro k
    rw [hp_tilde_eq k]
    have hfl_le : (n_fn k : ℝ) ≤ (gridDenom : ℝ) * q_fn k := Int.floor_le _
    have hfl_gt : (gridDenom : ℝ) * q_fn k < (n_fn k : ℝ) + 1 := Int.lt_floor_add_one _
    constructor
    · have h1 : q_fn k - (gridDenom : ℝ)⁻¹ < (n_fn k : ℝ) / (gridDenom : ℝ) := by
        rw [lt_div_iff₀ hGrid_real, sub_mul, inv_mul_cancel₀ hGrid_real.ne']
        linarith
      linarith [hGrid_lt_Δq]
    · rw [div_le_iff₀ hGrid_real]
      linarith

  let w₀ : ℝ := (2 * (M : ℝ) + 1)⁻¹
  have hw₀_pos : 0 < w₀ := inv_pos.mpr (by linarith)
  have hw₀_K : (K : ℝ) * w₀ = 1 := by
    dsimp only [w₀]
    rw [← hK_eq]
    exact mul_inv_cancel₀ hK_pos.ne'

  let plan_fn : Fin K → TradePlan d := fun k => {
    price := p_rat k
    mS0 := c⁻¹ • (mS0 - (u_fn k) • v)
    mB0 := c⁻¹ • (mB0 - (u_fn k) • v)
    RS0 := c⁻¹ • RS0
    RB0 := c⁻¹ • RB0
    mS1 := c⁻¹ • (mS1 - (u_fn k) • v)
    mB1 := c⁻¹ • (mB1 - (u_fn k) • v)
    RS1 := c⁻¹ • RS1
    RB1 := c⁻¹ • RB1
    posDef_RS0 := hRS0_pd.smul hc_inv_pos
    posDef_RB0 := hRB0_pd.smul hc_inv_pos
    posDef_RS1 := hRS1_pd.smul hc_inv_pos
    posDef_RB1 := hRB1_pd.smul hc_inv_pos
  }

  let L : List (ℝ × TradePlan d) := (List.finRange K).map (fun k => (w₀, plan_fn k))

  have h_evalLot : ∀ s b : Fin d → ℝ,
      (L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum =
        w₀ * ∑ k : Fin K, planRoundCost x (plan_fn k) s b := by
    intro s b
    dsimp only [L]
    rw [List.map_map, ← Fin.sum_univ_def]
    simp only [Function.comp_apply, Finset.mul_sum]

  let s_sh : (Fin d → ℝ) → Fin K → (Fin d → ℝ) := fun s k => c • s + (u_fn k) • v
  let Y₁_fn : (Fin d → ℝ) → (Fin d → ℝ) → Fin K → ℝ := fun s b k =>
    c⁻¹ * ((2 ^ 10 : ℝ) * tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s k) (s_sh b k))
  let Y₀_fn : (Fin d → ℝ) → (Fin d → ℝ) → Fin K → ℝ := fun s b k =>
    c⁻¹ * (max (dotProduct x (s_sh b k) - dotProduct x (s_sh s k)) 0 +
      (2 ^ 10 : ℝ) * tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s k) (s_sh b k))

  have h_max_scale : ∀ s b : Fin d → ℝ, ∀ k : Fin K,
      c⁻¹ * max (dotProduct x (s_sh b k) - dotProduct x (s_sh s k)) 0 =
        max (dotProduct x b - dotProduct x s) 0 := by
    intro s b k
    have hsub : dotProduct x (s_sh b k) - dotProduct x (s_sh s k) =
        c * (dotProduct x b - dotProduct x s) := by
      dsimp only [s_sh]
      rw [h_dot_shift, h_dot_shift]
      ring
    rw [hsub]
    by_cases h : 0 ≤ dotProduct x b - dotProduct x s
    · rw [max_eq_left (mul_nonneg hc_pos.le h), max_eq_left h, inv_mul_cancel_left₀ hc_ne]
    · have hneg : dotProduct x b - dotProduct x s ≤ 0 := le_of_not_ge h
      have hcneg : c * (dotProduct x b - dotProduct x s) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc_pos.le hneg
      rw [max_eq_right hcneg, max_eq_right hneg, mul_zero]

  have h_plan_cost_eq : ∀ s b : Fin d → ℝ, ∀ k : Fin K,
      planRoundCost x (plan_fn k) s b =
        if dotProduct x s ≤ p_tilde k ∧ p_tilde k ≤ dotProduct x b then
          Y₁_fn s b k
        else
          Y₀_fn s b k := by
    intro s b k
    have hS1 := h_pot_scale (u_fn k) mS1 s RS1 hRS1_pd
    have hB1 := h_pot_scale (u_fn k) mB1 b RB1 hRB1_pd
    have hS0 := h_pot_scale (u_fn k) mS0 s RS0 hRS0_pd
    have hB0 := h_pot_scale (u_fn k) mB0 b RB0 hRB0_pd
    have hmax := h_max_scale s b k
    dsimp only [planRoundCost, plan_fn, p_tilde, Y₁_fn, Y₀_fn, tradeQuadPotential, s_sh] at *
    by_cases hcond : dotProduct x s ≤ (p_rat k : ℝ) ∧ (p_rat k : ℝ) ≤ dotProduct x b
    · rw [if_pos hcond, if_pos hcond, hS1, hB1]
      ring
    · rw [if_neg hcond, if_neg hcond, hS0, hB0, ← hmax]
      ring

  have h_q_cond_iff : ∀ s b : Fin d → ℝ, ∀ k : Fin K,
      (dotProduct x s ≤ q_fn k ∧ q_fn k ≤ dotProduct x b) ↔
        (dotProduct x (s_sh s k) ≤ pa ∧ pa ≤ dotProduct x (s_sh b k)) := by
    intro s b k
    dsimp only [q_fn, s_sh]
    rw [h_dot_shift, h_dot_shift, le_div_iff₀ hc_pos, div_le_iff₀ hc_pos]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

  let unroundedAvg : (Fin d → ℝ) → (Fin d → ℝ) → ℝ := fun s b =>
    w₀ * ∑ k : Fin K,
      if dotProduct x s ≤ q_fn k ∧ q_fn k ≤ dotProduct x b then
        Y₁_fn s b k
      else
        Y₀_fn s b k

  have h_Y_bounds : ∀ s b : Fin d → ℝ, vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 →
      ∀ k : Fin K,
        (0 ≤ Y₁_fn s b k ∧ Y₁_fn s b k ≤ 2 * B_max) ∧
        (0 ≤ Y₀_fn s b k ∧ Y₀_fn s b k ≤ 2 * B_max) := by
    intro s b hs hb k
    have hsk : vecL2Norm (s_sh s k) ≤ 1 := h_ball (u_fn k) (hu_bound k) s hs
    have hbk : vecL2Norm (s_sh b k) ≤ 1 := h_ball (u_fn k) (hu_bound k) b hb
    have hS1 := h_pot_range mS1 hmS1 RS1 hRS1_pd hRS1_tr hRS1_inv (s_sh s k) hsk
    have hB1 := h_pot_range mB1 hmB1 RB1 hRB1_pd hRB1_tr hRB1_inv (s_sh b k) hbk
    have hS0 := h_pot_range mS0 hmS0 RS0 hRS0_pd hRS0_tr hRS0_inv (s_sh s k) hsk
    have hB0 := h_pot_range mB0 hmB0 RB0 hRB0_pd hRB0_tr hRB0_inv (s_sh b k) hbk
    have h_abs_s : |dotProduct x (s_sh s k)| ≤ 1 := (h_proj (s_sh s k)).trans hsk
    have h_abs_b : |dotProduct x (s_sh b k)| ≤ 1 := (h_proj (s_sh b k)).trans hbk
    have h_max_nn : 0 ≤ max (dotProduct x (s_sh b k) - dotProduct x (s_sh s k)) 0 :=
      le_max_right _ _
    have h_max_le : max (dotProduct x (s_sh b k) - dotProduct x (s_sh s k)) 0 ≤ 2 := by
      have hs_b := abs_le.mp h_abs_s
      have hb_b := abs_le.mp h_abs_b
      exact max_le (by linarith) (by norm_num)
    have h1024 : (2 ^ 10 : ℝ) = 1024 := by norm_num
    have h_unscaled1_nn : 0 ≤ (2 ^ 10 : ℝ) * tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s k) (s_sh b k) := by
      unfold tradeQuadPotential
      rw [h1024]
      linarith [hS1.1, hB1.1]
    have h_unscaled1_le : (2 ^ 10 : ℝ) * tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s k) (s_sh b k) ≤ B_max := by
      unfold tradeQuadPotential
      change (2 ^ 10 : ℝ) * (agentQuadPotential mS1 RS1 (s_sh s k) + agentQuadPotential mB1 RB1 (s_sh b k)) ≤
        2 + 4096 * (d : ℝ) + 8192 * τ⁻¹
      rw [h1024]
      linarith [hS1.2, hB1.2]
    have h_unscaled0_nn : 0 ≤ max (dotProduct x (s_sh b k) - dotProduct x (s_sh s k)) 0 +
        (2 ^ 10 : ℝ) * tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s k) (s_sh b k) := by
      unfold tradeQuadPotential
      rw [h1024]
      linarith [h_max_nn, hS0.1, hB0.1]
    have h_unscaled0_le : max (dotProduct x (s_sh b k) - dotProduct x (s_sh s k)) 0 +
        (2 ^ 10 : ℝ) * tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s k) (s_sh b k) ≤ B_max := by
      unfold tradeQuadPotential
      change max (dotProduct x (s_sh b k) - dotProduct x (s_sh s k)) 0 +
        (2 ^ 10 : ℝ) * (agentQuadPotential mS0 RS0 (s_sh s k) + agentQuadPotential mB0 RB0 (s_sh b k)) ≤
        2 + 4096 * (d : ℝ) + 8192 * τ⁻¹
      rw [h1024]
      linarith [h_max_le, hS0.2, hB0.2]
    refine ⟨⟨mul_nonneg hc_inv_pos.le h_unscaled1_nn, ?_⟩,
            ⟨mul_nonneg hc_inv_pos.le h_unscaled0_nn, ?_⟩⟩
    · dsimp only [Y₁_fn]
      exact mul_le_mul hc_inv_le2 h_unscaled1_le h_unscaled1_nn (by norm_num)
    · dsimp only [Y₀_fn]
      exact mul_le_mul hc_inv_le2 h_unscaled0_le h_unscaled0_nn (by norm_num)

  have h_round_err : ∀ s b : Fin d → ℝ, vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 →
      |(L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum - unroundedAvg s b| ≤
        4 * B_max / (2 * (M : ℝ) + 1) := by
    intro s b hs hb
    rw [h_evalLot s b]
    dsimp only [unroundedAvg]
    have h_sum_plan : ∑ k : Fin K, planRoundCost x (plan_fn k) s b =
        ∑ k : Fin K, if dotProduct x s ≤ p_tilde k ∧ p_tilde k ≤ dotProduct x b then
          Y₁_fn s b k else Y₀_fn s b k :=
      Finset.sum_congr rfl fun k _ => h_plan_cost_eq s b k
    rw [h_sum_plan, ← mul_sub, abs_mul, abs_of_pos hw₀_pos]
    have h_bd := h_s6_round p_tilde (Y₁_fn s b) (Y₀_fn s b) (2 * B_max)
      (dotProduct x s) (dotProduct x b) (by positivity) hp_window
      (fun k => (h_Y_bounds s b hs hb k).1) (fun k => (h_Y_bounds s b hs hb k).2)
    calc w₀ * |(∑ k : Fin K, if dotProduct x s ≤ p_tilde k ∧ p_tilde k ≤ dotProduct x b then
            Y₁_fn s b k else Y₀_fn s b k) -
          (∑ k : Fin K, if dotProduct x s ≤ q_fn k ∧ q_fn k ≤ dotProduct x b then
            Y₁_fn s b k else Y₀_fn s b k)|
        ≤ w₀ * (2 * (2 * B_max)) := mul_le_mul_of_nonneg_left h_bd hw₀_pos.le
      _ = 4 * B_max / (2 * (M : ℝ) + 1) := by
          dsimp only [w₀]
          ring

  refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
  
  · intro wp hwp
    rcases List.mem_map.mp hwp with ⟨k, _, rfl⟩
    exact hw₀_pos.le
  
  · dsimp only [L]
    rw [List.map_map, ← Fin.sum_univ_def]
    simp only [Function.comp_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    exact hw₀_K
  
  · intro wp hwp
    rcases List.mem_map.mp hwp with ⟨k, _, rfl⟩
    exact ⟨n_fn k, hp_tilde_eq k⟩
  
  · intro s b hs hb
    have herr : (L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum - unroundedAvg s b ≤
        4 * B_max / (2 * (M : ℝ) + 1) :=
      (le_abs_self _).trans (h_round_err s b hs hb)
    have hunr_eq : unroundedAvg s b =
        c⁻¹ * (2 * (M : ℝ) + 1)⁻¹ * ∑ k : Fin (2 * M + 1),
          (let u_k : ℝ := (((k : ℕ) : ℝ) - (M : ℝ)) * Δu
           let s_k : Fin d → ℝ := c • s + u_k • v
           let b_k : Fin d → ℝ := c • b + u_k • v
           if dotProduct x s_k ≤ pa ∧ pa ≤ dotProduct x b_k then
             (2 ^ 10 : ℝ) * tradeQuadPotential mS1 mB1 RS1 RB1 s_k b_k
           else
             max (dotProduct x b_k - dotProduct x s_k) 0 +
               (2 ^ 10 : ℝ) * tradeQuadPotential mS0 mB0 RS0 RB0 s_k b_k) := by
      have h_sum_eq :
          (∑ k : Fin K, if dotProduct x s ≤ q_fn k ∧ q_fn k ≤ dotProduct x b then
            Y₁_fn s b k else Y₀_fn s b k) =
          c⁻¹ * ∑ k : Fin K,
            (let u_k : ℝ := (((k : ℕ) : ℝ) - (M : ℝ)) * Δu
             let s_k : Fin d → ℝ := c • s + u_k • v
             let b_k : Fin d → ℝ := c • b + u_k • v
             if dotProduct x s_k ≤ pa ∧ pa ≤ dotProduct x b_k then
               (2 ^ 10 : ℝ) * tradeQuadPotential mS1 mB1 RS1 RB1 s_k b_k
             else
               max (dotProduct x b_k - dotProduct x s_k) 0 +
                 (2 ^ 10 : ℝ) * tradeQuadPotential mS0 mB0 RS0 RB0 s_k b_k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hiff := h_q_cond_iff s b k
        by_cases hQ : dotProduct x s ≤ q_fn k ∧ q_fn k ≤ dotProduct x b
        · have hP : dotProduct x (s_sh s k) ≤ pa ∧ pa ≤ dotProduct x (s_sh b k) := hiff.mp hQ
          rw [if_pos hQ]
          dsimp only [Y₁_fn, s_sh, u_fn] at hP ⊢
          rw [if_pos hP]
        · have hP : ¬ (dotProduct x (s_sh s k) ≤ pa ∧ pa ≤ dotProduct x (s_sh b k)) :=
            fun hp_in => hQ (hiff.mpr hp_in)
          rw [if_neg hQ]
          dsimp only [Y₀_fn, s_sh, u_fn] at hP ⊢
          rw [if_neg hP]
      dsimp only [unroundedAvg, w₀]
      rw [h_sum_eq]
      dsimp only [K]
      ring
    linarith
  
  · intro δ hδ0 hδ1 hcδ_lt s b s' b' hs hb hs' hb' hss' hbb'
    have hδ_lt_Δq : δ < Δq := by
      rw [show Δq = Δu / c from rfl, lt_div_iff₀ hc_pos, mul_comm]
      exact hcδ_lt
    let S : ℝ := dotProduct x s
    let B : ℝ := dotProduct x b
    let S' : ℝ := dotProduct x s'
    let B' : ℝ := dotProduct x b'
    have hSS'_le : |S - S'| ≤ δ := by
      have heq : S - S' = dotProduct x (s - s') := (dotProduct_sub x s s').symm
      rw [heq]
      exact (h_proj (s - s')).trans hss'
    have hBB'_le : |B - B'| ≤ δ := by
      have heq : B - B' = dotProduct x (b - b') := (dotProduct_sub x b b').symm
      rw [heq]
      exact (h_proj (b - b')).trans hbb'
    have hSS'_lt : |S - S'| < Δq := lt_of_le_of_lt hSS'_le hδ_lt_Δq
    have hBB'_lt : |B - B'| < Δq := lt_of_le_of_lt hBB'_le hδ_lt_Δq
    let L_step : ℝ := (2 + 16384 * τ⁻¹) * δ
    have hLstep_nn : 0 ≤ L_step := by
      dsimp only [L_step]
      positivity
    have h_max_lip : |max (B - S) 0 - max (B' - S') 0| ≤ 2 * δ := by
      have hS_b := abs_le.mp hSS'_le
      have hB_b := abs_le.mp hBB'_le
      by_cases h1 : 0 ≤ B - S <;> by_cases h2 : 0 ≤ B' - S'
      · rw [max_eq_left h1, max_eq_left h2]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · rw [max_eq_left h1, max_eq_right (le_of_not_ge h2)]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · rw [max_eq_right (le_of_not_ge h1), max_eq_left h2]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · rw [max_eq_right (le_of_not_ge h1), max_eq_right (le_of_not_ge h2), sub_self, abs_zero]
        linarith
    have h_Y1_lip : ∀ k : Fin K, |Y₁_fn s b k - Y₁_fn s' b' k| ≤ L_step := by
      intro k
      have hsk : vecL2Norm (s_sh s k) ≤ 1 := h_ball (u_fn k) (hu_bound k) s hs
      have hbk : vecL2Norm (s_sh b k) ≤ 1 := h_ball (u_fn k) (hu_bound k) b hb
      have hsk' : vecL2Norm (s_sh s' k) ≤ 1 := h_ball (u_fn k) (hu_bound k) s' hs'
      have hbk' : vecL2Norm (s_sh b' k) ≤ 1 := h_ball (u_fn k) (hu_bound k) b' hb'
      have hds : vecL2Norm (s_sh s k - s_sh s' k) ≤ c * δ := by
        dsimp only [s_sh]
        rw [h_diff_shift]
        exact mul_le_mul_of_nonneg_left hss' hc_pos.le
      have hdb : vecL2Norm (s_sh b k - s_sh b' k) ≤ c * δ := by
        dsimp only [s_sh]
        rw [h_diff_shift]
        exact mul_le_mul_of_nonneg_left hbb' hc_pos.le
      have hlipS := h_pot_lip mS1 hmS1 RS1 hRS1_pd hRS1_inv (s_sh s k) (s_sh s' k) hsk hsk'
      have hlipB := h_pot_lip mB1 hmB1 RB1 hRB1_pd hRB1_inv (s_sh b k) (s_sh b' k) hbk hbk'
      have h_tr_lip : |tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s k) (s_sh b k) -
          tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s' k) (s_sh b' k)| ≤ 8 * τ⁻¹ * c * δ := by
        have h_eq : tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s k) (s_sh b k) -
            tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s' k) (s_sh b' k) =
            (agentQuadPotential mS1 RS1 (s_sh s k) - agentQuadPotential mS1 RS1 (s_sh s' k)) +
            (agentQuadPotential mB1 RB1 (s_sh b k) - agentQuadPotential mB1 RB1 (s_sh b' k)) := by
          unfold tradeQuadPotential
          ring
        rw [h_eq]
        calc |(agentQuadPotential mS1 RS1 (s_sh s k) - agentQuadPotential mS1 RS1 (s_sh s' k)) +
              (agentQuadPotential mB1 RB1 (s_sh b k) - agentQuadPotential mB1 RB1 (s_sh b' k))|
            ≤ |agentQuadPotential mS1 RS1 (s_sh s k) - agentQuadPotential mS1 RS1 (s_sh s' k)| +
              |agentQuadPotential mB1 RB1 (s_sh b k) - agentQuadPotential mB1 RB1 (s_sh b' k)| :=
              abs_add_le _ _
          _ ≤ 4 * τ⁻¹ * vecL2Norm (s_sh s k - s_sh s' k) +
              4 * τ⁻¹ * vecL2Norm (s_sh b k - s_sh b' k) := add_le_add hlipS hlipB
          _ ≤ 4 * τ⁻¹ * (c * δ) + 4 * τ⁻¹ * (c * δ) :=
              add_le_add (mul_le_mul_of_nonneg_left hds (by positivity))
                (mul_le_mul_of_nonneg_left hdb (by positivity))
          _ = 8 * τ⁻¹ * c * δ := by ring
      have h1024 : (2 ^ 10 : ℝ) = 1024 := by norm_num
      have h_sub : Y₁_fn s b k - Y₁_fn s' b' k =
          (c⁻¹ * 1024) * (tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s k) (s_sh b k) -
            tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s' k) (s_sh b' k)) := by
        dsimp only [Y₁_fn]
        rw [h1024]
        ring
      rw [h_sub, abs_mul, abs_of_pos (by positivity)]
      calc (c⁻¹ * 1024) * |tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s k) (s_sh b k) -
              tradeQuadPotential mS1 mB1 RS1 RB1 (s_sh s' k) (s_sh b' k)|
          ≤ (c⁻¹ * 1024) * (8 * τ⁻¹ * c * δ) :=
            mul_le_mul_of_nonneg_left h_tr_lip (by positivity)
        _ = 8192 * τ⁻¹ * δ := by
            field_simp [hc_ne]
            ring
        _ ≤ L_step := by
            dsimp only [L_step]
            nlinarith [hτ_inv_pos, hδ0]
    have h_Y0_lip : ∀ k : Fin K, |Y₀_fn s b k - Y₀_fn s' b' k| ≤ L_step := by
      intro k
      have hsk : vecL2Norm (s_sh s k) ≤ 1 := h_ball (u_fn k) (hu_bound k) s hs
      have hbk : vecL2Norm (s_sh b k) ≤ 1 := h_ball (u_fn k) (hu_bound k) b hb
      have hsk' : vecL2Norm (s_sh s' k) ≤ 1 := h_ball (u_fn k) (hu_bound k) s' hs'
      have hbk' : vecL2Norm (s_sh b' k) ≤ 1 := h_ball (u_fn k) (hu_bound k) b' hb'
      have hds : vecL2Norm (s_sh s k - s_sh s' k) ≤ c * δ := by
        dsimp only [s_sh]
        rw [h_diff_shift]
        exact mul_le_mul_of_nonneg_left hss' hc_pos.le
      have hdb : vecL2Norm (s_sh b k - s_sh b' k) ≤ c * δ := by
        dsimp only [s_sh]
        rw [h_diff_shift]
        exact mul_le_mul_of_nonneg_left hbb' hc_pos.le
      have hlipS := h_pot_lip mS0 hmS0 RS0 hRS0_pd hRS0_inv (s_sh s k) (s_sh s' k) hsk hsk'
      have hlipB := h_pot_lip mB0 hmB0 RB0 hRB0_pd hRB0_inv (s_sh b k) (s_sh b' k) hbk hbk'
      have h_tr_lip : |tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s k) (s_sh b k) -
          tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s' k) (s_sh b' k)| ≤ 8 * τ⁻¹ * c * δ := by
        have h_eq : tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s k) (s_sh b k) -
            tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s' k) (s_sh b' k) =
            (agentQuadPotential mS0 RS0 (s_sh s k) - agentQuadPotential mS0 RS0 (s_sh s' k)) +
            (agentQuadPotential mB0 RB0 (s_sh b k) - agentQuadPotential mB0 RB0 (s_sh b' k)) := by
          unfold tradeQuadPotential
          ring
        rw [h_eq]
        calc |(agentQuadPotential mS0 RS0 (s_sh s k) - agentQuadPotential mS0 RS0 (s_sh s' k)) +
              (agentQuadPotential mB0 RB0 (s_sh b k) - agentQuadPotential mB0 RB0 (s_sh b' k))|
            ≤ |agentQuadPotential mS0 RS0 (s_sh s k) - agentQuadPotential mS0 RS0 (s_sh s' k)| +
              |agentQuadPotential mB0 RB0 (s_sh b k) - agentQuadPotential mB0 RB0 (s_sh b' k)| :=
              abs_add_le _ _
          _ ≤ 4 * τ⁻¹ * vecL2Norm (s_sh s k - s_sh s' k) +
              4 * τ⁻¹ * vecL2Norm (s_sh b k - s_sh b' k) := add_le_add hlipS hlipB
          _ ≤ 4 * τ⁻¹ * (c * δ) + 4 * τ⁻¹ * (c * δ) :=
              add_le_add (mul_le_mul_of_nonneg_left hds (by positivity))
                (mul_le_mul_of_nonneg_left hdb (by positivity))
          _ = 8 * τ⁻¹ * c * δ := by ring
      have h1024 : (2 ^ 10 : ℝ) = 1024 := by norm_num
      have h_sub : Y₀_fn s b k - Y₀_fn s' b' k =
          (max (B - S) 0 - max (B' - S') 0) +
          (c⁻¹ * 1024) * (tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s k) (s_sh b k) -
            tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s' k) (s_sh b' k)) := by
        dsimp only [Y₀_fn, S, B, S', B']
        rw [mul_add, mul_add, h_max_scale s b k, h_max_scale s' b' k, h1024]
        ring
      rw [h_sub]
      calc |(max (B - S) 0 - max (B' - S') 0) +
            (c⁻¹ * 1024) * (tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s k) (s_sh b k) -
              tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s' k) (s_sh b' k))|
          ≤ |max (B - S) 0 - max (B' - S') 0| +
            |(c⁻¹ * 1024) * (tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s k) (s_sh b k) -
              tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s' k) (s_sh b' k))| := abs_add_le _ _
        _ = |max (B - S) 0 - max (B' - S') 0| +
            (c⁻¹ * 1024) * |tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s k) (s_sh b k) -
              tradeQuadPotential mS0 mB0 RS0 RB0 (s_sh s' k) (s_sh b' k)| := by
            have hc1024 : 0 < c⁻¹ * 1024 := by positivity
            rw [abs_mul, abs_of_pos hc1024]
        _ ≤ 2 * δ + (c⁻¹ * 1024) * (8 * τ⁻¹ * c * δ) :=
            add_le_add h_max_lip (mul_le_mul_of_nonneg_left h_tr_lip (by positivity))
        _ = 2 * δ + 8192 * τ⁻¹ * δ := by
            congr 1
            field_simp [hc_ne]
            ring
        _ ≤ L_step := by
            dsimp only [L_step]
            nlinarith [hτ_inv_pos, hδ0]
    have h_pert_avg : |unroundedAvg s b - unroundedAvg s' b'| ≤
        4 * B_max / (2 * (M : ℝ) + 1) + L_step := by
      dsimp only [unroundedAvg]
      rw [← mul_sub, abs_mul, abs_of_pos hw₀_pos]
      have h_bd := h_s6_pert (Y₁_fn s b) (Y₀_fn s b) (Y₁_fn s' b') (Y₀_fn s' b')
        (2 * B_max) L_step S B S' B' (by positivity) hLstep_nn hSS'_lt hBB'_lt
        (fun k => (h_Y_bounds s b hs hb k).1) (fun k => (h_Y_bounds s b hs hb k).2)
        (fun k => (h_Y_bounds s' b' hs' hb' k).1) (fun k => (h_Y_bounds s' b' hs' hb' k).2)
        h_Y1_lip h_Y0_lip
      calc w₀ * |(∑ k : Fin K, if S ≤ q_fn k ∧ q_fn k ≤ B then Y₁_fn s b k else Y₀_fn s b k) -
            (∑ k : Fin K, if S' ≤ q_fn k ∧ q_fn k ≤ B' then Y₁_fn s' b' k else Y₀_fn s' b' k)|
          ≤ w₀ * (2 * (2 * B_max) + (K : ℝ) * L_step) :=
            mul_le_mul_of_nonneg_left h_bd hw₀_pos.le
        _ = w₀ * (4 * B_max) + (w₀ * (K : ℝ)) * L_step := by ring
        _ = 4 * B_max / (2 * (M : ℝ) + 1) + L_step := by
            rw [mul_comm w₀ (K : ℝ), hw₀_K, one_mul]
            dsimp only [w₀]
            ring
    have hr1 := h_round_err s b hs hb
    have hr2 := h_round_err s' b' hs' hb'
    have h_tri : |(L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum -
        (L.map (fun wp => wp.1 * planRoundCost x wp.2 s' b')).sum| ≤
        |(L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum - unroundedAvg s b| +
        |unroundedAvg s b - unroundedAvg s' b'| +
        |unroundedAvg s' b' - (L.map (fun wp => wp.1 * planRoundCost x wp.2 s' b')).sum| := by
      let E1 := (L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum - unroundedAvg s b
      let E2 := unroundedAvg s b - unroundedAvg s' b'
      let E3 := unroundedAvg s' b' - (L.map (fun wp => wp.1 * planRoundCost x wp.2 s' b')).sum
      have h_id : (L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum -
          (L.map (fun wp => wp.1 * planRoundCost x wp.2 s' b')).sum = (E1 + E2) + E3 := by
        dsimp only [E1, E2, E3]
        ring
      rw [h_id]
      linarith [abs_add_le (E1 + E2) E3, abs_add_le E1 E2]
    rw [abs_sub_comm (unroundedAvg s' b')] at h_tri
    dsimp only [L_step] at h_pert_avg
    have h_sum12 : 4 * B_max / (2 * (M : ℝ) + 1) + 4 * B_max / (2 * (M : ℝ) + 1) +
        4 * B_max / (2 * (M : ℝ) + 1) = 12 * B_max / (2 * (M : ℝ) + 1) := by ring
    linarith [h_tri, hr1, h_pert_avg, hr2, h_sum12]

theorem lem_unit_ball_finite_net (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (net : Fin N → (Fin d → ℝ) × (Fin d → ℝ)),
      0 < N ∧
      (∀ i : Fin N, vecL2Norm (net i).1 ≤ 1 ∧ vecL2Norm (net i).2 ≤ 1) ∧
      (∀ s b : Fin d → ℝ, vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 →
        ∃ i : Fin N, vecL2Norm (s - (net i).1) ≤ δ ∧ vecL2Norm (b - (net i).2) ≤ δ) :=
by
  classical
  let toE : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := fun v => WithLp.toLp 2 v
  have hnorm_ofLp : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = vecL2Norm x.ofLp := by
    intro x
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs, vecL2Norm]
  have hnorm_toE : ∀ v : Fin d → ℝ, ‖toE v‖ = vecL2Norm v := fun v =>
    hnorm_ofLp (toE v)
  have hdist_toE : ∀ (u : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d)),
      vecL2Norm (u - x.ofLp) = dist (toE u) x := by
    intro u x
    rw [← hnorm_toE (u - x.ofLp)]
    have hsub : toE (u - x.ofLp) = toE u - x := rfl
    rw [hsub, ← dist_eq_norm]
  let B : Set (EuclideanSpace ℝ (Fin d)) :=
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  have hB_compact : IsCompact B :=
    isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  obtain ⟨t, ht_sub, ht_cov⟩ :=
    hB_compact.elim_nhds_subcover (fun x => Metric.closedBall x δ)
      (fun x _ => Metric.closedBall_mem_nhds x hδ)
  have h0_in_B : (0 : EuclideanSpace ℝ (Fin d)) ∈ B :=
    Metric.mem_closedBall_self zero_le_one
  obtain ⟨x₀, hx₀, _⟩ := Set.mem_iUnion₂.mp (ht_cov h0_in_B)
  have hM₀_pos : 0 < t.card := Finset.card_pos.mpr ⟨x₀, hx₀⟩
  let M₀ : ℕ := t.card
  let N : ℕ := M₀ * M₀
  have hN_pos : 0 < N := Nat.mul_pos hM₀_pos hM₀_pos
  let g : Fin M₀ ≃ ↥t := t.equivFin.symm
  let e : Fin M₀ × Fin M₀ ≃ Fin N := finProdFinEquiv
  let net : Fin N → (Fin d → ℝ) × (Fin d → ℝ) :=
    fun i => ((g (e.symm i).1).1.ofLp, (g (e.symm i).2).1.ofLp)
  refine ⟨N, net, hN_pos, ?_, ?_⟩
  · intro i
    constructor
    · have hmem1 : (g (e.symm i).1).1 ∈ B := ht_sub _ (g (e.symm i).1).2
      have hnorm1 : ‖(g (e.symm i).1).1‖ ≤ 1 := mem_closedBall_zero_iff.mp hmem1
      dsimp [net]
      rw [← hnorm_ofLp]
      exact hnorm1
    · have hmem2 : (g (e.symm i).2).1 ∈ B := ht_sub _ (g (e.symm i).2).2
      have hnorm2 : ‖(g (e.symm i).2).1‖ ≤ 1 := mem_closedBall_zero_iff.mp hmem2
      dsimp [net]
      rw [← hnorm_ofLp]
      exact hnorm2
  · intro s b hs hb
    have hs_B : toE s ∈ B := by
      refine mem_closedBall_zero_iff.mpr ?_
      rw [hnorm_toE]
      exact hs
    have hb_B : toE b ∈ B := by
      refine mem_closedBall_zero_iff.mpr ?_
      rw [hnorm_toE]
      exact hb
    obtain ⟨xs, hxs_mem, hxs_ball⟩ := Set.mem_iUnion₂.mp (ht_cov hs_B)
    obtain ⟨xb, hxb_mem, hxb_ball⟩ := Set.mem_iUnion₂.mp (ht_cov hb_B)
    have hxs_dist : dist (toE s) xs ≤ δ := Metric.mem_closedBall.mp hxs_ball
    have hxb_dist : dist (toE b) xb ≤ δ := Metric.mem_closedBall.mp hxb_ball
    let j : Fin M₀ := g.symm ⟨xs, hxs_mem⟩
    let k : Fin M₀ := g.symm ⟨xb, hxb_mem⟩
    let i : Fin N := e (j, k)
    refine ⟨i, ?_, ?_⟩
    · have hi1 : (net i).1 = xs.ofLp := by
        dsimp [net, i, j]
        rw [Equiv.symm_apply_apply e (j, k)]
        dsimp
        rw [Equiv.apply_symm_apply g ⟨xs, hxs_mem⟩]
      rw [hi1, hdist_toE]
      exact hxs_dist
    · have hi2 : (net i).2 = xb.ofLp := by
        dsimp [net, i, k]
        rw [Equiv.symm_apply_apply e (j, k)]
        dsimp
        rw [Equiv.apply_symm_apply g ⟨xb, hxb_mem⟩]
      rw [hi2, hdist_toE]
      exact hxb_dist

theorem lem_fintype_minimax_separation {N : ℕ} (hN : 0 < N) {α : Type*}
    (F : α → (Fin N → ℝ)) (θ : ℝ)
    (h_resp : ∀ w : Fin N → ℝ, (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
      ∃ a : α, ∑ i, w i * F a i < θ) :
    ∃ mix : List (ℝ × α),
      (∀ wa ∈ mix, 0 ≤ wa.1) ∧
      (mix.map Prod.fst).sum = 1 ∧
      (∀ i : Fin N, (mix.map (fun wa => wa.1 * F wa.2 i)).sum < θ) :=
by
  classical
  
  have hN_real : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  let w₀ : Fin N → ℝ := fun _ => (N : ℝ)⁻¹
  have hw₀_nn : ∀ i : Fin N, 0 ≤ w₀ i := fun _ => inv_nonneg.mpr (le_of_lt hN_real)
  have hw₀_sum : ∑ i : Fin N, w₀ i = 1 := by
    dsimp [w₀]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt hN_real)
  obtain ⟨a₀, _⟩ := h_resp w₀ hw₀_nn hw₀_sum

  
  let U : Set (Fin N → ℝ) := Set.univ.pi (fun _ : Fin N => Set.Iio θ)
  have hU_mem : ∀ y : Fin N → ℝ, y ∈ U ↔ ∀ i : Fin N, y i < θ := by
    intro y
    simp [U]
  have hU_conv : Convex ℝ U := convex_pi (fun _ _ => convex_Iio θ)
  have hU_open : IsOpen U := isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Iio)
  let y₀ : Fin N → ℝ := fun _ => θ - 1
  have hy₀_mem : y₀ ∈ U := (hU_mem y₀).mpr (fun _ => by dsimp [y₀]; linarith)

  let C : Set (Fin N → ℝ) := convexHull ℝ (Set.range F)
  have hC_conv : Convex ℝ C := convex_convexHull ℝ (Set.range F)
  have hF_mem_C : ∀ a : α, F a ∈ C := fun a =>
    subset_convexHull ℝ (Set.range F) ⟨a, rfl⟩

  
  have h_not_disj : ¬ Disjoint U C := by
    intro h_disj
    obtain ⟨f, u, hfU, hfC⟩ := geometric_hahn_banach_open hU_conv hU_open hC_conv h_disj
    let e_vec : Fin N → (Fin N → ℝ) := fun i => Pi.single i (1 : ℝ)
    let μ : Fin N → ℝ := fun i => f (e_vec i)
    have hf_coord : ∀ y : Fin N → ℝ, f y = ∑ i : Fin N, μ i * y i := by
      intro y
      have hy_decomp : y = ∑ i : Fin N, y i • e_vec i := by
        ext k
        rw [Finset.sum_apply]
        simp [e_vec, Pi.single_apply]
      conv_lhs => rw [hy_decomp]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [f.map_smul, smul_eq_mul, mul_comm]
    
    have hμ_nn : ∀ i : Fin N, 0 ≤ μ i := by
      intro i₀
      by_contra h_neg_not
      have hμ_neg : μ i₀ < 0 := lt_of_not_ge h_neg_not
      have h_pos : 0 < -μ i₀ := neg_pos.mpr hμ_neg
      let t : ℝ := max 1 ((u - f y₀ + 1) / (-μ i₀))
      have ht_ge1 : 1 ≤ t := le_max_left _ _
      have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_ge1
      have ht_div : (u - f y₀ + 1) / (-μ i₀) ≤ t := le_max_right _ _
      have ht_mul : u - f y₀ + 1 ≤ t * (-μ i₀) := (div_le_iff₀ h_pos).mp ht_div
      let y_t : Fin N → ℝ := y₀ - t • e_vec i₀
      have hy_t_U : y_t ∈ U := by
        rw [hU_mem]
        intro j
        by_cases hj : j = i₀
        · subst hj
          simp only [y_t, y₀, e_vec, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
          linarith
        · simp only [y_t, y₀, e_vec, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero]
          linarith
      have hf_lt : f y_t < u := hfU y_t hy_t_U
      have hf_eq : f y_t = f y₀ - t * μ i₀ := by
        dsimp [y_t]
        rw [map_sub, f.map_smul, smul_eq_mul]
      linarith
    
    let S_μ : ℝ := ∑ i : Fin N, μ i
    have hS_nn : 0 ≤ S_μ := Finset.sum_nonneg (fun i _ => hμ_nn i)
    have hS_pos : 0 < S_μ := by
      by_contra h_not_pos
      have hS_zero : S_μ = 0 := le_antisymm (le_of_not_gt h_not_pos) hS_nn
      have hμ_zero : ∀ i ∈ (Finset.univ : Finset (Fin N)), μ i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hμ_nn i)).mp hS_zero
      have hf_zero : ∀ y : Fin N → ℝ, f y = 0 := by
        intro y
        rw [hf_coord y]
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [hμ_zero i hi, zero_mul]
      have hu1 : f y₀ < u := hfU y₀ hy₀_mem
      have hu2 : u ≤ f (F a₀) := hfC (F a₀) (hF_mem_C a₀)
      rw [hf_zero y₀] at hu1
      rw [hf_zero (F a₀)] at hu2
      linarith
    
    have hSθ_le : S_μ * θ ≤ u := by
      by_contra h_not_le
      have hu_lt : u < S_μ * θ := lt_of_not_ge h_not_le
      let η : ℝ := (S_μ * θ - u) / (2 * S_μ)
      have hη_pos : 0 < η := div_pos (by linarith) (by linarith)
      let y_η : Fin N → ℝ := fun _ => θ - η
      have hy_η_U : y_η ∈ U := (hU_mem y_η).mpr (fun _ => by dsimp [y_η]; linarith)
      have hf_lt : f y_η < u := hfU y_η hy_η_U
      have hf_val : f y_η = (S_μ * θ + u) / 2 := by
        rw [hf_coord y_η]
        dsimp [y_η]
        rw [← Finset.sum_mul]
        change S_μ * (θ - η) = (S_μ * θ + u) / 2
        dsimp [η]
        field_simp [ne_of_gt hS_pos]
        ring
      linarith
    
    let w : Fin N → ℝ := fun i => μ i / S_μ
    have hw_nn : ∀ i : Fin N, 0 ≤ w i := fun i => div_nonneg (hμ_nn i) (le_of_lt hS_pos)
    have hw_sum : ∑ i : Fin N, w i = 1 := by
      dsimp [w]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hS_pos)
    obtain ⟨a, ha_lt⟩ := h_resp w hw_nn hw_sum
    have h_mul_lt : S_μ * (∑ i : Fin N, w i * F a i) < S_μ * θ :=
      mul_lt_mul_of_pos_left ha_lt hS_pos
    have h_mul_eq : S_μ * (∑ i : Fin N, w i * F a i) = f (F a) := by
      rw [Finset.mul_sum, hf_coord (F a)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      dsimp [w]
      field_simp [ne_of_gt hS_pos]
    have hfFa_ge : u ≤ f (F a) := hfC (F a) (hF_mem_C a)
    linarith

  
  obtain ⟨y, hyU, hyC⟩ := Set.not_disjoint_iff.mp h_not_disj
  have hy_lt : ∀ i : Fin N, y i < θ := (hU_mem y).mp hyU
  obtain ⟨ι, hι_fin, β, z, hβ_nn, hβ_sum, hz_mem, hz_sum⟩ :=
    mem_convexHull_iff_exists_fintype.mp hyC
  letI : Fintype ι := hι_fin
  choose g hg using hz_mem
  let m : ℕ := Fintype.card ι
  let e : Fin m ≃ ι := (Fintype.equivFin ι).symm
  let mix : List (ℝ × α) := List.ofFn (fun k : Fin m => (β (e k), g (e k)))
  refine ⟨mix, ?_, ?_, ?_⟩
  · intro wa hwa
    rcases List.mem_ofFn.mp hwa with ⟨k, rfl⟩
    exact hβ_nn (e k)
  · simp only [mix, List.map_ofFn, Function.comp, List.sum_ofFn]
    rw [Equiv.sum_comp e]
    exact hβ_sum
  · intro i
    have h_sum_eq : (mix.map (fun wa => wa.1 * F wa.2 i)).sum = y i := by
      simp only [mix, List.map_ofFn, Function.comp, List.sum_ofFn, hg]
      rw [Equiv.sum_comp e (fun j => β j * z j i)]
      have hy_i : (∑ j : ι, β j • z j) i = y i := congr_fun hz_sum i
      rw [← hy_i, Finset.sum_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [Pi.smul_apply, smul_eq_mul]
    rw [h_sum_eq]
    exact hy_lt i

/-- **Lemma 3.3 (A valid lottery exists, `lem:trade-lottery`, Section 3.2 & Appendix D.2)**:
For every `m = (m_S, m_B) ∈ ℝ^{2d}`, every block-diagonal `R = diag(R_S, R_B) ≻ 0`, every context
`x` with `‖x‖₂ ≤ 1`, and every `γ ∈ (0, 1]`, there exists a finite lottery of plans with common
prices on a rational grid `k / gridDenom` (`gridDenom > 0`), nonnegative weights summing to `1`,
and `E[ℓ(w) + 2^{10} Φ(m⁺, R⁺, w)] ≤ 2^{10} Φ(m, R, w) + γ` for every `w = (s, b) ∈ K` (Eq. (21)). -/
theorem lem_trade_lottery {d : ℕ}
    (mS mB : Fin d → ℝ)
    (RS RB : Matrix (Fin d) (Fin d) ℝ) (hRS : RS.PosDef) (hRB : RB.PosDef)
    (x : Fin d → ℝ) (hx : vecL2Norm x ≤ 1)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ (lottery : List (ℝ × TradePlan d)) (gridDenom : ℕ),
      0 < gridDenom ∧
      (∀ wp ∈ lottery, 0 ≤ wp.1) ∧
      (lottery.map Prod.fst).sum = 1 ∧
      (∀ wp ∈ lottery, ∃ k : ℤ, (wp.2.price : ℝ) = (k : ℝ) / (gridDenom : ℝ)) ∧
      (∀ s b : Fin d → ℝ, vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 →
        (lottery.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum ≤
          (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB s b + γ) :=
by
  classical
  by_cases hx0 : x = 0
  · let plan₀ : TradePlan d := {
      price := 0
      mS0 := mS
      mB0 := mB
      RS0 := RS
      RB0 := RB
      mS1 := mS
      mB1 := mB
      RS1 := RS
      RB1 := RB
      posDef_RS0 := hRS
      posDef_RB0 := hRB
      posDef_RS1 := hRS
      posDef_RB1 := hRB
    }
    refine ⟨[((1 : ℝ), plan₀)], 1, Nat.zero_lt_one, ?_, ?_, ?_, ?_⟩
    · intro wp hwp
      simp only [List.mem_singleton] at hwp
      rw [hwp]
      norm_num
    · simp
    · intro wp hwp
      simp only [List.mem_singleton] at hwp
      rw [hwp]
      exact ⟨0, by simp [plan₀]⟩
    · intro s b _ _
      have hcost : planRoundCost x plan₀ s b =
          (2 ^ 10 : ℝ) * tradeQuadPotential mS mB RS RB s b := by
        simp [planRoundCost, hx0, plan₀]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]
      linarith [hcost, hγ0]
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx0
    have hd_pos : 0 < d := i₀.pos
    have hd_real : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
    have h_sq_pos : 0 < ∑ i : Fin d, (x i) ^ 2 := by
      have hi₀_sq : 0 < (x i₀) ^ 2 := sq_pos_of_ne_zero hi₀
      have h_le : (x i₀) ^ 2 ≤ ∑ i : Fin d, (x i) ^ 2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i₀)
      linarith
    let nx : ℝ := vecL2Norm x
    have hnx_pos : 0 < nx := Real.sqrt_pos.mpr h_sq_pos
    let v : Fin d → ℝ := (nx ^ 2)⁻¹ • x
    obtain ⟨C0, L0, hC0_pos, hL0_pos, h_ball, h_drift, h_pot_lip⟩ :=
      lem_initial_potential_jitter_and_lip mS mB RS RB hRS hRB x hx0 hx
    let ε : ℝ := min (1 / 4) (γ / (6 * C0))
    have hε0 : 0 < ε := lt_min (by norm_num) (div_pos hγ0 (by positivity))
    have hε1 : ε ≤ 1 / 4 := min_le_left _ _
    have hε_C0 : C0 * ε ≤ γ / 6 := by
      have h1 : ε ≤ γ / (6 * C0) := min_le_right _ _
      calc C0 * ε ≤ C0 * (γ / (6 * C0)) := mul_le_mul_of_nonneg_left h1 (le_of_lt hC0_pos)
        _ = γ / 6 := by field_simp [ne_of_gt hC0_pos]
    let c : ℝ := 1 - ε
    have hc_ge : 3 / 4 ≤ c := by dsimp [c]; linarith [hε1]
    have hc_pos : 0 < c := by linarith
    have hc_inv_le2 : c⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hc_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    let τ : ℝ := min 1 (γ / (12 * 2048 * (d : ℝ)))
    have hτ0 : 0 < τ := lt_min zero_lt_one (div_pos hγ0 (by positivity))
    have hτ1 : τ ≤ 1 := min_le_left _ _
    have hτ_bound : c⁻¹ * (2048 * (d : ℝ) * τ) ≤ γ / 6 := by
      have h1 : τ ≤ γ / (12 * 2048 * (d : ℝ)) := min_le_right _ _
      have h2 : 2048 * (d : ℝ) * τ ≤ γ / 12 := by
        calc 2048 * (d : ℝ) * τ
            ≤ 2048 * (d : ℝ) * (γ / (12 * 2048 * (d : ℝ))) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = γ / 12 := by field_simp [ne_of_gt hd_real]
      have h3 : 0 ≤ 2048 * (d : ℝ) * τ := by positivity
      calc c⁻¹ * (2048 * (d : ℝ) * τ)
          ≤ 2 * (γ / 12) := mul_le_mul hc_inv_le2 h2 h3 (by norm_num)
        _ = γ / 6 := by ring
    let B_max : ℝ := 2 + 4096 * (d : ℝ) + 8192 * τ⁻¹
    have hBmax_pos : 0 < B_max := by positivity
    obtain ⟨M, hM_gt⟩ := exists_nat_gt (24 * B_max / γ)
    have hM_real_pos : 0 < (M : ℝ) := lt_trans (div_pos (by positivity) hγ0) hM_gt
    have hM_pos : 0 < M := Nat.cast_pos.mp hM_real_pos
    let K_jit : ℕ := 2 * M + 1
    have hKjit_eq : (K_jit : ℝ) = 2 * (M : ℝ) + 1 := by push_cast [K_jit]; ring
    have hKjit_pos : 0 < (K_jit : ℝ) := by linarith
    have h48_lt : 48 * B_max < (2 * (M : ℝ) + 1) * γ := by
      have h1 : 24 * B_max < (M : ℝ) * γ := (div_lt_iff₀ hγ0).mp hM_gt
      nlinarith
    have hM_bound4 : 4 * B_max / (2 * (M : ℝ) + 1) < γ / 12 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 12)]
      linarith
    have hM_bound12 : 12 * B_max / (2 * (M : ℝ) + 1) < γ / 4 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
      linarith
    let Δu : ℝ := ε * nx / (M : ℝ)
    have hΔu_pos : 0 < Δu := div_pos (mul_pos hε0 hnx_pos) hM_real_pos
    let L_lip : ℝ := (2 + 16384 * τ⁻¹) + L0
    have hLlip_pos : 0 < L_lip := by positivity
    let δ : ℝ := min 1 (min (Δu / (2 * c)) (γ / (6 * L_lip)))
    have hδ0 : 0 < δ := lt_min zero_lt_one (lt_min (div_pos hΔu_pos (by positivity))
      (div_pos hγ0 (by positivity)))
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ_step : c * δ < Δu := by
      have h1 : δ ≤ Δu / (2 * c) := le_trans (min_le_right _ _) (min_le_left _ _)
      have h2 : c * δ ≤ Δu / 2 := by
        calc c * δ ≤ c * (Δu / (2 * c)) := mul_le_mul_of_nonneg_left h1 (le_of_lt hc_pos)
          _ = Δu / 2 := by field_simp [ne_of_gt hc_pos]
      linarith
    have hδ_lip : L_lip * δ ≤ γ / 6 := by
      have h1 : δ ≤ γ / (6 * L_lip) := le_trans (min_le_right _ _) (min_le_right _ _)
      calc L_lip * δ ≤ L_lip * (γ / (6 * L_lip)) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hLlip_pos)
        _ = γ / 6 := by field_simp [ne_of_gt hLlip_pos]
    obtain ⟨gridDenom, hGrid_gt⟩ := exists_nat_gt (c / Δu)
    have hGrid_real_pos : 0 < (gridDenom : ℝ) := lt_trans (div_pos hc_pos hΔu_pos) hGrid_gt
    have hGrid_pos : 0 < gridDenom := Nat.cast_pos.mp hGrid_real_pos
    have hGridStep : c / (gridDenom : ℝ) < Δu := by
      rw [div_lt_iff₀ hGrid_real_pos]
      have h1 : c < (gridDenom : ℝ) * Δu := (div_lt_iff₀ hΔu_pos).mp hGrid_gt
      linarith
    obtain ⟨N, net, hN_pos, hnet_ball, hnet_cover⟩ := lem_unit_ball_finite_net d hδ0
    let u_fn : Fin K_jit → ℝ := fun k => (((k : ℕ) : ℝ) - (M : ℝ)) * Δu
    have hu_bound : ∀ k : Fin K_jit, |u_fn k| ≤ ε * nx := by
      intro k
      have hk_le : (k : ℕ) ≤ 2 * M := Nat.lt_succ_iff.mp k.isLt
      have hk_real_le : ((k : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hk_le
      have hk_real_nn : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
      have habs : |((k : ℕ) : ℝ) - (M : ℝ)| ≤ (M : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |u_fn k|
          = |((k : ℕ) : ℝ) - (M : ℝ)| * |Δu| := abs_mul _ _
        _ = |((k : ℕ) : ℝ) - (M : ℝ)| * Δu := by rw [abs_of_pos hΔu_pos]
        _ ≤ (M : ℝ) * Δu := mul_le_mul_of_nonneg_right habs (le_of_lt hΔu_pos)
        _ = ε * nx := by
            dsimp [Δu]
            field_simp [ne_of_gt hM_real_pos]
    let evalLot : List (ℝ × TradePlan d) → (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
      fun L s b => (L.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum
    let Phi0 : (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
      fun s b => tradeQuadPotential mS mB RS RB s b
    let ValidBasePred : List (ℝ × TradePlan d) → Prop := fun L =>
      (∀ wp ∈ L, 0 ≤ wp.1) ∧
      (L.map Prod.fst).sum = 1 ∧
      (∀ wp ∈ L, ∃ k : ℤ, (wp.2.price : ℝ) = (k : ℝ) / (gridDenom : ℝ)) ∧
      (∀ s b s' b' : Fin d → ℝ,
        vecL2Norm s ≤ 1 → vecL2Norm b ≤ 1 → vecL2Norm s' ≤ 1 → vecL2Norm b' ≤ 1 →
        vecL2Norm (s - s') ≤ δ → vecL2Norm (b - b') ≤ δ →
        |evalLot L s b - evalLot L s' b'| ≤
          12 * B_max / (2 * (M : ℝ) + 1) + (2 + 16384 * τ⁻¹) * δ)
    let ValidBase := { L : List (ℝ × TradePlan d) // ValidBasePred L }
    let F : ValidBase → (Fin N → ℝ) := fun a i =>
      evalLot a.1 (net i).1 (net i).2 - (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2
    have h_resp : ∀ lam : Fin N → ℝ, (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 →
        ∃ a : ValidBase, ∑ i, lam i * F a i < γ / 2 := by
      intro lam hlam_nn hlam_sum
      let K_tot : ℕ := N * K_jit
      let e : Fin N × Fin K_jit ≃ Fin K_tot := finProdFinEquiv
      let w_tilde : Fin K_tot → ℝ := fun r => lam (e.symm r).1 * (K_jit : ℝ)⁻¹
      let s_tilde : Fin K_tot → (Fin d → ℝ) :=
        fun r => c • (net (e.symm r).1).1 + (u_fn (e.symm r).2) • v
      let b_tilde : Fin K_tot → (Fin d → ℝ) :=
        fun r => c • (net (e.symm r).1).2 + (u_fn (e.symm r).2) • v
      have hw_tilde_nn : ∀ r : Fin K_tot, 0 ≤ w_tilde r := fun r =>
        mul_nonneg (hlam_nn _) (inv_nonneg.mpr (le_of_lt hKjit_pos))
      have hw_tilde_sum : ∑ r : Fin K_tot, w_tilde r = 1 := by
        rw [← Equiv.sum_comp e]
        simp only [w_tilde, Equiv.symm_apply_apply]
        rw [Fintype.sum_prod_type]
        have h_inner : ∀ i : Fin N, ∑ _k : Fin K_jit, lam i * (K_jit : ℝ)⁻¹ = lam i := by
          intro i
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp [ne_of_gt hKjit_pos]
        simp_rw [h_inner]
        exact hlam_sum
      have hs_tilde : ∀ r : Fin K_tot, vecL2Norm (s_tilde r) ≤ 1 := fun r =>
        h_ball ε (u_fn (e.symm r).2) hε0 hε1 (hu_bound _) _ (hnet_ball _).1
      have hb_tilde : ∀ r : Fin K_tot, vecL2Norm (b_tilde r) ≤ 1 := fun r =>
        h_ball ε (u_fn (e.symm r).2) hε0 hε1 (hu_bound _) _ (hnet_ball _).2
      obtain ⟨pa, h_toi⟩ := lem_scalar_trade_or_info w_tilde hw_tilde_nn hw_tilde_sum
        (fun r => dotProduct x (s_tilde r)) (fun r => dotProduct x (b_tilde r))
      let E : Finset (Fin K_tot) :=
        Finset.univ.filter (fun r => dotProduct x (s_tilde r) ≤ pa ∧ pa ≤ dotProduct x (b_tilde r))
      let Ec : Finset (Fin K_tot) := Finset.univ \ E
      have h_toi_E : ∑ r ∈ Ec, w_tilde r *
          max (dotProduct x (b_tilde r) - dotProduct x (s_tilde r)) 0 ≤
          2048 * ((finWeightedStdDev w_tilde Finset.univ (fun r => dotProduct x (s_tilde r)) -
                    finWeightedStdDev w_tilde E (fun r => dotProduct x (s_tilde r)) -
                    finWeightedStdDev w_tilde Ec (fun r => dotProduct x (s_tilde r))) +
                  (finWeightedStdDev w_tilde Finset.univ (fun r => dotProduct x (b_tilde r)) -
                    finWeightedStdDev w_tilde E (fun r => dotProduct x (b_tilde r)) -
                    finWeightedStdDev w_tilde Ec (fun r => dotProduct x (b_tilde r)))) := h_toi
      obtain ⟨mS1, mS0, RS1, RS0, hRS1_pd, hRS0_pd, hmS1, hmS0, hRS1_tr, hRS0_tr,
              hRS1_inv, hRS0_inv, hS_tang⟩ :=
        lem_directional_and_tangent_bounds w_tilde hw_tilde_nn hw_tilde_sum s_tilde hs_tilde
          mS RS hRS x hx E τ hτ0 hτ1
      obtain ⟨mB1, mB0, RB1, RB0, hRB1_pd, hRB0_pd, hmB1, hmB0, hRB1_tr, hRB0_tr,
              hRB1_inv, hRB0_inv, hB_tang⟩ :=
        lem_directional_and_tangent_bounds w_tilde hw_tilde_nn hw_tilde_sum b_tilde hb_tilde
          mB RB hRB x hx E τ hτ0 hτ1
      let baseCost : (Fin d → ℝ) → (Fin d → ℝ) → ℝ := fun s' b' =>
        if dotProduct x s' ≤ pa ∧ pa ≤ dotProduct x b' then
          (2 ^ 10 : ℝ) * tradeQuadPotential mS1 mB1 RS1 RB1 s' b'
        else
          max (dotProduct x b' - dotProduct x s') 0 +
            (2 ^ 10 : ℝ) * tradeQuadPotential mS0 mB0 RS0 RB0 s' b'
      have h_sum_E : ∑ r ∈ E, w_tilde r * baseCost (s_tilde r) (b_tilde r) =
          (2 ^ 10 : ℝ) * (∑ r ∈ E, w_tilde r * agentQuadPotential mS1 RS1 (s_tilde r)) +
          (2 ^ 10 : ℝ) * (∑ r ∈ E, w_tilde r * agentQuadPotential mB1 RB1 (b_tilde r)) := by
        have h_congr : ∀ r ∈ E, w_tilde r * baseCost (s_tilde r) (b_tilde r) =
            (2 ^ 10 : ℝ) * (w_tilde r * agentQuadPotential mS1 RS1 (s_tilde r)) +
            (2 ^ 10 : ℝ) * (w_tilde r * agentQuadPotential mB1 RB1 (b_tilde r)) := by
          intro r hr
          have hcond : dotProduct x (s_tilde r) ≤ pa ∧ pa ≤ dotProduct x (b_tilde r) :=
            (Finset.mem_filter.mp hr).2
          dsimp [baseCost, tradeQuadPotential]
          rw [if_pos hcond]
          ring
        rw [Finset.sum_congr rfl h_congr, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have h_sum_Ec : ∑ r ∈ Ec, w_tilde r * baseCost (s_tilde r) (b_tilde r) =
          (∑ r ∈ Ec, w_tilde r * max (dotProduct x (b_tilde r) - dotProduct x (s_tilde r)) 0) +
          (2 ^ 10 : ℝ) * (∑ r ∈ Ec, w_tilde r * agentQuadPotential mS0 RS0 (s_tilde r)) +
          (2 ^ 10 : ℝ) * (∑ r ∈ Ec, w_tilde r * agentQuadPotential mB0 RB0 (b_tilde r)) := by
        have h_congr : ∀ r ∈ Ec, w_tilde r * baseCost (s_tilde r) (b_tilde r) =
            (w_tilde r * max (dotProduct x (b_tilde r) - dotProduct x (s_tilde r)) 0 +
             (2 ^ 10 : ℝ) * (w_tilde r * agentQuadPotential mS0 RS0 (s_tilde r))) +
            (2 ^ 10 : ℝ) * (w_tilde r * agentQuadPotential mB0 RB0 (b_tilde r)) := by
          intro r hr
          have hr_not : r ∉ E := (Finset.mem_sdiff.mp hr).2
          have hcond : ¬ (dotProduct x (s_tilde r) ≤ pa ∧ pa ≤ dotProduct x (b_tilde r)) := by
            intro hc_in
            exact hr_not (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hc_in⟩)
          dsimp [baseCost, tradeQuadPotential]
          rw [if_neg hcond]
          ring
        rw [Finset.sum_congr rfl h_congr, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
      have h_split_univ : ∑ r : Fin K_tot, w_tilde r * baseCost (s_tilde r) (b_tilde r) =
          (∑ r ∈ Ec, w_tilde r * baseCost (s_tilde r) (b_tilde r)) +
          (∑ r ∈ E, w_tilde r * baseCost (s_tilde r) (b_tilde r)) :=
        (Finset.sum_sdiff (Finset.subset_univ E)).symm
      have h_prior_sum :
          (2 ^ 10 : ℝ) * (∑ r : Fin K_tot, w_tilde r * agentQuadPotential mS RS (s_tilde r)) +
          (2 ^ 10 : ℝ) * (∑ r : Fin K_tot, w_tilde r * agentQuadPotential mB RB (b_tilde r)) =
          ∑ r : Fin K_tot, w_tilde r * ((2 ^ 10 : ℝ) * Phi0 (s_tilde r) (b_tilde r)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        dsimp [Phi0, tradeQuadPotential]
        ring
      have h_bayes_tot :
          ∑ r : Fin K_tot, w_tilde r *
            (baseCost (s_tilde r) (b_tilde r) - (2 ^ 10 : ℝ) * Phi0 (s_tilde r) (b_tilde r)) ≤
            2048 * (d : ℝ) * τ := by
        have h_sub : ∑ r : Fin K_tot, w_tilde r *
            (baseCost (s_tilde r) (b_tilde r) - (2 ^ 10 : ℝ) * Phi0 (s_tilde r) (b_tilde r)) =
            (∑ r : Fin K_tot, w_tilde r * baseCost (s_tilde r) (b_tilde r)) -
            (∑ r : Fin K_tot, w_tilde r * ((2 ^ 10 : ℝ) * Phi0 (s_tilde r) (b_tilde r))) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun r _ => by ring)
        rw [h_sub, h_split_univ, h_sum_Ec, h_sum_E, ← h_prior_sum]
        have h1024 : (2 ^ 10 : ℝ) = 1024 := by norm_num
        rw [h1024]
        linarith [h_toi_E, hS_tang, hB_tang]
      obtain ⟨L, hL_nn, hL_sum, hL_grid, hL_cost, hL_lip⟩ :=
        lem_discrete_jitter_plan_approx x hx0 hx ε hε0 hε1 τ hτ0 hτ1 M hM_pos gridDenom hGrid_pos
          hGridStep pa mS0 mB0 mS1 mB1 hmS0 hmB0 hmS1 hmB1 RS0 RB0 RS1 RB1
          hRS0_pd hRB0_pd hRS1_pd hRB1_pd hRS0_tr hRB0_tr hRS1_tr hRB1_tr
          hRS0_inv hRB0_inv hRS1_inv hRB1_inv
      have hL_valid : ValidBasePred L :=
        ⟨hL_nn, hL_sum, hL_grid, hL_lip δ hδ0 hδ1 hδ_step⟩
      refine ⟨⟨L, hL_valid⟩, ?_⟩
      have h_net_pt : ∀ i : Fin N,
          F ⟨L, hL_valid⟩ i ≤
            4 * B_max / (2 * (M : ℝ) + 1) +
            ∑ k : Fin K_jit, (K_jit : ℝ)⁻¹ *
              (c⁻¹ * baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
                (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2) := by
        intro i
        have hc_i := hL_cost (net i).1 (net i).2 (hnet_ball i).1 (hnet_ball i).2
        have h_rhs_eq :
            c⁻¹ * (2 * (M : ℝ) + 1)⁻¹ * ∑ k : Fin K_jit,
              baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
            (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2 =
            ∑ k : Fin K_jit, (K_jit : ℝ)⁻¹ *
              (c⁻¹ * baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
                (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2) := by
          have h_const_sum : ∑ _k : Fin K_jit, (K_jit : ℝ)⁻¹ *
              ((2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2) =
              (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp [ne_of_gt hKjit_pos]
          have h_mul_in : c⁻¹ * (K_jit : ℝ)⁻¹ * ∑ k : Fin K_jit,
              baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) =
              ∑ k : Fin K_jit, (K_jit : ℝ)⁻¹ *
                (c⁻¹ * baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k)))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => by ring)
          calc c⁻¹ * (2 * (M : ℝ) + 1)⁻¹ * ∑ k : Fin K_jit,
                baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
              (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2
              = c⁻¹ * (K_jit : ℝ)⁻¹ * ∑ k : Fin K_jit,
                  baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
                ∑ _k : Fin K_jit, (K_jit : ℝ)⁻¹ *
                  ((2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2) := by
                  rw [← hKjit_eq, h_const_sum]
            _ = ∑ k : Fin K_jit, (K_jit : ℝ)⁻¹ *
                  (c⁻¹ * baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k)))) -
                ∑ _k : Fin K_jit, (K_jit : ℝ)⁻¹ *
                  ((2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2) := by
                  rw [h_mul_in]
            _ = ∑ k : Fin K_jit, (K_jit : ℝ)⁻¹ *
                  (c⁻¹ * baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
                    (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2) := by
                  rw [← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl (fun k _ => by ring)
        have hc_i' : evalLot L (net i).1 (net i).2 ≤
            4 * B_max / (2 * (M : ℝ) + 1) +
            c⁻¹ * (2 * (M : ℝ) + 1)⁻¹ * ∑ k : Fin K_jit,
              baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) := by
          simpa only [evalLot, baseCost, s_tilde, b_tilde, u_fn, Equiv.symm_apply_apply] using hc_i
        dsimp [F]
        linarith
      have h_lam_F : ∑ i : Fin N, lam i * F ⟨L, hL_valid⟩ i ≤
          4 * B_max / (2 * (M : ℝ) + 1) +
          ∑ r : Fin K_tot, w_tilde r *
            (c⁻¹ * baseCost (s_tilde r) (b_tilde r) -
              (2 ^ 10 : ℝ) * Phi0 (net (e.symm r).1).1 (net (e.symm r).1).2) := by
        have h_step1 : ∑ i : Fin N, lam i * F ⟨L, hL_valid⟩ i ≤
            ∑ i : Fin N, lam i * (4 * B_max / (2 * (M : ℝ) + 1) +
              ∑ k : Fin K_jit, (K_jit : ℝ)⁻¹ *
                (c⁻¹ * baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
                  (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2)) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h_net_pt i) (hlam_nn i))
        have h_step2 : ∑ i : Fin N, lam i * (4 * B_max / (2 * (M : ℝ) + 1) +
              ∑ k : Fin K_jit, (K_jit : ℝ)⁻¹ *
                (c⁻¹ * baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
                  (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2)) =
            4 * B_max / (2 * (M : ℝ) + 1) +
            ∑ r : Fin K_tot, w_tilde r *
              (c⁻¹ * baseCost (s_tilde r) (b_tilde r) -
                (2 ^ 10 : ℝ) * Phi0 (net (e.symm r).1).1 (net (e.symm r).1).2) := by
          rw [← Equiv.sum_comp e]
          simp only [w_tilde, Equiv.symm_apply_apply]
          rw [Fintype.sum_prod_type]
          have h_split : ∑ i : Fin N, lam i * (4 * B_max / (2 * (M : ℝ) + 1) +
                ∑ k : Fin K_jit, (K_jit : ℝ)⁻¹ *
                  (c⁻¹ * baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
                    (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2)) =
              (∑ i : Fin N, lam i * (4 * B_max / (2 * (M : ℝ) + 1))) +
              ∑ i : Fin N, lam i * ∑ k : Fin K_jit, (K_jit : ℝ)⁻¹ *
                (c⁻¹ * baseCost (s_tilde (e (i, k))) (b_tilde (e (i, k))) -
                  (2 ^ 10 : ℝ) * Phi0 (net i).1 (net i).2) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => by ring)
          rw [h_split, ← Finset.sum_mul, hlam_sum, one_mul]
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => by ring)
        linarith
      have h_decomp_r :
          ∑ r : Fin K_tot, w_tilde r *
            (c⁻¹ * baseCost (s_tilde r) (b_tilde r) -
              (2 ^ 10 : ℝ) * Phi0 (net (e.symm r).1).1 (net (e.symm r).1).2) ≤
          c⁻¹ * (2048 * (d : ℝ) * τ) + C0 * ε := by
        have h_pt : ∀ r : Fin K_tot,
            w_tilde r * (c⁻¹ * baseCost (s_tilde r) (b_tilde r) -
              (2 ^ 10 : ℝ) * Phi0 (net (e.symm r).1).1 (net (e.symm r).1).2) ≤
            c⁻¹ * (w_tilde r * (baseCost (s_tilde r) (b_tilde r) -
              (2 ^ 10 : ℝ) * Phi0 (s_tilde r) (b_tilde r))) +
            w_tilde r * (C0 * ε) := by
          intro r
          have hdr : |(2 ^ 10 : ℝ) * (c⁻¹ * Phi0 (s_tilde r) (b_tilde r) -
              Phi0 (net (e.symm r).1).1 (net (e.symm r).1).2)| ≤ C0 * ε :=
            h_drift ε (u_fn (e.symm r).2) hε0 hε1 (hu_bound _)
              (net (e.symm r).1).1 (net (e.symm r).1).2
              (hnet_ball _).1 (hnet_ball _).2
          have hdr' : (2 ^ 10 : ℝ) * (c⁻¹ * Phi0 (s_tilde r) (b_tilde r) -
              Phi0 (net (e.symm r).1).1 (net (e.symm r).1).2) ≤ C0 * ε :=
            le_trans (le_abs_self _) hdr
          have h_id : w_tilde r * (c⁻¹ * baseCost (s_tilde r) (b_tilde r) -
              (2 ^ 10 : ℝ) * Phi0 (net (e.symm r).1).1 (net (e.symm r).1).2) =
              c⁻¹ * (w_tilde r * (baseCost (s_tilde r) (b_tilde r) -
                (2 ^ 10 : ℝ) * Phi0 (s_tilde r) (b_tilde r))) +
              w_tilde r * ((2 ^ 10 : ℝ) * (c⁻¹ * Phi0 (s_tilde r) (b_tilde r) -
                Phi0 (net (e.symm r).1).1 (net (e.symm r).1).2)) := by ring
          have h_w_mul := mul_le_mul_of_nonneg_left hdr' (hw_tilde_nn r)
          linarith
        calc ∑ r : Fin K_tot, w_tilde r *
              (c⁻¹ * baseCost (s_tilde r) (b_tilde r) -
                (2 ^ 10 : ℝ) * Phi0 (net (e.symm r).1).1 (net (e.symm r).1).2)
            ≤ ∑ r : Fin K_tot, (c⁻¹ * (w_tilde r * (baseCost (s_tilde r) (b_tilde r) -
                (2 ^ 10 : ℝ) * Phi0 (s_tilde r) (b_tilde r))) +
                w_tilde r * (C0 * ε)) := Finset.sum_le_sum (fun r _ => h_pt r)
          _ = c⁻¹ * (∑ r : Fin K_tot, w_tilde r * (baseCost (s_tilde r) (b_tilde r) -
                (2 ^ 10 : ℝ) * Phi0 (s_tilde r) (b_tilde r))) +
              (∑ r : Fin K_tot, w_tilde r) * (C0 * ε) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
          _ ≤ c⁻¹ * (2048 * (d : ℝ) * τ) + C0 * ε := by
              rw [hw_tilde_sum, one_mul]
              have h_c_mul := mul_le_mul_of_nonneg_left h_bayes_tot (inv_nonneg.mpr (le_of_lt hc_pos))
              linarith
      linarith [h_lam_F, h_decomp_r, hM_bound4, hτ_bound, hε_C0, hγ0]
    obtain ⟨mix, hmix_nn, hmix_sum, hmix_lt⟩ :=
      lem_fintype_minimax_separation hN_pos F (γ / 2) h_resp
    let lottery : List (ℝ × TradePlan d) :=
      mix.flatMap (fun wa => wa.2.1.map (fun wp => (wa.1 * wp.1, wp.2)))
    have h_flat_eval : ∀ (g : TradePlan d → ℝ) (l : List (ℝ × ValidBase)),
        ((l.flatMap (fun wa => wa.2.1.map (fun wp => (wa.1 * wp.1, wp.2)))).map
          (fun wp => wp.1 * g wp.2)).sum =
        (l.map (fun wa => wa.1 * (wa.2.1.map (fun wp => wp.1 * g wp.2)).sum)).sum := by
      intro g l
      induction l with
      | nil => simp
      | cons hd tl ih =>
        rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]
        congr 1
        rw [List.map_map]
        have h_inner : List.map ((fun wp : ℝ × TradePlan d => wp.1 * g wp.2) ∘
            (fun wp : ℝ × TradePlan d => (hd.1 * wp.1, wp.2))) hd.2.1 =
            List.map (fun wp : ℝ × TradePlan d => hd.1 * (wp.1 * g wp.2)) hd.2.1 := by
          refine List.map_congr_left (fun wp _ => ?_)
          simp [Function.comp, mul_assoc]
        rw [h_inner, List.sum_map_mul_left]
    refine ⟨lottery, gridDenom, hGrid_pos, ?_, ?_, ?_, ?_⟩
    · intro wp hwp
      rcases List.mem_flatMap.mp hwp with ⟨wa, hwa_mem, hwp_map⟩
      rcases List.mem_map.mp hwp_map with ⟨wp', hwp'_mem, rfl⟩
      exact mul_nonneg (hmix_nn wa hwa_mem) (wa.2.2.1 wp' hwp'_mem)
    · have h1 := h_flat_eval (fun _ => 1) mix
      have h_lhs : (lottery.map Prod.fst).sum =
          (lottery.map (fun wp => wp.1 * (1 : ℝ))).sum := by
        simp [mul_one]
      have h_rhs : (mix.map (fun wa : ℝ × ValidBase =>
          wa.1 * (wa.2.1.map (fun wp => wp.1 * (1 : ℝ))).sum)).sum =
          (mix.map Prod.fst).sum := by
        have h_congr : List.map (fun wa : ℝ × ValidBase =>
            wa.1 * (wa.2.1.map (fun wp => wp.1 * (1 : ℝ))).sum) mix =
            List.map Prod.fst mix := by
          refine List.map_congr_left (fun wa _ => ?_)
          have h_wa_sum : (wa.2.1.map (fun wp => wp.1 * (1 : ℝ))).sum = 1 := by
            simpa [mul_one] using wa.2.2.2.1
          rw [h_wa_sum, mul_one]
        rw [h_congr]
      rw [h_lhs, h1, h_rhs, hmix_sum]
    · intro wp hwp
      rcases List.mem_flatMap.mp hwp with ⟨wa, _, hwp_map⟩
      rcases List.mem_map.mp hwp_map with ⟨wp', hwp'_mem, rfl⟩
      exact wa.2.2.2.2.1 wp' hwp'_mem
    · intro s b hs hb
      obtain ⟨i, hs_i, hb_i⟩ := hnet_cover s b hs hb
      have h_lot_eq : (lottery.map (fun wp => wp.1 * planRoundCost x wp.2 s b)).sum =
          (mix.map (fun wa => wa.1 * evalLot wa.2.1 s b)).sum :=
        h_flat_eval (fun p => planRoundCost x p s b) mix
      have h_pt_bound : ∀ wa ∈ mix,
          evalLot wa.2.1 s b - (2 ^ 10 : ℝ) * Phi0 s b ≤ F wa.2 i + 5 * γ / 12 := by
        intro wa _
        have h_lot_lip : |evalLot wa.2.1 s b - evalLot wa.2.1 (net i).1 (net i).2| ≤
            12 * B_max / (2 * (M : ℝ) + 1) + (2 + 16384 * τ⁻¹) * δ :=
          wa.2.2.2.2.2 s b (net i).1 (net i).2 hs hb (hnet_ball i).1 (hnet_ball i).2 hs_i hb_i
        have h_lot_lip' : evalLot wa.2.1 s b - evalLot wa.2.1 (net i).1 (net i).2 ≤
            12 * B_max / (2 * (M : ℝ) + 1) + (2 + 16384 * τ⁻¹) * δ :=
          le_trans (le_abs_self _) h_lot_lip
        have h_phi_lip : |(2 ^ 10 : ℝ) * (Phi0 s b - Phi0 (net i).1 (net i).2)| ≤ L0 * δ :=
          h_pot_lip δ hδ0 s b (net i).1 (net i).2 hs hb (hnet_ball i).1 (hnet_ball i).2 hs_i hb_i
        have h_phi_lip' : (2 ^ 10 : ℝ) * (Phi0 (net i).1 (net i).2 - Phi0 s b) ≤ L0 * δ := by
          have h_neg : (2 ^ 10 : ℝ) * (Phi0 (net i).1 (net i).2 - Phi0 s b) =
              -((2 ^ 10 : ℝ) * (Phi0 s b - Phi0 (net i).1 (net i).2)) := by ring
          rw [h_neg]
          exact le_trans (neg_le_abs _) h_phi_lip
        dsimp [F, L_lip] at *
        linarith [hM_bound12, hδ_lip]
      have h_list_mono : ∀ (l : List (ℝ × ValidBase)),
          (∀ wa ∈ l, 0 ≤ wa.1) →
          (∀ wa ∈ l, evalLot wa.2.1 s b - (2 ^ 10 : ℝ) * Phi0 s b ≤ F wa.2 i + 5 * γ / 12) →
          (l.map (fun wa => wa.1 * evalLot wa.2.1 s b)).sum -
            (l.map Prod.fst).sum * ((2 ^ 10 : ℝ) * Phi0 s b) ≤
          (l.map (fun wa => wa.1 * F wa.2 i)).sum +
            (l.map Prod.fst).sum * (5 * γ / 12) := by
        intro l
        induction l with
        | nil => intro _ _; simp
        | cons hd tl ih =>
          intro hnn hbd
          simp only [List.map_cons, List.sum_cons]
          have h_hd_nn : 0 ≤ hd.1 := hnn hd List.mem_cons_self
          have h_hd_bd := hbd hd List.mem_cons_self
          have h_hd_mul : hd.1 * (evalLot hd.2.1 s b - (2 ^ 10 : ℝ) * Phi0 s b) ≤
              hd.1 * (F hd.2 i + 5 * γ / 12) :=
            mul_le_mul_of_nonneg_left h_hd_bd h_hd_nn
          have h_tl := ih (fun wa hwa => hnn wa (List.mem_cons_of_mem _ hwa))
            (fun wa hwa => hbd wa (List.mem_cons_of_mem _ hwa))
          linarith
      have h_comb := h_list_mono mix hmix_nn h_pt_bound
      rw [hmix_sum, one_mul, one_mul] at h_comb
      rw [h_lot_eq]
      linarith [h_comb, hmix_lt i, hγ0]

end TraceSqrt
