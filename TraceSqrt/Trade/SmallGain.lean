import TraceSqrt.Defs
import TraceSqrt.Trade.TradeProfile

set_option maxHeartbeats 4000000

/-!
# Equations (38)–(39): Area Bound under `H` and Small Gain or Large Information

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Appendix D.1, Equations `eq:trade-area` (38) and `eq:trade-small-gain` (39)).
-/

namespace TraceSqrt

/-- **Equations (38)–(39) (`eq:trade-area` and `eq:trade-small-gain`)**:
For every square-integrable pair `(S, B)` on a probability space `(Ω, μ)`:
1. Both `α = tradeProfile S B μ` and its piecewise upper envelope `H = tradeProfileEnvelope S B μ`
   are Lebesgue integrable on `ℝ`,
2. `G = ∫ α(p) dp ≤ ∫ H(p) dp ≤ 162 D̄ + max ((μ_B - μ_S) - (σ_S + σ_B) / 3) 0` (Eq. (38)), and
3. `min(G, (σ_S + σ_B) / 3) ≤ 162 D̄` (Eq. (39)). -/
theorem lem_trade_small_gain {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (S B : Ω → ℝ) (hS : MeasureTheory.MemLp S 2 μ) (hB : MeasureTheory.MemLp B 2 μ) :
    let muS := ∫ ω, S ω ∂μ
    let muB := ∫ ω, B ω ∂μ
    let sigS := rvStdDev S μ
    let sigB := rvStdDev B μ
    let Dbar := supInfoDrop S B μ
    MeasureTheory.Integrable (tradeProfile S B μ) MeasureTheory.volume ∧
    MeasureTheory.Integrable (tradeProfileEnvelope S B μ) MeasureTheory.volume ∧
    (∫ p : ℝ, tradeProfile S B μ p) = availableGain S B μ ∧
    availableGain S B μ ≤ ∫ p : ℝ, tradeProfileEnvelope S B μ p ∧
    (∫ p : ℝ, tradeProfileEnvelope S B μ p) ≤
      162 * Dbar + max ((muB - muS) - (sigS + sigB) / 3) 0 ∧
    min (availableGain S B μ) ((sigS + sigB) / 3) ≤ 162 * Dbar :=
by
  dsimp only
  set muS : ℝ := ∫ ω, S ω ∂μ
  set muB : ℝ := ∫ ω, B ω ∂μ
  set sigS : ℝ := rvStdDev S μ
  set sigB : ℝ := rvStdDev B μ
  set Dbar : ℝ := supInfoDrop S B μ
  set α : ℝ → ℝ := tradeProfile S B μ
  set H : ℝ → ℝ := tradeProfileEnvelope S B μ
  set G : ℝ := availableGain S B μ
  set σ : ℝ := sigS + sigB

  have hS_int : MeasureTheory.Integrable S μ := hS.integrable one_le_two
  have hB_int : MeasureTheory.Integrable B μ := hB.integrable one_le_two
  obtain ⟨hα_int, hα_area⟩ :=
    (claim_gain_decomposition μ S B hS.aemeasurable hB.aemeasurable).2 hS_int hB_int

  have hsigS_nn : 0 ≤ sigS := Real.sqrt_nonneg _
  have hsigB_nn : 0 ≤ sigB := Real.sqrt_nonneg _
  have hDbar_nn : 0 ≤ Dbar := by
    have h0 : 0 ≤ totalInfoDrop S B μ 0 := (claim_D_nonneg μ S B hS hB 0).2.2
    have h_bdd : BddAbove (Set.range (totalInfoDrop S B μ)) := by
      refine ⟨sigS + sigB, ?_⟩
      rintro _ ⟨q, rfl⟩
      have hSq : 0 ≤ μ.real (tradeEvent S B q) * condStdDev S μ (tradeEvent S B q) +
          μ.real (tradeEvent S B q)ᶜ * condStdDev S μ (tradeEvent S B q)ᶜ :=
        add_nonneg (mul_nonneg MeasureTheory.measureReal_nonneg (Real.sqrt_nonneg _))
          (mul_nonneg MeasureTheory.measureReal_nonneg (Real.sqrt_nonneg _))
      have hBq : 0 ≤ μ.real (tradeEvent S B q) * condStdDev B μ (tradeEvent S B q) +
          μ.real (tradeEvent S B q)ᶜ * condStdDev B μ (tradeEvent S B q)ᶜ :=
        add_nonneg (mul_nonneg MeasureTheory.measureReal_nonneg (Real.sqrt_nonneg _))
          (mul_nonneg MeasureTheory.measureReal_nonneg (Real.sqrt_nonneg _))
      change agentInfoDrop S S B μ q + agentInfoDrop B S B μ q ≤ sigS + sigB
      dsimp only [agentInfoDrop, sigS, sigB] at *
      linarith
    exact le_trans h0 (le_csSup h_bdd ⟨0, rfl⟩)

  set a1 : ℝ := muS - sigS / 3
  set a2 : ℝ := muS + sigS / 3
  set b1 : ℝ := muB - sigB / 3
  set b2 : ℝ := muB + sigB / 3
  set cS : ℝ := if sigS = 0 then (1 : ℝ) else (225 * Dbar) / (2 * sigS)
  set cB : ℝ := if sigB = 0 then (1 : ℝ) else (225 * Dbar) / (2 * sigB)

  have hcS_nn : 0 ≤ cS := by
    dsimp [cS]; split_ifs <;> positivity
  have hcB_nn : 0 ≤ cB := by
    dsimp [cB]; split_ifs <;> positivity

  let H1 : ℝ → ℝ := (Set.Iio a1).indicator (fun p => (2 * sigS * Dbar) / (muS - p) ^ 2)
  let H2 : ℝ → ℝ := (Set.Icc a1 a2).indicator (fun _ => cS)
  let H3 : ℝ → ℝ := (Set.Ioo a2 b1).indicator (fun _ => (1 : ℝ))
  let H4 : ℝ → ℝ := (Set.Icc b1 b2).indicator (fun _ => cB)
  let H5 : ℝ → ℝ := (Set.Ioi b2).indicator (fun p => (2 * sigB * Dbar) / (p - muB) ^ 2)

  have hH1_nn : ∀ p : ℝ, 0 ≤ H1 p :=
    fun p => Set.indicator_nonneg (fun _ _ => by positivity) p
  have hH2_nn : ∀ p : ℝ, 0 ≤ H2 p :=
    fun p => Set.indicator_nonneg (fun _ _ => hcS_nn) p
  have hH3_nn : ∀ p : ℝ, 0 ≤ H3 p :=
    fun p => Set.indicator_nonneg (fun _ _ => zero_le_one) p
  have hH4_nn : ∀ p : ℝ, 0 ≤ H4 p :=
    fun p => Set.indicator_nonneg (fun _ _ => hcB_nn) p
  have hH5_nn : ∀ p : ℝ, 0 ≤ H5 p :=
    fun p => Set.indicator_nonneg (fun _ _ => by positivity) p

  have hH_nn : ∀ p : ℝ, 0 ≤ H p := by
    intro p
    exact le_trans (MeasureTheory.measureReal_nonneg) (claim_trade_profile μ S B hS hB p)

  have hH_meas : Measurable H := by
    have hm_tS : Measurable (fun p : ℝ => (2 * sigS * Dbar) / (muS - p) ^ 2) :=
      measurable_const.div ((measurable_const.sub measurable_id).pow_const 2)
    have hm_tB : Measurable (fun p : ℝ => (2 * sigB * Dbar) / (p - muB) ^ 2) :=
      measurable_const.div ((measurable_id.sub measurable_const).pow_const 2)
    have h_eq : H = fun p : ℝ =>
        if p ∈ Set.Iio a1 then (2 * sigS * Dbar) / (muS - p) ^ 2
        else if p ∈ Set.Iic a2 then cS
        else if p ∈ Set.Iio b1 then (1 : ℝ)
        else if p ∈ Set.Iic b2 then cB
        else (2 * sigB * Dbar) / (p - muB) ^ 2 := by
      ext p
      simp only [H, tradeProfileEnvelope, muS, muB, sigS, sigB, Dbar, a1, a2, b1, b2, cS, cB,
        Set.mem_Iio, Set.mem_Iic]
    rw [h_eq]
    exact Measurable.ite measurableSet_Iio hm_tS
      (Measurable.ite measurableSet_Iic measurable_const
        (Measurable.ite measurableSet_Iio measurable_const
          (Measurable.ite measurableSet_Iic measurable_const hm_tB)))

  have hH_dom : ∀ p : ℝ, H p ≤ H1 p + H2 p + H3 p + H4 p + H5 p := by
    intro p
    have h1 := hH1_nn p
    have h2 := hH2_nn p
    have h3 := hH3_nn p
    have h4 := hH4_nn p
    have h5 := hH5_nn p
    change (if p < a1 then (2 * sigS * Dbar) / (muS - p) ^ 2
      else if p ≤ a2 then cS
      else if p < b1 then (1 : ℝ)
      else if p ≤ b2 then cB
      else (2 * sigB * Dbar) / (p - muB) ^ 2) ≤ H1 p + H2 p + H3 p + H4 p + H5 p
    split_ifs with hp1 hp2 hp3 hp4
    · have : H1 p = (2 * sigS * Dbar) / (muS - p) ^ 2 :=
        Set.indicator_of_mem (show p ∈ Set.Iio a1 from hp1) _
      linarith
    · have hp_mem : p ∈ Set.Icc a1 a2 := ⟨not_lt.mp hp1, hp2⟩
      have : H2 p = cS := Set.indicator_of_mem hp_mem _
      linarith
    · have hp_mem : p ∈ Set.Ioo a2 b1 := ⟨not_le.mp hp2, hp3⟩
      have : H3 p = 1 := Set.indicator_of_mem hp_mem _
      linarith
    · have hp_mem : p ∈ Set.Icc b1 b2 := ⟨not_lt.mp hp3, hp4⟩
      have : H4 p = cB := Set.indicator_of_mem hp_mem _
      linarith
    · have hp_mem : p ∈ Set.Ioi b2 := not_le.mp hp4
      have : H5 p = (2 * sigB * Dbar) / (p - muB) ^ 2 := Set.indicator_of_mem hp_mem _
      linarith

  -- Integrability and integral bound for right-tail template `x > m + s / 3`
  have h_right_tail : ∀ (m s : ℝ), 0 ≤ s →
      MeasureTheory.IntegrableOn (fun p : ℝ => (2 * s * Dbar) / (p - m) ^ 2)
        (Set.Ioi (m + s / 3)) MeasureTheory.volume ∧
      (∫ p in Set.Ioi (m + s / 3), (2 * s * Dbar) / (p - m) ^ 2) ≤ 6 * Dbar := by
    intro m s hs_nn
    rcases eq_or_lt_of_le hs_nn with hs0 | hs_pos
    · subst hs0
      have h_zero : (fun p : ℝ => (2 * (0 : ℝ) * Dbar) / (p - m) ^ 2) = 0 := by
        ext p; simp
      rw [h_zero]
      exact ⟨MeasureTheory.integrableOn_zero, by simp [hDbar_nn]⟩
    · set c : ℝ := m + s / 3
      let g : ℝ → ℝ := fun x => -(x - m)⁻¹
      let g' : ℝ → ℝ := fun x => ((x - m) ^ 2)⁻¹
      have h_deriv : ∀ x ∈ Set.Ici c, HasDerivAt g (g' x) x := by
        intro x hx
        have hpos : 0 < x - m := by
          have hcx : c ≤ x := hx
          dsimp [c] at hcx; linarith
        have hd_lin : HasDerivAt (fun y : ℝ => y - m) 1 x := by
          simpa using (hasDerivAt_id x).sub_const m
        have hd_inv : HasDerivAt (fun y : ℝ => (y - m)⁻¹) (-1 / (x - m) ^ 2) x :=
          hd_lin.inv hpos.ne'
        convert hd_inv.neg using 1
        ring
      have h_g'_nn : ∀ x ∈ Set.Ioi c, 0 ≤ g' x := fun x _ => by dsimp [g']; positivity
      have h_tendsto : Filter.Tendsto g Filter.atTop (nhds 0) := by
        have ht1 : Filter.Tendsto (fun x : ℝ => x - m) Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_add_const_right Filter.atTop (-m) Filter.tendsto_id
        have ht2 : Filter.Tendsto (fun x : ℝ => (x - m)⁻¹) Filter.atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp ht1
        simpa using ht2.neg
      have h_g'_int : MeasureTheory.IntegrableOn g' (Set.Ioi c) MeasureTheory.volume :=
        MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' h_deriv h_g'_nn h_tendsto
      have h_g'_val : (∫ x in Set.Ioi c, g' x) = 3 / s := by
        have h_cont : ContinuousWithinAt g (Set.Ici c) c :=
          (h_deriv c Set.self_mem_Ici).continuousAt.continuousWithinAt
        have h_int := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg h_cont
          (fun x hx => h_deriv x (Set.Ioi_subset_Ici_self hx)) h_g'_nn h_tendsto
        rw [h_int]
        have h_diff : c - m = s / 3 := by dsimp [c]; ring
        dsimp [g]
        rw [h_diff]
        have hs_ne : s ≠ 0 := hs_pos.ne'
        field_simp
        ring
      have h_fn_eq : (fun p : ℝ => (2 * s * Dbar) / (p - m) ^ 2) =
          fun p : ℝ => (2 * s * Dbar) * g' p := by
        ext p; dsimp [g']; rw [div_eq_mul_inv]
      rw [h_fn_eq]
      refine ⟨h_g'_int.const_mul (2 * s * Dbar), ?_⟩
      rw [MeasureTheory.integral_const_mul, h_g'_val]
      have hs_ne : s ≠ 0 := hs_pos.ne'
      have h_prod : (2 * s * Dbar) * (3 / s) = 6 * Dbar := by field_simp; ring
      linarith

  obtain ⟨hH5_intOn, hH5_valOn⟩ := h_right_tail muB sigB hsigB_nn
  have hH5_int : MeasureTheory.Integrable H5 MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).mpr hH5_intOn
  have hH5_val : (∫ p, H5 p) ≤ 6 * Dbar := by
    dsimp [H5]
    rw [MeasureTheory.integral_indicator measurableSet_Ioi]
    exact hH5_valOn

  obtain ⟨hH1_neg_intOn, hH1_neg_valOn⟩ := h_right_tail (-muS) sigS hsigS_nn
  have h_neg_a1 : -muS + sigS / 3 = -a1 := by dsimp [a1]; ring
  rw [h_neg_a1] at hH1_neg_intOn hH1_neg_valOn
  have hH1_intOn : MeasureTheory.IntegrableOn
      (fun p : ℝ => (2 * sigS * Dbar) / (muS - p) ^ 2) (Set.Iio a1) MeasureTheory.volume := by
    have h_ic := (hH1_neg_intOn.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm).comp_neg_Iic
    have h_io := h_ic.congr_set_ae MeasureTheory.Iio_ae_eq_Iic
    have h_fn : (fun p : ℝ => (2 * sigS * Dbar) / (-p - -muS) ^ 2) =
        fun p : ℝ => (2 * sigS * Dbar) / (muS - p) ^ 2 := by
      ext p; congr 1; ring
    rwa [h_fn] at h_io
  have hH1_int : MeasureTheory.Integrable H1 MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Iio).mpr hH1_intOn
  have hH1_val : (∫ p, H1 p) ≤ 6 * Dbar := by
    have h_eq : H1 = fun p => (Set.Ioi (-a1)).indicator
        (fun q => (2 * sigS * Dbar) / (q - -muS) ^ 2) (-p) := by
      ext p
      by_cases hp : p < a1
      · have hnp : -a1 < -p := by linarith
        simp [H1, Set.indicator, hp, hnp]
        ring
      · have hnp : ¬ (-a1 < -p) := by linarith
        simp [H1, Set.indicator, hp, hnp]
    rw [h_eq, MeasureTheory.integral_neg_eq_self,
        MeasureTheory.integral_indicator measurableSet_Ioi]
    exact hH1_neg_valOn

  have hH2_int : MeasureTheory.Integrable H2 MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hH2_val : (∫ p, H2 p) ≤ 75 * Dbar := by
    dsimp [H2]
    rw [MeasureTheory.integral_indicator_const cS measurableSet_Icc, smul_eq_mul,
        Real.volume_real_Icc_of_le (by dsimp [a1, a2]; linarith)]
    rcases eq_or_lt_of_le hsigS_nn with hsig0 | hsig_pos
    · have ha_eq : a2 - a1 = 0 := by dsimp [a1, a2]; rw [← hsig0]; ring
      rw [ha_eq, zero_mul]
      positivity
    · have hcS_eq : cS = (225 * Dbar) / (2 * sigS) := if_neg hsig_pos.ne'
      rw [hcS_eq]
      have h_prod : (a2 - a1) * ((225 * Dbar) / (2 * sigS)) = 75 * Dbar := by
        dsimp [a1, a2]
        have hne : sigS ≠ 0 := hsig_pos.ne'
        field_simp
        ring
      linarith

  have hH3_int : MeasureTheory.Integrable H3 MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mpr
      (MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
  have hH3_val : (∫ p, H3 p) = max ((muB - muS) - (sigS + sigB) / 3) 0 := by
    dsimp [H3]
    rw [MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Ioo,
        smul_eq_mul, mul_one, Real.volume_real_Ioo]
    congr 1
    dsimp [a2, b1]
    ring

  have hH4_int : MeasureTheory.Integrable H4 MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hH4_val : (∫ p, H4 p) ≤ 75 * Dbar := by
    dsimp [H4]
    rw [MeasureTheory.integral_indicator_const cB measurableSet_Icc, smul_eq_mul,
        Real.volume_real_Icc_of_le (by dsimp [b1, b2]; linarith)]
    rcases eq_or_lt_of_le hsigB_nn with hsig0 | hsig_pos
    · have hb_eq : b2 - b1 = 0 := by dsimp [b1, b2]; rw [← hsig0]; ring
      rw [hb_eq, zero_mul]
      positivity
    · have hcB_eq : cB = (225 * Dbar) / (2 * sigB) := if_neg hsig_pos.ne'
      rw [hcB_eq]
      have h_prod : (b2 - b1) * ((225 * Dbar) / (2 * sigB)) = 75 * Dbar := by
        dsimp [b1, b2]
        have hne : sigB ≠ 0 := hsig_pos.ne'
        field_simp
        ring
      linarith

  let Hsum : ℝ → ℝ := fun p => H1 p + H2 p + H3 p + H4 p + H5 p
  have hHsum_int : MeasureTheory.Integrable Hsum MeasureTheory.volume :=
    (((hH1_int.add hH2_int).add hH3_int).add hH4_int).add hH5_int

  have hH_int : MeasureTheory.Integrable H MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono' hHsum_int hH_meas.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (hH_nn p)]
    exact hH_dom p

  have hG_le_H : G ≤ ∫ p, H p := by
    dsimp [G]
    rw [← hα_area]
    exact MeasureTheory.integral_mono hα_int hH_int (claim_trade_profile μ S B hS hB)

  have hH_le_area : (∫ p, H p) ≤ 162 * Dbar + max ((muB - muS) - (sigS + sigB) / 3) 0 := by
    have h_mono : (∫ p, H p) ≤ ∫ p, Hsum p :=
      MeasureTheory.integral_mono hH_int hHsum_int hH_dom
    have h_sum_int : (∫ p, Hsum p) =
        (∫ p, H1 p) + (∫ p, H2 p) + (∫ p, H3 p) + (∫ p, H4 p) + (∫ p, H5 p) := by
      have h1234 := ((hH1_int.add hH2_int).add hH3_int).add hH4_int
      have h123 := (hH1_int.add hH2_int).add hH3_int
      have h12 := hH1_int.add hH2_int
      have eq12345 : (∫ p, Hsum p) =
          (∫ p, (H1 p + H2 p + H3 p + H4 p)) + ∫ p, H5 p :=
        MeasureTheory.integral_add (f := fun p => H1 p + H2 p + H3 p + H4 p) h1234 hH5_int
      have eq1234 : (∫ p, (H1 p + H2 p + H3 p + H4 p)) =
          (∫ p, (H1 p + H2 p + H3 p)) + ∫ p, H4 p :=
        MeasureTheory.integral_add (f := fun p => H1 p + H2 p + H3 p) h123 hH4_int
      have eq123 : (∫ p, (H1 p + H2 p + H3 p)) =
          (∫ p, (H1 p + H2 p)) + ∫ p, H3 p :=
        MeasureTheory.integral_add (f := fun p => H1 p + H2 p) h12 hH3_int
      have eq12 : (∫ p, (H1 p + H2 p)) = (∫ p, H1 p) + ∫ p, H2 p :=
        MeasureTheory.integral_add hH1_int hH2_int
      linarith [eq12345, eq1234, eq123, eq12]
    rw [h_sum_int, hH3_val] at h_mono
    linarith [hH1_val, hH2_val, hH4_val, hH5_val]

  have h_mean_gap : muB - muS ≤ G := by
    have hBS_int : MeasureTheory.Integrable (fun ω => B ω - S ω) μ := hB_int.sub hS_int
    have hmax_int : MeasureTheory.Integrable (fun ω => max (B ω - S ω) 0) μ :=
      hBS_int.sup (MeasureTheory.integrable_zero Ω ℝ μ)
    dsimp [muS, muB, G, availableGain]
    rw [← MeasureTheory.integral_sub hB_int hS_int]
    exact MeasureTheory.integral_mono hBS_int hmax_int (fun ω => le_max_left _ _)

  have h_max_le : max ((muB - muS) - σ / 3) 0 ≤ max (G - σ / 3) 0 :=
    max_le_max (by linarith) (le_refl 0)

  have hG_le : G ≤ 162 * Dbar + max (G - σ / 3) 0 := by
    dsimp [σ] at h_max_le ⊢
    linarith [hG_le_H, hH_le_area, h_max_le]

  have h_min_le : min G (σ / 3) ≤ 162 * Dbar := by
    by_cases hGσ : G ≤ σ / 3
    · have h_min : min G (σ / 3) = G := min_eq_left hGσ
      have h_max : max (G - σ / 3) 0 = 0 := max_eq_right (by linarith)
      linarith
    · push_neg at hGσ
      have h_min : min G (σ / 3) = σ / 3 := min_eq_right hGσ.le
      have h_max : max (G - σ / 3) 0 = G - σ / 3 := max_eq_left (by linarith)
      linarith

  exact ⟨hα_int, hH_int, hα_area, hG_le_H, hH_le_area, h_min_le⟩

end TraceSqrt
