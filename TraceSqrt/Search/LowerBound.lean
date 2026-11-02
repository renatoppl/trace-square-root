import TraceSqrt.Defs

set_option maxHeartbeats 4000000

/-!
# Proposition E.1: Contextual Search Standard Lower Bound (`prop:lower-bound`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Appendix E, Proposition E.1).
-/

namespace TraceSqrt

/-- **Proposition E.1 (Lower bound for contextual search, `prop:lower-bound`)**:
For every `d ≥ 1`, `T ≥ d`, probability space `(Ω, μ)`, and randomized learner, there exist
deterministic contexts `ctxs` of Euclidean norm at most `1` such that:
1. The uniform Bayesian prior over `{-1/√d, +1/√d}^d` incurs expected loss at least `√d`, and
2. There is a fixed unit-norm target `z` (`‖z‖₂ = 1`) incurring expected loss at least `√d`. -/
theorem prop_search_lower_bound (d T : ℕ) (hd : 0 < d) (hT : d ≤ T)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (learner : SearchLearner d Ω) :
    ∃ ctxs : Fin T → (Fin d → ℝ),
      (∀ t : Fin T, vecL2Norm (ctxs t) ≤ 1) ∧
      ((2 ^ d : ENNReal)⁻¹ *
          ∑ signs : Fin d → Bool,
            ∫⁻ ω, ENNReal.ofReal (searchCumulativeLoss learner (hypercubeTarget signs) T ctxs ω) ∂μ ≥
        ENNReal.ofReal (Real.sqrt d)) ∧
      (∃ z : Fin d → ℝ,
        vecL2Norm z = 1 ∧
        ∫⁻ ω, ENNReal.ofReal (searchCumulativeLoss learner z T ctxs ω) ∂μ ≥
          ENNReal.ofReal (Real.sqrt d)) :=
by
  let stdCtxs : ∀ m : ℕ, Fin m → (Fin d → ℝ) :=
    fun m t j => if j.val = t.val then (1 : ℝ) else 0

  have h_ctx_norm : ∀ t : Fin T, vecL2Norm (stdCtxs T t) ≤ 1 := by
    intro t
    rw [vecL2Norm, Real.sqrt_le_one]
    by_cases ht : t.val < d
    · let i₀ : Fin d := ⟨t.val, ht⟩
      have h_sum_eq : (∑ i : Fin d, (stdCtxs T t i) ^ 2) =
          ∑ i : Fin d, if i = i₀ then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hiff : i.val = t.val ↔ i = i₀ := by simp [Fin.ext_iff, i₀]
        by_cases hi : i = i₀
        · rw [if_pos hi]; simp [stdCtxs, hiff.mpr hi]
        · rw [if_neg hi]; simp [stdCtxs, mt hiff.mp hi]
      rw [h_sum_eq, Finset.sum_ite_eq']
      simp
    · have h_sum_zero : (∑ i : Fin d, (stdCtxs T t i) ^ 2) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have hne : i.val ≠ t.val := by omega
        simp [stdCtxs, hne]
      linarith

  have h_hyp_norm : ∀ signs : Fin d → Bool, vecL2Norm (hypercubeTarget signs) = 1 := by
    intro signs
    rw [vecL2Norm]
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := hd_pos.le
    have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
    have h_sq : ∀ j : Fin d, (hypercubeTarget signs j) ^ 2 = 1 / (d : ℝ) := by
      intro j
      unfold hypercubeTarget
      cases signs j <;> simp [div_pow, Real.sq_sqrt hd_nonneg]
    have h_sum : (∑ j : Fin d, (hypercubeTarget signs j) ^ 2) = 1 := by
      simp [h_sq, Finset.sum_const, nsmul_eq_mul, hd_ne]
    rw [h_sum, Real.sqrt_one]

  let step : (Fin d → ℝ) → Ω → (ℝ × List ((Fin d → ℝ) × ℝ)) → Fin T → (ℝ × List ((Fin d → ℝ) × ℝ)) :=
    fun z ω acc t =>
      let lossSoFar := acc.1
      let hist := acc.2
      let xt := stdCtxs T t
      let pt := learner.postPrice ω hist xt
      let yt := paperSign (dotProduct xt z - pt)
      let ell := |dotProduct xt z - pt|
      (lossSoFar + ell, hist ++ [(xt, yt)])
  have h_loss_nonneg : ∀ (z : Fin d → ℝ) (ω : Ω),
      0 ≤ searchCumulativeLoss learner z T (stdCtxs T) ω := by
    intro z ω
    have h_fold : ∀ (l : List (Fin T)) (a : ℝ) (hist : List ((Fin d → ℝ) × ℝ)),
        0 ≤ a → 0 ≤ (l.foldl (step z ω) (a, hist)).1 := by
      intro l
      induction l with
      | nil =>
        intro a hist ha
        exact ha
      | cons t ts ih =>
        intro a hist ha
        simp only [List.foldl_cons]
        exact ih _ _ (add_nonneg ha (abs_nonneg _))
    exact h_fold (List.finRange T) 0 [] le_rfl
  have h_loss_meas : ∀ (z : Fin d → ℝ),
      Measurable (fun ω => searchCumulativeLoss learner z T (stdCtxs T) ω) := by
    intro z
    have h_fold : ∀ (l : List (Fin T)) (loss₀ : Ω → ℝ) (hist₀ : List ((Fin d → ℝ) × ℝ)),
        Measurable loss₀ →
        Measurable (fun ω => (l.foldl (step z ω) (loss₀ ω, hist₀)).1) := by
      intro l
      induction l with
      | nil =>
        intro loss₀ hist₀ hloss₀
        exact hloss₀
      | cons t ts ih =>
        intro loss₀ hist₀ hloss₀
        let p : Ω → ℝ := fun ω => learner.postPrice ω hist₀ (stdCtxs T t)
        have hp : Measurable p := learner.measurable_postPrice hist₀ (stdCtxs T t)
        let u : Ω → ℝ := fun ω => dotProduct (stdCtxs T t) z - p ω
        have hu : Measurable u := measurable_const.sub hp
        let loss₁ : Ω → ℝ := fun ω => loss₀ ω + |u ω|
        have hloss₁ : Measurable loss₁ := hloss₀.add (continuous_abs.measurable.comp hu)
        have h_eq_ite :
            (fun ω => ((t :: ts).foldl (step z ω) (loss₀ ω, hist₀)).1) =
            (fun ω =>
              if 0 ≤ u ω then
                (ts.foldl (step z ω) (loss₁ ω, hist₀ ++ [(stdCtxs T t, 1)])).1
              else
                (ts.foldl (step z ω) (loss₁ ω, hist₀ ++ [(stdCtxs T t, -1)])).1) := by
          funext ω
          dsimp only [List.foldl_cons, step, paperSign, p, u, loss₁]
          by_cases h : 0 ≤ stdCtxs T t ⬝ᵥ z - learner.postPrice ω hist₀ (stdCtxs T t)
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h]
        rw [h_eq_ite]
        have hset : MeasurableSet {ω : Ω | 0 ≤ u ω} := measurableSet_Ici.preimage hu
        exact Measurable.ite hset (ih loss₁ _ hloss₁) (ih loss₁ _ hloss₁)
    exact h_fold (List.finRange T) (fun _ => 0) [] measurable_const

  have h_pointwise_sum : ∀ ω : Ω,
      (2 : ℝ) ^ d * Real.sqrt d ≤
        ∑ signs : Fin d → Bool,
          searchCumulativeLoss learner (hypercubeTarget signs) T (stdCtxs T) ω := by
    intro ω
    have h_traj_congr : ∀ (m : ℕ) (ctxs : Fin m → (Fin d → ℝ)) (z₁ z₂ : Fin d → ℝ),
        (∀ t : Fin m, dotProduct (ctxs t) z₁ = dotProduct (ctxs t) z₂) →
        searchTrajectory learner z₁ ω m ctxs = searchTrajectory learner z₂ ω m ctxs := by
      intro m ctxs z₁ z₂ hdot
      unfold searchTrajectory
      refine congrArg (fun f => (List.finRange m).foldl f (0, [])) ?_
      funext acc t
      simp only [hdot t]
    have h_loss_succ : ∀ (m : ℕ) (z : Fin d → ℝ),
        let xm : Fin d → ℝ := fun j => if j.val = m then (1 : ℝ) else 0
        searchCumulativeLoss learner z (m + 1) (stdCtxs (m + 1)) ω =
          searchCumulativeLoss learner z m (stdCtxs m) ω +
            |dotProduct xm z -
              learner.postPrice ω (searchTrajectory learner z ω m (stdCtxs m)).2 xm| := by
      intro m z
      simp [searchCumulativeLoss, searchTrajectory, List.finRange_succ_last,
        List.foldl_append, List.foldl_map, stdCtxs]
    have h_active_round : ∀ (m : ℕ) (hm : m < d),
        let xm : Fin d → ℝ := fun j => if j.val = m then (1 : ℝ) else 0
        (2 : ℝ) ^ d / Real.sqrt d ≤
          ∑ s : Fin d → Bool,
            |dotProduct xm (hypercubeTarget s) -
              learner.postPrice ω (searchTrajectory learner (hypercubeTarget s) ω m (stdCtxs m)).2 xm| := by
      intro m hm xm
      let k : Fin d := ⟨m, hm⟩
      let flipK : (Fin d → Bool) → (Fin d → Bool) := fun s => Function.update s k (!s k)
      have h_inv : Function.Involutive flipK := by
        intro s
        ext j
        by_cases hj : j = k <;> simp [flipK, hj]
      let eK : (Fin d → Bool) ≃ (Fin d → Bool) := ⟨flipK, flipK, h_inv, h_inv⟩
      have h_hist_eq : ∀ s : Fin d → Bool,
          (searchTrajectory learner (hypercubeTarget (flipK s)) ω m (stdCtxs m)).2 =
            (searchTrajectory learner (hypercubeTarget s) ω m (stdCtxs m)).2 := by
        intro s
        refine congrArg Prod.snd (h_traj_congr m (stdCtxs m) _ _ fun t => ?_)
        unfold dotProduct
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j.val = t.val
        · have hjk : j ≠ k := by
            intro h_eq
            have hk_val : j.val = m := congrArg Fin.val h_eq
            omega
          simp [stdCtxs, hj, flipK, hypercubeTarget, hjk]
        · simp [stdCtxs, hj]
      have h_dot_xm : ∀ z : Fin d → ℝ, dotProduct xm z = z k := by
        intro z
        unfold dotProduct
        have h_sum_eq : (∑ j : Fin d, xm j * z j) = ∑ j : Fin d, if j = k then z j else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have hiff : j.val = m ↔ j = k := by simp [Fin.ext_iff, k]
          by_cases hjk : j = k
          · rw [if_pos hjk]; simp [xm, hiff.mpr hjk]
          · rw [if_neg hjk]; simp [xm, mt hiff.mp hjk]
        rw [h_sum_eq, Finset.sum_ite_eq']
        simp
      let ell : (Fin d → Bool) → ℝ := fun s =>
        |dotProduct xm (hypercubeTarget s) -
          learner.postPrice ω (searchTrajectory learner (hypercubeTarget s) ω m (stdCtxs m)).2 xm|
      have h_pair : ∀ s : Fin d → Bool, 2 / Real.sqrt d ≤ ell s + ell (eK s) := by
        intro s
        change 2 / Real.sqrt d ≤ ell s + ell (flipK s)
        dsimp only [ell]
        rw [h_dot_xm, h_dot_xm, h_hist_eq s]
        let p : ℝ := learner.postPrice ω (searchTrajectory learner (hypercubeTarget s) ω m (stdCtxs m)).2 xm
        change 2 / Real.sqrt d ≤ |hypercubeTarget s k - p| + |hypercubeTarget (flipK s) k - p|
        have hfk : flipK s k = !s k := Function.update_self k (!s k) s
        unfold hypercubeTarget
        rw [hfk]
        cases s k
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          have h1 := le_abs_self (1 / Real.sqrt d - p)
          have h2 := neg_le_abs (-1 / Real.sqrt d - p)
          have h_id : (1 / Real.sqrt d - p) + -(-1 / Real.sqrt d - p) = 2 / Real.sqrt d := by ring
          linarith
        · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
          have h1 := le_abs_self (1 / Real.sqrt d - p)
          have h2 := neg_le_abs (-1 / Real.sqrt d - p)
          have h_id : (1 / Real.sqrt d - p) + -(-1 / Real.sqrt d - p) = 2 / Real.sqrt d := by ring
          linarith
      have h_sum_pair : ∑ _s : Fin d → Bool, (2 / Real.sqrt d) ≤
          ∑ s : Fin d → Bool, (ell s + ell (eK s)) :=
        Finset.sum_le_sum fun s _ => h_pair s
      rw [Finset.sum_add_distrib, Equiv.sum_comp eK ell] at h_sum_pair
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h_sum_pair
      have h_id2 : (2 : ℝ) ^ d * (2 / Real.sqrt d) = 2 * ((2 : ℝ) ^ d / Real.sqrt d) := by ring
      have h_res : (2 : ℝ) ^ d / Real.sqrt d ≤ ∑ s : Fin d → Bool, ell s := by linarith
      exact h_res
    have h_prefix : ∀ m : ℕ,
        ((min m d : ℕ) : ℝ) * ((2 : ℝ) ^ d / Real.sqrt d) ≤
          ∑ s : Fin d → Bool,
            searchCumulativeLoss learner (hypercubeTarget s) m (stdCtxs m) ω := by
      intro m
      induction m with
      | zero =>
        simp [searchCumulativeLoss, searchTrajectory]
      | succ m ih =>
        have h_unroll :
            (∑ s : Fin d → Bool,
              searchCumulativeLoss learner (hypercubeTarget s) (m + 1) (stdCtxs (m + 1)) ω) =
            (∑ s : Fin d → Bool,
              searchCumulativeLoss learner (hypercubeTarget s) m (stdCtxs m) ω) +
            (∑ s : Fin d → Bool,
              |dotProduct (fun j : Fin d => if j.val = m then (1 : ℝ) else 0) (hypercubeTarget s) -
                learner.postPrice ω
                  (searchTrajectory learner (hypercubeTarget s) ω m (stdCtxs m)).2
                  (fun j : Fin d => if j.val = m then (1 : ℝ) else 0)|) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun s _ => h_loss_succ m (hypercubeTarget s)
        rw [h_unroll]
        by_cases hm : m < d
        · have hmin1 : min (m + 1) d = m + 1 := by omega
          have hmin0 : min m d = m := by omega
          rw [hmin1]
          rw [hmin0] at ih
          have hact := h_active_round m hm
          push_cast
          linarith
        · have hmin1 : min (m + 1) d = d := by omega
          have hmin0 : min m d = d := by omega
          rw [hmin1]
          rw [hmin0] at ih
          have hnonneg : 0 ≤ ∑ s : Fin d → Bool,
              |dotProduct (fun j : Fin d => if j.val = m then (1 : ℝ) else 0) (hypercubeTarget s) -
                learner.postPrice ω
                  (searchTrajectory learner (hypercubeTarget s) ω m (stdCtxs m)).2
                  (fun j : Fin d => if j.val = m then (1 : ℝ) else 0)| :=
            Finset.sum_nonneg fun _ _ => abs_nonneg _
          linarith
    have hT_bound := h_prefix T
    have hminT : min T d = d := Nat.min_eq_right hT
    rw [hminT] at hT_bound
    have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
    have hsqrt_ne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
    have h_alg : ((d : ℕ) : ℝ) * ((2 : ℝ) ^ d / Real.sqrt d) = (2 : ℝ) ^ d * Real.sqrt d := by
      have hsq : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt hd_pos.le
      calc
        ((d : ℕ) : ℝ) * ((2 : ℝ) ^ d / Real.sqrt d)
            = (Real.sqrt d * Real.sqrt d) * ((2 : ℝ) ^ d / Real.sqrt d) := by rw [hsq]
        _ = (2 : ℝ) ^ d * Real.sqrt d := by field_simp [hsqrt_ne]
    linarith

  let L : (Fin d → Bool) → Ω → ℝ :=
    fun s ω => searchCumulativeLoss learner (hypercubeTarget s) T (stdCtxs T) ω
  let A : (Fin d → Bool) → ENNReal :=
    fun s => ∫⁻ ω, ENNReal.ofReal (L s ω) ∂μ
  have hA_meas : ∀ s : Fin d → Bool, Measurable (fun ω => ENNReal.ofReal (L s ω)) :=
    fun s => ENNReal.measurable_ofReal.comp (h_loss_meas (hypercubeTarget s))
  have h_sum_A :
      (2 ^ d : ENNReal) * ENNReal.ofReal (Real.sqrt d) ≤ ∑ s : Fin d → Bool, A s := by
    have h_interchange :
        (∑ s : Fin d → Bool, A s) =
          ∫⁻ ω, (∑ s : Fin d → Bool, ENNReal.ofReal (L s ω)) ∂μ :=
      (MeasureTheory.lintegral_finset_sum Finset.univ fun s _ => hA_meas s).symm
    rw [h_interchange]
    have h_pw : ∀ ω : Ω,
        (2 ^ d : ENNReal) * ENNReal.ofReal (Real.sqrt d) ≤
          ∑ s : Fin d → Bool, ENNReal.ofReal (L s ω) := by
      intro ω
      rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => h_loss_nonneg (hypercubeTarget s) ω)]
      have h_le := ENNReal.ofReal_le_ofReal (h_pointwise_sum ω)
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2) d,
        ENNReal.ofReal_ofNat] at h_le
      exact h_le
    calc
      (2 ^ d : ENNReal) * ENNReal.ofReal (Real.sqrt d)
          = ((2 ^ d : ENNReal) * ENNReal.ofReal (Real.sqrt d)) * μ Set.univ := by
            rw [MeasureTheory.measure_univ, mul_one]
      _ = ∫⁻ _ω, (2 ^ d : ENNReal) * ENNReal.ofReal (Real.sqrt d) ∂μ :=
            (MeasureTheory.lintegral_const _).symm
      _ ≤ ∫⁻ ω, (∑ s : Fin d → Bool, ENNReal.ofReal (L s ω)) ∂μ :=
            MeasureTheory.lintegral_mono h_pw
  have h2_ne_zero : (2 ^ d : ENNReal) ≠ 0 := pow_ne_zero d (by norm_num)
  have h2_ne_top : (2 ^ d : ENNReal) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have h_avg :
      ENNReal.ofReal (Real.sqrt d) ≤ (2 ^ d : ENNReal)⁻¹ * ∑ s : Fin d → Bool, A s := by
    calc
      ENNReal.ofReal (Real.sqrt d)
          = 1 * ENNReal.ofReal (Real.sqrt d) := (one_mul _).symm
      _ = ((2 ^ d : ENNReal)⁻¹ * (2 ^ d : ENNReal)) * ENNReal.ofReal (Real.sqrt d) := by
            rw [ENNReal.inv_mul_cancel h2_ne_zero h2_ne_top]
      _ = (2 ^ d : ENNReal)⁻¹ * ((2 ^ d : ENNReal) * ENNReal.ofReal (Real.sqrt d)) := by
            rw [mul_assoc]
      _ ≤ (2 ^ d : ENNReal)⁻¹ * ∑ s : Fin d → Bool, A s := by gcongr
  obtain ⟨s₀, _, hs₀_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin d → Bool)) A Finset.univ_nonempty
  have h_sum_le_max : (∑ s : Fin d → Bool, A s) ≤ (2 ^ d : ENNReal) * A s₀ := by
    have hcard := Finset.sum_le_card_nsmul Finset.univ A (A s₀) hs₀_max
    simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow] using hcard
  have h_max : ENNReal.ofReal (Real.sqrt d) ≤ A s₀ := by
    calc
      ENNReal.ofReal (Real.sqrt d)
          ≤ (2 ^ d : ENNReal)⁻¹ * ∑ s : Fin d → Bool, A s := h_avg
      _ ≤ (2 ^ d : ENNReal)⁻¹ * ((2 ^ d : ENNReal) * A s₀) := by gcongr
      _ = ((2 ^ d : ENNReal)⁻¹ * (2 ^ d : ENNReal)) * A s₀ := by rw [← mul_assoc]
      _ = 1 * A s₀ := by rw [ENNReal.inv_mul_cancel h2_ne_zero h2_ne_top]
      _ = A s₀ := one_mul _
  exact ⟨stdCtxs T, h_ctx_norm, h_avg, ⟨hypercubeTarget s₀, h_hyp_norm s₀, h_max⟩⟩

/-- **Potential-normalized Bayesian search lower bound (Appendix E, Proposition E.1)**:
Under the uniform hypercube prior `π = unifBoolPrior d` (`d ≥ 1`), the covariance matrix is
`Cov_π(z) = (1 / d) I_d` with trace-square-root potential `Ψ(Cov_π(z)) = √d`, and for every `T ≥ d`
and every randomized learner there exist deterministic unit-ball contexts `ctxs` under which the
Bayesian expected cumulative loss is at least `Ψ(Cov_π(z))`. -/
theorem prop_search_lower_bound_potential (d T : ℕ) (hd : 0 < d) (hT : d ≤ T)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (learner : SearchLearner d Ω) :
    let π := unifBoolPrior d
    rvCovMat hypercubeTarget π = (1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ) ∧
    psdTraceSqrt (rvCovMat hypercubeTarget π) = Real.sqrt d ∧
    (∃ ctxs : Fin T → (Fin d → ℝ),
      (∀ t : Fin T, vecL2Norm (ctxs t) ≤ 1) ∧
      (2 ^ d : ENNReal)⁻¹ *
        ∑ signs : Fin d → Bool,
          ∫⁻ ω, ENNReal.ofReal (searchCumulativeLoss learner (hypercubeTarget signs) T ctxs ω) ∂μ ≥
        ENNReal.ofReal (psdTraceSqrt (rvCovMat hypercubeTarget π))) := by
  dsimp only
  set π := unifBoolPrior d
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
  have hsq_sqrt : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
  set α : ℝ := 1 / Real.sqrt d
  have hα_pos : 0 < α := by positivity
  have hα_sq : α ^ 2 = 1 / (d : ℝ) := by
    dsimp [α]
    rw [div_pow, one_pow, hsq_sqrt]

  have h_int : ∀ f : (Fin d → Bool) → ℝ,
      Measurable f → (∫ c, f c ∂π) = (2 ^ d : ℝ)⁻¹ * ∑ c : Fin d → Bool, f c := by
    intro f hf
    dsimp [π, unifBoolPrior]
    rw [MeasureTheory.integral_smul_measure, smul_eq_mul]
    have h_toReal : ((2 ^ d : ENNReal)⁻¹).toReal = (2 ^ d : ℝ)⁻¹ := by
      rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    rw [h_toReal]
    congr 1
    have h_dirac_int : ∀ c ∈ (Finset.univ : Finset (Fin d → Bool)),
        MeasureTheory.Integrable f (MeasureTheory.Measure.dirac c) :=
      fun c _ => MeasureTheory.integrable_dirac (by simp)
    rw [MeasureTheory.integral_finset_sum_measure h_dirac_int]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact MeasureTheory.integral_dirac' f c hf.stronglyMeasurable

  let sgn : (Fin d → Bool) → Fin d → ℝ := fun c i => if c i then 1 else -1
  have hsgn_meas : ∀ i : Fin d, Measurable (fun c : Fin d → Bool => sgn c i) := by
    intro i
    exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)
      measurable_const measurable_const

  have h_sum_sgn_zero : ∀ i : Fin d, (∑ c : Fin d → Bool, sgn c i) = 0 := by
    intro i
    let flip : (Fin d → Bool) → (Fin d → Bool) := fun c => Function.update c i (!c i)
    have h_inv : Function.Involutive flip := fun c => by
      ext j; by_cases hj : j = i <;> simp [flip, hj]
    have h_eq : (∑ c : Fin d → Bool, sgn (flip c) i) = ∑ c : Fin d → Bool, sgn c i :=
      Equiv.sum_comp h_inv.toPerm (fun c => sgn c i)
    have h_neg : ∀ c : Fin d → Bool, sgn (flip c) i = -sgn c i := fun c => by
      cases hc : c i <;> simp [sgn, flip, hc]
    simp_rw [h_neg, Finset.sum_neg_distrib] at h_eq
    linarith

  have h_sum_sgn_prod : ∀ i j : Fin d,
      (∑ c : Fin d → Bool, sgn c i * sgn c j) = if i = j then (2 ^ d : ℝ) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have h_one : ∀ c : Fin d → Bool, sgn c i * sgn c i = 1 := fun c => by
        cases hc : c i <;> simp [sgn, hc]
      simp [h_one]
    · rw [if_neg hij]
      let flip : (Fin d → Bool) → (Fin d → Bool) := fun c => Function.update c j (!c j)
      have h_inv : Function.Involutive flip := fun c => by
        ext k; by_cases hk : k = j <;> simp [flip, hk]
      have h_eq : (∑ c : Fin d → Bool, sgn (flip c) i * sgn (flip c) j) =
          ∑ c : Fin d → Bool, sgn c i * sgn c j :=
        Equiv.sum_comp h_inv.toPerm (fun c => sgn c i * sgn c j)
      have h_neg : ∀ c : Fin d → Bool, sgn (flip c) i * sgn (flip c) j = -(sgn c i * sgn c j) := by
        intro c
        have hfi : flip c i = c i := Function.update_of_ne hij (!c j) c
        simp only [sgn, hfi]
        cases hc : c j <;> simp [flip, hc]
      simp_rw [h_neg, Finset.sum_neg_distrib] at h_eq
      linarith

  have h_decomp : ∀ (c : Fin d → Bool) (i : Fin d),
      hypercubeTarget c i = α * sgn c i := by
    intro c i
    dsimp [hypercubeTarget, sgn, α]
    cases c i <;> simp <;> ring

  have h2d_ne0_real : (2 ^ d : ℝ) ≠ 0 := pow_ne_zero d (by norm_num)

  have hCov : rvCovMat hypercubeTarget π = (1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    have hW_meas : ∀ i : Fin d, Measurable (fun c => hypercubeTarget c i) := fun i => by
      have h_fn : (fun c => hypercubeTarget c i) = fun c => α * sgn c i :=
        funext fun c => h_decomp c i
      rw [h_fn]
      exact measurable_const.mul (hsgn_meas i)
    have h_mean : ∀ i : Fin d, rvMeanVec hypercubeTarget π i = 0 := fun i => by
      change (∫ c, hypercubeTarget c i ∂π) = 0
      rw [h_int (fun c => hypercubeTarget c i) (hW_meas i)]
      simp_rw [h_decomp]
      rw [← Finset.mul_sum, h_sum_sgn_zero i, mul_zero, mul_zero]
    ext i j
    simp only [rvCovMat, Matrix.of_apply, h_mean, sub_zero,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have h_prod_fn : (fun c : Fin d → Bool => hypercubeTarget c i * hypercubeTarget c j) =
        fun c => α ^ 2 * (sgn c i * sgn c j) := by
      ext c; rw [h_decomp c i, h_decomp c j]; ring
    have h_prod_meas : Measurable (fun c : Fin d → Bool => α ^ 2 * (sgn c i * sgn c j)) :=
      measurable_const.mul ((hsgn_meas i).mul (hsgn_meas j))
    rw [h_prod_fn, h_int _ h_prod_meas, ← Finset.mul_sum, h_sum_sgn_prod i j, hα_sq]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      field_simp
    · simp [hij]

  have h_tr_sqrt : psdTraceSqrt ((1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ)) = Real.sqrt d := by
    rw [← hα_sq]
    set S : Matrix (Fin d) (Fin d) ℝ := (α ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)
    have hS_psd : S.PosSemidef := Matrix.PosSemidef.one.smul (sq_nonneg α)
    have h_tr_eq : psdTraceSqrt S = Matrix.trace hS_psd.sqrt := by
      unfold psdTraceSqrt
      rw [dif_pos hS_psd]
      congr 1
      have h_dec : (fun a b : Fin d => Classical.propDecidable (a = b)) = instDecidableEqFin d :=
        Subsingleton.elim _ _
      rw [h_dec]
    set R : Matrix (Fin d) (Fin d) ℝ := hS_psd.sqrt
    have hR_psd : R.PosSemidef := by
      unfold R Matrix.PosSemidef.sqrt
      let f : Fin d → ℝ := RCLike.ofReal ∘ (fun x : ℝ => √x) ∘ hS_psd.isHermitian.eigenvalues
      have hdiag : (Matrix.diagonal f).PosSemidef :=
        Matrix.posSemidef_diagonal_iff.mpr fun i => by simp [f, Real.sqrt_nonneg]
      simpa only [Matrix.star_eq_conjTranspose] using
        hdiag.mul_mul_conjTranspose_same hS_psd.isHermitian.eigenvectorUnitary.val
    have hR_sq : R * R = S := by
      unfold R Matrix.PosSemidef.sqrt
      let U : Matrix (Fin d) (Fin d) ℝ := hS_psd.isHermitian.eigenvectorUnitary.val
      have hU_mem : U ∈ Matrix.unitaryGroup (Fin d) ℝ := hS_psd.isHermitian.eigenvectorUnitary.prop
      have hstarU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU_mem
      let f : Fin d → ℝ := RCLike.ofReal ∘ (fun x : ℝ => √x) ∘ hS_psd.isHermitian.eigenvalues
      change (U * Matrix.diagonal f * star U) * (U * Matrix.diagonal f * star U) = S
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
            Matrix.diagonal (RCLike.ofReal ∘ hS_psd.isHermitian.eigenvalues) := by
        congr 1; ext i
        have h_ev : 0 ≤ hS_psd.isHermitian.eigenvalues i := hS_psd.eigenvalues_nonneg i
        simp [f, RCLike.ofReal_real_eq_id, ← sq, Real.sq_sqrt h_ev]
      rw [h_diag_eq]
      simpa [Unitary.conjStarAlgAut_apply, U] using (hS_psd.isHermitian.spectral_theorem).symm
    have h_factor : (R + α • (1 : Matrix (Fin d) (Fin d) ℝ)) *
        (R - α • (1 : Matrix (Fin d) (Fin d) ℝ)) = 0 := by
      rw [Matrix.mul_sub, Matrix.add_mul, Matrix.add_mul, hR_sq,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← sq]
      change (S + α • R) - (α • R + S) = 0
      abel
    have hR_eq : R = α • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      suffices h_sub : R - α • (1 : Matrix (Fin d) (Fin d) ℝ) = 0 from sub_eq_zero.mp h_sub
      ext i j
      let D := R - α • (1 : Matrix (Fin d) (Fin d) ℝ)
      let w : Fin d → ℝ := D.mulVec (Pi.single j 1)
      have hw_zero_mul : (R + α • (1 : Matrix (Fin d) (Fin d) ℝ)).mulVec w = 0 := by
        dsimp [w, D]
        rw [Matrix.mulVec_mulVec, h_factor, Matrix.zero_mulVec]
      have h_dot0 : dotProduct w (R.mulVec w) + α * dotProduct w w = 0 := by
        have h0 : dotProduct w ((R + α • (1 : Matrix (Fin d) (Fin d) ℝ)).mulVec w) = 0 := by
          rw [hw_zero_mul, dotProduct_zero]
        rwa [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
             dotProduct_add, dotProduct_smul, smul_eq_mul] at h0
      have hR_nn : 0 ≤ dotProduct w (R.mulVec w) := by
        simpa [star_trivial] using hR_psd.dotProduct_mulVec_nonneg w
      have hww_nn : 0 ≤ dotProduct w w :=
        Finset.sum_nonneg fun k _ => by simpa [sq] using sq_nonneg (w k)
      have hww0 : dotProduct w w = 0 := by nlinarith
      have hwi0 : w i = 0 := by
        have h_le : (w i) ^ 2 ≤ dotProduct w w := by
          simpa [dotProduct, sq] using
            Finset.single_le_sum (fun k _ => sq_nonneg (w k)) (Finset.mem_univ i)
        nlinarith [sq_nonneg (w i)]
      simpa [w, D, Matrix.mulVec_single, mul_one] using hwi0
    rw [h_tr_eq, hR_eq, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    dsimp [α]
    have hsqrt_ne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
    field_simp
    linarith [hsq_sqrt]

  have hPot : psdTraceSqrt (rvCovMat hypercubeTarget π) = Real.sqrt d := by
    rw [hCov, h_tr_sqrt]
  obtain ⟨ctxs, h_ctxs_norm, h_avg, _⟩ := prop_search_lower_bound d T hd hT μ learner
  refine ⟨hCov, hPot, ctxs, h_ctxs_norm, ?_⟩
  rwa [hPot]

end TraceSqrt
