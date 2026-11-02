import TraceSqrt.Defs

set_option maxHeartbeats 4000000

/-!
# Proposition E.2: Lower Bound for Contextual Bilateral Trade (`prop:trade-lb`)

From *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*
(Appendix E, Proposition E.2 `prop:trade-lb`).
-/

namespace TraceSqrt

/-- **Proposition E.2 (Lower bound for contextual bilateral trade, `prop:trade-lb`)**:
For every `d ≥ 1`, `T ≥ d`, probability space `(Ω, μ)`, and per-round budget-balanced randomized
broker (`p_t ≤ q_t`), there exist deterministic contexts `ctxs` of norm at most `1` such that:
1. Under the uniform coordinate prior on `{(0, 1/(3√d)), (2/(3√d), 1/√d)}^d`, every support point
   lies in `K = B_2^d × B_2^d` and the Bayesian expected regret is at least `√d / 6`, and
2. There exists a fixed pair `(s, b) ∈ B_2^d × B_2^d` with expected regret at least `√d / 6`. -/
theorem prop_trade_lower_bound (d T : ℕ) (hd : 0 < d) (hT : d ≤ T)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (broker : BudgetBalancedBroker d Ω) :
    ∃ ctxs : Fin T → (Fin d → ℝ),
      (∀ t : Fin T, vecL2Norm (ctxs t) ≤ 1) ∧
      (∀ choice : Fin d → Bool,
        vecL2Norm (priorSellerVec choice) ≤ 1 ∧ vecL2Norm (priorBuyerVec choice) ≤ 1) ∧
      ((2 ^ d : ENNReal)⁻¹ *
          ∑ choice : Fin d → Bool,
            ∫⁻ ω, ENNReal.ofReal
              (tradeCumulativeRegret broker (priorSellerVec choice) (priorBuyerVec choice) T ctxs ω) ∂μ ≥
        ENNReal.ofReal (Real.sqrt d / 6)) ∧
      (∃ s b : Fin d → ℝ,
        vecL2Norm s ≤ 1 ∧
        vecL2Norm b ≤ 1 ∧
        ∫⁻ ω, ENNReal.ofReal (tradeCumulativeRegret broker s b T ctxs ω) ∂μ ≥
          ENNReal.ofReal (Real.sqrt d / 6)) :=
by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
  have hsqrt_ne : Real.sqrt d ≠ 0 := ne_of_gt hsqrt_pos
  have hsq_sqrt : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)

  have h_norm_zero : vecL2Norm (0 : Fin d → ℝ) ≤ 1 := by
    rw [vecL2Norm, Real.sqrt_le_one]
    simp

  have h_norm_single : ∀ i : Fin d, vecL2Norm (Pi.single i (1 : ℝ)) ≤ 1 := by
    intro i
    let v : Fin d → ℝ := Pi.single i (1 : ℝ)
    change vecL2Norm v ≤ 1
    rw [vecL2Norm, Real.sqrt_le_one]
    have hsum : (∑ j : Fin d, (v j) ^ 2) = 1 := by
      have hterm : ∀ j : Fin d, (v j) ^ 2 = if j = i then 1 else 0 := by
        intro j
        by_cases hj : j = i <;> simp [v, hj]
      simp_rw [hterm]
      simp
    linarith

  have h_norm_prior : ∀ choice : Fin d → Bool,
      vecL2Norm (priorSellerVec choice) ≤ 1 ∧ vecL2Norm (priorBuyerVec choice) ≤ 1 := by
    intro choice
    constructor
    · rw [vecL2Norm, Real.sqrt_le_one]
      have hcoord : ∀ j : Fin d, (priorSellerVec choice j) ^ 2 ≤ (d : ℝ)⁻¹ := by
        intro j
        unfold priorSellerVec
        split_ifs
        · have h_eq : (2 / (3 * Real.sqrt d)) ^ 2 = (4 / 9) * (d : ℝ)⁻¹ := by
            rw [div_pow, mul_pow, hsq_sqrt]
            ring
          rw [h_eq]
          have h_inv_pos : 0 < (d : ℝ)⁻¹ := inv_pos.mpr hd_pos
          linarith
        · simp [le_of_lt (inv_pos.mpr hd_pos)]
      calc
        ∑ j : Fin d, (priorSellerVec choice j) ^ 2
          ≤ ∑ _j : Fin d, (d : ℝ)⁻¹ := Finset.sum_le_sum (fun j _ => hcoord j)
        _ = (d : ℝ) * (d : ℝ)⁻¹ := by simp
        _ = 1 := mul_inv_cancel₀ hd_ne
    · rw [vecL2Norm, Real.sqrt_le_one]
      have hcoord : ∀ j : Fin d, (priorBuyerVec choice j) ^ 2 ≤ (d : ℝ)⁻¹ := by
        intro j
        unfold priorBuyerVec
        split_ifs
        · have h_eq : (1 / Real.sqrt d) ^ 2 = (d : ℝ)⁻¹ := by
            rw [div_pow, one_pow, hsq_sqrt, one_div]
          linarith
        · have h_eq : (1 / (3 * Real.sqrt d)) ^ 2 = (1 / 9) * (d : ℝ)⁻¹ := by
            rw [div_pow, mul_pow, hsq_sqrt]
            ring
          rw [h_eq]
          have h_inv_pos : 0 < (d : ℝ)⁻¹ := inv_pos.mpr hd_pos
          linarith
      calc
        ∑ j : Fin d, (priorBuyerVec choice j) ^ 2
          ≤ ∑ _j : Fin d, (d : ℝ)⁻¹ := Finset.sum_le_sum (fun j _ => hcoord j)
        _ = (d : ℝ) * (d : ℝ)⁻¹ := by simp
        _ = 1 := mul_inv_cancel₀ hd_ne

  have h_traj_succ : ∀ (s b : Fin d → ℝ) (ω : Ω) (m : ℕ) (ctxsm : Fin (m + 1) → (Fin d → ℝ)),
      let prev := tradeTrajectory broker s b ω m (fun i => ctxsm (Fin.castSucc i))
      let xm := ctxsm (Fin.last m)
      let offer := broker.postOffer ω prev.2 xm
      tradeTrajectory broker s b ω (m + 1) ctxsm =
        (prev.1 + tradeRoundLoss s b xm offer.1 offer.2,
         prev.2 ++ [(xm, tradeFeedbackBit s b xm offer.1 offer.2)]) := by
    intros s b ω m ctxsm
    simp only [tradeTrajectory, List.finRange_succ_last, List.foldl_append, List.foldl_map,
      List.foldl_cons, List.foldl_nil]

  have h_loss_nonneg : ∀ (s b x : Fin d → ℝ) (p q : ℝ), 0 ≤ tradeRoundLoss s b x p q := by
    intros s b x p q
    unfold tradeRoundLoss tradeFeedbackBit
    apply mul_nonneg (le_max_right _ _)
    split_ifs <;> norm_num

  have h_regret_mono : ∀ (s b : Fin d → ℝ) (ω : Ω) (n : ℕ),
      ∀ (k : ℕ) (hk : k ≤ n) (ctxsn : Fin n → (Fin d → ℝ)),
        tradeCumulativeRegret broker s b k (fun i => ctxsn (Fin.castLE hk i)) ω ≤
          tradeCumulativeRegret broker s b n ctxsn ω := by
    intros s b ω n
    induction n with
    | zero =>
      intros k hk ctxsn
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simp [tradeCumulativeRegret, tradeTrajectory]
    | succ m ih =>
      intros k hk ctxsn
      rcases Nat.of_le_succ hk with hkm | rfl
      · have hcast : (fun i : Fin k => ctxsn (Fin.castLE hk i)) =
            (fun i : Fin k => (fun j : Fin m => ctxsn (Fin.castSucc j)) (Fin.castLE hkm i)) := by
          funext i
          congr 1
        rw [hcast]
        have hprev := ih k hkm (fun j => ctxsn (Fin.castSucc j))
        have hstep := h_traj_succ s b ω m ctxsn
        unfold tradeCumulativeRegret at hprev ⊢
        rw [hstep]
        dsimp only
        linarith [h_loss_nonneg s b (ctxsn (Fin.last m))
          (broker.postOffer ω (tradeTrajectory broker s b ω m (fun i => ctxsn (Fin.castSucc i))).2 (ctxsn (Fin.last m))).1
          (broker.postOffer ω (tradeTrajectory broker s b ω m (fun i => ctxsn (Fin.castSucc i))).2 (ctxsn (Fin.last m))).2]
      · have hcast : (fun i : Fin (m + 1) => ctxsn (Fin.castLE hk i)) = ctxsn := by
          funext i
          simp
        rw [hcast]

  have h_regret_nonneg : ∀ (s b : Fin d → ℝ) (n : ℕ) (ctxsn : Fin n → (Fin d → ℝ)) (ω : Ω),
      0 ≤ tradeCumulativeRegret broker s b n ctxsn ω := by
    intros s b n ctxsn ω
    have h0 := h_regret_mono s b ω n 0 (Nat.zero_le n) ctxsn
    simpa [tradeCumulativeRegret, tradeTrajectory] using h0

  have h_regret_meas : ∀ (s b : Fin d → ℝ) (n : ℕ) (ctxsn : Fin n → (Fin d → ℝ)),
      Measurable (tradeCumulativeRegret broker s b n ctxsn) := by
    classical
    intros s b n
    suffices h_inv : ∀ (ctxsn : Fin n → (Fin d → ℝ)),
        Measurable (fun ω => (tradeTrajectory broker s b ω n ctxsn).1) ∧
        (∃ H : Finset (List ((Fin d → ℝ) × ℝ)),
          ∀ ω, (tradeTrajectory broker s b ω n ctxsn).2 ∈ H) ∧
        (∀ L : List ((Fin d → ℝ) × ℝ),
          MeasurableSet {ω | (tradeTrajectory broker s b ω n ctxsn).2 = L}) by
      intro ctxsn
      exact (h_inv ctxsn).1
    induction n with
    | zero =>
      intro ctxs0
      refine ⟨?_, ⟨{[]}, ?_⟩, ?_⟩
      · simp [tradeTrajectory, measurable_const]
      · intro ω
        simp [tradeTrajectory]
      · intro L
        by_cases hL : ([] : List ((Fin d → ℝ) × ℝ)) = L
        · convert MeasurableSet.univ
          ext ω
          simp [tradeTrajectory, hL]
        · convert MeasurableSet.empty
          ext ω
          simp [tradeTrajectory, hL]
    | succ m ih =>
      intro ctxsm
      obtain ⟨hM_prev, ⟨H, hH_mem⟩, hM_lvl⟩ := ih (fun i => ctxsm (Fin.castSucc i))
      let prev : Ω → ℝ × List ((Fin d → ℝ) × ℝ) :=
        fun ω => tradeTrajectory broker s b ω m (fun i => ctxsm (Fin.castSucc i))
      let xm : Fin d → ℝ := ctxsm (Fin.last m)
      let offerL : List ((Fin d → ℝ) × ℝ) → Ω → ℝ × ℝ :=
        fun L ω => broker.postOffer ω L xm
      let EL : List ((Fin d → ℝ) × ℝ) → Set Ω :=
        fun L => {ω | dotProduct xm s ≤ (offerL L ω).1} ∩ {ω | (offerL L ω).2 ≤ dotProduct xm b}
      have hEL_meas : ∀ L, MeasurableSet (EL L) := by
        intro L
        have hOff : Measurable (offerL L) := broker.measurable_postOffer L xm
        exact (measurableSet_le measurable_const hOff.fst).inter
          (measurableSet_le hOff.snd measurable_const)
      let yL : List ((Fin d → ℝ) × ℝ) → Ω → ℝ :=
        fun L ω => tradeFeedbackBit s b xm (offerL L ω).1 (offerL L ω).2
      have hyL_eq : ∀ L ω, yL L ω = if ω ∈ EL L then 1 else 0 := by
        intros L ω
        unfold yL tradeFeedbackBit EL
        simp [Set.mem_inter_iff]
      let ellL : List ((Fin d → ℝ) × ℝ) → Ω → ℝ :=
        fun L ω => tradeRoundLoss s b xm (offerL L ω).1 (offerL L ω).2
      have hellL_meas : ∀ L, Measurable (ellL L) := by
        intro L
        have hyM : Measurable (yL L) := by
          have : yL L = fun ω => if ω ∈ EL L then (1 : ℝ) else 0 := by
            funext ω
            exact hyL_eq L ω
          rw [this]
          exact Measurable.ite (hEL_meas L) measurable_const measurable_const
        unfold ellL tradeRoundLoss
        exact measurable_const.mul (measurable_const.sub hyM)
      have hstep : ∀ ω, tradeTrajectory broker s b ω (m + 1) ctxsm =
          ((prev ω).1 + ellL (prev ω).2 ω, (prev ω).2 ++ [(xm, yL (prev ω).2 ω)]) := by
        intro ω
        exact h_traj_succ s b ω m ctxsm
      refine ⟨?_, ?_, ?_⟩
      · have h_eq_sum : (fun ω => (tradeTrajectory broker s b ω (m + 1) ctxsm).1) =
            fun ω => (prev ω).1 + ∑ L ∈ H, (if (prev ω).2 = L then ellL L ω else 0) := by
          funext ω
          rw [hstep ω]
          dsimp only
          congr 1
          have hsum := Finset.sum_ite_eq H (prev ω).2 (fun L => ellL L ω)
          rw [if_pos (hH_mem ω)] at hsum
          exact hsum.symm
        rw [h_eq_sum]
        refine hM_prev.add (Finset.measurable_sum H fun L _ => ?_)
        exact Measurable.ite (hM_lvl L) (hellL_meas L) measurable_const
      · refine ⟨H.biUnion (fun L => {L ++ [(xm, (0 : ℝ))], L ++ [(xm, (1 : ℝ))]}), ?_⟩
        intro ω
        rw [hstep ω]
        dsimp only
        rw [Finset.mem_biUnion]
        refine ⟨(prev ω).2, hH_mem ω, ?_⟩
        unfold yL tradeFeedbackBit
        split_ifs <;> simp
      · intro L'
        have h_const_meas : ∀ P : Prop, MeasurableSet {ω : Ω | P} := by
          intro P
          by_cases hP : P <;> simp [hP]
        have hset_eq : {ω | (tradeTrajectory broker s b ω (m + 1) ctxsm).2 = L'} =
            ⋃ L ∈ H, ({ω | (prev ω).2 = L} ∩
              ((EL L ∩ {ω | L ++ [(xm, (1 : ℝ))] = L'}) ∪
               ((EL L)ᶜ ∩ {ω | L ++ [(xm, (0 : ℝ))] = L'}))) := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_union,
            Set.mem_compl_iff, exists_prop]
          rw [hstep ω]
          dsimp only
          constructor
          · intro h_eq
            refine ⟨(prev ω).2, hH_mem ω, rfl, ?_⟩
            by_cases hE : ω ∈ EL (prev ω).2
            · left
              refine ⟨hE, ?_⟩
              rw [hyL_eq (prev ω).2 ω, if_pos hE] at h_eq
              exact h_eq
            · right
              refine ⟨hE, ?_⟩
              rw [hyL_eq (prev ω).2 ω, if_neg hE] at h_eq
              exact h_eq
          · rintro ⟨L, _, hprevL, ⟨hE, hL'⟩ | ⟨hnE, hL'⟩⟩
            · rw [hprevL, hyL_eq L ω, if_pos hE, hL']
            · rw [hprevL, hyL_eq L ω, if_neg hnE, hL']
        rw [hset_eq]
        refine Finset.measurableSet_biUnion H fun L _ => ?_
        exact (hM_lvl L).inter
          (((hEL_meas L).inter (h_const_meas _)).union
           ((hEL_meas L).compl.inter (h_const_meas _)))

  let ctxsPref : ∀ k : ℕ, k ≤ d → Fin k → (Fin d → ℝ) :=
    fun k hk i => Pi.single ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ (1 : ℝ)

  have h_pref_congr : ∀ (ω : Ω) (k : ℕ) (hk : k ≤ d) (c₁ c₂ : Fin d → Bool),
      (∀ j : Fin d, j.val < k → c₁ j = c₂ j) →
      tradeTrajectory broker (priorSellerVec c₁) (priorBuyerVec c₁) ω k (ctxsPref k hk) =
        tradeTrajectory broker (priorSellerVec c₂) (priorBuyerVec c₂) ω k (ctxsPref k hk) := by
    intros ω k
    induction k with
    | zero =>
      intros hk c₁ c₂ _
      simp [tradeTrajectory]
    | succ m ih =>
      intros hk' c₁ c₂ hc
      have hm : m ≤ d := Nat.le_of_succ_le hk'
      have h_ctxs_eq : (fun i => ctxsPref (m + 1) hk' (Fin.castSucc i)) = ctxsPref m hm := by
        funext i
        simp [ctxsPref]
      have h_prev_eq :
          tradeTrajectory broker (priorSellerVec c₁) (priorBuyerVec c₁) ω m (ctxsPref m hm) =
          tradeTrajectory broker (priorSellerVec c₂) (priorBuyerVec c₂) ω m (ctxsPref m hm) :=
        ih hm c₁ c₂ (fun j hj => hc j (Nat.lt_succ_of_lt hj))
      let idx : Fin d := ⟨m, hk'⟩
      have h_xm : ctxsPref (m + 1) hk' (Fin.last m) = Pi.single idx (1 : ℝ) := by
        simp [ctxsPref, idx]
      have hc_idx : c₁ idx = c₂ idx := hc idx (Nat.lt_succ_self m)
      have hs_dot : dotProduct (Pi.single idx (1 : ℝ)) (priorSellerVec c₁) =
          dotProduct (Pi.single idx (1 : ℝ)) (priorSellerVec c₂) := by
        simp [single_dotProduct, priorSellerVec, hc_idx]
      have hb_dot : dotProduct (Pi.single idx (1 : ℝ)) (priorBuyerVec c₁) =
          dotProduct (Pi.single idx (1 : ℝ)) (priorBuyerVec c₂) := by
        simp [single_dotProduct, priorBuyerVec, hc_idx]
      rw [h_traj_succ (priorSellerVec c₁) (priorBuyerVec c₁) ω m (ctxsPref (m + 1) hk'),
          h_traj_succ (priorSellerVec c₂) (priorBuyerVec c₂) ω m (ctxsPref (m + 1) hk')]
      rw [h_ctxs_eq, h_prev_eq, h_xm]
      simp only [tradeRoundLoss, tradeFeedbackBit, hs_dot, hb_dot]

  have h_pair_loss : ∀ (idx : Fin d) (p q : ℝ), p ≤ q →
      ∀ (c₀ c₁ : Fin d → Bool), c₀ idx = false → c₁ idx = true →
        1 / (3 * Real.sqrt d) ≤
          tradeRoundLoss (priorSellerVec c₀) (priorBuyerVec c₀) (Pi.single idx (1 : ℝ)) p q +
          tradeRoundLoss (priorSellerVec c₁) (priorBuyerVec c₁) (Pi.single idx (1 : ℝ)) p q := by
    intros idx p q hpq c₀ c₁ hc₀ hc₁
    let x : Fin d → ℝ := Pi.single idx (1 : ℝ)
    have hs₀ : dotProduct x (priorSellerVec c₀) = 0 := by
      simp [x, single_dotProduct, priorSellerVec, hc₀]
    have hb₀ : dotProduct x (priorBuyerVec c₀) = 1 / (3 * Real.sqrt d) := by
      simp [x, single_dotProduct, priorBuyerVec, hc₀]
    have hs₁ : dotProduct x (priorSellerVec c₁) = 2 / (3 * Real.sqrt d) := by
      simp [x, single_dotProduct, priorSellerVec, hc₁]
    have hb₁ : dotProduct x (priorBuyerVec c₁) = 1 / Real.sqrt d := by
      simp [x, single_dotProduct, priorBuyerVec, hc₁]
    have hgap_pos : 0 < 1 / (3 * Real.sqrt d) := by positivity
    have hdiff₁ : 1 / Real.sqrt d - 2 / (3 * Real.sqrt d) = 1 / (3 * Real.sqrt d) := by
      field_simp
      ring
    unfold tradeRoundLoss tradeFeedbackBit
    rw [hs₀, hb₀, hs₁, hb₁, sub_zero, hdiff₁, max_eq_left (le_of_lt hgap_pos)]
    split_ifs with h0 h1 h1'
    · exfalso
      have h_le : 2 / (3 * Real.sqrt d) ≤ 1 / (3 * Real.sqrt d) :=
        le_trans h1.1 (le_trans hpq h0.2)
      have h3pos : 0 < 3 * Real.sqrt d := by positivity
      have := (div_le_div_iff_of_pos_right h3pos).mp h_le
      linarith
    · linarith
    · linarith
    · linarith

  have h_pref_sum : ∀ (ω : Ω) (k : ℕ) (hk : k ≤ d),
      (2 ^ d : ℝ) * ((k : ℝ) / (6 * Real.sqrt d)) ≤
        ∑ c : Fin d → Bool,
          (tradeTrajectory broker (priorSellerVec c) (priorBuyerVec c) ω k (ctxsPref k hk)).1 := by
    intros ω k
    induction k with
    | zero =>
      intro hk
      simp [tradeTrajectory]
    | succ m ih =>
      intro hk'
      have hm : m ≤ d := Nat.le_of_succ_le hk'
      have h_ctxs_eq : (fun i => ctxsPref (m + 1) hk' (Fin.castSucc i)) = ctxsPref m hm := by
        funext i
        simp [ctxsPref]
      let idx : Fin d := ⟨m, hk'⟩
      let xk : Fin d → ℝ := Pi.single idx (1 : ℝ)
      have h_xm : ctxsPref (m + 1) hk' (Fin.last m) = xk := by
        simp [ctxsPref, xk, idx]
      let prev : (Fin d → Bool) → ℝ × List ((Fin d → ℝ) × ℝ) :=
        fun c => tradeTrajectory broker (priorSellerVec c) (priorBuyerVec c) ω m (ctxsPref m hm)
      let ell : (Fin d → Bool) → ℝ :=
        fun c =>
          let offer := broker.postOffer ω (prev c).2 xk
          tradeRoundLoss (priorSellerVec c) (priorBuyerVec c) xk offer.1 offer.2
      have h_unfold : ∀ c : Fin d → Bool,
          (tradeTrajectory broker (priorSellerVec c) (priorBuyerVec c) ω (m + 1) (ctxsPref (m + 1) hk')).1 =
            (prev c).1 + ell c := by
        intro c
        rw [h_traj_succ (priorSellerVec c) (priorBuyerVec c) ω m (ctxsPref (m + 1) hk')]
        dsimp only
        rw [h_ctxs_eq, h_xm]
      simp_rw [h_unfold]
      rw [Finset.sum_add_distrib]
      let flip : (Fin d → Bool) → (Fin d → Bool) := fun c => Function.update c idx (!c idx)
      have hflip_invol : Function.Involutive flip := by
        intro c
        ext j
        by_cases hj : j = idx <;> simp [flip, hj]
      have hsum_flip : (∑ c : Fin d → Bool, ell (flip c)) = ∑ c : Fin d → Bool, ell c := by
        exact Equiv.sum_comp hflip_invol.toPerm ell
      have hpair_ge : ∀ c : Fin d → Bool, 1 / (3 * Real.sqrt d) ≤ ell c + ell (flip c) := by
        intro c
        have hprev_flip : prev (flip c) = prev c := by
          apply h_pref_congr ω m hm (flip c) c
          intros j hj
          have hj_ne : j ≠ idx := by
            intro h_eq
            have : j.val = m := congrArg Fin.val h_eq
            omega
          exact Function.update_of_ne hj_ne (!c idx) c
        let offer := broker.postOffer ω (prev c).2 xk
        have hpq : offer.1 ≤ offer.2 := broker.budget_balanced ω (prev c).2 xk
        have hell_c : ell c = tradeRoundLoss (priorSellerVec c) (priorBuyerVec c) xk offer.1 offer.2 := rfl
        have hell_flip : ell (flip c) =
            tradeRoundLoss (priorSellerVec (flip c)) (priorBuyerVec (flip c)) xk offer.1 offer.2 := by
          dsimp only [ell]
          rw [hprev_flip]
        rw [hell_c, hell_flip]
        cases hc : c idx
        · have hfc : flip c idx = true := by simp [flip, hc]
          exact h_pair_loss idx offer.1 offer.2 hpq c (flip c) hc hfc
        · have hfc : flip c idx = false := by simp [flip, hc]
          have := h_pair_loss idx offer.1 offer.2 hpq (flip c) c hfc hc
          linarith
      have h2sum : (2 ^ d : ℝ) * (1 / (3 * Real.sqrt d)) ≤ 2 * ∑ c : Fin d → Bool, ell c := by
        calc
          (2 ^ d : ℝ) * (1 / (3 * Real.sqrt d))
            = ∑ _c : Fin d → Bool, (1 / (3 * Real.sqrt d)) := by simp
          _ ≤ ∑ c : Fin d → Bool, (ell c + ell (flip c)) :=
            Finset.sum_le_sum (fun c _ => hpair_ge c)
          _ = (∑ c : Fin d → Bool, ell c) + (∑ c : Fin d → Bool, ell (flip c)) :=
            Finset.sum_add_distrib
          _ = 2 * ∑ c : Fin d → Bool, ell c := by
            rw [hsum_flip]
            ring
      have h_ell_sum : (2 ^ d : ℝ) * (1 / (6 * Real.sqrt d)) ≤ ∑ c : Fin d → Bool, ell c := by
        have : (2 ^ d : ℝ) * (1 / (3 * Real.sqrt d)) =
            2 * ((2 ^ d : ℝ) * (1 / (6 * Real.sqrt d))) := by
          field_simp
          ring
        linarith
      have h_ih := ih hm
      have h_alg : (2 ^ d : ℝ) * (((m + 1 : ℕ) : ℝ) / (6 * Real.sqrt d)) =
          (2 ^ d : ℝ) * ((m : ℝ) / (6 * Real.sqrt d)) +
          (2 ^ d : ℝ) * (1 / (6 * Real.sqrt d)) := by
        push_cast
        field_simp
      linarith

  let ctxs : Fin T → (Fin d → ℝ) :=
    fun t => if h : t.val < d then Pi.single ⟨t.val, h⟩ (1 : ℝ) else 0
  refine ⟨ctxs, ?_, h_norm_prior, ?_⟩
  · intro t
    dsimp only [ctxs]
    split_ifs with h
    · exact h_norm_single ⟨t.val, h⟩
    · exact h_norm_zero
  · have h_ctxs_restr : (fun i : Fin d => ctxs (Fin.castLE hT i)) = ctxsPref d (le_refl d) := by
      funext i
      simp [ctxs, ctxsPref]
    let R : (Fin d → Bool) → Ω → ℝ :=
      fun c ω => tradeCumulativeRegret broker (priorSellerVec c) (priorBuyerVec c) T ctxs ω
    let B : ℝ := Real.sqrt d / 6
    have h_sum_T : ∀ ω : Ω, (2 ^ d : ℝ) * B ≤ ∑ c : Fin d → Bool, R c ω := by
      intro ω
      have h_d := h_pref_sum ω d (le_refl d)
      have hd_alg : (d : ℝ) / (6 * Real.sqrt d) = B := by
        dsimp only [B]
        field_simp
        linarith [hsq_sqrt]
      rw [hd_alg] at h_d
      calc
        (2 ^ d : ℝ) * B
          ≤ ∑ c : Fin d → Bool,
              (tradeTrajectory broker (priorSellerVec c) (priorBuyerVec c) ω d (ctxsPref d (le_refl d))).1 := h_d
        _ ≤ ∑ c : Fin d → Bool, R c ω := by
          refine Finset.sum_le_sum fun c _ => ?_
          have hmono := h_regret_mono (priorSellerVec c) (priorBuyerVec c) ω T d hT ctxs
          rw [h_ctxs_restr] at hmono
          exact hmono
    let I : (Fin d → Bool) → ENNReal := fun c => ∫⁻ ω, ENNReal.ofReal (R c ω) ∂μ
    have h_sum_I : (2 ^ d : ENNReal) * ENNReal.ofReal B ≤ ∑ c : Fin d → Bool, I c := by
      have h_fubini : (∑ c : Fin d → Bool, I c) =
          ∫⁻ ω, (∑ c : Fin d → Bool, ENNReal.ofReal (R c ω)) ∂μ := by
        symm
        refine MeasureTheory.lintegral_finset_sum Finset.univ fun c _ => ?_
        exact (h_regret_meas (priorSellerVec c) (priorBuyerVec c) T ctxs).ennreal_ofReal
      rw [h_fubini]
      have h_ptwise : ∀ ω : Ω,
          (2 ^ d : ENNReal) * ENNReal.ofReal B ≤ ∑ c : Fin d → Bool, ENNReal.ofReal (R c ω) := by
        intro ω
        have h_ofReal_sum :
            (∑ c : Fin d → Bool, ENNReal.ofReal (R c ω)) =
              ENNReal.ofReal (∑ c : Fin d → Bool, R c ω) := by
          symm
          exact ENNReal.ofReal_sum_of_nonneg fun c _ =>
            h_regret_nonneg (priorSellerVec c) (priorBuyerVec c) T ctxs ω
        rw [h_ofReal_sum]
        calc
          (2 ^ d : ENNReal) * ENNReal.ofReal B
            = ENNReal.ofReal ((2 ^ d : ℝ) * B) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
          _ ≤ ENNReal.ofReal (∑ c : Fin d → Bool, R c ω) := ENNReal.ofReal_le_ofReal (h_sum_T ω)
      calc
        (2 ^ d : ENNReal) * ENNReal.ofReal B
          = ∫⁻ _ω, ((2 ^ d : ENNReal) * ENNReal.ofReal B) ∂μ := by
            simp [MeasureTheory.lintegral_const, MeasureTheory.measure_univ]
        _ ≤ ∫⁻ ω, (∑ c : Fin d → Bool, ENNReal.ofReal (R c ω)) ∂μ :=
          MeasureTheory.lintegral_mono h_ptwise
    constructor
    · have h2d_ne_zero : (2 ^ d : ENNReal) ≠ 0 := pow_ne_zero d two_ne_zero
      have h2d_ne_top : (2 ^ d : ENNReal) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
      calc
        (2 ^ d : ENNReal)⁻¹ * ∑ c : Fin d → Bool, I c
          ≥ (2 ^ d : ENNReal)⁻¹ * ((2 ^ d : ENNReal) * ENNReal.ofReal B) := by
            gcongr
        _ = ((2 ^ d : ENNReal)⁻¹ * (2 ^ d : ENNReal)) * ENNReal.ofReal B := by
            rw [mul_assoc]
        _ = ENNReal.ofReal B := by
            rw [ENNReal.inv_mul_cancel h2d_ne_zero h2d_ne_top, one_mul]
    · have h_exists_c : ∃ c : Fin d → Bool, I c ≥ ENNReal.ofReal B := by
        by_contra! h_lt
        have hB_ne_top : ENNReal.ofReal B ≠ ⊤ := ENNReal.ofReal_ne_top
        have hI_ne_top : ∀ c : Fin d → Bool, I c ≠ ⊤ := fun c =>
          ne_of_lt (lt_of_lt_of_le (h_lt c) (le_of_lt ENNReal.ofReal_lt_top))
        have h_nnreal_lt : ∀ c : Fin d → Bool, (I c).toNNReal < (ENNReal.ofReal B).toNNReal :=
          fun c => (ENNReal.toNNReal_lt_toNNReal (hI_ne_top c) hB_ne_top).mpr (h_lt c)
        have h_univ_nonempty : (Finset.univ : Finset (Fin d → Bool)).Nonempty :=
          ⟨fun _ => false, Finset.mem_univ _⟩
        have h_sum_nnreal_lt :
            ∑ c : Fin d → Bool, (I c).toNNReal <
              ∑ _c : Fin d → Bool, (ENNReal.ofReal B).toNNReal :=
          Finset.sum_lt_sum_of_nonempty h_univ_nonempty fun c _ => h_nnreal_lt c
        have h_coe_lt :
            ((∑ c : Fin d → Bool, (I c).toNNReal : NNReal) : ENNReal) <
              ((∑ _c : Fin d → Bool, (ENNReal.ofReal B).toNNReal : NNReal) : ENNReal) :=
          ENNReal.coe_lt_coe.mpr h_sum_nnreal_lt
        rw [ENNReal.coe_finset_sum, ENNReal.coe_finset_sum] at h_coe_lt
        have h_lhs : (∑ c : Fin d → Bool, ((I c).toNNReal : ENNReal)) = ∑ c : Fin d → Bool, I c := by
          refine Finset.sum_congr rfl fun c _ => ENNReal.coe_toNNReal (hI_ne_top c)
        have h_rhs : (∑ _c : Fin d → Bool, ((ENNReal.ofReal B).toNNReal : ENNReal)) =
            (2 ^ d : ENNReal) * ENNReal.ofReal B := by
          rw [ENNReal.coe_toNNReal hB_ne_top]
          simp
        rw [h_lhs, h_rhs] at h_coe_lt
        exact not_lt_of_ge h_sum_I h_coe_lt
      obtain ⟨c, hc⟩ := h_exists_c
      exact ⟨priorSellerVec c, priorBuyerVec c, (h_norm_prior c).1, (h_norm_prior c).2, hc⟩

/-- Under the uniform coordinate prior `π = unifBoolPrior d` of Proposition E.2 (`d ≥ 1`),
both marginal covariances equal `(1 / (9 d)) I_d` and the trace-square-root potential satisfies
`Ψ_tr(π) = 2 √d / 3` (Appendix E, remark following Proposition E.2). -/
theorem prop_trade_lower_bound_potential (d : ℕ) (hd : 0 < d) :
    let π := unifBoolPrior d
    rvCovMat priorSellerVec π = (1 / (9 * (d : ℝ))) • (1 : Matrix (Fin d) (Fin d) ℝ) ∧
    rvCovMat priorBuyerVec π = (1 / (9 * (d : ℝ))) • (1 : Matrix (Fin d) (Fin d) ℝ) ∧
    tradeBayesPotential priorSellerVec priorBuyerVec π = 2 * Real.sqrt d / 3 := by
  dsimp only
  set π := unifBoolPrior d
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
  have hsq_sqrt : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
  set α : ℝ := 1 / (3 * Real.sqrt d)
  have hα_pos : 0 < α := by positivity
  have hα_sq : α ^ 2 = 1 / (9 * (d : ℝ)) := by
    dsimp [α]
    rw [div_pow, mul_pow, hsq_sqrt]
    ring

  -- Expectation under `unifBoolPrior d` is the normalized finite sum over `Fin d → Bool`
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
        have hfj : sgn (flip c) j = -sgn c j := by cases hc : c j <;> simp [sgn, flip, hc]
        simp only [sgn, hfi] at hfj ⊢
        cases hc : c j <;> simp [sgn, flip, hc]
      simp_rw [h_neg, Finset.sum_neg_distrib] at h_eq
      linarith

  -- Express both seller and buyer vectors in terms of `sgn`
  have hS_decomp : ∀ (c : Fin d → Bool) (i : Fin d),
      priorSellerVec c i = α + α * sgn c i := by
    intro c i
    dsimp [priorSellerVec, sgn, α]
    cases c i <;> simp <;> field_simp <;> ring

  have hB_decomp : ∀ (c : Fin d → Bool) (i : Fin d),
      priorBuyerVec c i = 2 * α + α * sgn c i := by
    intro c i
    dsimp [priorBuyerVec, sgn, α]
    cases c i <;> simp <;> field_simp <;> ring

  have h2d_ne0_real : (2 ^ d : ℝ) ≠ 0 := pow_ne_zero d (by norm_num)

  have h_cov_calc : ∀ (W : (Fin d → Bool) → Fin d → ℝ) (m₀ : ℝ),
      (∀ c i, W c i = m₀ + α * sgn c i) →
      rvCovMat W π = (1 / (9 * (d : ℝ))) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    intro W m₀ hW
    have hW_meas : ∀ i : Fin d, Measurable (fun c => W c i) := fun i => by
      have h_fn : (fun c => W c i) = fun c => m₀ + α * sgn c i := funext fun c => hW c i
      rw [h_fn]
      exact measurable_const.add (measurable_const.mul (hsgn_meas i))
    have h_mean : ∀ i : Fin d, rvMeanVec W π i = m₀ := fun i => by
      change (∫ c, W c i ∂π) = m₀
      rw [h_int (fun c => W c i) (hW_meas i)]
      have h_sum : (∑ c : Fin d → Bool, W c i) = (2 ^ d : ℝ) * m₀ := by
        simp_rw [hW]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, h_sum_sgn_zero i, mul_zero, add_zero]
        simp
      rw [h_sum, inv_mul_cancel_left₀ h2d_ne0_real]
    ext i j
    simp only [rvCovMat, Matrix.of_apply, h_mean, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have h_prod_fn : (fun c : Fin d → Bool => (W c i - m₀) * (W c j - m₀)) =
        fun c => α ^ 2 * (sgn c i * sgn c j) := by
      ext c; rw [hW c i, hW c j]; ring
    have h_prod_meas : Measurable (fun c : Fin d → Bool => α ^ 2 * (sgn c i * sgn c j)) :=
      measurable_const.mul ((hsgn_meas i).mul (hsgn_meas j))
    rw [h_prod_fn, h_int _ h_prod_meas, ← Finset.mul_sum, h_sum_sgn_prod i j, hα_sq]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      field_simp
    · simp [hij]

  have hCovS := h_cov_calc priorSellerVec α hS_decomp
  have hCovB := h_cov_calc priorBuyerVec (2 * α) hB_decomp

  -- Evaluate `psdTraceSqrt ((α ^ 2) • 1) = d * α`
  have h_tr_sqrt : psdTraceSqrt ((1 / (9 * (d : ℝ))) • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      Real.sqrt d / 3 := by
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

  refine ⟨hCovS, hCovB, ?_⟩
  unfold tradeBayesPotential
  rw [hCovS, hCovB, h_tr_sqrt]
  ring

/-- Potential-normalized Bayesian lower bound (Appendix E, remark following Proposition E.2):
for every `d ≥ 1`, `T ≥ d`, and per-round budget-balanced randomized broker, the uniform
coordinate prior `π = unifBoolPrior d` is supported on `K = B_2^d × B_2^d` and forces Bayesian
expected regret at least `Ψ_tr(π) / 4`. -/
theorem cor_trade_lower_bound_potential (d T : ℕ) (hd : 0 < d) (hT : d ≤ T)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (broker : BudgetBalancedBroker d Ω) :
    let π := unifBoolPrior d
    ∃ ctxs : Fin T → (Fin d → ℝ),
      (∀ t : Fin T, vecL2Norm (ctxs t) ≤ 1) ∧
      (∀ choice : Fin d → Bool,
        vecL2Norm (priorSellerVec choice) ≤ 1 ∧ vecL2Norm (priorBuyerVec choice) ≤ 1) ∧
      ((2 ^ d : ENNReal)⁻¹ *
          ∑ choice : Fin d → Bool,
            ∫⁻ ω, ENNReal.ofReal
              (tradeCumulativeRegret broker (priorSellerVec choice) (priorBuyerVec choice) T ctxs ω) ∂μ ≥
        ENNReal.ofReal (tradeBayesPotential priorSellerVec priorBuyerVec π / 4)) := by
  dsimp only
  obtain ⟨ctxs, h_norm, h_supp, h_avg, _⟩ := prop_trade_lower_bound d T hd hT μ broker
  have h_pot : tradeBayesPotential priorSellerVec priorBuyerVec (unifBoolPrior d) =
      2 * Real.sqrt d / 3 := (prop_trade_lower_bound_potential d hd).2.2
  have h_eq : tradeBayesPotential priorSellerVec priorBuyerVec (unifBoolPrior d) / 4 =
      Real.sqrt d / 6 := by
    rw [h_pot]
    ring
  refine ⟨ctxs, h_norm, h_supp, ?_⟩
  rwa [h_eq]

end TraceSqrt
